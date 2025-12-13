import Init.Meta
import Parser
import Regex.Syntax.Flavor
import Regex.Data.Parsec.Basic

open Lean Lean.Syntax Parser Parser.Char

/-! Parse a regular expressions into a `Lean.Syntax` tree according to the `Syntax.Flavor`.
-/
namespace Regex.Grammar

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#internaloptions -/
inductive ExtendedKind where
    | None
    | Extended
    | ExtendedMore
deriving BEq, Repr

/-- State of the parser -/
private structure Parser where
   /-- Flag `x` or 'xx'  -/
  extended : ExtendedKind

instance : Inhabited Parser  := ⟨⟨.None⟩⟩

abbrev ParsecM := ReaderT Syntax.Flavor $ StateT Parser (SimpleParser Substring.Raw Char)

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC4 -/
private def isMetaCharacter : Char → Bool
  | '\\' | '^' | '$' | '.' | '[' | '|' | '(' | ')' | '*' | '+' | '?' | '{' => true
  | _ => false

private def isMetaCharacterInCharacterClass : Char → Bool
  | '-' | ']' => true
  | _ => false

private def mkLiteral (c : Char) (f t : String.Pos.Raw) : Syntax :=
  mkLit `literal (String.ofList [c]) (SourceInfo.synthetic f t)

private def mkNodeOfKind (kind : SyntaxNodeKind) (s : String) (f t : String.Pos.Raw) : Syntax :=
  mkLit kind s (SourceInfo.synthetic f t)

private def mkBackRefOrLiteral (b : String) (c : Char) (f t : String.Pos.Raw) : Syntax :=
  Syntax.node (SourceInfo.synthetic f t) `backReferenceNumberOrLiteral #[
      Syntax.atom .none b,
      Syntax.atom .none (String.ofList [c])
  ]

private def consumeChar? (c : Char ): ParsecM $ Option Syntax := attemptM do
  Parser.tryCharWithPosMap (· = c) mkLiteral

private def literal (inCharacterClass : Bool := false) : ParsecM Syntax := attemptM do
  let (f, t, c) ← Parser.withPos anyToken
  if inCharacterClass && !isMetaCharacterInCharacterClass c then
    pure $ mkLiteral c f t
  else if !inCharacterClass && !isMetaCharacter c then
    pure $ mkLiteral c f t
  else
    fail "invalid literal character"

private def isWsChar (c : Char) (inCharacterClass : Bool) : Bool :=
  if inCharacterClass then c = '\x09' || c = ' '
  else c = '\x09' || c = '\x0a' || c = '\x0b' || c = '\x0c' || c = '\x0d' || c = ' '

private def wsChar (inCharacterClass : Bool) : (SimpleParser Substring.Raw Char) Char := withBacktracking do
  let c ← anyToken
  if isWsChar c inCharacterClass then return c else fail ""

private def wsChars (inCharacterClass : Bool) : ParsecM Syntax := attemptM do
  let state ← get
  if inCharacterClass && state.extended == ExtendedKind.ExtendedMore
      || !inCharacterClass && state.extended != ExtendedKind.None
  then
    let (f, t, chars) ← withPos (manyChars (wsChar inCharacterClass))
    if chars.length > 0  then
      pure $ mkNodeOfKind `whitespace chars f t
    else fail ""
  else fail ""

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC24 -/
private def comments : ParsecM Syntax := attemptM do
  let state ← get
  if state.extended == ExtendedKind.Extended
  then
    if let some _ ← tryChar (· = '#') then
      if ← testChar (· = '\n') then
        let (f, t, _) ← withPos $ skipChar '\n'
        pure $ mkNodeOfKind `comment "" f t
      else
        let (f, t, chars) ← withPos $ manyChars (notFollowedBy (Char.char '\n') *> anyToken) <* skipChar? '\n'
        if chars.length > 0  then
          pure $ mkNodeOfKind `comment chars f t
        else fail ""
    else fail ""
  else fail ""

private def skipCommentsAndWsChars : ParsecM Unit := do
  let _ ← manyM (comments <|> wsChars false)
  pure ()

private def toControlChar  (c : Char) (f t : String.Pos.Raw) : ParsecM Syntax := do
  let val ←
    if c.isUpper then pure (c.val - 'A'.val + 1)
    else if c.isLower then pure (c.val - 'a'.val + 1)
    else if c.val ≥ 32 && c.val ≤ 64 then pure (c.val - 32 + 96)
    else if c.val ≥ 91 && c.val ≤ 96 then pure (c.val - 91 + 27)
    else fail "invalid control character"

  if h : UInt32.isValidChar val
  then pure $ mkLiteral ⟨val, h⟩ f t
  else fail "invalid control character"

private def controlChar : ParsecM Syntax := do
  let (f, t, c) ← withPos anyToken
  toControlChar c f t

private def isHexChar (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9' || 'a' ≤ c ∧ c ≤ 'f' || 'A' ≤ c ∧ c ≤ 'F'

private def hexCharToNat (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    c.val.toNat - '0'.val.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then
    c.val.toNat - 'a'.val.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then
    c.val.toNat - 'A'.val.toNat + 10
  else
    0

private def hexChar : ParsecM Nat := attemptM do
  if let some c ← tryChar isHexChar then pure $ hexCharToNat c
  else fail "invalid hex character"

private def isOctChar (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '7'

private def octCharToNat (c : Char) : Nat :=
  if isOctChar c then c.val.toNat - '0'.val.toNat else 0

private def octCharToNat' (c : Char) : Char × Nat :=
  if isOctChar c then (c, c.val.toNat - '0'.val.toNat) else (c, 0)

private def octChar : ParsecM Nat := attemptM do
  if let some c ← tryChar isOctChar then pure $ octCharToNat c
  else fail "invalid octal character"

private def octChar' : ParsecM $ Char × Nat := attemptM do
  if let some c ← tryChar isOctChar then pure $ octCharToNat' c
  else fail "invalid octal character"

private def decodeDigits (l : List Nat) (base : Nat) : Char :=
  let (_, val) := l |> List.foldr (init := (1, 0)) (fun v (n, acc)  =>
    (n*base, acc + n*v))
  Char.ofNat val

private def parenWithCharsM (p : ParsecM α) (startChar : Char := '{') (endChar : Char := '}')
    : ParsecM $ Array α := attemptM do
  skipChar startChar *> manyM p <* skipChar endChar

private def groupLetter : (SimpleParser Substring.Raw Char) Char := Parser.withBacktracking do
  let c ← anyToken
  if (c = ' ' ∨ ('0' ≤ c ∧ c ≤ '9')
      ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z'))
      then return c else fail s!"ASCII letter expected"

private def verticalBar : ParsecM Syntax := attemptM do
  let (f, t, c) ← withPos $ Char.char '|'
  pure $ mkNodeOfKind `verticalBar (String.ofList [c]) f t

private def dot : ParsecM Syntax := attemptM do
  let (f, t, c) ← withPos $ Char.char '.'
  pure $ mkNodeOfKind `dot (String.ofList [c]) f t

private def hyphen : ParsecM Syntax := attemptM do
  let (f, t, c) ← withPos $ Char.char '-'
  pure $ mkNodeOfKind `hyphen (String.ofList [c]) f t

private def characterClassSetOperation : ParsecM Syntax := do
  if Syntax.Flavor.Rust == (← read) then attemptM do
    if let some (f, _, c1) ← tryCharWithPos (· = '&') then
      let (_, t, c2) ← withPos $ Char.char '&'
      pure $ mkNodeOfKind `characterClassSetOperation (String.ofList [c1, c2]) f t
    else if let some (f, _, c1) ← tryCharWithPos (· = '-') then
      let (_, t, c2) ← withPos $ Char.char '-'
      pure $ mkNodeOfKind `characterClassSetOperation (String.ofList [c1, c2]) f t
    else if let some (f, _, c1) ← tryCharWithPos (· = '~') then
      let (_, t, c2) ← withPos $ Char.char '~'
      pure $ mkNodeOfKind `characterClassSetOperation (String.ofList [c1, c2]) f t
    else fail ""
  else fail ""

private def assertion : ParsecM Syntax := attemptM do
  if let some (f, t, c) ← tryCharWithPos (fun c => c = '^' || c = '$') then
    pure $ mkNodeOfKind `simpleAssertion (String.ofList [c]) f t
  else fail ""

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC16 -/
private def groupName : ParsecM String := do
  let takeName (c : Char): ParsecM String :=
    manyChars (notFollowedBy (Char.char c) *> groupLetter) <* skipChar c

  if ← trySkipChar (·  = '<') then takeName '>'
  else if ← trySkipChar (·  = '\'') then takeName '\''
  else if (← trySkipChar (·  = 'P')) && (← trySkipChar (·  = '<')) then takeName '>'
  else pure ""

private def capturingGroupKind : ParsecM Syntax := attemptM do
  let (f, _, _) ← withPos (Char.char ('?'))
  if ← testChar (fun c1 => c1 = '<' || c1 = '\'' || c1 = 'P') then
    let (_, t, name) ← withPosM (groupName (← read))
    pure $ mkNodeOfKind `capturingGroup name f t
  else fail "invalid capturing group character"

private def atomicGroupKind : ParsecM Syntax := attemptM do
  let (f, _, _) ← withPos (Char.char ('?'))
  if let some (_, t, _) ← tryCharWithPos (· = '>') then
    pure $ mkNodeOfKind `atomicGroup "" f t
  else fail "invalid capturing group character"

private def lookaroundGroupKind : ParsecM Syntax := attemptM do
  let (f, _, c) ← withPos (Char.char ('?'))
  if let some (_, t, c1) ← tryCharWithPos (fun c1 => c1 = '=' || c1 = '!') then
      pure $ mkNodeOfKind `lookaroundGroup (String.ofList [c, c1]) f t
  else if let some (_, _, c1) ← tryCharWithPos (· = '<') then
      if let some (_, t, c2) ← tryCharWithPos (fun x => x = '=' || x  = '!') then
        pure $ mkNodeOfKind `lookaroundGroup (String.ofList [c, c1, c2]) f t
      else fail "lookaround char expected"
  else fail "lookaround char expected"

private def defineGroupKind : ParsecM Syntax := attemptM do
  let (f, t, _) ← withPos (Char.char ('?'))
  skipString "(DEFINE)" *> (pure $ mkNodeOfKind `controlVerbGroup "" f t)

private def subroutineGroupKind : ParsecM Syntax := attemptM do
  let (f, t, _) ← withPos (Char.char ('?'))
  let c1 ← peekChar
  if c1 = '?' || c1 = '&' || c1 = '(' || c1 = 'P' || c1 = '|' || c1.isDigit then
    let chars ← manyChars (notFollowedBy (Char.char ')') *> groupLetter)
    pure $ mkNodeOfKind `subroutineGroupKind (String.ofList chars.toList)  f t
  else if c1 = '-' then
    skipAnyChar
    let chars ← many1Chars (notFollowedBy (Char.char ')') *> Char.ASCII.numeric)
    pure $ mkNodeOfKind `subroutineGroupKind (String.ofList ([c1] ++ chars.toList))  f t
  else fail ""

private def commentGroupKind : ParsecM Syntax := attemptM do
  let (f, t, _) ← withPos (Char.char ('?'))
  skipChar '#'
  let chars ← manyChars (notFollowedBy (Char.char ')') *> anyToken)
  pure $ mkNodeOfKind `commentGroupKind (String.ofList chars.toList)  f t

private def namedLookaroundGroupKind : ParsecM Syntax := attemptM do
  let (f, t, _) ← withPos (Char.char ('*'))
  skipString "pla:" *> (pure $ mkNodeOfKind `lookaroundGroup "?=" f t)
  <|> skipString "nla:" *> (pure $ mkNodeOfKind `lookaroundGroup "?!"  f t)
  <|> skipString "plb:" *> (pure $ mkNodeOfKind `lookaroundGroup "?<=" f t)
  <|> skipString "nlb:" *> (pure $ mkNodeOfKind `lookaroundGroup "?<!" f t)

private def controlName : (SimpleParser Substring.Raw Char) Syntax := withBacktracking do
  if let some (f, t, _) ← tryCharWithPos (· = ':') then
    let chars ← manyChars (Char.ASCII.alphanum <|> Char.char '(')
    pure $ mkNodeOfKind `controlName (String.ofList chars.toList)  f t
  else pure $ mkNodeOfKind `controlName ""  0 0

private def controlVerbGroupKind : ParsecM Syntax := attemptM do
  let (f, t, _) ← withPos (Char.char ('*'))
  (string "ACCEPT" <|> string "COMMIT" <|> string "MARK"<|> string "PRUNE"
      <|> string "SKIP" <|> string "THEN")
    *> controlName *> (pure $ mkNodeOfKind `controlVerbGroup "" f t)
  <|> controlName

private def containsString (s m : String) : Bool :=
  let arr := s.splitOn m
  arr.length >= 2

private def toExtendedKind (flags : String) : ExtendedKind :=
  if flags.contains '-' && flags.contains 'x'
    && flags.find (· = '-') < flags.find (· = 'x') then .None
  else if containsString flags "xx" then .ExtendedMore
  else if flags.contains 'x' then .Extended
  else .None

private def expandFlags (flags : String) : String :=
  match flags.toList with
  | '^' :: tail =>
    let flagsPos := "imsx".toList |> List.filter (fun c => tail.contains c)
    let flagsNeg := "imsx".toList |> List.filter (fun c => !tail.contains c)
    (String.ofList flagsPos) ++ "-" ++ (String.ofList flagsNeg)
  | _ => flags

private def nonCapturingGroupKind : ParsecM Syntax := attemptM do
  let (f, t, _) ← withPos (Char.char ('?'))
  let flags ← manyChars
    (notFollowedBy (Char.char ':' <|> Char.char ')') *> (Char.ASCII.alphanum <|> Char.char '-' <|> Char.char '^')) <* skipChar? ':'

  let flags := expandFlags flags
  if flags.length > 0 then
    let state ← get
    set {state with extended := toExtendedKind flags}

  pure $ mkNodeOfKind `nonCapturingGroup flags f t

private def groupKind : ParsecM Syntax := do
  if ← testChar (· = '?')
  then atomicGroupKind <|> subroutineGroupKind <|> capturingGroupKind
                  <|> lookaroundGroupKind <|> commentGroupKind
                  <|> nonCapturingGroupKind <|> defineGroupKind

  else if ← testChar (· = '*') then (namedLookaroundGroupKind <|> controlVerbGroupKind)
  else pure $ mkLit `capturingGroup "" (SourceInfo.none)

namespace EscapeSeq

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC5 -/
private def hexChars (f t : String.Pos.Raw): ParsecM Syntax := attemptM do
  if let some (_, t, arr) ← tryCharThenPWithPosM (· = '{') (parenWithCharsM hexChar) then
    pure $ mkLiteral (decodeDigits arr.toList 16) f t
  else if let some (_, t, u1) ← tryCharThenPWithPosM isHexChar hexChar then
    if let some (_, t, u2) ← tryCharThenPWithPosM isHexChar hexChar  then
        pure $ mkLiteral (decodeDigits [u1, u2] 16) f t
    else pure $ mkLiteral (decodeDigits [u1] 16) f t
  else pure $ mkLiteral (decodeDigits [0] 16) f t

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC5 -/
private def octChars (inCharacterClass : Bool) (c : Char) (u1 : Nat) (f t : String.Pos.Raw)
    : ParsecM Syntax := attemptM do
  if let some (_, _, (c2, u2)) ← tryCharThenPWithPosM isOctChar octChar' then
    if let some (_, _, u3) ← tryCharThenPWithPosM isOctChar octChar then
      pure $ mkLiteral (decodeDigits [u1, u2, u3] 8) f t
    else
      if inCharacterClass || (u1 = 0 && u2 = 0)
      then pure $ mkLiteral (decodeDigits [u1, u2] 8) f t
      else pure $ mkBackRefOrLiteral (String.ofList [c, c2]) (decodeDigits [u1, u2] 8) f t
  else if inCharacterClass || c = '0' then
    if h : UInt32.isValidChar u1.toUInt32 then
      pure $ mkLiteral ⟨u1.toUInt32, h⟩ f t
    else fail ""
  else pure $ mkNodeOfKind `backReferenceNumber (String.ofList [c]) f t

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC5 -/
private def nonPrintingChar (inCharacterClass : Bool := false) : ParsecM Syntax := attemptM do
  let (f, t, c) ← withPos anyToken
  if c = 'a' then pure $ mkLiteral '\x07' f t
  else if c = 'a' then pure $ mkLiteral '\x07' f t
  else if c = 'c' then controlChar
  else if c = 'e' then pure $ mkLiteral '\x1b' f t
  else if c = 'E' then pure $ mkNodeOfKind `endQuote (String.ofList [c]) f t
  else if c = 'f' then pure $ mkLiteral '\x0c' f t
  else if c = 'n' then pure $ mkLiteral '\x0a' f t
  else if c = 'r' then pure $ mkLiteral '\x0d' f t
  else if c = 't' then pure $ mkLiteral '\x09' f t
  else if c = 'o' then
    let (_, t, arr) ← withPosM (parenWithCharsM octChar)
    pure $ mkLiteral (decodeDigits arr.toList 8) f t
  else if c = 'x' then hexChars f t
  else if isOctChar c then octChars inCharacterClass c (octCharToNat c) f t
  else fail "fail nonPrintingChar"

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC19 -/
private def backReference : ParsecM Syntax := attemptM do
  if let some (f, t, c) ← tryCharWithPos Char.isDigit then
    pure $ mkNodeOfKind `backReferenceNumber (String.ofList [c]) f t
  else if let some _ ← tryCharWithPos (· = 'g') then
    if ← testChar (· = '{') then
      let (f, t, chars) ← withPosM $ (parenWithCharsM (Parser.coeSimpleParser.coe (groupLetter <|> char '-')))

      let kind := if Array.all chars (fun c => c.isDigit || c = '-')
                  then `backReferenceNumber
                  else `backReferenceName
      pure $ mkNodeOfKind kind (String.ofList chars.toList) f t
    else if let some (f, _, cm) ← tryCharWithPos (· = '-') then
      if let some (_, t, c) ← tryCharWithPos Char.isDigit then
        pure $ mkNodeOfKind `backReferenceNumber (String.ofList [cm, c]) f t
      else fail ""
    else if let some (f, t, c) ← tryCharWithPos Char.isDigit then
      pure $ mkNodeOfKind `backReferenceNumber (String.ofList [c]) f t
    else fail ""
  else if let some _ ← tryCharWithPos (· = 'k') then
    if ← testChar (· = '<') then
      let (f, t, chars) ← withPosM $ parenWithCharsM groupLetter '<' '>'
      let kind := `backReferenceName
      pure $ mkNodeOfKind kind (String.ofList chars.toList) f t
    else fail ""
  else fail ""

private def genericCharacterType : ParsecM Syntax := attemptM do
  let (f, t, c) ← withPos anyToken
  if c = 'd' || c = 'D' || c = 'h' || c = 'H' || c = 'N' || c = 's' || c = 'S'
     || c = 'v' || c = 'V' || c = 'w' || c = 'W'
  then pure $ mkNodeOfKind `genericCharacterType (String.ofList [c]) f t
  else fail ""

private def simpleAssertion (inCharacterClass : Bool := false) : ParsecM Syntax := attemptM do
  let (f, t, c) ← withPos anyToken
  if c = 'b' && inCharacterClass then pure $ mkLiteral ⟨8, by simp +arith +decide⟩ f t
  else if (← read) == Syntax.Flavor.Rust && (← testChar (c = 'b' && · = '{')) then
    let (_, t, chars) ← withPosM (parenWithCharsM (Parser.coeSimpleParser.coe (Char.ASCII.alphanum <|> char '-')))
    let s := String.ofList chars.toList
    if s = "start" || s = "end" || s = "start-half" || s = "end-half"
    then pure $ mkNodeOfKind `simpleAssertion s f t
    else fail ""
  else if c = 'b' || c = 'B' || c = 'A' || c = 'Z' || c = 'z' || c = 'G' || c = 'K' then
    pure $ mkNodeOfKind `simpleAssertion (String.ofList [c]) f t
  else fail ""

private def unicodeCharacterProperty : ParsecM Syntax := attemptM do
  let name := manyChars (groupLetter <|> Char.char '_')
  if let some c ← tryChar (fun c => c = 'p' || c = 'P') then
    let kind := if c = 'p' then `unicodeCharacterProperty else `unicodeCharacterPropertyNegated
    if ← trySkipChar (· = '{') then
      let (f, t, chars) ← withPos $ name
      if ← trySkipChar (· = '=') then
        let (_, t2, chars2) ← withPos $ name
        skipChar '}'
        pure $
          Syntax.node (SourceInfo.synthetic f t2) kind #[
              Syntax.atom .none chars,
              Syntax.atom .none "=",
              Syntax.atom .none chars2
          ]
      else
        skipChar '}'
        pure $ Syntax.node (SourceInfo.synthetic f t) kind #[Syntax.atom .none chars]
    else
      let (f, t, c) ← withPos Char.ASCII.alphanum
      pure $ Syntax.node (SourceInfo.synthetic f t) kind #[Syntax.atom .none (String.ofList [c])]
  else fail ""

private def escapedChar : ParsecM Syntax := attemptM do
  let (f, t, c) ← withPos anyToken
  pure $ mkLiteral c f t

private def literalChars : ParsecM Syntax := attemptM do
  skipChar 'Q'
  let chars ← manyChars (notFollowedBy (string "\\E") *> anyToken) <* skipString? "\\E"
  let list := chars.toList |> List.map (fun c => mkLiteral c 0 0)
  pure $ Syntax.node (SourceInfo.synthetic 0 0) `sequence list.toArray

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC5 -/
private def escapeSeq (inCharacterClass : Bool := false) : ParsecM Syntax := attemptM do
  let c ← peekChar
  if c = '\\' then
    skipChar c
    literalChars <|> nonPrintingChar inCharacterClass
          <|> (if !inCharacterClass then backReference else fail "")
          <|> simpleAssertion inCharacterClass
          <|> genericCharacterType   <|> unicodeCharacterProperty
          <|> escapedChar
  else fail ""

end EscapeSeq

private def repetitionModifier : ParsecM Syntax := do
  skipCommentsAndWsChars
  match ← peekChar? with
  | some c =>
    if c = '+' || c = '?'
    then skipChar c; pure $ mkLit `repetitionModifier (String.ofList [c]) SourceInfo.none
    else pure $ mkLit `repetitionModifier "" SourceInfo.none
  | none => pure $ mkLit `repetitionModifier "" SourceInfo.none

private def toRepetitionLeft (s : String) : Syntax :=
   mkLit `repetitionLeft s SourceInfo.none

private def toRepetitionRight (s : String) : Syntax :=
   mkLit `repetitionRight s SourceInfo.none

private def repetitionContent : ParsecM Syntax := attemptM do
  ws
  let c ← peekChar
  if c = ',' then
    let (f, _, _) ← withPos $ skipChar ','
    ws
    let c ← peekChar
    if c = '}' then fail "'}' unexpected"
    else
      ws
      let b ← manyChars Char.ASCII.numeric
      let litA := toRepetitionLeft ""
      let litB := toRepetitionRight b
      ws
      let (_, t, _) ← withPos (Char.char ('}'))
      let modifier ← repetitionModifier
      pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]
  else
    let (f, _, a) ← withPos $ manyChars Char.ASCII.numeric
    ws
    let litA := toRepetitionLeft a
    let c ← peekChar
    if c = '}' then
      let (_, t, _) ← withPos (Char.char ('}'))
      let litB := toRepetitionRight a
      let modifier ← repetitionModifier
      pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]
    else
      skipChar ','
      ws
      let b ← manyChars Char.ASCII.numeric
      ws
      let litB := toRepetitionRight b
      let (_, t, _) ← withPos (Char.char ('}'))
      let modifier ← repetitionModifier
      pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC17 -/
private def repetition : ParsecM Syntax := attemptM do
  skipCommentsAndWsChars
  let c ← peekChar
  if c = '{' then
    let (f, t, _) ← withPos (Char.char ('{'))
    if let some (f1, t1, _) ← tryCharWithPos (· = '}')
    then
      pure $ Syntax.node (SourceInfo.synthetic f t1) `sequence #[
          mkLiteral '{' f t,
          mkLiteral '}' f1 t1
      ]
    else
      repetitionContent <|> (pure $ mkLiteral c f t)
  else if c = '*' then
    let (f, t, _) ← withPos (Char.char ('*'))
    let litA := toRepetitionLeft "0"
    let litB := toRepetitionRight ""
    let modifier ← repetitionModifier
    pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]
  else if c = '+' then
    let (f, t, _) ← withPos (Char.char ('+'))
    let litA := toRepetitionLeft "1"
    let litB := toRepetitionRight ""
    let modifier ← repetitionModifier
    pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]
  else if c = '?' then
    let (f, t, _) ← withPos (Char.char ('?'))
    let litA := toRepetitionLeft "0"
    let litB := toRepetitionRight "1"
    let modifier ← repetitionModifier
    pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]
  else fail ""

private def posixCharacterClass : (SimpleParser Substring.Raw Char) Syntax := withBacktracking do
  let (f, _, _) ← withPos $ string "[:"
  let (_, t, chars) ← withPos $
      manyChars (notFollowedBy (string ":]") *> (Char.ASCII.alphanum <|> Char.char '^')) <* string ":]"
  pure $ mkNodeOfKind `posixCharacterClass chars f t

private def consumeStartOfCharacterClass : ParsecM $ Array Syntax := attemptM do
  if let some stx ← consumeChar? '^' then
    if let some stx' ← consumeChar? ']' then pure #[stx, stx']
    else pure #[stx]
  else if let some stx ← consumeChar? ']' then pure #[stx]
  else pure #[]

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC9 -/
private def characterClass (val : ParsecM Syntax) : ParsecM Syntax := attemptM do
  let (f, _, _) ← withPos (Char.char ('['))
  let start ← consumeStartOfCharacterClass
  let arr ← manyM (val (← read))
  let (_, t, _) ← withPos (Char.char (']'))
  pure $ Syntax.node (SourceInfo.synthetic f t) `characterClass (start ++ arr)

mutual

private partial def valInCharacterClass : ParsecM $ Syntax := do
  let p ← EscapeSeq.escapeSeq true
    <|> posixCharacterClass
    <|> wsChars true
    <|> (if Syntax.Flavor.Rust == (← read) then characterClass' else fail "")
    <|> characterClassSetOperation <|> hyphen
    <|> literal true
  pure $ p

private partial def characterClass' : ParsecM Syntax :=
  characterClass valInCharacterClass

end

private def getFlags (x : Syntax) : Option String :=
  match x with
  | Syntax.node _ `nonCapturingGroup #[Lean.Syntax.atom _ s] => some s
  | _ => none

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC14 -/
private def group (val : ParsecM Syntax) : ParsecM Syntax := attemptM do
  let state ← get
  let (f, _, _) ← withPos (Char.char ('('))
  let kind ← groupKind
  let arr ← manyM val
  let (_, t, _) ← withPos (Char.char (')'))

  let flags := Option.getD (getFlags kind) ""
  if arr.size =  0 then -- set state in outer group
    let state ← get
    set {state with extended := toExtendedKind flags}
  else set state -- set previous state

  pure $ Syntax.node (SourceInfo.synthetic f t) `group (#[kind] ++ arr)

private partial def val : ParsecM $ Syntax := do
  let p ← EscapeSeq.escapeSeq <|> (group val) <|> verticalBar <|> assertion
          <|> characterClass valInCharacterClass <|> repetition <|> comments
          <|> wsChars false <|> dot <|> literal
  pure $ p

private def sequence : ParsecM $ TSyntax `sequence := do
  let (f, t, arr) ← withPosM (manyM val)
  pure $ (TSyntax.mk (Syntax.node (SourceInfo.synthetic f t) `sequence arr))

/-- Parse a PCRE2 regular expressions into a `Lean.Syntax` tree. -/
def parse (s : String) (flavor : Syntax.Flavor) (extended : ExtendedKind := .None) : Except String $ TSyntax `sequence :=
  match (sequence flavor ⟨extended⟩) s with
  | Parser.Result.ok it res =>
      if Substring.Raw.bsize it = 0
      then Except.ok res.1
      else Except.error s!"offset {repr it}: cannot parse regex"
  | Parser.Result.error it err  => Except.error s!"offset {repr it}: {err}"
