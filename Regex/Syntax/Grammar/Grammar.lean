import Init.Meta
import Lean.Data.Parsec
import Regex.Syntax.Flavor

open Lean Lean.Parsec Lean.Syntax

/-! Parse a regular expressions into a `Lean.Syntax` tree according to the `Syntax.Flavor`.
-/
namespace Regex.Grammar

abbrev ParsecM (α : Type) := ReaderT Syntax.Flavor Parsec α

/-! Parsec Utils -/
namespace Utils

private def orElse (p : Parsec Syntax) (q : Unit → ParsecM Syntax) : ParsecM Syntax := do
  let flavor ← read
  Parsec.orElse p (fun () => q () flavor)

instance : HOrElse (Parsec Syntax) (ParsecM Syntax) (ParsecM Syntax) where
  hOrElse := orElse

private def attemptM (p : ParsecM α) : ParsecM α := do
  attempt (p (← read))

private def failM {α : Type} (msg : String) : ParsecM α :=
  fail msg

private def withPos (p : Parsec α) : Parsec (String.Pos × String.Pos × α) := fun it =>
  let pos := it.pos
  match p it with
  | .success rem a => .success rem (pos, rem.pos, a)
  | .error rem err => .error rem err

private def withPosM (p : ParsecM α) : ParsecM (String.Pos × String.Pos × α) := do
  withPos (p (← read))

private def withPosSkip : Parsec String.Pos := do
  let (_, t, _) ← withPos skip
  pure t

private def optSkipChar (c : Char) : Parsec Unit := do
  match ← peek? with
  | some c' => if c = c' then skip *> pure () else pure ()
  | none => pure ()

/-- exec `check` on current char -/
private def testChar (check : Char -> Bool) : Parsec Bool := do
  match ← peek? with
  | some c => if check c then pure true else pure false
  | none => pure false

/-- exec `check` on current char and consume char on success -/
private def tryChar (check : Char -> Bool) : Parsec $ Option Char := do
  match ← peek? with
  | some c => if check c then pure $ some (← anyChar) else pure none
  | none => pure none

/-- exec `check` on current char and skip char on success -/
private def trySkipChar (check : Char -> Bool) : Parsec Bool := do
  if let some _ ← tryChar check then pure true else pure false

/-- exec `check` on current char and then exec `f` on consumed char on success -/
private def tryCharThen (check : Char -> Bool) (f : Char → α) (msg : String := "") : Parsec α := do
  if let some c ← tryChar check then pure $ f c
  else fail msg

/-- exec `check` on current char and map `f` on consumed char on success -/
private def tryCharMap (check : Char -> Bool) (f : Char → α) : Parsec $ Option α := do
  if let some c ← tryChar check then pure $ f c
  else pure none

/-- exec `check` on current char and then exec `p` on success -/
private def tryCharThenPWithPos (check : Char -> Bool) (p : Parsec α)
    : Parsec $ Option (String.Pos × String.Pos × α) := do
  match ← peek? with
  | some c => if check c then pure $ some (← withPos p) else pure none
  | none => pure none

/-- exec `check` on current char and then exec `p` on success -/
private def tryCharThenPWithPosM (check : Char -> Bool) (p : ParsecM α)
    : ParsecM $ Option (String.Pos × String.Pos × α) := do
  let flavor ← read
  match ← peek? with
  | some c => if check c then pure $ some (← withPos (p flavor)) else pure none
  | none => pure none

private def tryCharWithPos (check : Char -> Bool) : Parsec $ Option (String.Pos × String.Pos × Char) := do
  tryCharThenPWithPos check anyChar

private def tryCharWithPosMap (check : Char -> Bool) (f : Char → String.Pos → String.Pos →α) : Parsec $ Option α := do
  if let some (p1, p2, c) ← tryCharWithPos check then pure $ f c p1 p2
  else pure none

end Utils

open Utils

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC4 -/
private def isMetaCharacter : Char → Bool
  | '\\' | '^' | '$' | '.' | '[' | '|' | '(' | ')' | '*' | '+' | '?' | '{' => true
  | _ => false

private def isMetaCharacterInCharacterClass : Char → Bool
  | '-' | ']' => true
  | _ => false

private def mkLiteral (c : Char) (f t : String.Pos) : Syntax :=
  mkLit `literal ⟨[c]⟩ (SourceInfo.synthetic f t)

private def mkNodeOfKind (kind : SyntaxNodeKind) (s : String) (f t : String.Pos) : Syntax :=
  mkLit kind s (SourceInfo.synthetic f t)

private def mkBackRefOrLiteral (b : String) (c : Char) (f t : String.Pos) : Syntax :=
  Syntax.node (SourceInfo.synthetic f t) `backReferenceNumberOrLiteral #[
      Syntax.atom .none b,
      Syntax.atom .none ⟨[c]⟩
  ]

private def consumeChar? (c : Char ): ParsecM $ Option Syntax := attempt do
  tryCharWithPosMap (· = c) mkLiteral

private def literal (inCharacterClass : Bool := false) : ParsecM Syntax := attempt do
  let (f, t, c) ← withPos anyChar
  if inCharacterClass && !isMetaCharacterInCharacterClass c then
    pure $ mkLiteral c f t
  else if !inCharacterClass && !isMetaCharacter c then
    pure $ mkLiteral c f t
  else
    fail "invalid literal character"

private def toControlChar  (c : Char) (f t : String.Pos) : ParsecM Syntax := do
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
  let (f, t, c) ← withPos anyChar
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

private def hexChar : ParsecM Nat := attempt do
  if let some c ← tryChar isHexChar then pure $ hexCharToNat c
  else fail "invalid hex character"

private def isOctChar (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '7'

private def octCharToNat (c : Char) : Nat :=
  if isOctChar c then c.val.toNat - '0'.val.toNat else 0

private def octCharToNat' (c : Char) : Char × Nat :=
  if isOctChar c then (c, c.val.toNat - '0'.val.toNat) else (c, 0)

private def octChar : ParsecM Nat := attempt do
  if let some c ← tryChar isOctChar then pure $ octCharToNat c
  else fail "invalid octal character"

private def octChar' : ParsecM $ Char × Nat := attempt do
  if let some c ← tryChar isOctChar then pure $ octCharToNat' c
  else fail "invalid octal character"

private def decodeDigits (l : List Nat) (base : Nat) : Char :=
  let (_, val) := l |> List.foldr (init := (1, 0)) (fun v (n, acc)  =>
    (n*base, acc + n*v))
  Char.ofNat val

private def parenWithChars (p : ParsecM α) (startChar : Char := '{') (endChar : Char := '}')
    : ParsecM $ Array α := attemptM do
  let _ ← pchar startChar
  let arr ← manyCore (p (← read)) #[]
  let _ ← pchar endChar
  pure arr

private def groupLetter : Parsec Char := attempt do
  let c ← anyChar
  if (c = ' ' ∨ ('0' ≤ c ∧ c ≤ '9')
      ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z'))
      then return c else fail s!"ASCII letter expected"

private def verticalBar : ParsecM Syntax := attempt do
  let (f, t, c) ← withPos $ pchar '|'
  pure $ mkNodeOfKind `verticalBar ⟨[c]⟩ f t

private def dot : ParsecM Syntax := attempt do
  let (f, t, c) ← withPos $ pchar '.'
  pure $ mkNodeOfKind `dot ⟨[c]⟩ f t

private def hyphen : ParsecM Syntax := attempt do
  let (f, t, c) ← withPos $ pchar '-'
  pure $ mkNodeOfKind `hyphen ⟨[c]⟩ f t

private def characterClassSetOperation : ParsecM Syntax := do
  if Syntax.Flavor.Rust == (← read) then attempt do
    if let some (f, _, c1) ← tryCharWithPos (· = '&') then
      let (_, t, c2) ← withPos $ pchar '&'
      pure $ mkNodeOfKind `characterClassSetOperation ⟨[c1, c2]⟩ f t
    else if let some (f, _, c1) ← tryCharWithPos (· = '-') then
      let (_, t, c2) ← withPos $ pchar '-'
      pure $ mkNodeOfKind `characterClassSetOperation ⟨[c1, c2]⟩ f t
    else if let some (f, _, c1) ← tryCharWithPos (· = '~') then
      let (_, t, c2) ← withPos $ pchar '~'
      pure $ mkNodeOfKind `characterClassSetOperation ⟨[c1, c2]⟩ f t
    else fail ""
  else fail ""

private def assertion : ParsecM Syntax := attempt do
  if let some (f, t, c) ← tryCharWithPos (fun c => c = '^' || c = '$') then
    pure $ mkNodeOfKind `simpleAssertion ⟨[c]⟩ f t
  else fail ""

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC16 -/
private def groupName : ParsecM String := do
  let takeName (c : Char): ParsecM String :=
    manyChars (notFollowedBy (pchar c) *> groupLetter) <* skipChar c

  if ← trySkipChar (·  = '<') then takeName '>'
  else if ← trySkipChar (·  = '\'') then takeName '\''
  else if (← trySkipChar (·  = 'P')) && (← trySkipChar (·  = '<')) then takeName '>'
  else pure ""

private def capturingGroupKind : ParsecM Syntax := attemptM do
  let (f, _, _) ← withPos (pchar ('?'))
  if ← testChar (fun c1 => c1 = '<' || c1 = '\'' || c1 = 'P') then
    let (_, t, name) ← withPos (groupName (← read))
    pure $ mkNodeOfKind `capturingGroup name f t
  else fail "invalid capturing group character"

private def atomicGroupKind : ParsecM Syntax := attempt do
  let (f, _, _) ← withPos (pchar ('?'))
  if let some (_, t, _) ← tryCharWithPos (· = '>') then
    pure $ mkNodeOfKind `atomicGroup "" f t
  else fail "invalid capturing group character"

private def lookaroundGroupKind : ParsecM Syntax := attempt do
  let (f, _, c) ← withPos (pchar ('?'))
  if let some (_, t, c1) ← tryCharWithPos (fun c1 => c1 = '=' || c1 = '!') then
      pure $ mkNodeOfKind `lookaroundGroup ⟨[c, c1]⟩ f t
  else if let some (_, _, c1) ← tryCharWithPos (· = '<') then
      if let some (_, t, c2) ← tryCharWithPos (fun x => x = '=' || x  = '!') then
        pure $ mkNodeOfKind `lookaroundGroup ⟨[c, c1, c2]⟩ f t
      else fail "lookaround char expected"
  else fail "lookaround char expected"

private def defineGroupKind : ParsecM Syntax := attempt do
  let (f, t, _) ← withPos (pchar ('?'))
  skipString "(DEFINE)" *> (pure $ mkNodeOfKind `controlVerbGroup "" f t)

private def subroutineGroupKind : ParsecM Syntax := attempt do
  let (f, t, _) ← withPos (pchar ('?'))
  let c1 ← peek!
  if c1 = '?' || c1 = '&' || c1 = '(' || c1 = 'P' || c1 = '|' || c1 = '-' || c1.isDigit then
    let chars ← manyChars (notFollowedBy (pchar ')') *> groupLetter)
    pure $ mkNodeOfKind `subroutineGroupKind ⟨chars.toList⟩  f t
  else fail ""

private def commentGroupKind : ParsecM Syntax := attempt do
  let (f, t, _) ← withPos (pchar ('?'))
  skipChar '#'
  let chars ← manyChars (notFollowedBy (pchar ')') *> anyChar)
  pure $ mkNodeOfKind `commentGroupKind ⟨chars.toList⟩  f t

private def namedLookaroundGroupKind : ParsecM Syntax := attempt do
  let (f, t, _) ← withPos (pchar ('*'))
  skipString "pla:" *> (pure $ mkNodeOfKind `lookaroundGroup "?=" f t)
  <|> skipString "nla:" *> (pure $ mkNodeOfKind `lookaroundGroup "?!"  f t)
  <|> skipString "plb:" *> (pure $ mkNodeOfKind `lookaroundGroup "?<=" f t)
  <|> skipString "nlb:" *> (pure $ mkNodeOfKind `lookaroundGroup "?<!" f t)

private def controlName : ParsecM Syntax := attempt do
  if let some (f, t, _) ← tryCharWithPos (· = ':') then
    let chars ← manyChars (asciiLetter <|> pchar '(')
    pure $ mkNodeOfKind `controlName ⟨chars.toList⟩  f t
  else pure $ mkNodeOfKind `controlName ""  0 0

private def controlVerbGroupKind : ParsecM Syntax := attemptM do
  let (f, t, _) ← withPos (pchar ('*'))
  (skipString "ACCEPT" <|> skipString "COMMIT" <|> skipString "MARK"<|> skipString "PRUNE"
      <|> skipString "SKIP" <|> skipString "THEN")
    *> controlName (← read) *> (pure $ mkNodeOfKind `controlVerbGroup "" f t)
  <|> controlName

private def nonCapturingGroupKind : ParsecM Syntax := attempt do
  let (f, t, _) ← withPos (pchar ('?'))
  let flags ← manyChars
    (notFollowedBy (pchar ':' <|> pchar ')') *> (asciiLetter <|> pchar '-' <|> pchar '^')) <* optSkipChar ':'
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
private def hexChars (f t : String.Pos): ParsecM Syntax := attemptM do
  if let some (_, t, arr) ← tryCharThenPWithPosM (· = '{') (parenWithChars hexChar) then
    pure $ mkLiteral (decodeDigits arr.toList 16) f t
  else if let some (_, t, u1) ← tryCharThenPWithPosM isHexChar hexChar then
    if let some (_, t, u2) ← tryCharThenPWithPosM isHexChar hexChar  then
        pure $ mkLiteral (decodeDigits [u1, u2] 16) f t
    else pure $ mkLiteral (decodeDigits [u1] 16) f t
  else pure $ mkLiteral (decodeDigits [0] 16) f t

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC5 -/
private def octChars (inCharacterClass : Bool) (c : Char) (u1 : Nat) (f t : String.Pos)
    : ParsecM Syntax := attemptM do
  if let some (_, _, (c2, u2)) ← tryCharThenPWithPosM isOctChar octChar' then
    if let some (_, _, u3) ← tryCharThenPWithPosM isOctChar octChar then
      pure $ mkLiteral (decodeDigits [u1, u2, u3] 8) f t
    else
      if inCharacterClass || (u1 = 0 && u2 = 0)
      then pure $ mkLiteral (decodeDigits [u1, u2] 8) f t
      else pure $ mkBackRefOrLiteral ⟨[c, c2]⟩  (decodeDigits [u1, u2] 8) f t
  else if inCharacterClass || c = '0' then
    if h : UInt32.isValidChar u1.toUInt32 then
      pure $ mkLiteral ⟨u1.toUInt32, h⟩ f t
    else fail ""
  else pure $ mkNodeOfKind `backReferenceNumber ⟨[c]⟩ f t

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC5 -/
private def nonPrintingChar (inCharacterClass : Bool := false) : ParsecM Syntax := attemptM do
  let (f, t, c) ← withPos anyChar
  if c = 'a' then pure $ mkLiteral '\x07' f t
  else if c = 'a' then pure $ mkLiteral '\x07' f t
  else if c = 'c' then controlChar
  else if c = 'e' then pure $ mkLiteral '\x1b' f t
  else if c = 'E' then pure $ mkNodeOfKind `endQuote ⟨[c]⟩ f t
  else if c = 'f' then pure $ mkLiteral '\x0c' f t
  else if c = 'n' then pure $ mkLiteral '\x0a' f t
  else if c = 'r' then pure $ mkLiteral '\x0d' f t
  else if c = 't' then pure $ mkLiteral '\x09' f t
  else if c = 'o' then
    let (_, t, arr) ← withPosM (parenWithChars octChar)
    pure $ mkLiteral (decodeDigits arr.toList 8) f t
  else if c = 'x' then hexChars f t
  else if isOctChar c then octChars inCharacterClass c (octCharToNat c) f t
  else fail "fail nonPrintingChar"

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC19 -/
private def backReference : ParsecM Syntax := attemptM do
  if let some (f, t, c) ← tryCharWithPos Char.isDigit then
    pure $ mkNodeOfKind `backReferenceNumber ⟨[c]⟩ f t
  else if let some _ ← tryCharWithPos (· = 'g') then
    if ← testChar (· = '{') then
      let (f, t, chars) ← withPosM $ (parenWithChars (groupLetter <|> pchar '-'))
      let kind := if Array.all chars (fun c => c.isDigit || c = '-')
                  then `backReferenceNumber
                  else `backReferenceName
      pure $ mkNodeOfKind kind ⟨chars.toList⟩ f t
    else if let some (f, _, cm) ← tryCharWithPos (· = '-') then
      if let some (_, t, c) ← tryCharWithPos Char.isDigit then
        pure $ mkNodeOfKind `backReferenceNumber ⟨[cm, c]⟩ f t
      else fail ""
    else if let some (f, t, c) ← tryCharWithPos Char.isDigit then
      pure $ mkNodeOfKind `backReferenceNumber ⟨[c]⟩ f t
    else fail ""
  else if let some _ ← tryCharWithPos (· = 'k') then
    if ← testChar (· = '<') then
      let (f, t, chars) ← withPosM $ parenWithChars groupLetter '<' '>'
      let kind := `backReferenceName
      pure $ mkNodeOfKind kind ⟨chars.toList⟩ f t
    else fail ""
  else fail ""

private def genericCharacterType : ParsecM Syntax := attempt do
  let (f, t, c) ← withPos anyChar
  if c = 'd' || c = 'D' || c = 'h' || c = 'H' || c = 'N' || c = 's' || c = 'S'
     || c = 'v' || c = 'V' || c = 'w' || c = 'W'
  then pure $ mkNodeOfKind `genericCharacterType ⟨[c]⟩ f t
  else fail ""

private def simpleAssertion (inCharacterClass : Bool := false) : ParsecM Syntax := attemptM do
  let (f, t, c) ← withPos anyChar
  if c = 'b' && inCharacterClass then pure $ mkLiteral ⟨8, by simp_arith⟩ f t
  else if (← read) == Syntax.Flavor.Rust && (← testChar (c = 'b' && · = '{')) then
    let (_, t, chars) ← withPosM (parenWithChars (asciiLetter <|> pchar '-'))
    let s : String := ⟨chars.toList⟩
    if s = "start" || s = "end" || s = "start-half" || s = "end-half"
    then pure $ mkNodeOfKind `simpleAssertion s f t
    else fail ""
  else if c = 'b' || c = 'B' || c = 'A' || c = 'Z' || c = 'z' || c = 'G' || c = 'K' then
    pure $ mkNodeOfKind `simpleAssertion ⟨[c]⟩ f t
  else fail ""

private def unicodeCharacterProperty : ParsecM Syntax := attempt do
  let name := manyChars (groupLetter <|> pchar '_')
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
      let (f, t, c) ← withPos asciiLetter
      pure $ Syntax.node (SourceInfo.synthetic f t) kind #[Syntax.atom .none ⟨[c]⟩]
  else fail ""

private def escapedChar : ParsecM Syntax := attempt do
  let (f, t, c) ← withPos anyChar
  pure $ mkLiteral c f t

private def literalChars : ParsecM Syntax := attempt do
  skipChar 'Q'
  let chars ← manyChars (notFollowedBy (skipString "\\E") *> anyChar) <* skipString "\\E"
  let list := chars.data |> List.map (fun c => mkLiteral c 0 0)
  pure $ Syntax.node (SourceInfo.synthetic 0 0) `sequence list.toArray

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC5 -/
private def escapeSeq (inCharacterClass : Bool := false) : ParsecM Syntax := attemptM do
  let c ← peek!
  if c = '\\' then
    skip
    literalChars <|> nonPrintingChar inCharacterClass
          <|> (if inCharacterClass then failM "" else backReference)
          <|> simpleAssertion inCharacterClass
          <|> genericCharacterType   <|> unicodeCharacterProperty
          <|> escapedChar
  else fail ""

end EscapeSeq

private def repetitionModifier : ParsecM Syntax := do
  match ← peek? with
  | some c =>
    if c = '+' || c = '?' then skip; pure $ mkLit `repetitionModifier ⟨[c]⟩ SourceInfo.none
    else pure $ mkLit `repetitionModifier "" SourceInfo.none
  | none => pure $ mkLit `repetitionModifier "" SourceInfo.none

private def toRepetitionLeft (s : String) : Syntax :=
   mkLit `repetitionLeft s SourceInfo.none

private def toRepetitionRight (s : String) : Syntax :=
   mkLit `repetitionRight s SourceInfo.none

private def repetitionContent : ParsecM Syntax := attemptM do
  ws
  let c ← peek!
  if c = ',' then
    let (f, _, _) ← withPos $ skipChar ','
    ws
    let c ← peek!
    if c = '}' then fail ""
    else
      let b ← manyCore digit #[]
      ws
      let litA := toRepetitionLeft ""
      let litB := toRepetitionRight ⟨b.toList⟩
      let (_, t, _) ← withPos (pchar ('}'))
      let modifier ← repetitionModifier
      pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]
  else
    let (f, _, a) ← withPos $ manyCore digit #[]
    ws
    let litA := toRepetitionLeft ⟨a.toList⟩
    let c ← peek!
    if c = '}' then
      let (_, t, _) ← withPos (pchar ('}'))
      let litB := toRepetitionRight ⟨a.toList⟩
      let modifier ← repetitionModifier
      pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]
    else
      skipChar ','
      ws
      let b ← manyCore digit #[]
      ws
      let litB := toRepetitionRight ⟨b.toList⟩
      let (_, t, _) ← withPos (pchar ('}'))
      let modifier ← repetitionModifier
      pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC17 -/
private def repetition : ParsecM Syntax := attemptM do
  let c ← peek!
  if c = '{' then
    let (f, t, _) ← withPos (pchar ('{'))
    if let some (f1, t1, _) ← tryCharWithPos (· = '}')
    then
      pure $ Syntax.node (SourceInfo.synthetic f t1) `sequence #[
          mkLiteral '{' f t,
          mkLiteral '}' f1 t1
      ]
    else
      repetitionContent <|> (pure $ mkLiteral c f t)
  else if c = '*' then
    let (f, t, _) ← withPos (pchar ('*'))
    let litA := toRepetitionLeft "0"
    let litB := toRepetitionRight ""
    let modifier ← repetitionModifier
    pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]
  else if c = '+' then
    let (f, t, _) ← withPos (pchar ('+'))
    let litA := toRepetitionLeft "1"
    let litB := toRepetitionRight ""
    let modifier ← repetitionModifier
    pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]
  else if c = '?' then
    let (f, t, _) ← withPos (pchar ('?'))
    let litA := toRepetitionLeft "0"
    let litB := toRepetitionRight "1"
    let modifier ← repetitionModifier
    pure $ Syntax.node (SourceInfo.synthetic f t) `repetition #[litA, litB, modifier]
  else fail ""

private def toPosixCharacterClass (p : Parsec String ): Parsec Syntax := attempt do
  pure $ mkNodeOfKind `posixCharacterClass (← p) 0 0

private def posixCharacterClass : Parsec Syntax := attempt do
  (pstring "[:alnum:]" <|> pstring "[:ascii:]" <|> pstring "[:alpha:]" <|> pstring "[:blank:]"
   <|> pstring "[:cntrl:]" <|> pstring "[:digit:]" <|> pstring "[:lower:]" <|> pstring "[:word:]"
   <|> pstring "[:print:]" <|> pstring "[:punct:]" <|> pstring "[:space:]"
   <|> pstring "[:upper:]" <|>
   pstring "[:^alnum:]" <|> pstring "[:^ascii:]" <|> pstring "[:^alpha:]" <|> pstring "[:^blank:]"
   <|> pstring "[:^cntrl:]" <|> pstring "[:^digit:]" <|> pstring "[:^lower:]" <|> pstring "[:^word:]"
   <|> pstring "[:^print:]" <|> pstring "[:^punct:]" <|> pstring "[:^space:]"
   <|> pstring "[:^upper:]")
  |> toPosixCharacterClass

private def consumeStartOfCharacterClass : ParsecM $ Array Syntax := attemptM do
  if let some stx ← consumeChar? '^' then
    if let some stx' ← consumeChar? ']' then pure #[stx, stx']
    else pure #[stx]
  else if let some stx ← consumeChar? ']' then pure #[stx]
  else pure #[]

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC9 -/
private def characterClass (val : ParsecM Syntax) : ParsecM Syntax := attemptM do
  let (f, _, _) ← withPos (pchar ('['))
  let start ← consumeStartOfCharacterClass
  let arr ← manyCore (val (← read)) #[]
  let (_, t, _) ← withPos (pchar (']'))
  pure $ Syntax.node (SourceInfo.synthetic f t) `characterClass (start ++ arr)

mutual

private partial def valInCharacterClass : ParsecM $ Syntax := do
  let p ← EscapeSeq.escapeSeq true
    <|> posixCharacterClass
    <|> (if Syntax.Flavor.Rust == (← read) then characterClass' else failM "")
    <|> characterClassSetOperation <|> hyphen
    <|> literal true
  pure $ p

private partial def characterClass' : ParsecM Syntax :=
  characterClass valInCharacterClass

end

/-- https://www.pcre.org/current/doc/html/pcre2pattern.html#SEC14 -/
private def group (val : ParsecM Syntax) : ParsecM Syntax := attemptM do
  let (f, _, _) ← withPos (pchar ('('))
  let kind ← groupKind
  let arr ← manyCore (val (← read)) #[]
  let (_, t, _) ← withPos (pchar (')'))
  pure $ Syntax.node (SourceInfo.synthetic f t) `group (#[kind] ++ arr)

private partial def val : ParsecM $ Syntax := do
  let p ← EscapeSeq.escapeSeq <|> (group val) <|> verticalBar <|> assertion
          <|> characterClass valInCharacterClass <|> repetition <|> dot <|> literal
  pure $ p

private def sequence : ParsecM $ TSyntax `sequence := do
  let (f, t, arr) ← withPos (manyCore (val (← read)) #[])
  pure $ (TSyntax.mk (Syntax.node (SourceInfo.synthetic f t) `sequence arr))

/-- Parse a PCRE2 regular expressions into a `Lean.Syntax` tree. -/
def parse (s : String) (flavor : Syntax.Flavor) : Except String $ TSyntax `sequence :=
  match (sequence flavor) s.mkIterator with
  | Parsec.ParseResult.success it res =>
      if it.atEnd
      then Except.ok res
      else Except.error s!"offset {repr it.i.byteIdx}: cannot parse regex"
  | Parsec.ParseResult.error it err  => Except.error s!"offset {repr it.i.byteIdx}: {err}"
