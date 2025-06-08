import Regex.Syntax.Grammar.Grammar
import Regex.Syntax.Grammar.Translate
import Regex.Syntax.Ast.Ast
import Regex.Data.Array.Basic
import Regex.Syntax.Flavor

open Lean Lean.Parser

/-!
## Parse

Parse the regular expression (`parse`)
-/
namespace Syntax.AstItems

/-- State of the parser -/
private structure Parser where
  /-- The current capture index. -/
  capture_index : Nat
  /-- The names of capture groups. -/
  capture_group_names : List (Nat × String)
  /-- The maximal single digit backreference. -/
  max_backreference : Nat

instance : Inhabited Parser := ⟨0, [], 0⟩

abbrev ParserM := ReaderT Flavor $ StateT Parser (Except String)

/-- match syntax make by `Lean.Syntax.mkLit` -/
private def valuesOfLitSyntax (x : Syntax) :=
  match x with
  | Syntax.node _ k #[Lean.Syntax.atom info s] => some (k, info , s)
  | _ => none

private def valueOfLitSyntax (x : Syntax) (kind : SyntaxNodeKind) :=
  match x with
  | Syntax.node _ k #[Lean.Syntax.atom _ s] => if k = kind then some s else none
  | _ => none

private def extractNegated (arr : Array Syntax)
    : Bool × {arr' : Array Syntax // sizeOf arr' ≤ sizeOf arr} :=
  match h : arr.head? with
  | some (head, tail) =>
      have : sizeOf tail < sizeOf arr := Array.sizeOf_head?_of_tail h
      match valueOfLitSyntax head `literal with
      | some v => if v = "^" then (true, ⟨tail, by omega⟩) else (false, ⟨arr, by simp⟩)
      | none => (false, ⟨arr, by simp⟩)
  | none => (false, ⟨arr, by simp⟩)

private def parseLiteral (p : String) (x : Syntax) : ParserM Ast := do
  match x with
  | Syntax.node _ `literal #[Lean.Syntax.atom (.synthetic f t) ⟨[c]⟩] =>
      pure $ .Literal $ Literal.toLiteral c p f t
  | _ => Except.error s!"ill-formed literal syntax {x}"

private def parseHyphen (p : String) (x : Syntax) : ParserM Ast := do
  match x with
  | Syntax.node _ `hyphen #[Lean.Syntax.atom (.synthetic f t) ⟨[c]⟩] =>
      pure $ .Literal $ Literal.toLiteral c p f t
  | _ => Except.error s!"ill-formed literal syntax {x}"

private def nameToClassSetItems : List (String × ClassAsciiKind) :=
  [
    ("alnum", .Alnum),
    ("alpha", .Alpha),
    ("ascii", .Ascii),
    ("blank", .Blank),
    ("cntrl", .Cntrl),
    ("digit", .Digit),
    ("lower", .Lower),
    ("print", .Print),
    ("punct", .Punct),
    ("space", .Space),
    ("upper", .Upper),
    ("word", .Word),
  ]

private def parsePosixCharacterClass (p : String) (x : Syntax) : ParserM ClassSetItem := do
  match x with
  | Syntax.node _ `posixCharacterClass #[Lean.Syntax.atom (.synthetic f t) name] =>
    let (negated, name) :=
      match name.toList with
      | '^' :: tail => (true, String.mk tail)
      | _ => (false, name)
    match nameToClassSetItems |> List.find? (fun (n, _) => n = name) with
    | some (_, cls) => pure $ ClassSetItem.Ascii ⟨⟨p, f, t⟩ , cls, negated⟩
    | none => Except.error s!"unkown posixCharacterClass {name}"
  | _ => Except.error s!"ill-formed literal syntax {x}"

private def parseDot (p : String) (x : Syntax) : ParserM Ast := do
  match x with
  | Syntax.node _ `dot #[Lean.Syntax.atom (.synthetic f t) _] =>
      pure (.Dot ⟨p, f, t⟩)
  | _ => Except.error s!"ill-formed dot syntax {x}"

private def getPerlClass (c : Char) : ParserM $ Bool × ClassPerlKind := do
  match c with
  | 'd' => pure (false, ClassPerlKind.Digit)
  | 'D' => pure (true, ClassPerlKind.Digit)
  | 'h' => pure (false, ClassPerlKind.HorizontalSpace)
  | 'H' => pure (true, ClassPerlKind.HorizontalSpace)
  | 'n' => pure (false, ClassPerlKind.Newline)
  | 'N' => pure (true, ClassPerlKind.Newline)
  | 's' => pure (false, ClassPerlKind.Space)
  | 'S' => pure (true, ClassPerlKind.Space)
  | 'v' => pure (false, ClassPerlKind.VerticalSpace)
  | 'V' => pure (true, ClassPerlKind.VerticalSpace)
  | 'w' => pure (false, ClassPerlKind.Word)
  | 'W' => pure (true, ClassPerlKind.Word)
  | _ => Except.error s!"expected valid Perl class but got {c}"

private def parseGenericCharacterType (p : String) (x : Syntax) : ParserM Ast := do
  match valuesOfLitSyntax x with
  | some (_, (.synthetic f t), ⟨[c]⟩) =>
      -- ClassUnicodeKind.Named
      let (negated, kind) ← getPerlClass c
      pure $ Ast.ClassPerl ⟨⟨p, f, t⟩, kind, negated⟩
  | _ => Except.error s!"no GenericCharacterType values in {x}"

private def parseUnicodeCharacterProperty (p : String) (x : Syntax) : ParserM Ast := do
  match x with
  | Syntax.node (.synthetic f t) kind arr =>
      let negated := kind = `unicodeCharacterPropertyNegated
      match arr.toList with
      | [.atom _ ⟨[c]⟩] =>
        pure $ Ast.ClassUnicode ⟨⟨p, f, t⟩ , negated, ClassUnicodeKind.OneLetter c⟩
      | [.atom _ v] =>
        pure $ Ast.ClassUnicode ⟨⟨p, f, t⟩ , negated, ClassUnicodeKind.Named v⟩
      | (.atom _ a) :: (.atom _ "=") :: [.atom _ b] =>
        pure $ Ast.ClassUnicode ⟨⟨p, f, t⟩ , negated, ClassUnicodeKind.NamedValue .Equal a b⟩
      | _ => Except.error s!"ill-formed UnicodeCharacterProperty array in {x}"
  | _ => Except.error s!"no UnicodeCharacterProperty values in {x}"

private def parseBackReference (p : String) (x : Syntax) : ParserM Ast := do
  let state ← get
  match valuesOfLitSyntax x with
  | some (_, (.synthetic f t), v) =>
      let (minus, v) := match v.toList with | '-' :: tail => (true, String.mk tail) | _ => (false, v)
      match v.toNat? with
      | some n =>
        if n > state.max_backreference then set {state with max_backreference := n}
        pure $ Ast.BackRef ⟨⟨p, f, t⟩ , if minus then state.capture_index + 1 - n else n⟩
      | none =>
          match state.capture_group_names |> List.find? (fun (_, n) => n = v) with
          | some (n, _) =>
            if n > state.max_backreference then set {state with max_backreference := n}
            pure $ Ast.BackRef ⟨⟨p, f, t⟩ , n⟩
          | none => throw (toError p .GroupNameNotFound)
  | _ => Except.error s!"no BackReference values in {x}"

private def parseBackReferenceOrLiteral (p : String) (x : Syntax) : ParserM Ast := do
  let state ← get
  match x with
  | Syntax.node (.synthetic f t) `backReferenceNumberOrLiteral #[b, l] =>
    let (b, c) ←
      match b, l with
      | .atom .none b, .atom .none ⟨[c]⟩  => pure (b, c)
      | _, _ => Except.error s!"ill-formed BackRefOrLiteral in {x}"

    match b.toNat? with
    | some n =>
      if n ≤ state.capture_index
      then
        if n > state.max_backreference then set {state with max_backreference := n}
        pure $ Ast.BackRef ⟨⟨p, f, t⟩ , n⟩
      else
        pure $ .Literal $ Literal.toLiteral c p f t
    | _ => Except.error s!"no BackReference values in {x}"

  | _ => Except.error s!"ill-formed BackRefOrLiteral in {x}"

private def parseAssertion (p : String) (x : Syntax) : ParserM Ast := do
  let flavor ← read
  let toAssertionKind (s : String) : ParserM AssertionKind := do
    match s with
    | "^" => pure AssertionKind.StartLine
    | "$" => pure $ if flavor == Flavor.Pcre
                    then AssertionKind.EndLineWithOptionalLF
                    else AssertionKind.EndLine
    | "b" => pure AssertionKind.WordBoundary
    | "z" => pure AssertionKind.EndText
    | "A" => pure AssertionKind.StartText
    | "B" => pure AssertionKind.NotWordBoundary
    | "G" => if flavor == Flavor.Pcre
             then pure AssertionKind.PreviousMatch
             else Except.error (toError p .EscapeUnrecognized)
    | "K" => if flavor == Flavor.Pcre
             then pure AssertionKind.ClearMatches
             else Except.error (toError p .EscapeUnrecognized)
    | "Z" => pure AssertionKind.EndTextWithOptionalLF
    | "start" => pure AssertionKind.WordBoundaryStart
    | "end" => pure AssertionKind.WordBoundaryStart
    | "start-half" => pure AssertionKind.WordBoundaryStartHalf
    | "end-half" => pure AssertionKind.WordBoundaryEndHalf
    | _ => Except.error s!"unkown assertionKind {s}"

  match x with
  | Syntax.node _ `simpleAssertion #[Lean.Syntax.atom (.synthetic f t) s] =>
      pure (.Assertion ⟨⟨p, f, t⟩, ← toAssertionKind s⟩)
  | _ => Except.error s!"ill-formed assertion syntax {x}"

private def toFlags (chars : List Char) : ParserM $ Array FlagsItem := do
  let items ← chars |> List.mapM (fun c =>
    match c with
    | '-' => pure ⟨"", FlagsItemKind.Negation⟩
    | 'i' => pure ⟨"", FlagsItemKind.Flag .CaseInsensitive⟩
    | 'm' => pure ⟨"", FlagsItemKind.Flag .MultiLine⟩
    | 's' => pure ⟨"", FlagsItemKind.Flag .DotMatchesNewLine⟩
    | 'u' => pure ⟨"", FlagsItemKind.Flag .Unicode⟩
    | 'U' => pure ⟨"", FlagsItemKind.Flag .SwapGreed⟩
    | 'R' => pure ⟨"", FlagsItemKind.Flag .CRLF⟩
    | 'x' => pure ⟨"", FlagsItemKind.Flag .Extended⟩
    | _ => throw (toError "" .FlagUnrecognized))
  pure items.toArray

private def parseGroupKind (p : String) (x : Syntax) : ParserM GroupKind := do
  match valuesOfLitSyntax x with
  | some (`capturingGroup, _, "") =>
      let parser ← get
      let capture_index := parser.capture_index + 1
      set { parser with capture_index := capture_index }
      pure $ GroupKind.CaptureIndex capture_index none
  | some (`capturingGroup, _, name) =>
      let parser ← get
      if parser.capture_group_names |> List.find? (fun (_, n) => n = name) |> Option.isSome
      then throw (toError p .GroupNameDuplicate) else
        let capture_index := parser.capture_index + 1
        let parser :=
          { parser with
            capture_index := capture_index
            capture_group_names := parser.capture_group_names ++ [(capture_index, name)]
          }
        set parser
        pure $ GroupKind.CaptureIndex capture_index (if name.length>0 then some name else none)
  | some (`nonCapturingGroup, (.synthetic f t), s) =>
      pure $ GroupKind.NonCapturing ⟨⟨p, f, t⟩, ← toFlags s.toList⟩
  | some (`lookaroundGroup, _, kind) =>
      match kind with
      | "?=" => pure $ GroupKind.Lookaround .PositiveLookahead
      | "?!" => pure $ GroupKind.Lookaround .NegativeLookahead
      | "?<=" => pure $ GroupKind.Lookaround (.PositiveLookbehind 0)
      | "?<!" => pure $ GroupKind.Lookaround (.NegativeLookbehind 0)
      | _ => Except.error s!"unkown lookaround kind {kind}"
  | some (`atomicGroup, _, _) => throw  (toError p .FeatureNotImplementedAtomicGroup)
  | some (`controlName, _, _) => throw  (toError p .FeatureNotImplementedControlVerbs)
  | some (`controlVerbGroup, _, _) => throw  (toError p .FeatureNotImplementedControlVerbs)
  | some (`commentGroupKind, _, _) => throw  (toError p .FeatureNotImplementedControlVerbs)
  | some (`subroutineGroupKind, _, _) => throw  (toError p .FeatureNotImplementedSubroutines)
  | _ => Except.error s!"ill-formed group kind syntax {x}"

private def toConcat (asts : Array Ast) : Ast :=
  match asts with | #[ast] => ast | _ => .Concat ⟨"", asts⟩

private def toRepetitionKind (p l r : String) : ParserM RepetitionKind := do
  match l.toNat?, r.toNat? with
  | some l , some r =>
    if l < r then pure $ RepetitionKind.Range (RepetitionRange.Bounded l r)
    else if l = r then pure $ RepetitionKind.Range (RepetitionRange.Exactly l)
    else Except.error (toError p .RepetitionCountUnclosed)
  | some l , none =>
    pure $ RepetitionKind.Range (RepetitionRange.AtLeast l)
  | none , some r =>
    pure $ RepetitionKind.Range  (RepetitionRange.Bounded 0 r)
  | _, _ => Except.error "invalid repetition kind {l} {r}"

private def toRepetition (p : String) (f t : String.Pos) (l r m : String) (ast : Ast)
    : ParserM Ast := do
  let (greedy, possessive) :=
    match m.toList with
    | ['+'] => (true, true)
    | ['?'] => (false, false)
    | _ => (true, false)
  pure $
    Ast.Repetition $ Repetition.mk ⟨p,f, t⟩ ⟨⟨p,f, t⟩, ← toRepetitionKind p l r⟩ greedy possessive ast

private def toClassSetItem (ast : Ast) : ParserM ClassSetItem := do
  match ast with
  | .Literal lit => pure $ ClassSetItem.Literal lit
  | .ClassPerl cls => pure $ ClassSetItem.Perl cls
  | .ClassUnicode cls => pure $ ClassSetItem.Unicode cls
  | .ClassBracketed cls => pure $ ClassSetItem.Bracketed cls
  | _ => Except.error s!"unexpected ast for class set item {ast}"

private def rangeToClassSetItem (p : String) (a b : Syntax) : ParserM ClassSetItem := do
  match valuesOfLitSyntax a , valuesOfLitSyntax b  with
  | some (`literal, (.synthetic fa ta), a), some (`literal, (.synthetic fb tb), b) =>
    match a.toList, b.toList with
    | [a], [b] =>
      if h : a.val ≤ b.val
      then pure
        $ ClassSetItem.Range
        $ ClassSetRange.mk ⟨p, fa, tb⟩ (Literal.toLiteral a p fa ta) (Literal.toLiteral b p fb tb) h
      else Except.error s!"unexpected range for class set item {a} {b}"
    | _, _ => Except.error s!"unexpected range for class set item {a} {b}"
  | some (`endQuote, _, _), _ => throw  (toError p .EndQuoteWithoutOpenQuote)
  | _, _ => Except.error s!"unexpected kind for class set item {a} {b}"

/-- set fixed width for look behind -/
private def set_width (pattern : String) (g : Group) : ParserM Group := do
  match g with
  | ⟨span, .Lookaround (.PositiveLookbehind _), ast⟩ =>
      let width ← get_fixed_width pattern ast
      pure (Group.mk span (.Lookaround (.PositiveLookbehind width)) ast)
  | ⟨span, .Lookaround (.NegativeLookbehind _), ast⟩ =>
      let width ← get_fixed_width pattern ast
      pure (Group.mk span (.Lookaround (.NegativeLookbehind width)) ast)
  | _ => pure g

private def unfoldUnion (union : ClassSetUnion) : Sum ClassSetItem ClassSetBinaryOp :=
  let ⟨span, items⟩ := union
  match items.size with
  | 0 => Sum.inl $ ClassSetItem.Empty span
  | 1 => if h: 0 < items.size then
    let item := items[0]'h
    match item with
    | .Bracketed ⟨_, _, .BinaryOp cls⟩  => Sum.inr cls
    | _ => Sum.inl $ item else Sum.inl $ ClassSetItem.Empty span
  | _ => Sum.inl $ ClassSetItem.Union union

private def toNode? (t : Syntax)
    : Option { x : SourceInfo × SyntaxNodeKind × Array Syntax // sizeOf x.2.2 < sizeOf t } :=
  match h : t with
  | .node si kind args => some ⟨(si, kind, args), by simp [h]; omega⟩
  | _ => none

private def parseSimpleClassSetItem (p : String) (x : Syntax) (kind : SyntaxNodeKind)
    ( arr : Array Syntax) : ParserM $ Option ClassSetItem := do
  match kind with
  | `whitespace => pure $ ClassSetItem.Empty ""
  |  `literal => pure (← parseLiteral p x >>= toClassSetItem)
  |  `hyphen => pure (← parseHyphen p x >>= toClassSetItem)
  |  `range => pure (← rangeToClassSetItem p arr[0]! arr[1]!)
  |  `genericCharacterType => pure (← parseGenericCharacterType p x >>= toClassSetItem)
  |  `posixCharacterClass => parsePosixCharacterClass p x
  |  `endQuote => throw (toError p .EndQuoteWithoutOpenQuote)
  |  `unicodeCharacterProperty => pure (← parseUnicodeCharacterProperty p x >>= toClassSetItem)
  |  `unicodeCharacterPropertyNegated => pure (← parseUnicodeCharacterProperty p x >>= toClassSetItem)
  | _ => pure none

private def parseSimpleVal (p : String) (x : Syntax) : ParserM $ Option Ast := do
  match x.getKind with
  | `whitespace => pure Ast.Empty
  | `comment => pure Ast.Empty
  | `literal => parseLiteral p x
  | `dot => parseDot p x
  | `simpleAssertion => parseAssertion p x
  | `backReferenceNumber => parseBackReference p x
  | `backReferenceName => parseBackReference p x
  | `backReferenceNumberOrLiteral => parseBackReferenceOrLiteral p x
  | `genericCharacterType => parseGenericCharacterType p x
  | `unicodeCharacterProperty => parseUnicodeCharacterProperty p x
  | `unicodeCharacterPropertyNegated => parseUnicodeCharacterProperty p x
  | `endQuote => throw  (toError p .EndQuoteWithoutOpenQuote)
  | `controlVerbGroup => throw  (toError p .FeatureNotImplementedControlVerbs)
  | `controlName => throw  (toError p .FeatureNotImplementedControlVerbs)
  | `subroutineGroupKind => throw  (toError p .FeatureNotImplementedSubroutines)
  | `commentGroupKind => throw  (toError p .FeatureNotImplementedFlagExtended)
  | _ => pure none

mutual

private def parseClassSetItem (p : String) (x : Syntax) : ParserM ClassSetItem := do
  match toNode? x with
  | some x' =>
    match ← parseSimpleClassSetItem p x x'.val.2.1 x'.val.2.2 with
    | some item => pure item
    | none =>
      match x'.val.2.1 with
      | `characterClass  => parseCharacterClass p x'.val.2.2 >>= toClassSetItem
      | `characterClassSetOperation => parseCharacterClassSetOp p x'.val.2.2 >>= toClassSetItem
      | _ => Except.error s!"unexpected class set item {x}"
  | _ =>  Except.error s!"unexpected class set item {x}"
termination_by sizeOf x

private def parseVal (p : String) (x : Syntax) : ParserM Ast := do
  match ← parseSimpleVal p x with
  | some x => pure x
  | none =>
    match x.getKind with
    | `group =>
        if let some ⟨((.synthetic f t), `group, arr), _⟩ := toNode? x then parseGroup p f t arr
        else Except.error s!"ill-formed group syntax {x}"
    | `alternatives =>
        if let some ⟨(_, `alternatives, arr), _⟩ := toNode? x then parseAlternatives p arr
        else Except.error s!"ill-formed alternatives syntax {x}"
    | `repetition =>
        if let some ⟨((.synthetic f t), `repetition, arr), _⟩ := toNode? x then parseRepetition  p f t arr
        else Except.error s!"ill-formed repetition syntax {x}"
    | `sequence =>
        if let some ⟨(_, `sequence, arr), _⟩ := toNode? x then parseSequence p arr
        else Except.error s!"ill-formed sequence syntax {x}"
    | `characterClass =>
        if let some ⟨(_, `characterClass, arr), _⟩ := toNode? x then parseCharacterClass p arr
        else Except.error s!"ill-formed sequence syntax {x}"
    | _ => Except.error s!"ill-formed val syntax {x}"
termination_by sizeOf x

private def folder (p : String) (acc : Array Ast) (x : Syntax)
  (parse : String → Syntax → ParserM Ast) : ParserM $ Array Ast:= do
  let ast ← parse p x
  pure $ acc ++ #[ast]

private def fold (p : String) (arr : Array Syntax) : ParserM $ Array Ast := do
  arr.attach.foldlM (fun acc (h : { x // x ∈ arr}) =>
        folder p acc h.val (fun _ _ =>
          have : sizeOf h.val < sizeOf arr := Array.sizeOf_lt_of_mem h.property
          parseVal p h.val)) #[]
termination_by sizeOf arr

private def parseGroup (p : String) (f t : String.Pos) (arr : Array Syntax) : ParserM Ast := do
  match h : arr.head? with
  | some (kind, arr') =>
    have : sizeOf arr' < sizeOf arr := Array.sizeOf_head?_of_tail h
    match ← parseGroupKind p kind, arr'.size with
    | GroupKind.NonCapturing flags, 0 => pure $ Ast.Flags ⟨"", flags⟩
    | kind , _ =>
        let group := Syntax.AstItems.Group.mk ⟨p, f, t⟩ kind (toConcat (← fold p arr'))
        let group ← set_width p group
        pure $ Ast.Group group
  | _ => Except.error "group array is empty"
termination_by sizeOf arr

private def parseAlternatives (p : String) (arr : Array Syntax) : ParserM Ast := do
  let asts ← arr.attach.foldlM (fun acc (h : { x // x ∈ arr}) =>
        folder p acc h.val (fun _ _ =>
          have : sizeOf h.val < sizeOf arr := Array.sizeOf_lt_of_mem h.property
          parseVal p h.val)) #[]
  pure (.Alternation ⟨⟨"", 0, 0⟩, asts⟩)
termination_by sizeOf arr

private def parseRepetition (p : String) (f t : String.Pos) (arr : Array Syntax) : ParserM Ast := do
  match hsize : arr.size, arr[0]?, arr[1]?, arr[2]?, hs : arr[3]? with
  | 4, some left, some right, some modifier, some s =>
    match valueOfLitSyntax left `repetitionLeft,
      valueOfLitSyntax right `repetitionRight,
      valueOfLitSyntax modifier `repetitionModifier with
    | some l, some r, some m =>
      have : sizeOf s < sizeOf arr := by
        simp_all +zetaDelta
        rw [← hs]
        exact Array.sizeOf_get arr 3 (by omega)
      pure $ (← toRepetition p f t l r m (← parseVal p s))
    | _, _, _ => Except.error s!"ill-formed repetition parts {left} {right}"
  | _, _, _, _, _ => Except.error s!"ill-formed repetition array {arr}"
termination_by sizeOf arr

private def innerParseCharacterClassSetOp (p op : String) (left right : Array Syntax) : ParserM Ast := do
  let itemsLeft ← left.attach.mapM (fun (item : { x // x ∈ left }) =>
    have : sizeOf item.val < sizeOf left := Array.sizeOf_lt_of_mem item.property
    parseClassSetItem p item.val)
  let itemsRight ← right.attach.mapM (fun (item : { x // x ∈ right }) =>
    have : sizeOf item.val < sizeOf right := Array.sizeOf_lt_of_mem item.property
    parseClassSetItem p item)
  let itemLeft := Syntax.AstItems.ClassSetUnion.into_item ⟨"", itemsLeft⟩
  let itemRight := Syntax.AstItems.ClassSetUnion.into_item ⟨"", itemsRight⟩
  let kind ← match op with
      | "&&" => pure ClassSetBinaryOpKind.Intersection
      | "--" => pure ClassSetBinaryOpKind.Difference
      | "~~" => pure ClassSetBinaryOpKind.SymmetricDifference
      | _ => Except.error s!"ill-formed characterClassSetOp op {op}"
  let op := ClassSetBinaryOp.mk "" kind (.Item itemLeft) (.Item itemRight)
  let cls : ClassBracketed := ⟨"", false, ClassSet.BinaryOp op⟩
  pure $ Ast.ClassBracketed cls
termination_by max (sizeOf left) (sizeOf right)

private def parseCharacterClassSetOp (p : String) (arr : Array Syntax) : ParserM Ast :=
  let arr' := arr.attach
  match arr'.size, arr'[0]?, arr'[1]?, arr'[2]? with
  | 3, some op, some left', some right' =>
    let left : Syntax := left'.val
    let right : Syntax := right'.val
    have : sizeOf left < sizeOf arr := Array.sizeOf_lt_of_mem left'.property
    have : sizeOf right < sizeOf arr := Array.sizeOf_lt_of_mem right'.property
    match op.val.isLit? `op, left, right with
    | some op, Syntax.node _ `first largs, Syntax.node _ `second rargs =>
      have : max (sizeOf largs) (sizeOf rargs) < sizeOf arr := by simp_all +zetaDelta; omega
      innerParseCharacterClassSetOp p op largs rargs
    | _, _, _ => Except.error s!"ill-formed characterClassSetOp {arr}"
  | _, _, _, _ => Except.error s!"ill-formed characterClassSetOp {arr}"
termination_by sizeOf arr

private def parseCharacterClass (p : String) (arr : Array Syntax) : ParserM Ast := do
  let (negated, arr') := extractNegated arr
  let items ← arr'.val.attach.mapM (fun (h : { x // x ∈ arr'.val}) =>
    have : sizeOf h.val < sizeOf arr'.val := Array.sizeOf_lt_of_mem h.property
    parseClassSetItem p h.val)
  let cls : ClassBracketed :=
    match unfoldUnion ⟨"", items⟩ with
    |.inl item => ⟨"", negated, ClassSet.Item item⟩
    |.inr op => ⟨"", negated, ClassSet.BinaryOp op⟩
  pure $ Ast.ClassBracketed cls
termination_by sizeOf arr

private def parseSequence (p : String) (arr : Array Syntax) : ParserM Ast := do
  let ast ← arr.attach.foldlM (fun acc (h : { x // x ∈ arr}) =>
        folder p acc h.val (fun _ _ =>
          have : sizeOf h.val < sizeOf arr := Array.sizeOf_lt_of_mem h.property
          parseVal p h.val)) #[]

  pure $ toConcat ast
termination_by sizeOf arr

end

private def parseSequence' (p : String) (x : Syntax) : ParserM Ast := do
  match x with
  | Syntax.node _ `sequence arr => parseSequence p arr
  | _ => Except.error s!"ill-formed sequence syntax {x}"

/-- Parse the regular expression and return an abstract syntax tree. -/
def parse (p : String)  (flavor : Syntax.Flavor) (extended : Regex.Grammar.ExtendedKind := .None) : Except String Ast := do
  let stx ← Regex.Grammar.parse p flavor extended >>= Regex.Grammar.translate
  let (ast, parser) ← parseSequence' p stx.raw flavor default

  if parser.capture_index < parser.max_backreference
     && (← checkBackRefences parser.max_backreference ast)
  then Except.error (toError p .BackRefenceInvalid)
  else pure ast
