import Std.Data.Nat.Lemmas
import Regex.Syntax.Ast.Ast
import Regex.Utils

namespace Syntax.Ast

/-!
## Parse

Parse the regular expression (`parse`)
-/

/-- positive Nat -/
private structure NatPos where
  val   : Nat
  gt : 0 < val

theorem Nat.zero_lt_one_add (a : Nat) : 0 < 1 + a := by
  simp [Nat.one_add, Nat.succ_pos]

theorem Nat.sum_lt_of_not_gt (n i m: Nat) (h₁ : ¬i ≥ n) (h₂ : 0 < m)
    : n - (i + m) < n - i := by
  have h₃ : i < n := Nat.lt_of_not_le h₁
  have h₄ : i < i + m := Nat.lt_add_of_pos_right h₂
  simp [Nat.sub_lt_sub_left h₃ h₄]

theorem Nat.succ_lt_of_not_gt (n i : Nat) (h : ¬i ≥ n) : n - (i + 1) < n - i := by
  apply Nat.sum_lt_of_not_gt n i 1 h (Nat.succ_pos _)

theorem Nat.sum_succ_lt_of_not_gt (n i m: Nat) (h₁ : ¬i ≥ n)
    : n - (i + m + 1) < n - i := by
  apply Nat.sum_lt_of_not_gt n i (m + 1) h₁ (Nat.succ_pos _)

namespace NatPos

private def one : NatPos := ⟨1, by simp⟩

/-- succ of Nat as NatPos value -/
private def succ (n : Nat) : NatPos := ⟨1 + n, Nat.zero_lt_one_add _⟩

end NatPos

/-- GroupState represents a single stack frame while parsing nested groups and alternations. -/
private inductive GroupState where
  /-- This state is pushed whenever an opening group is found. -/
  | Group (concat: Concat) (group: Group) : GroupState
  /-- This state is pushed whenever a new alternation branch is found. -/
  | Alternation (alt: Alternation) : GroupState

/-- ClassState represents a single stack frame while parsing character classes. -/
private inductive ClassState where
  /-- This state is pushed whenever an opening bracket is found. -/
  | Open (union: ClassSetUnion) (set: ClassBracketed) : ClassState
  /-- This state is pushed when a operator is seen. -/
  | Op (kind: ClassSetBinaryOpKind) (lhs: ClassSet) : ClassState

/-- State of the parser -/
private structure Parser where
  /-- The current capture index. -/
  capture_index : Nat
  /-- A stack of grouped sub-expressions, including alternations. -/
  stack_group: Array GroupState
  /-- A stack of nested character classes. -/
  stack_class: Array ClassState

instance : Inhabited Parser := ⟨0, #[], #[]⟩

abbrev ParserM := StateT Parser (Except String)

/-- Represents the count of parsed chars -/
abbrev NChars := Nat

private def is_hex(c : Char) : Bool :=
  ('0' <= c && c <= '9') || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')

private def is_ascii (c : Char) : Bool :=
  c.val <= 0x7F

/-- Returns true if the given character has significance in a regex. -/
private def is_meta_character (c: Char) : Bool :=
  match c with
    | '\\' | '.' | '+' | '*' | '?' | '(' | ')' | '|' | '[' | ']' | '{'
    | '}' | '^' | '$' | '#' | '&' | '-' | '~' => true
    | _ => false

/-- Returns true if the given character can be escaped in a regex. -/
private def is_escapeable_character (c: Char) : Bool :=
  if is_meta_character c then true
  else if !is_ascii c then false
  else if '0' <= c && c <= '9' then false
  else if 'A' <= c && c <= 'Z' then false
  else if 'a' <= c && c <= 'z' then false
  else if c = '<' || c = '>' then false
  else true

/-- Parse a hex representation of any Unicode scalar value. -/
private def parse_hex_brace (pattern : String) (i : Nat) (kind: HexLiteralKind)
    : Except String (NChars × Literal) := do
  let chars := (pattern.data.drop (i + 1)).takeWhile (· != '}')
  if chars.all (is_hex ·) && chars.length > 0 && chars.length <= 6
  then
    let val ← decodeHexDigits chars
    if h : isValidChar val
    then
      Except.ok (chars.length + 2, ⟨(toSpan pattern i (i + chars.length + 1)),
        LiteralKind.HexBrace kind, ⟨val, h⟩⟩)
    else Except.error (toError pattern .EscapeHexInvalid)
  else Except.error (toError pattern .EscapeHexInvalidDigit)

/-- Parse an N-digit hex representation of a Unicode codepoint. -/
private def parse_hex_digits (pattern : String) (i : Nat) (kind: HexLiteralKind)
    : Except String (NChars × Literal) := do
  if i + kind.digits <= pattern.length
  then
    let chars := (pattern.data.drop i).take kind.digits
    if chars.all (is_hex ·)
    then
      let n ← decodeHexDigits chars
      if h : isValidChar n
      then
        Except.ok (kind.digits, ⟨⟨pattern, ⟨i⟩, ⟨i + kind.digits⟩⟩, LiteralKind.Hex kind, ⟨n, h⟩⟩)
      else Except.error (toError pattern .EscapeHexInvalid)
    else Except.error (toError pattern .EscapeHexInvalidDigit)
  else Except.error (toError pattern .EscapeUnexpectedEof)

/-- Parse a hex representation of a Unicode codepoint. -/
private def parse_hex (pattern : String) (i : Nat)
    : Except String (NChars × Literal) := do
  let kind := match pattern.getAtCodepoint i with
    | 'x' => HexLiteralKind.X
    | _ => HexLiteralKind.UnicodeShort
  if pattern.getAtCodepoint (i + 1) = '{'
  then parse_hex_brace pattern (i + 1) kind
  else parse_hex_digits pattern (i + 1) kind

/-- Attempt to parse an ASCII character class, e.g., `[:alnum:]`. -/
private def maybe_parse_ascii_class (pattern : String) (i : Nat)
    : Except String (Option (NChars × ClassAscii)) := do
  if pattern.getAtCodepoint (i+1) != ':' then Except.ok none
  else
    let (n, negated) := if pattern.getAtCodepoint (i+2) = '^' then (3, true) else (2, false)
    let chars := (pattern.data.drop (i + n)).takeWhile (· != ':')
    if i + n + chars.length < pattern.length
      && pattern.getAtCodepoint (i + n + chars.length) = ':'
      && pattern.getAtCodepoint (i + n + 1 + chars.length) = ']'
    then
      let name : String := ⟨chars⟩
      match ClassAsciiKind.from_name name with
      | some kind =>
        let cls : ClassAscii := ⟨⟨pattern, ⟨i - 2⟩, ⟨i + n + chars.length⟩⟩,
                                kind, negated ⟩
        Except.ok (some (1 + n + chars.length, cls))
      | none => Except.error (toError pattern .UnkownAsciiClass)
    else
      Except.ok none

/-- Parse a Unicode class in either the single character notation `\pN`
    or the multi-character bracketed notation `\p{Greek}`.
    Assumes '\p' is already parsed. -/
private def parse_unicode_class (negated : Bool) (pattern : String) (i : Nat)
    : Except String (NChars × ClassUnicode) := do
  let c := pattern.getAtCodepoint (i)
  if c = '{'
  then
    let chars := (pattern.data.drop (i + 1)).takeWhile (· != '}')
    if i + 1 + chars.length < pattern.length && pattern.getAtCodepoint (i + 1 + chars.length) = '}'
    then
      let cls : ClassUnicode :=
        match (⟨chars⟩ : String).splitOn "=" with
        | [n, v] =>
            ⟨toSpan pattern (i - 2) (i + 1 + chars.length + 1),
            negated,
            ClassUnicodeKind.NamedValue ClassUnicodeOpKind.Equal n v⟩
        | _ =>
            ⟨toSpan pattern (i - 2) (i + 1 + chars.length + 1),
            negated,
            ClassUnicodeKind.Named ⟨chars⟩ ⟩
        Except.ok (1 + 1 + chars.length, cls)
    else
      Except.error (toError pattern .EscapeUnexpectedEof)
  else
    let cls : ClassUnicode := ⟨toSpan pattern (i - 2) (i + 1), negated, ClassUnicodeKind.OneLetter c⟩
    Except.ok (1, cls)

/-- Parse a Perl character class, e.g., `\d` or `\W`. -/
private def parse_perl_class (pattern : String) (i : Nat) : Except String ClassPerl := do
  let c := pattern.getAtCodepoint (i)
  let (neg, kind) ← match c with
        | 'd' => pure (false, ClassPerlKind.Digit)
        | 'D' => pure (true, ClassPerlKind.Digit)
        | 's' => pure (false, ClassPerlKind.Space)
        | 'S' => pure (true, ClassPerlKind.Space)
        | 'w' => pure (false, ClassPerlKind.Word)
        | 'W' => pure (true, ClassPerlKind.Word)
        | _ => Except.error s!"expected valid Perl class but got {c}"

  Except.ok ⟨⟨pattern, ⟨i⟩, ⟨i + 1⟩⟩, kind, neg⟩

/-- Parse an escape sequence as a primitive AST. -/
private def parse_escape (pattern : String) (i : Nat) : Except String (NatPos × Primitive) := do
  let toVerbatim (c : Char) : Primitive :=
    let lit : Literal := ⟨toSpan pattern (i - 1) (i + 1), LiteralKind.Verbatim, c⟩
    Primitive.Literal lit
  let c := pattern.getAtCodepoint (i)
  match c with
  | 'u' | 'x' =>
    let (n, lit) ← parse_hex pattern i
    Except.ok (NatPos.succ n, Primitive.Literal lit)
  | 'p' | 'P' =>
    let (n, cls) ← parse_unicode_class (c = 'P') pattern (i + 1)
    Except.ok (NatPos.succ n, Primitive.Unicode cls)
  | 'd' | 's' | 'w' | 'D' | 'S' | 'W' =>
    let cls ← parse_perl_class pattern i
    Except.ok (NatPos.succ 0, Primitive.Perl cls)
  | 'a' => Except.ok (NatPos.one, toVerbatim '\x07')
  | 'f' => Except.ok (NatPos.one, toVerbatim '\x0C')
  | 't' => Except.ok (NatPos.one, toVerbatim '\t')
  | 'n' => Except.ok (NatPos.one, toVerbatim '\n')
  | 'r' => Except.ok (NatPos.one, toVerbatim '\r')
  | 'V' => Except.ok (NatPos.one, toVerbatim '\x0B')
  | 'b' =>
    Except.ok (NatPos.succ 0,
      Primitive.Assertion ⟨toSpan pattern i (i + 1), AssertionKind.WordBoundary⟩)
  | 'z' =>
    Except.ok (NatPos.succ 0,
      Primitive.Assertion ⟨toSpan pattern i (i + 1), AssertionKind.EndText⟩)
  | 'A' =>
    Except.ok (NatPos.succ 0,
      Primitive.Assertion ⟨toSpan pattern i (i + 1), AssertionKind.StartText⟩)
  | 'B' =>
    Except.ok (NatPos.succ 0,
      Primitive.Assertion ⟨toSpan pattern i (i + 1), AssertionKind.NotWordBoundary⟩)
  | _ =>
    if is_meta_character c
    then Except.ok (NatPos.one, toVerbatim c)
    else if is_escapeable_character c
    then Except.ok (NatPos.one, toVerbatim c)
    else Except.error (toError pattern .EscapeUnrecognized)

/-- Parse a decimal number into a u32 -/
private def parse_decimal (pattern : String) (i : Nat)
    : Except String (NatPos × Nat) := do
  if i < pattern.length
  then
    let chars := (pattern.data.drop i).takeWhile (fun c => '0' <= c && c <= '9')
    if h : 0 < chars.length then
      let val := chars |> List.foldl (init := 0) (fun b c => (c.val - '0'.val).toNat+10*b)
      Except.ok (⟨chars.length, h⟩, val)
    else Except.error (toError pattern .DecimalInvalid)
  else Except.error (toError pattern .DecimalInvalid)

private def parse_counted_repetition (pattern : String) (i : Nat) (concat : Concat)
    : Except String (NChars × Concat) := do
  match concat.asts.pop? with
  | some (ast, asts) =>
    if match ast with | .Empty => true | .Flags _ => true | _ => false
    then Except.error (toErrorAt pattern i .RepetitionMissing)
    else
      let greedy  := true
      let (n, count_start) ← parse_decimal pattern i
      let c := pattern.getAtCodepoint (i+n.val)
      if c = ',' then
        let c := pattern.getAtCodepoint (i+n.val+1)
        if c = '}' then
          let asts := asts.push (
              Ast.Repetition
                (Repetition.mk
                  (Syntax.Ast.span ast)
                  ⟨(toSpan pattern (i) (i+n.val+2)),
                  (RepetitionKind.Range (RepetitionRange.AtLeast count_start))⟩
                  greedy
                  ast
              ))
          Except.ok (1 +(n.val+1), (Concat.mk (Syntax.Ast.span ast) asts))
        else
          let (m, count_end) ← parse_decimal pattern (i+n.val+1)
          let c := pattern.getAtCodepoint (i+n.val+1+m.val)
          if c = '}' then
            let asts := asts.push (
                Ast.Repetition
                  (Repetition.mk
                    (Syntax.Ast.span ast)
                    ⟨(toSpan pattern (i) (i+n.val+2)),
                    (RepetitionKind.Range (RepetitionRange.Bounded count_start count_end))⟩
                    greedy
                    ast
                ))
            Except.ok (1 + (n.val+m.val+1), (Concat.mk (Syntax.Ast.span ast) asts))
          else Except.error (toError pattern .RepetitionCountUnclosed)
      else if c = '}' then
        let asts := asts.push (
            Ast.Repetition
              (Repetition.mk
                (Syntax.Ast.span ast)
                ⟨(toSpan pattern (i-1) (i+n.val+1)),
                (RepetitionKind.Range (RepetitionRange.Exactly count_start))⟩
                greedy
                ast
            ))
        Except.ok (1 + n.val, (Concat.mk (Syntax.Ast.span ast) asts))
      else Except.error (toError pattern .RepetitionCountUnclosed)
  | none => Except.error (toErrorAt pattern i .RepetitionMissing)

/-- Parse a single item in a character class as a primitive -/
private def parse_set_class_item (pattern : String) (i : Nat)
    : Except String (NatPos × Primitive) := do
  let c := pattern.getAtCodepoint i
  match c with
  | '\\' =>
    let (⟨n, _⟩ , p) ← parse_escape pattern (i + 1)
    Except.ok (NatPos.succ n, p)
  | _ =>
    let lit := ⟨⟨pattern, ⟨i⟩, ⟨i + 1⟩⟩, LiteralKind.Verbatim, c⟩
    Except.ok (⟨1, by simp⟩ , Primitive.Literal lit)

/-- Parse a single primitive item in a character class set. -/
private def parse_set_class_range (pattern : String) (i : Nat)
    : Except String (NatPos × ClassSetItem) := do
  let (⟨n1, h⟩, prim1) ←  parse_set_class_item pattern i
  let c := pattern.getAtCodepoint (i + n1)
  if c != '-' || (pattern.getAtCodepoint (i + n1 + 1)) = ']'
  then
    Except.ok (⟨n1, h⟩, ←prim1.into_class_set_item)
  else
    let (⟨n2, _⟩, prim2) ←  parse_set_class_item pattern (i + n1 + 1)
    let lit1 ←prim1.into_class_literal
    let lit2 ←prim2.into_class_literal
    if lit1.c.val <= lit2.c.val
    then
      let range : ClassSetRange :=
        ⟨⟨pattern, ⟨i⟩, ⟨i + n1 + n2 + 1⟩⟩, lit1, lit2⟩
      Except.ok (⟨1 + n1 + n2, by simp_arith[Nat.zero_lt_one_add _]⟩, ClassSetItem.Range range)
    else Except.error (toError pattern .ClassRangeInvalid)

/-- Parses the opening of a character class set. -/
private def parse_set_class_open (pattern : String) (i : Nat)
    : Except String (NChars × ClassBracketed × ClassSetUnion) :=
  let span := toSpan pattern i (i + 1)
  let union : ClassSetUnion := ⟨span, #[]⟩
  let item : ClassSetItem := ClassSetItem.Union union
  let c := pattern.getAtCodepoint (i + 1)
  let (n, negated) :=  if c = '^' then (1, true) else (0, false)

  let c := pattern.getAtCodepoint (i + 1 + n)
  /- If `]` is the *first* char in a set, then interpret it as a literal `]`. -/
  let (m, union) :=
    if union.items.size = 0 && c = ']'
    then (1, ⟨span, union.items.push (ClassSetItem.Literal ⟨span, LiteralKind.Verbatim, c⟩ )⟩)
    else (0, union)

  let clsBracketed := ClassBracketed.mk (toSpan pattern i (i+1)) negated (ClassSet.Item item)
  Except.ok (n + m, (clsBracketed, union))

/-- Parse the opening of a character class and push the current class onto the parser's stack. -/
private def push_class_open (pattern : String) (i : Nat) (parent_union: ClassSetUnion)
    : ParserM (NChars × ClassSetUnion) := do
  let parser ← get
  let (n, nested_set, nested_union) ←  parse_set_class_open pattern i
  let stack := parser.stack_class.push (ClassState.Open parent_union nested_set)
  set {parser with stack_class := stack}
  pure (n, nested_union)

/-- Pop a character class set op from the character class parser stack. -/
private def pop_class_op (rhs: ClassSet) : ParserM ClassSet := do
  let parser ← get
  match parser.stack_class.pop? with
  | some (ClassState.Open union clsset, stack) =>
    let stack := stack.push (ClassState.Open union clsset)
    set {parser with stack_class := stack}
    pure rhs
  | some (ClassState.Op _ _, _) => throw "ClassState.Op nyi"
  | _ => throw "internal error: pop_class_op unexpected empty character class stack"

/-- Parse the end of a character class set and pop the character class parser stack. -/
private def pop_class (nested_union : ClassSetUnion)
    : ParserM (Either ClassSetUnion ClassBracketed) := do
  let ⟨span, _⟩ := nested_union
  let item := ClassSet.Item nested_union.into_item
  let prevset ←  pop_class_op item
  let parser ← get
  match parser.stack_class.pop? with
  | some (ClassState.Open _ ⟨_, negated, _⟩, stack) =>
    let clsset : ClassBracketed := ⟨span, negated, prevset⟩
    if stack.size = 0
    then
      set {parser with stack_class := stack}
      pure (Either.Right clsset)
    else throw "pop_class, .ClassSetItem.Bracketed nyi"
  | some (ClassState.Op _ _, _) => throw "pop_class, .Op nyi"
  | none => throw "internal error: pop_class unexpected empty character class stack"

private def parse_set_class_loop (pattern : String) (i : Nat) (union : ClassSetUnion)
    : ParserM (NChars × ClassBracketed) := do
  if h₀ : i >= pattern.length
  then Except.error (toError pattern .ClassUnclosed)
  else
    let ⟨span, items⟩ := union
    let c := pattern.getAtCodepoint i
    match c with
    | '[' =>
      let maybe_parsed :=
        if (← get).stack_class.size > 0
        then
          match ← maybe_parse_ascii_class pattern i with
          | some (n, cls) =>
            let union : ClassSetUnion := ⟨span, items.push (ClassSetItem.Ascii cls)⟩
            some (n, union)
          | none => none
        else none

      let (n, union) ←
        match maybe_parsed with
        | some (n, union) => pure (n, union)
        | none => push_class_open pattern i union
      have : pattern.length - (i + n + 1) < pattern.length - i :=
        Nat.sum_succ_lt_of_not_gt pattern.length i n h₀
      parse_set_class_loop pattern (i + n + 1) union
    | ']' =>
      match ← pop_class union with
      | .Left nested_union =>
        have : pattern.length - (i + 1) < pattern.length - i :=
          Nat.succ_lt_of_not_gt pattern.length i h₀
        parse_set_class_loop pattern (i + 1) nested_union
      | .Right cls =>
        pure (i + 1, cls)
    | _ =>
      let (⟨n, h⟩, range) ←  parse_set_class_range pattern i
      let union : ClassSetUnion := ⟨span, items.push range⟩
      have : pattern.length - (i + n) < pattern.length - i :=
        Nat.sum_lt_of_not_gt pattern.length i n h₀ h
      parse_set_class_loop pattern (i + n) union
termination_by _ => pattern.length - i

/-- Parse a standard character class consisting primarily of characters or character ranges. -/
private def parse_set_class (pattern : String) (i : Nat)
    : ParserM (NatPos × ClassBracketed) := do
  let union : ClassSetUnion := ⟨toSpan pattern i (i+1), #[]⟩
  let (i', cls) ← parse_set_class_loop pattern i union
  let n := i' - i
  if h : 0 < n
  then pure (⟨n, h⟩, cls)
  else throw s!"parse_set_class: internal error excpeted i {i} < i' {i'}"

/-- Parse a primitive AST. e.g., A literal, non-set character class or assertion.-/
private def parse_primitive (pattern : String) (i : Nat) : Except String (NatPos × Primitive) := do
  let c := pattern.getAtCodepoint i
  match c with
  | '\\' =>
    let (⟨n, _⟩, p) ← parse_escape pattern (i + 1)
    Except.ok (⟨1 + n, Nat.zero_lt_one_add _⟩, p)
  | '.' => Except.ok (⟨1, by simp⟩, Primitive.Dot (toSpan pattern i (i + 1)))
  | '^' => Except.ok (⟨1, by simp⟩,
              Primitive.Assertion ⟨toSpan pattern i (i + 1), AssertionKind.StartLine⟩)
  | '$' => Except.ok (⟨1, by simp⟩,
              Primitive.Assertion ⟨toSpan pattern i (i + 1), AssertionKind.EndLine⟩)
  | _ =>
    let lit := ⟨⟨pattern, ⟨i⟩, ⟨i + 1⟩⟩, LiteralKind.Verbatim, c⟩
    Except.ok (⟨1, by simp⟩, Primitive.Literal lit)

/-- Parses an uncounted repetition operation. -/
private def parse_uncounted_repetition (pattern : String) (i : Nat) (kind: RepetitionKind)
    (concat : Concat) : Except String (NChars × Concat) := do
  match Array.pop? concat.asts with
  | some (ast, asts) =>
    let op : Ast.RepetitionOp := ⟨⟨pattern, ⟨i⟩, ⟨i + 1⟩⟩, kind⟩
    let c := pattern.getAtCodepoint (i + 1)
    let (n, greedy)  := if c = '?' then (1, false) else (0, true)
    let r : Repetition := Repetition.mk (toSpan pattern i (i + 1)) op greedy ast
    let asts := asts.push (Ast.Repetition r)
    Except.ok (n, Concat.mk (concat.span) asts)
  | none => Except.error (toErrorAt pattern i .RepetitionMissing)

/-- Pushes or adds the given branch of an alternation to the parser's internal stack of state.-/
private def push_or_add_alternation (pattern : String) (i : Nat) (concat : Concat)
    : ParserM PUnit := do
  let parser ← get
  match Array.pop? parser.stack_group with
  | some (GroupState.Alternation ⟨span, asts⟩, stack_group) =>
    let alt : Alternation := ⟨span, asts.push (concat.into_ast)⟩
    set {parser with stack_group := stack_group.push (GroupState.Alternation alt)}
    pure ()
  | _ =>
    let alt := Alternation.mk (toSpan pattern i (i + 1)) #[concat.into_ast]
    set {parser with stack_group := parser.stack_group.push (GroupState.Alternation alt)}
    pure ()

/-- Parse and push a single alternation on to the parser's internal stack. -/
private def push_alternate (pattern : String) (i : Nat) (concat : Concat)
    : ParserM Concat := do
  let _ ← push_or_add_alternation pattern i concat
  pure (Concat.mk (toSpan pattern i (i + 1)) #[])

/-- Parse the current character as a flag. -/
private def parse_flag (c : Char) : Except String Flag :=
  match c with
  | 'i' => Except.ok Flag.CaseInsensitive
  | 'm' => Except.ok Flag.MultiLine
  | 's' => Except.ok Flag.DotMatchesNewLine
  | 'U' => Except.ok Flag.SwapGreed
  | 'u' => Except.ok Flag.Unicode
  | 'R' => Except.ok Flag.CRLF
  | 'x' => Except.ok Flag.IgnoreWhitespace
  | _ => Except.error (toError c.toString .FlagUnrecognized)

/-- Parse a sequence of flags starting at the current character.-/
private def parse_flags (pattern : String) (i : Nat)
    : Except String (NChars × Flags) := do
  let chars := (pattern.data.drop i).takeWhile (fun c => c != ':' && c != ')') |> List.toArray
  let span := toSpan pattern i (i + 1)
  let items : Array FlagsItem ←
    chars |> Array.mapM (fun c => do
      if c = '-' then pure ⟨span, FlagsItemKind.Negation⟩
      else
        let f ← parse_flag c
        pure ⟨span, FlagsItemKind.Flag f⟩)
  let flags : Flags := ⟨(toSpan pattern i chars.size), items⟩
  Except.ok (chars.size, flags)

/-- Parse a group (which contains a sub-expression) or a set of flags. -/
private def parse_group (pattern : String) (i : Nat)
    : ParserM (NChars × (Either SetFlags Group)) := do
  let parser ← get
  let c1 := pattern.getAtCodepoint i
  let c2 := pattern.getAtCodepoint (i + 1)
  let c3 := pattern.getAtCodepoint (i + 2)
  if c1 = '?' && c2  = 'P' && c3  = '<' then
    let chars := (pattern.data.drop (i+2)).takeWhile (· != '>')
    let n := chars.length + 3
    let parser := {parser with capture_index := parser.capture_index + 1 }
    -- todo: add CaptureName
    let g := Group.mk (toSpan pattern i (i + n + 1)) (.CaptureIndex parser.capture_index) Ast.Empty
    set parser
    pure (n, Either.Right g)
  else if c1 = '?'
  then
    let (n, flags) ← parse_flags pattern (i + 1)
    let c1 := pattern.getAtCodepoint (i + 1 + n)
    if c1 = ')'
    then
      if flags.items.size = 0 then Except.error (toError pattern .RepetitionMissing)
      else
        let sf : SetFlags := ⟨toSpan pattern i (i + 1), flags⟩
        pure (n + 2, Either.Left sf)
    else
      let g := Group.mk (toSpan pattern i (i + 1)) (.NonCapturing flags) Ast.Empty
      pure (n + 2, Either.Right g)
  else
    let parser := {parser with capture_index := parser.capture_index + 1 }
    let g := Group.mk (toSpan pattern i (i + 1)) (.CaptureIndex parser.capture_index) Ast.Empty
    set parser
    pure (0, Either.Right g)

/-- Parse and push a group AST. -/
private def push_group (pattern : String) (i : Nat) (concat : Concat)
    : ParserM (NChars × Concat) := do
  let (n, group) ← parse_group pattern i
  match group with
  | .Left flags =>
    pure (n, Concat.mk (toSpan pattern i (i + 1)) (concat.asts.push (Ast.Flags flags)))
  | .Right group =>
    let parser ← get
    set {parser with stack_group := parser.stack_group.push (GroupState.Group concat group)}
    pure (n, Concat.mk (toSpan pattern i (i + 1)) #[])

/-- Pop a group AST from the parser's internal stack and set the group's AST to the concatenation.-/
private def pop_group (pattern : String) (i : Nat) (group_concat : Concat)
    : ParserM Concat := do
  let parser ← get
  match Array.pop? parser.stack_group with
  | some (GroupState.Group prior_concat ⟨⟨s, start, _⟩ , kind, _⟩ , stack_group) =>
    let group := Group.mk ⟨s, start, ⟨i⟩ ⟩ kind group_concat.into_ast
    let prior_concat := Concat.mk prior_concat.span (prior_concat.asts.push (Ast.Group group))
    set {parser with stack_group := stack_group }
    pure prior_concat
  | some (GroupState.Alternation alt, stack_group) =>
    match Array.pop? stack_group with
    | some (GroupState.Group prior_concat ⟨⟨s, start, _⟩ , kind, _⟩ , stack_group) =>
      let ⟨span, asts⟩ := alt
      let asts := asts.push (group_concat.into_ast)
      let alt : Alternation := ⟨span, asts⟩
      let group := Group.mk ⟨s, start, ⟨i⟩ ⟩ kind alt.into_ast
      let prior_concat := Concat.mk prior_concat.span (prior_concat.asts.push (Ast.Group group))
      set {parser with stack_group := stack_group }
      pure prior_concat
    | _ => throw (toError pattern .GroupUnopened)
  | _ => throw (toError pattern .GroupUnopened)

private def pop_group_end (pattern : String) (concat : Concat) (parser : Parser)
    : Except String Ast :=
  match Array.pop? parser.stack_group with
  | some (GroupState.Alternation ⟨span, asts⟩, stack_group) =>
    if stack_group.size != 0
    then Except.error (toError pattern .GroupUnclosed "pop_group_end GroupState.Alternation")
    else
      let alt : Alternation := ⟨span, asts.push (concat.into_ast)⟩
      Except.ok (Ast.Alternation alt)
  | some (GroupState.Group _ _, _) =>
    Except.error (toError pattern .GroupUnclosed "pop_group_end GroupState.Group")
  | none =>
    Except.ok concat.into_ast

/-- Parse the regular expression and return an abstract syntax tree. -/
def parse (pattern : String) : Except String Ast := do
  let concat : Concat := Concat.mk (toSpan pattern 0 pattern.length) #[]
  let (concat, parser) ← loop pattern 0 concat default
  pop_group_end pattern concat parser
  where
    /-- loop over chars of `pattern` to parse the regular expression -/
    loop (pattern : String) (i : Nat) (concat : Concat) : ParserM Concat := do
    if h₀ : i >= pattern.length
    then pure concat
    else
      let c := pattern.getAtCodepoint i
      match c with
      | '(' =>
        let (n, concat) ← push_group pattern (i + 1) concat
        have : pattern.length - (i + n + 1) < pattern.length - i := by
          simp [Nat.sum_succ_lt_of_not_gt _ _ _ h₀]
        loop pattern (i+n+1) concat
      | ')' =>
        let concat ← pop_group pattern (i + 1) concat
        have : pattern.length - (i + 1) < pattern.length - i := by
          simp [Nat.succ_lt_of_not_gt _ _ h₀]
        loop pattern (i+1) concat
      | '|' =>
        let concat ← push_alternate pattern i concat
        have : pattern.length - (i + 1) < pattern.length - i := by
          simp [Nat.succ_lt_of_not_gt _ _ h₀]
        loop pattern (i+1) concat
      | '[' =>
        let (⟨n, h₁⟩, cls) ← parse_set_class pattern i
        let asts := concat.asts.push (Ast.ClassBracketed cls)
        have : pattern.length - (i + n) < pattern.length - i := by
          simp [Nat.sum_lt_of_not_gt _ _ _ h₀ h₁]
        loop pattern (i+n) (Concat.mk (concat.span) asts)
      | '?' =>
        let (n, p) ← parse_uncounted_repetition pattern i RepetitionKind.ZeroOrOne concat
        have : pattern.length - (i + n + 1) < pattern.length - i := by
          simp [Nat.sum_succ_lt_of_not_gt _ _ _ h₀]
        loop pattern (i+n+1) p
      | '*' =>
        let (n, p) ← parse_uncounted_repetition pattern i RepetitionKind.ZeroOrMore concat
        have : pattern.length - (i + n + 1) < pattern.length - i := by
          simp [Nat.sum_succ_lt_of_not_gt _ _ _ h₀]
        loop pattern (i+n+1) p
      | '+' =>
        let (n, p) ← parse_uncounted_repetition pattern i RepetitionKind.OneOrMore concat
        have : pattern.length - (i + n + 1) < pattern.length - i := by
          simp [Nat.sum_succ_lt_of_not_gt _ _ _ h₀]
        loop pattern (i+n+1) p
      | '{' =>
        let (n, concat) ← parse_counted_repetition pattern (i + 1) concat
        have : pattern.length - (i + n + 1) < pattern.length - i := by
          simp [Nat.sum_succ_lt_of_not_gt _ _ _ h₀]
        loop pattern (i+n+1) concat
      | _ =>
        let (⟨n, h₁⟩, p) ← parse_primitive pattern i
        let asts := concat.asts.push p.into_ast
        have : pattern.length - (i + n) < pattern.length - i := by
          simp [Nat.sum_lt_of_not_gt _ _ _ h₀ h₁]
        loop pattern (i+n) (Concat.mk (concat.span) asts)
  termination_by _ => pattern.length - i
