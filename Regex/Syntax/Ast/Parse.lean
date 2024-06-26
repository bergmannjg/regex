import Batteries.Data.Nat.Lemmas
import Regex.Data.Array.Basic
import Regex.Syntax.Ast.Ast
import Regex.Utils

namespace Syntax

/-- Flavor of regular expressions -/
inductive Flavor where
  /-- Perl-compatible regular expressions (https://www.pcre.org/current/doc/html). -/
  | Pcre : Flavor
  /-- Rust-compatible regular expressions (https://docs.rs/regex/latest/regex/#syntax). -/
  | Rust : Flavor
deriving BEq

instance : Inhabited Flavor := ⟨Syntax.Flavor.Pcre⟩

end Syntax

namespace Syntax.AstItems

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
  /-- The maximal single digit backreference. -/
  max_backreference : Nat
  /-- Disable pattern metacharacters from \Q until \E -/
  disabled_metacharacters : Bool
  /-- A stack of grouped sub-expressions, including alternations. -/
  stack_group: Array GroupState
  /-- A stack of nested character classes. -/
  stack_class: Array ClassState

instance : Inhabited Parser := ⟨0, 0, false, #[], #[]⟩

abbrev ParserM := ReaderT Flavor $ StateT Parser (Except String)

/-- Represents the count of parsed chars -/
abbrev NChars := Nat

private def is_hex(c : Char) : Bool :=
  ('0' <= c && c <= '9') || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')

private def is_ascii (c : Char) : Bool :=
  c.val <= 0x7F

private def is_whitespace (c : Char) :=
  c = ' ' || '\x09' ≤ c && c ≤ '\x0d'

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

/- todo : check FlagsItemKind.Negation -/
def is_whitespace_enabled (concat : Concat) : Bool :=
  Array.any concat.asts (fun ast =>
    match ast with
    | .Flags ⟨_, ⟨_, flags⟩⟩ =>
      Array.any flags (fun flag =>
        match flag with
        | ⟨_, .Flag .IgnoreWhitespace⟩  => true
        | _ => false)
    | _ => false)

private def consume_space (concat : Concat) (pattern : String) (i : Nat) : Nat :=
  if !is_whitespace_enabled concat then i
  else if i >= pattern.length then i
  else if is_whitespace (pattern.getAtCodepoint i)
  then consume_space concat pattern (i+1)
  else i
termination_by pattern.length - i

theorem consume_space_ge (concat : Concat) (pattern : String) (i : Nat)
    : i ≤ consume_space concat pattern i := by
  induction i using consume_space.induct concat pattern with
  | case1 _ _ => unfold consume_space; split <;> omega
  | case2 _ _ _ => unfold consume_space; split <;> omega
  | case3 _ _ _ _ => unfold consume_space; split <;> omega
  | case4 _ _  _ => unfold consume_space; split <;> omega

/-- get NextNonSpaceChar and returns consumed chars -/
private def nextNonSpaceChar (pattern : String) (i : Nat) (offset : Nat := 0) : NChars × Char :=
  if i + offset >= pattern.length then (offset, default)
  else if is_whitespace (pattern.getAtCodepoint (i+offset))
  then nextNonSpaceChar pattern i (offset + 1)
  else (1 + offset, pattern.getAtCodepoint (i + offset))
termination_by pattern.length - (i + offset)

end AstItems
end Syntax

/-- test if NextNonSpaceChar is `c` and returns consumed chars inclusive `c` -/
def Char.isNextNonSpaceChar (c : Char) (p : String) (i : Nat) : Option Syntax.AstItems.NChars :=
  let (offset, c1) := Syntax.AstItems.nextNonSpaceChar p i
  if c = c1 then some offset else none

namespace Syntax
namespace AstItems

/-- Parse a hex representation of any Unicode scalar value. -/
private def parse_hex_brace (pattern : String) (i : Nat) (kind: HexLiteralKind)
    : Except String (NChars × Literal) := do
  let chars := (pattern.data.drop (i + 1)).takeWhile (· != '}')
  if chars.all (is_hex ·) && chars.length > 0 && chars.length <= 6
  then
    let val ← Char.decodeHexDigits chars
    if h : isValidChar val
    then
      Except.ok (chars.length + 2, ⟨(String.toSpan pattern i (i + chars.length + 1)),
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
      let n ← Char.decodeHexDigits chars
      if h : isValidChar n
      then
        Except.ok (kind.digits, ⟨⟨pattern, ⟨i⟩, ⟨i + kind.digits⟩⟩, LiteralKind.Hex kind, ⟨n, h⟩⟩)
      else Except.error (toError pattern .EscapeHexInvalid)
    else Except.error (toError pattern .EscapeHexInvalidDigit)
  else Except.error (toError pattern .EscapeUnexpectedEof)

private def guess_kind (pattern : String) (i : Nat) : HexLiteralKind :=
  if i + 2 <= pattern.length
  then
    let c := pattern.getAtCodepoint (i + 2)
    if c.isHexDigit then HexLiteralKind.X else HexLiteralKind.x
  else HexLiteralKind.x

/-- Parse a hex representation of a Unicode codepoint. -/
private def parse_hex (pattern : String) (i : Nat)
    : ParserM (NChars × Literal) := do
  let flavor ← read
  let kind := match pattern.getAtCodepoint i with
    | 'x' => guess_kind pattern i
    | _ => HexLiteralKind.UnicodeShort
  if pattern.getAtCodepoint (i + 1) = '{'
  then parse_hex_brace pattern (i + 1) kind
  else
    if flavor == Flavor.Pcre && 'x' = pattern.getAtCodepoint i && !(pattern.getAtCodepoint (i+1)).isHexDigit
    then
      let lit : Literal := ⟨String.toSpan pattern (i - 1) (i + 1), LiteralKind.Verbatim, ⟨0, by simp_arith⟩⟩
      pure (0, lit)
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

/-- Attempt to parse a specialty word boundary. That is, `\b{start}`,
    `\b{end}`, `\b{start-half}` or `\b{end-half}`. -/
private def maybe_parse_special_word_boundary (pattern : String) (i : Nat)
    : Except String (Option (NChars × AssertionKind)) := do
  let n := 2
  let chars := (pattern.data.drop (i + n)).takeWhile (· != '}')
  if i + n + chars.length < pattern.length
  then
    let name : String := ⟨chars⟩
    match name with
    | "start" => Except.ok (some (n + chars.length, AssertionKind.WordBoundaryStart))
    | "end" => Except.ok (some (n + chars.length, AssertionKind.WordBoundaryEnd))
    | "start-half" => Except.ok (some (n + chars.length, AssertionKind.WordBoundaryStartHalf))
    | "end-half" => Except.ok (some (n + chars.length, AssertionKind.WordBoundaryEndHalf))
    | _ => Except.error (toError pattern .SpecialWordBoundaryUnrecognized)
  else
    Except.ok none

private def maybe_parse_backref_num (pattern : String) (i : Nat)
    : ParserM $ Option (NChars × BackRef) := do
  let state ← get
  let (offset0, c) := nextNonSpaceChar pattern i
  let c1 := pattern.getAtCodepoint (i + offset0)
  let (_, c2) := nextNonSpaceChar pattern (i + offset0 + 1)
  match (c.isDigit, c1.isDigit, c2.isDigit) with
  | (true, false, _) =>
    let span := String.toSpan pattern (i - 1) (i)
    let n := (c.val - '0'.val).toNat
    if 0 = n then pure none
    else
      if n > state.max_backreference then set {state with max_backreference := n}
      pure (some (offset0, ⟨span, n⟩))
  | (true, true, false) =>
    let span := String.toSpan pattern (i - 1) (i)
    let n := (c.val - '0'.val).toNat * 10 + (c1.val - '0'.val).toNat
    if 0 < n && n ≤ state.capture_index
    then pure (some (offset0 + 1, ⟨span, n⟩))
    else pure none
  | (_, _, _) => pure none

private def maybe_parse_backref (pattern : String) (i : Nat)
    : ParserM $ Option (NChars × BackRef) := do
  let state ← get
  let c := pattern.getAtCodepoint (i)
  if c.isDigit
  then maybe_parse_backref_num pattern i
  else if c = 'g' then
    let (offset1, c1) := nextNonSpaceChar pattern (i + 1)
    let (offset2, c2) := nextNonSpaceChar pattern (i + 1 + offset1)
    match (c1, c2) with
    | ('{', '-')  =>
      let offset := offset1 + offset2
      match ← maybe_parse_backref_num pattern (i + 1 + offset) with
      | some (n, ⟨span, b⟩) =>
        let (offset2, c2) := nextNonSpaceChar pattern (i + 1 + offset + n)
        if c2 = '}' then
          if b ≤ state.capture_index then pure (1 + offset + n + offset2, (⟨span, state.capture_index + 1 - b⟩ : BackRef))
          else pure none
        else pure none
      | none => pure none
    | ('{', _)  =>
      match ← maybe_parse_backref_num pattern (i + 1 + offset1) with
      | some (n, b) =>
        let (offset2, c2) := nextNonSpaceChar pattern (i + 1 + offset1 + n)
        if c2 = '}' then pure (1 + offset1 + n + offset2, b) else pure none
      | none => pure none
    | ('-', _)  =>
      match ← maybe_parse_backref_num pattern (i + 1 + offset1) with
      | some (n, ⟨span, b⟩) =>
        if b ≤ state.capture_index then pure (1 + offset1 + n, (⟨span, state.capture_index + 1 - b⟩ : BackRef))
        else pure none
      | none => pure none
    | (_, _)  =>
      match ← maybe_parse_backref_num pattern (i + offset1) with
      | some (n, b) => pure (offset1 + n, b)
      | none => pure none
  else pure none

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
            ⟨String.toSpan pattern (i - 2) (i + 1 + chars.length + 1),
            negated,
            ClassUnicodeKind.NamedValue ClassUnicodeOpKind.Equal n v⟩
        | _ =>
            ⟨String.toSpan pattern (i - 2) (i + 1 + chars.length + 1),
            negated,
            ClassUnicodeKind.Named ⟨chars⟩ ⟩
        Except.ok (1 + 1 + chars.length, cls)
    else
      Except.error (toError pattern .EscapeUnexpectedEof)
  else
    let cls : ClassUnicode := ⟨String.toSpan pattern (i - 2) (i + 1), negated, ClassUnicodeKind.OneLetter c⟩
    Except.ok (1, cls)

/-- Parse a Perl character class, e.g., `\d` or `\W`. -/
private def parse_perl_class (pattern : String) (i : Nat) : ParserM ClassPerl := do
  let c := pattern.getAtCodepoint (i)
  let (neg, kind) ← match c with
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

  pure ⟨⟨pattern, ⟨i⟩, ⟨i + 1⟩⟩, kind, neg⟩

private def parse_control_char (pattern : String) (i : Nat)
    : Except String (NatPos × Primitive) := do
  let toControl (n : UInt32) : Primitive :=
    let c : Char := if h : UInt32.isValidChar (n) then ⟨n, h⟩ else ⟨0, by simp_arith⟩
    let lit : Literal := ⟨String.toSpan pattern (i - 1) (i + 1), LiteralKind.Verbatim, c⟩
    Primitive.Literal lit
  let c := pattern.getAtCodepoint (i+1)
  if c.isUpper then pure (NatPos.succ 1, toControl (c.val - 'A'.val + 1))
  else if c.isLower then pure (NatPos.succ 1, toControl (c.val - 'a'.val + 1))
  else if c.val ≥ 32 && c.val ≤ 64 then pure (NatPos.succ 1, toControl (c.val - 32 + 96))
  else if c.val ≥ 91 && c.val ≤ 96 then pure (NatPos.succ 1, toControl (c.val - 91 + 27))
  else Except.error (toError pattern .EscapeUnrecognized)

/-- Parse an escape sequence as a primitive AST. -/
private def parse_escape (pattern : String) (i : Nat) (inSetClass : Bool := false)
    : ParserM (NatPos × Primitive) := do
  let flavor ← read
  let toVerbatim (c : Char) : Primitive :=
    let lit : Literal := ⟨String.toSpan pattern (i - 1) (i + 1), LiteralKind.Verbatim, c⟩
    Primitive.Literal lit
  let c := pattern.getAtCodepoint (i)
  match c with
  | 'u' | 'x' =>
    let (n, lit) ← parse_hex pattern i
    pure (NatPos.succ n, Primitive.Literal lit)
  | 'p' | 'P' =>
    let (n, cls) ← parse_unicode_class (c = 'P') pattern (i + 1)
    pure (NatPos.succ n, Primitive.Unicode cls)
  | 'd' | 'h' | 's' | 'v' | 'w' | 'D' | 'H' | 'N' | 'S' | 'V' | 'W' =>
    let cls ← parse_perl_class pattern i
    pure (NatPos.succ 0, Primitive.Perl cls)
  | 'a' => pure (NatPos.one, toVerbatim '\x07')
  | 'b' =>
    if inSetClass then pure (NatPos.one, toVerbatim '\x08')
    else if '{' = pattern.getAtCodepoint (i + 1) then
      match ← maybe_parse_special_word_boundary pattern i with
      | some (n, kind) =>
        pure (NatPos.succ n,
          Primitive.Assertion ⟨String.toSpan pattern i (i + n + 1), kind⟩)
      | none => Except.error (toError pattern .EscapeUnrecognized)
    else
      pure (NatPos.succ 0,
        Primitive.Assertion ⟨String.toSpan pattern i (i + 1), AssertionKind.WordBoundary⟩)
  | 'c' =>
    if flavor == Flavor.Pcre
    then parse_control_char pattern i
    else Except.error (toError pattern .EscapeUnrecognized)
  | 'e' => pure (NatPos.one, toVerbatim '\x07')
  | 'f' => pure (NatPos.one, toVerbatim '\x0C')
  | 'n' => pure (NatPos.one, toVerbatim '\n')
  | 'o' =>
      let c1 := pattern.getAtCodepoint (i+1)
      if c1 = '{' then
          let chars := (pattern.data.drop (i + 2)).takeWhile (fun c => '0' <= c && c <= '7')
          let c2 := pattern.getAtCodepoint (i+2+chars.length)
          if c2 = '}' && 0 < chars.length && chars.length <= 3 then
            let n ← Char.decodeOctDigits chars
            if h : isValidChar n
            then
              let x : AstItems.Literal := ⟨String.toSpan pattern i (i + 2 + chars.length), LiteralKind.Verbatim, ⟨n, h⟩⟩
              pure (NatPos.succ (2 + chars.length), Primitive.Literal x)
            else Except.error (toError pattern .EscapeOctalInvalid)
          else Except.error (toError pattern .EscapeOctalInvalid)
      else
       pure (NatPos.one, toVerbatim c)
  | 'r' => pure (NatPos.one, toVerbatim '\r')
  | 't' => pure (NatPos.one, toVerbatim '\t')
  | 'z' =>
    pure (NatPos.succ 0,
      Primitive.Assertion ⟨String.toSpan pattern i (i + 1), AssertionKind.EndText⟩)
  | 'A' =>
    pure (NatPos.succ 0,
      Primitive.Assertion ⟨String.toSpan pattern i (i + 1), AssertionKind.StartText⟩)
  | 'B' =>
    pure (NatPos.succ 0,
      Primitive.Assertion ⟨String.toSpan pattern i (i + 1), AssertionKind.NotWordBoundary⟩)
  | 'G' =>
    if flavor == Flavor.Pcre
    then  pure (NatPos.succ 0,
      Primitive.Assertion ⟨String.toSpan pattern i (i + 1), AssertionKind.PreviousMatch⟩)
    else Except.error (toError pattern .EscapeUnrecognized)
  | 'K' =>
    if flavor == Flavor.Pcre
    then  pure (NatPos.succ 0,
      Primitive.Assertion ⟨String.toSpan pattern i (i + 1), AssertionKind.ClearMatches⟩)
    else Except.error (toError pattern .EscapeUnrecognized)
  | 'Z' =>
    pure (NatPos.succ 0,
      Primitive.Assertion ⟨String.toSpan pattern i (i + 1), AssertionKind.EndTextWithOptionalLF⟩)
  | _ =>
    if is_meta_character c
    then pure (NatPos.one, toVerbatim c)
    else if is_escapeable_character c
    then pure (NatPos.one, toVerbatim c)
    else if flavor == Flavor.Pcre then
      let c1 := pattern.getAtCodepoint (i+1)
      let c2 := pattern.getAtCodepoint (i+2)
      if c.isDigit && !c1.isDigit
      then if inSetClass && '8' ≤ c && c ≤ '9' then pure (NatPos.one, toVerbatim c) else
        let n ← Char.decodeOctDigits [c]
        if h : isValidChar n
        then
          let x : AstItems.Literal := ⟨String.toSpan pattern i (i + 1), LiteralKind.Verbatim, ⟨n, h⟩⟩
          pure (NatPos.succ 0, Primitive.Literal x)
        else Except.error (toError pattern .EscapeHexInvalid)
      else if c.isDigit && c1.isDigit && c2.isDigit
      then
        let n ← Char.decodeOctDigits [c, c1, c2]
        if h : isValidChar n
        then
          let x : AstItems.Literal := ⟨String.toSpan pattern i (i + 1), LiteralKind.Verbatim, ⟨n, h⟩⟩
          pure (NatPos.succ 2, Primitive.Literal x)
        else Except.error (toError pattern .EscapeHexInvalid)
      else if c.isDigit && c1.isDigit && !c2.isDigit
      then
        let n ← Char.decodeOctDigits [c, c1]
        if h : isValidChar n
        then
          let x : AstItems.Literal := ⟨String.toSpan pattern i (i + 1), LiteralKind.Verbatim, ⟨n, h⟩⟩
          pure (NatPos.succ 1, Primitive.Literal x)
        else Except.error (toError pattern .EscapeHexInvalid)
      else pure (NatPos.one, toVerbatim c)
    else Except.error (toError pattern .EscapeUnrecognized)

private def parse_decimal (pattern : String) (i : Nat) : Except String (NChars × Nat) := do
  if i < pattern.length
  then
    let ws := (pattern.data.drop i).takeWhile (fun c => is_whitespace c)
    let chars := (pattern.data.drop (i + ws.length)).takeWhile (fun c => '0' <= c && c <= '9')
    if 0 < chars.length then
      let val := chars |> List.foldl (init := 0) (fun b c => (c.val - '0'.val).toNat+10*b)
      Except.ok (chars.length + ws.length, val)
    else Except.error (toError pattern .DecimalInvalid)
  else Except.error (toError pattern .DecimalInvalid)

theorem parse_decimal_gt_zero (pattern : String) (i : Nat)
    (h : parse_decimal pattern i = Except.ok (offset, n)) : 0 < offset := by
  unfold  parse_decimal at h
  split at h <;> try simp_all
  split at h <;> try simp_all
  rename_i hCharsLt
  let ws := List.takeWhile (fun c => Syntax.AstItems.is_whitespace c) (List.drop i pattern.data)
  have hWs : ws
            = List.takeWhile (fun c => Syntax.AstItems.is_whitespace c) (List.drop i pattern.data)
            := by simp

  let chars := List.takeWhile (fun c => decide ('0' ≤ c) && decide (c ≤ '9'))
                (List.drop (i + (List.takeWhile
                  (fun c => Syntax.AstItems.is_whitespace c) (List.drop i pattern.data)).length)
                pattern.data)
  have hChars : chars
            = List.takeWhile (fun c => decide ('0' ≤ c) && decide (c ≤ '9'))
                (List.drop (i + (List.takeWhile
                  (fun c => Syntax.AstItems.is_whitespace c) (List.drop i pattern.data)).length)
                pattern.data)
            := by simp

  rw [← hWs, ← hChars] at h
  rw [← hChars] at hCharsLt

  have hWsLength : 0 ≤ ws.length := by simp
  have h : chars.length + ws.length = offset := h.left
  have hLt : 0 < chars.length + ws.length := by omega
  simp_all

/-- parse 'm}' or '}' after ',' -/
private def parse_counted_repetition_values_after_comma (pattern : String) (i : Nat)
    : Except String (NChars × Option Nat) := do
  let none' : Option Nat := none
  if let some offset := '}'.isNextNonSpaceChar pattern i  then
    pure (offset, none')
  else
    let (offset, m) ← parse_decimal pattern i
    if let some offset' := '}'.isNextNonSpaceChar pattern (i + offset) then
      let offset := offset + offset'
      pure (offset, some m)
    else Except.error (toError pattern .RepetitionCountUnclosed)

/-- parse 'n,m}', ',m}', 'n,}' or ',}' after '{' -/
private def parse_counted_repetition_values (pattern : String) (i : Nat)
    : Except String (Nat × Option Nat × Option Nat) := do
  let none' : Option Nat := none
  if let some offset := ','.isNextNonSpaceChar pattern i then
    match ←parse_counted_repetition_values_after_comma pattern (i + offset) with
    | (nChars, none) => pure (offset + nChars, none', none')
    | (nChars, some m) => pure (offset + nChars, none', some m)
  else
    let (offset, n) ← parse_decimal pattern i
    if let some offsetC := ','.isNextNonSpaceChar pattern (i + offset) then
      let offset := offset + offsetC
      match ←parse_counted_repetition_values_after_comma pattern (i + offset) with
      | (nChars, none) => pure (offset + nChars, some n, none')
      | (nChars, some m) => pure (offset + nChars, some n, some m)
    else if let some offsetC := '}'.isNextNonSpaceChar pattern (i + offset) then
      pure (offset + offsetC, some n, some n)
    else Except.error ""

private def parse_possessive_greedy (pattern : String) (i : Nat) : Bool × Bool × Nat :=
  let c := pattern.getAtCodepoint i
  if c = '+' then (true, true, 1)
  else if c = '?' then (false, false, 1)
  else (false, true, 0)

private def parse_counted_repetition (pattern : String) (i : Nat) (concat : Concat)
    : Except String (NChars × Concat) := do
  match concat.asts.pop? with
  | some (ast, asts) =>
    if match ast with | .Empty => true | .Flags _ => true | _ => false
    then Except.error (toErrorAt pattern i .RepetitionMissing)
    else
      match ←parse_counted_repetition_values pattern i with
      | (offset, none, some m) =>
          let (possessive, greedy, offset2) := parse_possessive_greedy pattern (i + offset)
          let offset:= offset + offset2
          let asts := asts.push (
              Ast.Repetition
                (Repetition.mk
                  (Syntax.AstItems.span ast)
                  ⟨(String.toSpan pattern i (i+offset)),
                  (RepetitionKind.Range (RepetitionRange.Bounded 0 m))⟩
                  greedy
                  possessive
                  ast
              ))
          pure (offset, (Concat.mk (Syntax.AstItems.span ast) asts))
      | (offset, some n, some m) =>
          let (possessive, greedy, offset2) := parse_possessive_greedy pattern (i + offset)
          let offset:= offset + offset2
          let asts := asts.push (
              Ast.Repetition
                (Repetition.mk
                  (Syntax.AstItems.span ast)
                  ⟨(String.toSpan pattern (i) (i+offset)),
                  (RepetitionKind.Range
                    (if n = m then (RepetitionRange.Exactly n) else (RepetitionRange.Bounded n m)))⟩
                  greedy
                  possessive
                  ast
              ))
          pure (offset, (Concat.mk (Syntax.AstItems.span ast) asts))
      | (offset, some m, none) =>
          let (possessive, greedy, offset2) := parse_possessive_greedy pattern (i + offset)
          let offset:= offset + offset2
          let asts := asts.push (
              Ast.Repetition
                (Repetition.mk
                  (Syntax.AstItems.span ast)
                  ⟨(String.toSpan pattern (i-1) (i+offset)),
                  (RepetitionKind.Range (RepetitionRange.AtLeast m))⟩
                  greedy
                  possessive
                  ast
              ))
          pure (offset, (Concat.mk (Syntax.AstItems.span ast) asts))
      | (_, _, _) =>
          Except.error (toError pattern .RepetitionCountUnclosed)
  | none => Except.error (toErrorAt pattern i .RepetitionMissing)

/-- Parse a single item in a character class as a primitive -/
private def parse_set_class_item (pattern : String) (i : Nat)
    : ParserM (NatPos × Option Primitive) := do
  let flavor ← read
  let state ← get
  let c := pattern.getAtCodepoint i
  match c with
  | '\\' =>
    let c1 := pattern.getAtCodepoint (i + 1)
    if flavor == Flavor.Pcre && c1 = 'Q'
    then
      set {state with disabled_metacharacters := true}
      pure (⟨2, by simp⟩ , none)
    else if flavor == Flavor.Pcre && c1 = 'E'
    then
      if !state.disabled_metacharacters
      then throw (toError pattern .EndQuoteWithoutOpenQuote)
      else
        set {state with disabled_metacharacters := false}
        pure (⟨2, by simp⟩ , none)
    else
      let (⟨n, _⟩ , p) ← parse_escape pattern (i + 1) true
      pure (NatPos.succ n, p)
  | _ =>
    let lit := ⟨⟨pattern, ⟨i⟩, ⟨i + 1⟩⟩, LiteralKind.Verbatim, c⟩
    pure (⟨1, by simp⟩ , Primitive.Literal lit)

/-- Parse a single primitive item in a character class set. -/
private def parse_set_class_range (pattern : String) (i : Nat)
    : ParserM (NatPos × ClassSetItem) := do
  let (⟨n1, h⟩, prim1) ←  parse_set_class_item pattern i
  match prim1 with
  | some prim1 =>
    let c := pattern.getAtCodepoint (i + n1)
    let state ← get
    if c != '-' || (pattern.getAtCodepoint (i + n1 + 1)) = ']' || state.disabled_metacharacters
    then
      pure (⟨n1, h⟩, ←prim1.into_class_set_item)
    else
      let (⟨n2, _⟩, prim2) ←  parse_set_class_item pattern (i + n1 + 1)
      match prim2 with
      | some prim2 =>
        let lit1 ←prim1.into_class_literal
        let lit2 ←prim2.into_class_literal
        if h : lit1.c.val <= lit2.c.val
        then
          let range : ClassSetRange :=
            ⟨⟨pattern, ⟨i⟩, ⟨i + n1 + n2 + 1⟩⟩, lit1, lit2, h⟩
          pure (⟨1 + n1 + n2, by simp_arith[Nat.zero_lt_one_add _]⟩, ClassSetItem.Range range)
        else Except.error (toError pattern .ClassRangeInvalid)
      | none => Except.error (toError pattern .ClassRangeInvalid)
  | none => pure (⟨n1, h⟩, ClassSetItem.Empty "".toSubstring)

/-- Parses the opening of a character class set. -/
private def parse_set_class_open (pattern : String) (i : Nat)
    : Except String (NChars × ClassBracketed × ClassSetUnion) :=
  let span := String.toSpan pattern i (i + 1)
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

  let clsBracketed := ClassBracketed.mk (String.toSpan pattern i (i+1)) negated (ClassSet.Item item)
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
  | some (ClassState.Op kind lhs, stack) =>
    set {parser with stack_class := stack}
    let op : ClassSetBinaryOp := ClassSetBinaryOp.mk default kind lhs rhs
    pure (ClassSet.BinaryOp op)
  | _ => throw "internal error: pop_class_op unexpected empty character class stack"

/-- Parse the end of a character class set and pop the character class parser stack. -/
private def pop_class (nested_union : ClassSetUnion)
    : ParserM (Sum ClassSetUnion ClassBracketed) := do
  let ⟨span, _⟩ := nested_union
  let item := ClassSet.Item nested_union.into_item
  let prevset ← pop_class_op item
  let parser ← get
  match parser.stack_class.pop? with
  | some (ClassState.Open ⟨uspan, uitems⟩ ⟨_, negated, _⟩, stack) =>
    let clsset : ClassBracketed := ⟨span, negated, prevset⟩
    if stack.size = 0
    then
      set {parser with stack_class := stack}
      pure (Sum.inr clsset)
    else
      set {parser with stack_class := stack}
      let union : ClassSetUnion := ⟨uspan, uitems.push (ClassSetItem.Bracketed clsset)⟩
      pure (Sum.inl union)
  | some (ClassState.Op _ _, _) => throw "internal error: pop_class, unexpected ClassState.Op"
  | none => throw "internal error: pop_class unexpected empty character class stack"

/-- Push the current set of class items on to the class parser's stack as
    the left hand side of the given operator. -/
def push_class_op (next_kind: ClassSetBinaryOpKind) (next_union: ClassSetUnion)
    : ParserM ClassSetUnion := do
  let item : ClassSet := ClassSet.Item next_union.into_item
  let new_lhs ← pop_class_op item
  let parser ← get
  let stack := parser.stack_class.push (ClassState.Op next_kind new_lhs)
  set {parser with stack_class := stack}
  let union : ClassSetUnion := ⟨default, #[]⟩
  pure union

private def parse_set_class_loop (pattern : String) (i : Nat) (union : ClassSetUnion)
    : ParserM (NChars × ClassBracketed) := do
  let flavor ← read
  let state ← get
  let handle_other_char (span : Substring) (items : Array ClassSetItem)
      (h₀ : ¬i ≥ String.length pattern)  : ParserM (NChars × ClassBracketed) := do
    let (⟨n, h⟩, range) ←  parse_set_class_range pattern i
    let union : ClassSetUnion := ⟨span, items.push range⟩
    have : pattern.length - (i + n) < pattern.length - i :=
      Nat.sum_lt_of_not_gt pattern.length i n h₀ h
    parse_set_class_loop pattern (i + n) union

  if h₀ : i >= pattern.length
  then Except.error (toError pattern .ClassUnclosed)
  else
    let ⟨span, items⟩ := union
    let c := pattern.getAtCodepoint i
    match c with
    | '[' =>
      if state.disabled_metacharacters then handle_other_char span items h₀ else
      let maybe_parsed :=
        if (← get).stack_class.size > 0
        then
          match maybe_parse_ascii_class pattern i with
          | Except.ok (some (n, cls)) =>
            let union : ClassSetUnion := ⟨span, items.push (ClassSetItem.Ascii cls)⟩
            some (n, union)
          | _ => none
        else none

      let (n, union) ←
        match maybe_parsed with
        | some (n, union) => pure (n, union)
        | none =>
            if flavor == Syntax.Flavor.Pcre && (← get).stack_class.size > 0 then
              let (⟨n, _⟩, range) ←  parse_set_class_range pattern i
              let union : ClassSetUnion := ⟨span, items.push range⟩
              pure (n-1, union)
            else push_class_open pattern i union
      have : pattern.length - (i + n + 1) < pattern.length - i :=
        Nat.sum_succ_lt_of_not_gt pattern.length i n h₀
      parse_set_class_loop pattern (i + n + 1) union
    | ']' =>
      if state.disabled_metacharacters then handle_other_char span items h₀ else
      match ← pop_class union with
      | Sum.inl nested_union =>
        have : pattern.length - (i + 1) < pattern.length - i :=
          Nat.succ_lt_of_not_gt pattern.length i h₀
        parse_set_class_loop pattern (i + 1) nested_union
      | Sum.inr cls =>
        pure (i + 1, cls)
    | '&' =>
      if pattern.getAtCodepoint (i+1) = '&' then
        let n := 1
        let union ← push_class_op ClassSetBinaryOpKind.Intersection union
        have : pattern.length - (i + n + 1) < pattern.length - i :=
          Nat.sum_succ_lt_of_not_gt pattern.length i n h₀
        parse_set_class_loop pattern (i + n + 1) union
      else handle_other_char span items h₀
    | '-' =>
      if pattern.getAtCodepoint (i+1) = '-' then
        let n := 1
        let union ← push_class_op ClassSetBinaryOpKind.Difference union
        have : pattern.length - (i + n + 1) < pattern.length - i :=
          Nat.sum_succ_lt_of_not_gt pattern.length i n h₀
        parse_set_class_loop pattern (i + n + 1) union
      else handle_other_char span items h₀
    | '~' =>
      if pattern.getAtCodepoint (i+1) = '~' then
        let n := 1
        let union ← push_class_op ClassSetBinaryOpKind.SymmetricDifference union
        have : pattern.length - (i + n + 1) < pattern.length - i :=
          Nat.sum_succ_lt_of_not_gt pattern.length i n h₀
        parse_set_class_loop pattern (i + n + 1) union
      else handle_other_char span items h₀
    | _ => handle_other_char span items h₀
termination_by pattern.length - i

/-- Parse a standard character class consisting primarily of characters or character ranges. -/
private def parse_set_class (pattern : String) (i : Nat)
    : ParserM (NatPos × ClassBracketed) := do
  let union : ClassSetUnion := ⟨String.toSpan pattern i (i+1), #[]⟩
  let (i', cls) ← parse_set_class_loop pattern i union
  let n := i' - i
  if h : 0 < n
  then pure (⟨n, h⟩, cls)
  else throw s!"parse_set_class: internal error excpeted i {i} < i' {i'}"

/-- Parse a primitive AST. e.g., A literal, non-set character class or assertion.-/
private def parse_primitive (pattern : String) (i : Nat) : ParserM (NatPos × Primitive) := do
  let flavor ← read
  let state ← get
  let c := pattern.getAtCodepoint i
  match c with
  | '\\' =>
    match ← maybe_parse_backref pattern (i + 1) with
    | some (n, br) => pure (NatPos.succ n, Primitive.BackRef br)
    | none =>
      let (⟨n, _⟩, p) ← parse_escape pattern (i + 1)
      pure (⟨1 + n, Nat.zero_lt_one_add _⟩, p)
  | '.' => pure (⟨1, by simp⟩, Primitive.Dot (String.toSpan pattern i (i + 1)))
  | '^' => pure (⟨1, by simp⟩,
              Primitive.Assertion ⟨String.toSpan pattern i (i + 1), AssertionKind.StartLine⟩)
  | '$' =>  if state.disabled_metacharacters then
              let lit := ⟨⟨pattern, ⟨i⟩, ⟨i + 1⟩⟩, LiteralKind.Verbatim, c⟩
              pure (⟨1, by simp⟩, Primitive.Literal lit)
            else
              pure (⟨1, by simp⟩,
                Primitive.Assertion ⟨String.toSpan pattern i (i + 1),
                  if flavor == Flavor.Pcre
                  then AssertionKind.EndLineWithOptionalLF
                  else AssertionKind.EndLine⟩)
  | _ =>
    let lit := ⟨⟨pattern, ⟨i⟩, ⟨i + 1⟩⟩, LiteralKind.Verbatim, c⟩
    pure (⟨1, by simp⟩, Primitive.Literal lit)

/-- Parses an uncounted repetition operation. -/
private def parse_uncounted_repetition (pattern : String) (i : Nat) (kind: RepetitionKind) (possessive : Bool)
    (concat : Concat) : Except String (NChars × Concat) := do
  match Array.pop? concat.asts with
  | some (ast, asts) =>
    let op : AstItems.RepetitionOp := ⟨⟨pattern, ⟨i⟩, ⟨i + 1⟩⟩, kind⟩
    let c := pattern.getAtCodepoint (i + 1)
    let (n, greedy)  := if c = '?' then (1, false) else (0, true)
    if !greedy && possessive then Except.error (toErrorAt pattern i .RepetitionUngreedyAndPossessive) else
    let r : Repetition := Repetition.mk (String.toSpan pattern i (i + 1)) op greedy possessive ast
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
    let alt := Alternation.mk (String.toSpan pattern i (i + 1)) #[concat.into_ast]
    set {parser with stack_group := parser.stack_group.push (GroupState.Alternation alt)}
    pure ()

/-- Parse and push a single alternation on to the parser's internal stack. -/
private def push_alternate (pattern : String) (i : Nat) (concat : Concat)
    : ParserM Concat := do
  let _ ← push_or_add_alternation pattern i concat
  pure (Concat.mk (String.toSpan pattern i (i + 1)) #[])

/-- Parse the current character as a flag. -/
private def parse_flag (c : Char) (pattern : String) : Except String Flag :=
  match c with
  | 'i' => Except.ok Flag.CaseInsensitive
  | 'm' => Except.ok Flag.MultiLine
  | 's' => Except.ok Flag.DotMatchesNewLine
  | 'U' => Except.ok Flag.SwapGreed
  | 'u' => Except.ok Flag.Unicode
  | 'R' => Except.ok Flag.CRLF
  | 'x' => throw  (toError pattern .FeatureNotImplementedFlagExtended)
  | _ => Except.error (toError c.toString .FlagUnrecognized)

/-- Parse a sequence of flags starting at the current character.-/
private def parse_flags (pattern : String) (i : Nat)
    : Except String (NChars × Flags) := do
  let chars := (pattern.data.drop i).takeWhile (fun c => c != ':' && c != ')') |> List.toArray
  let span := String.toSpan pattern i (i + 1)
  let items : Array FlagsItem ←
    chars |> Array.mapM (fun c => do
      if c = '-' then pure ⟨span, FlagsItemKind.Negation⟩
      else
        let f ← parse_flag c pattern
        pure ⟨span, FlagsItemKind.Flag f⟩)
  let flags : Flags := ⟨(String.toSpan pattern i chars.size), items⟩
  Except.ok (chars.size, flags)

/-- Parse a group (which contains a sub-expression) or a set of flags. -/
private def parse_group (pattern : String) (i : Nat)
    : ParserM (NChars × (Sum SetFlags Group)) := do
  let flavor ← read
  let parser ← get
  let c1 := pattern.getAtCodepoint i
  let c2 := pattern.getAtCodepoint (i + 1)
  let c3 := pattern.getAtCodepoint (i + 2)
  if c1 = '?' && c2  = '<' && c3.isAlpha then
    throw  (toError pattern .FeatureNotImplementedNamedGroups)
  else if c1 = '?' && c2  = 'P' && (c3 = '<'  || c3 = '=') then
    throw  (toError pattern .FeatureNotImplementedNamedGroups)
  else if c1 = '?' && c2  = '\'' then
    throw  (toError pattern .FeatureNotImplementedNamedGroups)
  else if c1 = '?' && c2.isDigit then
    throw  (toError pattern .FeatureNotImplementedSubroutines)
  else if c1 = '?' && (c2 = '-'  || c2 = '+') && c3.isDigit then
    throw  (toError pattern .FeatureNotImplementedSubroutines)
  else if c1 = '?' && c2 = '&' then
    throw  (toError pattern .FeatureNotImplementedSubroutines)
  else if c1 = '?' && c2 = '?' then
    throw  (toError pattern .FeatureNotImplementedSubroutines)
  else if c1 = '?' && c2 = '^' then
    throw  (toError pattern .FeatureNotImplementedFlagShorthand)
  else if c1 = '?' && c2 = '>' then
    throw  (toError pattern .FeatureNotImplementedAtomicGroup)
  else if c1 = '?' && c2 = '(' then
    throw  (toError pattern .FeatureNotImplementedConditionalExpression)
  else if c1 = '?' && c2 = '|' then
    throw  (toError pattern .FeatureNotImplementedBranchResetGroup)
  else if c1 = '*' && (c2.isUpper || c2 = 'a' || c2 = ':') then
    throw  (toError pattern .FeatureNotImplementedControlVerbs)
  else if c1 = '?' && c2  = '#' then
    let chars := (pattern.data.drop (i+1)).takeWhile (· != ')')
    let n := chars.length + 2
    let s : String := ⟨chars⟩
    let sf : SetFlags := ⟨String.toSpan pattern i (i + 1), ⟨s.toSubstring, #[]⟩ ⟩
    pure (n, Sum.inl sf)
  else if c1 = '?' && c2  = '=' then
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.Lookaround .PositiveLookahead) Ast.Empty
    pure (2, Sum.inr g)
  else if c1 = '*' && String.startsAtCodepoint pattern "pla:" (i+1) then
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.Lookaround .PositiveLookahead) Ast.Empty
    pure (5, Sum.inr g)
  else if c1 = '*' && String.startsAtCodepoint pattern "nla:" (i+1) then
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.Lookaround .NegativeLookahead) Ast.Empty
    pure (5, Sum.inr g)
  else if c1 = '*' && String.startsAtCodepoint pattern "positive_lookahead:" (i+1) then
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.Lookaround .PositiveLookahead) Ast.Empty
    pure (20, Sum.inr g)
  else if c1 = '*' && String.startsAtCodepoint pattern "negative_lookbehind:" (i+1) then
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.Lookaround (.NegativeLookbehind 0)) Ast.Empty
    pure (21, Sum.inr g)
  else if c1 = '?' && c2  = '!' then
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.Lookaround .NegativeLookahead) Ast.Empty
    pure (2, Sum.inr g)
  else if c1 = '?' && c2  = '<' && c3  = '=' then
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.Lookaround (.PositiveLookbehind 0)) Ast.Empty
    pure (3, Sum.inr g)
  else if c1 = '*' && String.startsAtCodepoint pattern "plb:" (i+1) then
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.Lookaround (.PositiveLookbehind 0)) Ast.Empty
    pure (5, Sum.inr g)
  else if c1 = '*' && String.startsAtCodepoint pattern "positive_lookbehind:" (i+1) then
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.Lookaround (.PositiveLookbehind 0)) Ast.Empty
    pure (21, Sum.inr g)
  else if c1 = '*' && String.startsAtCodepoint pattern "nlb:" (i+1) then
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.Lookaround (.NegativeLookbehind 0)) Ast.Empty
    pure (5, Sum.inr g)
  else if c1 = '?' && c2  = '<' && c3  = '!' then
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.Lookaround (.NegativeLookbehind 0)) Ast.Empty
    pure (3, Sum.inr g)
  else if c1 = '?'
  then
    let (n, flags) ← parse_flags pattern (i + 1)
    let c1 := pattern.getAtCodepoint (i + 1 + n)
    if c1 = ')'
    then
      if flavor != Syntax.Flavor.Pcre && flags.items.size = 0
      then Except.error (toError pattern .RepetitionMissing)
      else
        let sf : SetFlags := ⟨String.toSpan pattern i (i + 1), flags⟩
        pure (n + 2, Sum.inl sf)
    else
      let g := Group.mk (String.toSpan pattern i (i + 1)) (.NonCapturing flags) Ast.Empty
      pure (n + 2, Sum.inr g)
  else
    let parser := {parser with capture_index := parser.capture_index + 1 }
    let g := Group.mk (String.toSpan pattern i (i + 1)) (.CaptureIndex parser.capture_index) Ast.Empty
    set parser
    pure (0, Sum.inr g)

/-- Parse and push a group AST. -/
private def push_group (pattern : String) (i : Nat) (concat : Concat)
    : ParserM (NChars × Concat) := do
  let (n, group) ← parse_group pattern i
  match group with
  | .inl flags =>
    match flags with
    | ⟨_, ⟨_, #[]⟩⟩ => pure (n, concat)
    | _ => pure (n, Concat.mk (String.toSpan pattern i (i + 1)) (concat.asts.push (Ast.Flags flags)))
  | .inr group =>
    let parser ← get
    set {parser with stack_group := parser.stack_group.push (GroupState.Group concat group)}
    pure (n, Concat.mk (String.toSpan pattern i (i + 1)) #[])

private def get_fixed_width (pattern : String) (ast : Ast) : Except String Nat := do
  match ast with
  | .Literal _ => pure 1
  | .Dot _ => pure 1
  | .ClassBracketed _ => pure 1
  | .ClassUnicode _ => pure 1
  | .ClassPerl _ => pure 1
  | .Assertion _ => pure 0
  | .Flags _ => pure 0
  | .Concat concat =>
      match concat with
      | ⟨_, asts⟩ =>
        let width ← asts.attach.foldlM (init := 0) (fun s (ast : { x // x ∈ asts}) => do
            have : sizeOf ast.val < sizeOf asts := Array.sizeOf_lt_of_mem ast.property
            let width ← get_fixed_width pattern ast.val
            pure (s + width))
        pure width
  | .Alternation alt =>
      match alt with
      | ⟨_, asts⟩ =>
        let widths ← asts.attach.mapM (fun (ast : { x // x ∈ asts}) => do
            have : sizeOf ast.val < sizeOf asts := Array.sizeOf_lt_of_mem ast.property
            let width ← get_fixed_width pattern ast.val
            pure width)
        if h : 0 < widths.size
        then
          let width := widths.get ⟨0, h⟩
          if Array.all widths (fun w => w = width)
          then pure width
          else throw (toError pattern .FixedWidtExcpected)
        else throw (toError pattern .FixedWidtExcpected)
  | .Repetition rep  =>
      match rep with
      | AstItems.Repetition.mk _ (RepetitionOp.mk _ (.Range (.Exactly n))) _ _ _ => pure n
      | _ => throw (toError pattern .FixedWidtExcpected)
  | .Group ⟨_, GroupKind.CaptureIndex _, ast⟩  =>
        let width ← get_fixed_width pattern ast
        pure width
  | .Group ⟨_, GroupKind.Lookaround _, _⟩  =>
        pure 0
  | _ => throw (toError pattern .FixedWidtExcpected)
termination_by sizeOf ast

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

/-- Pop a group AST from the parser's internal stack and set the group's AST to the concatenation.-/
private def pop_group (pattern : String) (i : Nat) (group_concat : Concat)
    : ParserM Concat := do
  let parser ← get
  match Array.pop? parser.stack_group with
  | some (GroupState.Group prior_concat ⟨⟨s, start, _⟩ , kind, _⟩ , stack_group) =>
    let group := Group.mk ⟨s, start, ⟨i⟩ ⟩ kind group_concat.into_ast
    let group ← set_width pattern group
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
      let group ← set_width pattern group
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

private def add_char_to_concat (pattern : String) (i : Nat) (c : Char) (concat : Concat) : Concat :=
  let lit : Literal := ⟨⟨pattern, ⟨i⟩, ⟨i + 1⟩⟩, LiteralKind.Verbatim, c⟩
  let p : Primitive := Primitive.Literal lit
  let asts := concat.asts.push p.into_ast
  (Concat.mk (concat.span) asts)

private def checkBackRefence (b : Nat) (ast: Ast) : Except String Bool := do
  let check (ast : Ast) :=
    match ast with
    | .Group ⟨_, AstItems.GroupKind.CaptureIndex b', _⟩ => b = b'
    | _ => false

  match AstItems.find ast check with
  | some ast =>
      match get_fixed_width "" ast with
      | Except.ok _ => pure true
      | Except.error _ => Except.error s!"fixed width capture group of backreference {b} expected"
  | none => Except.error s!"capture group {b} not found"

/-- capture groups with a backreference should have fixed width -/
private def checkBackRefences (b : Nat) (ast: Ast) : Except String Bool := do
  if b = 0 then pure true
  else
    if ← checkBackRefence b ast then checkBackRefences (b - 1) ast else pure false

/-- Parse the regular expression and return an abstract syntax tree. -/
def parse (pattern : String) (flavor : Syntax.Flavor) : Except String Ast := do
  let concat : Concat := Concat.mk (String.toSpan pattern 0 pattern.length) #[]
  let (concat, parser) ← loop pattern 0 concat flavor default
  let ast ← pop_group_end pattern concat parser
  if parser.capture_index < parser.max_backreference
     && (← checkBackRefences parser.max_backreference ast)
  then Except.error (toError pattern .BackRefenceInvalid)
  else pure ast

  where
    /-- loop over chars of `pattern` to parse the regular expression -/
    loop (pattern : String) (i' : Nat) (concat : Concat) : ParserM Concat := do
      let flavor ← read
      let state ← get
      let i := consume_space concat pattern i'
      have : i' ≤ i := consume_space_ge concat pattern i'
      if h₀ : i >= pattern.length
      then pure concat
      else
        let c := pattern.getAtCodepoint i
        match c with
        | '(' =>
          if state.disabled_metacharacters
          then loop pattern (i+1) (add_char_to_concat pattern i c concat) else
            let (n, concat) ← push_group pattern (i + 1) concat
            have : pattern.length - (i + n + 1) < pattern.length - i := by
              simp [Nat.sum_succ_lt_of_not_gt _ _ _ h₀]
            loop pattern (i+n+1) concat
        | ')' =>
          if state.disabled_metacharacters
          then loop pattern (i+1) (add_char_to_concat pattern i c concat) else
            let concat ← pop_group pattern (i + 1) concat
            have : pattern.length - (i + 1) < pattern.length - i := by
              simp [Nat.succ_lt_of_not_gt _ _ h₀]
            loop pattern (i+1) concat
        | '|' =>
          if state.disabled_metacharacters
          then loop pattern (i+1) (add_char_to_concat pattern i c concat) else
            let concat ← push_alternate pattern i concat
            have : pattern.length - (i + 1) < pattern.length - i := by
              simp [Nat.succ_lt_of_not_gt _ _ h₀]
            loop pattern (i+1) concat
        | '[' =>
          if state.disabled_metacharacters
          then loop pattern (i+1) (add_char_to_concat pattern i c concat) else
            let (⟨n, h₁⟩, cls) ← parse_set_class pattern i
            let asts := concat.asts.push (Ast.ClassBracketed cls)
            have : pattern.length - (i + n) < pattern.length - i := by
              simp [Nat.sum_lt_of_not_gt _ _ _ h₀ h₁]
            loop pattern (i+n) (Concat.mk (concat.span) asts)
        | '?' =>
          if state.disabled_metacharacters
          then loop pattern (i+1) (add_char_to_concat pattern i c concat) else
            let (possessive, offset) :=
                  if (i + 1) < pattern.length && pattern.getAtCodepoint (i + 1) = '+'
                  then (true, 1) else (false, 0)
            let (n, p) ← parse_uncounted_repetition pattern i RepetitionKind.ZeroOrOne possessive concat
            have : pattern.length - (i + n + 1) < pattern.length - i := by
              simp [Nat.sum_succ_lt_of_not_gt _ _ _ h₀]
            loop pattern (i+n+1+offset) p
        | '*' =>
          if state.disabled_metacharacters
          then loop pattern (i+1) (add_char_to_concat pattern i c concat) else
            let (possessive, offset) :=
                  if (i + 1) < pattern.length && pattern.getAtCodepoint (i + 1) = '+'
                  then (true, 1) else (false, 0)
            let (n, p) ← parse_uncounted_repetition pattern i RepetitionKind.ZeroOrMore possessive concat
            have : pattern.length - (i + n + 1) < pattern.length - i := by
              simp [Nat.sum_succ_lt_of_not_gt _ _ _ h₀]
            loop pattern (i+n+1+offset) p
        | '+' =>
          if state.disabled_metacharacters
          then loop pattern (i+1) (add_char_to_concat pattern i c concat) else
            let (possessive, offset) :=
                  if (i + 1) < pattern.length && pattern.getAtCodepoint (i + 1) = '+'
                  then (true, 1) else (false, 0)
            let (n, p) ← parse_uncounted_repetition pattern i RepetitionKind.OneOrMore possessive concat
            have : pattern.length - (i + n + 1) < pattern.length - i := by
              simp [Nat.sum_succ_lt_of_not_gt _ _ _ h₀]
            loop pattern (i+n+1+offset) p
        | '{' =>
          if state.disabled_metacharacters
          then loop pattern (i+1) (add_char_to_concat pattern i c concat) else
            match parse_counted_repetition pattern (i + 1) concat with
            | Except.ok (n, concat) =>
                have : pattern.length - (i + n + 1) < pattern.length - i := by
                  simp [Nat.sum_succ_lt_of_not_gt _ _ _ h₀]
                loop pattern (i+n+1) concat
            | Except.error e =>
                if flavor == Flavor.Pcre
                then loop pattern (i+1) (add_char_to_concat pattern i c concat) else
                throw e
        | _ =>
          let c1 := pattern.getAtCodepoint (i + 1)
          if flavor == Flavor.Pcre && c = '\\' && c1 = 'Q'
          then
            set {state with disabled_metacharacters := true}
            loop pattern (i+2) concat
          else if flavor == Flavor.Pcre && c = '\\' && c1 = 'E'
          then
            if !state.disabled_metacharacters
            then throw (toError pattern .EndQuoteWithoutOpenQuote)
            else
              set {state with disabled_metacharacters := false}
              loop pattern (i+2) concat
          else if c = '\\' && state.disabled_metacharacters
          then
            loop pattern (i+1) (add_char_to_concat pattern i c concat)
          else
            let (⟨n, h₁⟩, p) ← parse_primitive pattern i
            let asts := concat.asts.push p.into_ast
            have : pattern.length - (i + n) < pattern.length - i := by
              simp [Nat.sum_lt_of_not_gt _ _ _ h₀ h₁]
            loop pattern (i+n) (Concat.mk (concat.span) asts)
    termination_by pattern.length - i'
