import Regex.Utils
import Regex.Interval
import Regex.Unicode

/-!
## High-level intermediate representation for a regular expression.

A high-level intermediate representation `Syntax.Hir` for a regular expression.
-/

namespace Syntax

abbrev ClassUnicodeRange := Range Char

instance : Inhabited ClassUnicodeRange := ⟨⟨0, by simp_arith⟩, ⟨0, by simp_arith⟩, by simp_arith⟩

structure ClassUnicode where
  set: IntervalSet Char

instance : ToString (Range Char) where
  toString r := s!"{intAsString r.start.val}-{intAsString r.end.val}"

private def rangesToString (arr : Array (Range Char)) : String :=
  arr |> Array.map (fun r => s!"    {r.start}-{r.end},\n") |> Array.toList |> String.join

instance : ToString (IntervalSet Char) where
  toString set := s!"ranges: {set.ranges}"

instance : ToString ClassUnicode where
  toString cls := s!"{cls.set}"

/-- see UInt32.isValidChar -/
instance : Inhabited ClassUnicode :=
  let cls1 : Range Char := ⟨'\u0000', ⟨0xD7FF, by simp_arith⟩, by simp_arith⟩
  let cls2 : Range Char := ⟨⟨0xE000, by simp_arith⟩, ⟨0x10FFFF, by simp_arith⟩, by simp_arith⟩
  let ranges := #[cls1, cls2]
  ⟨⟨Interval.canonicalize ranges⟩⟩

namespace ClassUnicode

def empty : ClassUnicode :=
  ⟨⟨#[], Ranges.empty_isNonOverlapping⟩⟩

def canonicalize (cls : ClassUnicode) : ClassUnicode :=
  ⟨Interval.canonicalize cls.set.ranges⟩

def union (cls1 cls2 : ClassUnicode) : ClassUnicode :=
  ⟨Interval.union cls1.set cls2.set⟩

def intersection (cls1 cls2 : ClassUnicode) : ClassUnicode :=
  ⟨Interval.intersection cls1.set cls2.set⟩

def difference (cls1 cls2 : ClassUnicode) : ClassUnicode :=
  ⟨Interval.difference cls1.set cls2.set⟩

def symmetric_difference (cls1 cls2 : ClassUnicode) : ClassUnicode :=
  ⟨Interval.symmetric_difference cls1.set cls2.set⟩

def negate (cls : ClassUnicode) : ClassUnicode :=
  ⟨Interval.negate cls.set⟩

def case_fold (cls : ClassUnicode) : ClassUnicode :=
  let ranges := cls.set.ranges
  let init : Array (Range Char) := #[]
  let ranges := ranges |> Array.foldl (init := init) (fun acc r =>
    let folded := Unicode.case_fold_range r
    acc ++ folded)

  ⟨Interval.canonicalize ranges⟩

end ClassUnicode

inductive Class where
  /-- A set of characters represented by Unicode scalar values. -/
  | Unicode : ClassUnicode -> Class

instance : ToString Class where
  toString cls :=
    match cls  with
    | .Unicode cls => s!"{cls}"

/-- The high-level intermediate representation for a look-around assertion. -/
inductive Look where
  /-- Match the beginning of text. -/
  | Start : Look
  /-- Match the end of text. -/
  | End : Look
  /-- Match the beginning of a line or the beginning of text. -/
  | StartLF : Look
  /-- Match the end of a line or the end of text. -/
  | EndLF : Look
  /-- Match the beginning of a line or the beginning of text. -/
  | StartCRLF : Look
  /-- Match the end of a line or the end of text. -/
  | EndCRLF : Look
  /-- Match a Unicode-aware word boundary. -/
  | WordUnicode : Look
  /--  Match a Unicode-aware negation of a word boundary. -/
  | WordUnicodeNegate : Look
  /-- Match the start of a Unicode word boundary. -/
  | WordStartUnicode : Look
  /-- Match the end of a Unicode word boundary. -/
  | WordEndUnicode : Look
  /-- Match the start half of a Unicode word boundary. -/
  | WordStartHalfUnicode : Look
  /-- Match the end half of a Unicode word boundary. -/
  | WordEndHalfUnicode : Look
deriving BEq

namespace Look

def toString : Look -> String
  | .Start => s!"Start"
  | .End => s!"End"
  | .StartLF => s!"StartLF"
  | .EndLF => s!"EndLF"
  | .StartCRLF => s!"StartCRLF"
  | .EndCRLF => s!"EndCRLF"
  | .WordUnicode => s!"WordUnicode"
  | .WordUnicodeNegate => s!"WordUnicodeNegate"
  | .WordStartUnicode => s!"WordStartUnicode"
  | .WordEndUnicode => s!"WordEndUnicode"
  | .WordStartHalfUnicode => s!"WordStartHalfUnicode"
  | .WordEndHalfUnicode => s!"WordEndHalfUnicode"

end Look

instance : ToString Look where
  toString := Look.toString

/-- A type that collects various properties of an HIR value.-/
structure Properties where
    minimum_len: Option UInt32
    maximum_len: Option UInt32
    look_set_prefix: Array Look

instance : Inhabited Properties := ⟨none, none, #[]⟩

/-- A translator's representation of a regular expression's flags at any given moment in time. -/
structure Flags where
  case_insensitive: Option Bool
  multi_line: Option Bool
  dot_matches_new_line: Option Bool
  swap_greed: Option Bool
  crlf: Option Bool

instance : Inhabited Flags := ⟨⟨none, none, none, none, none⟩⟩

instance : ToString Flags where
  toString s :=
    s!"Flags {s.case_insensitive} {s.multi_line} {s.dot_matches_new_line} {s.swap_greed}"

mutual

/-- A concatenation of regular expressions. -/
inductive Repetition where
  | mk (min: Nat) (max: Option Nat) (greedy : Bool) (sub: Hir) : Repetition

/-- The high-level intermediate representation for a capturing group. -/
inductive Capture where
  | mk (index: Nat) (name: Option String) (sub: Hir) : Capture

/-- The underlying kind of an arbitrary [`Hir`] expression. -/
inductive HirKind where
  /-- The empty regular expression, which matches everything, including the empty string. -/
  | Empty : HirKind
  /-- A literal string that matches exactly these bytes. -/
  | Literal : Char -> HirKind
  /-- A single character class that matches any of the characters in the class. -/
  | Class : Class -> HirKind
  /-- A look-around assertion. A look-around match always has zero length. -/
  | Look : Look -> HirKind
  /-- A repetition operation applied to a sub-expression. -/
  | Repetition : Repetition -> HirKind
  /-- A capturing group, which contains a sub-expression. -/
  | Capture : Capture -> HirKind
  /-- A concatenation of expressions. -/
  | Concat : Array Hir -> HirKind
  /-- An alternation of expressions. -/
  | Alternation : Array Hir -> HirKind

/-- A high-level intermediate representation (HIR) for a regular expression. -/
inductive Hir where
  | mk (kind: HirKind) (props : Properties) : Hir

end

instance : Inhabited Hir := ⟨Hir.mk HirKind.Empty default⟩

namespace Hir

partial def fold [Inhabited α] (hir : Hir) (f : α -> Hir -> α) (init :  α): α :=
  let ⟨kind, _⟩ := hir
  match kind with
  | .Empty => f init hir
  | .Literal _ => f init hir
  | .Class _ => f init hir
  | .Look _ => f init hir
  | .Repetition ⟨_, _, _, sub⟩  => fold sub f init
  | .Capture _ => f init hir
  | .Concat hirs => hirs |> Array.foldl (init := init) (fun a h => fold h f a)
  | .Alternation hirs => hirs |> Array.foldl (init := init) (fun a h => fold h f a)

/-- check if an `hir` contains `look` -/
def contains (hir : Hir) (look : Look) : Bool :=
  fold (init := false) hir
    (fun acc ⟨kind, props⟩ =>
      match kind with
      | .Look _ => acc || props.look_set_prefix.contains look
      | _ => acc)

def kind (hir : Hir) : HirKind := match hir with | .mk kind _ => kind

def properties (hir : Hir) : Properties := match hir with | .mk _ properties => properties

def toProperties (kind: HirKind) : Properties :=
  match kind with
  | .Class (.Unicode cls) =>
      /- the length, in bytes, of the smallest string matched by this character class. -/
      let min := if cls.set.ranges.size > 0 then some 1 else none
      ⟨min, none, #[]⟩
  | .Look look => ⟨none, none, #[look]⟩
  | _ => default

partial def toString (hir : Hir) (col : Nat): String :=
  let col := col + 2
  let pre := "\n" ++ (multiple ' ' col "")
  match hir.kind with
  | .Empty => s!"Empty"
  | .Literal c => s!"Literal '{intAsString c.val}'"
  | .Class cls => s!"Class {cls}"
  | .Look look => s!"Look {look}"
  | .Repetition rep =>
    match rep with
    | .mk min max greedy sub => s!"Repetition {min} {max} greedy {greedy}{pre}sub {toString sub col}"
  | .Capture c =>
    match c with
    | .mk index name sub => s!"Capture {index} {name}{pre}sub {toString sub col}"
  | .Concat hirs =>
      let hirs := Array.mapIdx hirs (fun i s => (i, s))
      let hirs := String.join (hirs.toList |> List.map (fun (i, ast) =>
          let iv := String.mk (Nat.toDigits 0 i.val)
          pre ++ iv ++ ": " ++ (toString ast col)))
      s!"Concat {hirs}"
  | .Alternation hirs =>
      let hirs := Array.mapIdx hirs (fun i s => (i, s))
      let hirs := String.join (hirs.toList |> List.map (fun (i, ast) =>
          let iv := String.mk (Nat.toDigits 0 i.val)
          pre ++ iv ++ ": " ++ (toString ast col)))
      s!"Alternation {hirs}"

end Hir

instance : ToString Hir where
  toString hir := Hir.toString hir 0

/-- A type describing the different flavors of `.`. -/
inductive Dot where
    /-- Matches the UTF-8 encoding of any Unicode scalar value.
        This is equivalent to `(?su:.)` and also `\p{any}`. -/
    | AnyChar : Dot
    /-- Matches the UTF-8 encoding of any Unicode scalar value except for `\n`.
        This is equivalent to `(?u-s:.)` and also `[\p{any}--\n]`. -/
    | AnyCharExceptLF : Dot
    /-- Matches the UTF-8 encoding of any Unicode scalar value except for `\r` and `\n`.
        This is equivalent to `(?uR-s:.)` and also `[\p{any}--\r\n]`. -/
    | AnyCharExceptCRLF : Dot

def dot (dot: Dot) : Hir :=
    match dot with
    | Dot.AnyChar =>
      let kind : HirKind := HirKind.Class (Class.Unicode default)
      Hir.mk kind (Hir.toProperties kind)
    | Dot.AnyCharExceptLF =>
      let range1 : ClassUnicodeRange := ⟨'\u0000', '\u0009', by simp_arith⟩
      let range2 : ClassUnicodeRange := ⟨'\u000B', ⟨0xD7FF, by simp_arith⟩, by simp_arith⟩
      let range3 : ClassUnicodeRange := ⟨⟨0xE000, by simp_arith⟩, ⟨0x10FFFF, by simp_arith⟩, by simp_arith⟩
      let cls : ClassUnicode := ⟨Interval.canonicalize #[range1, range2, range3]⟩
      let kind : HirKind := HirKind.Class (Class.Unicode cls)
      Hir.mk kind (Hir.toProperties kind)
    | Dot.AnyCharExceptCRLF =>
      let range1 : ClassUnicodeRange := ⟨'\u0000', '\u0009', by simp_arith⟩
      let range2 : ClassUnicodeRange := ⟨'\u000B', '\u000C', by simp_arith⟩
      let range3 : ClassUnicodeRange := ⟨'\u000E', ⟨0xD7FF, by simp_arith⟩, by simp_arith⟩
      let range4 : ClassUnicodeRange := ⟨⟨0xE000, by simp_arith⟩, ⟨0x10FFFF, by simp_arith⟩, by simp_arith⟩
      let cls : ClassUnicode := ⟨Interval.canonicalize #[range1, range2, range3, range4]⟩
      let kind : HirKind := HirKind.Class (Class.Unicode cls)
      Hir.mk kind (Hir.toProperties kind)

/-- An HirFrame is a single stack frame, represented explicitly, which is
    created for each item in the Ast that we traverse.-/
inductive HirFrame where
  | Expr : Hir -> HirFrame
  | Literal : Char -> HirFrame
  | ClassUnicode : ClassUnicode -> HirFrame
  | Repetition : HirFrame
  | Group : (old_flags: Syntax.Flags) -> HirFrame
  | Concat : HirFrame
  | Alternation : HirFrame

namespace HirFrame

def toString : HirFrame -> String
  | .Expr hir => s!"Expr '{hir}'"
  | .Literal c => s!"Literal {c}"
  | .ClassUnicode cls => s!"ClassUnicode cls set size {cls.set.ranges.size}"
  | .Repetition => "Repetition"
  | .Group flags => s!"Group {flags}"
  | .Concat => "Concat"
  | .Alternation => "Alternation"

def unwrap_expr (frame : HirFrame) : Except String Hir :=
  match frame with
  | .Expr expr => Except.ok expr
  | .Literal c => Except.ok ⟨HirKind.Literal c, default⟩
  | _ => Except.error "unwrap_expr, Literal or Expr expected"

/-- Assert that the current stack frame is a Unicode class expression and return it.-/
def unwrap_class_unicode (frame : HirFrame) : Except String Syntax.ClassUnicode :=
  match frame with
  | .ClassUnicode cls => Except.ok cls
  | _ => Except.error "unwrap_repetition, Repetition expected"

/-- Assert that the current stack frame is a repetition. -/
def unwrap_repetition (frame : HirFrame) : Except String Unit :=
  match frame with
  | .Repetition => Except.ok ()
  | _ => Except.error "unwrap_repetition, Repetition expected"

/-- Assert that the current stack frame is a group. -/
def unwrap_group (frame : HirFrame) : Except String Flags :=
  match frame with
  | .Group flags => Except.ok flags
  | _ => Except.error "unwrap_repetition, Repetition expected"

end HirFrame

instance : ToString HirFrame where
  toString := HirFrame.toString
