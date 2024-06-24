import Batteries.Data.Array.Basic
import Regex.Utils
import Regex.Interval
import Regex.Unicode

/-!
## High-level intermediate representation for a regular expression.

A high-level intermediate representation `Syntax.Hir` for a regular expression.
-/

namespace Syntax

abbrev ClassUnicodeRange := NonemptyInterval Char

instance : Inhabited ClassUnicodeRange := ⟨⟨⟨0, by simp_arith⟩, ⟨0, by simp_arith⟩⟩, by simp_arith⟩

structure ClassUnicode where
  set: IntervalSet Char

instance : ToString (NonemptyInterval Char) where
  toString r := s!"{UInt32.intAsString r.fst.val}-{UInt32.intAsString r.snd.val}"

private def rangesToString (arr : Array (NonemptyInterval Char)) : String :=
  arr |> Array.map (fun r => s!"    {r.fst}-{r.snd},\n") |> Array.toList |> String.join

instance : ToString (IntervalSet Char) where
  toString set := s!"ranges: {set.intervals}"

instance : ToString ClassUnicode where
  toString cls := s!"{cls.set}"

/-- see UInt32.isValidChar -/
instance : Inhabited ClassUnicode :=
  let cls1 : NonemptyInterval Char := ⟨⟨'\u0000', ⟨0xD7FF, by simp_arith⟩⟩, by simp_arith⟩
  let cls2 : NonemptyInterval Char := ⟨⟨⟨0xE000, by simp_arith⟩, ⟨0x10FFFF, by simp_arith⟩⟩, by simp_arith⟩
  let ranges := #[cls1, cls2]
  ⟨⟨IntervalSet.canonicalize ranges⟩⟩

namespace ClassUnicode

def empty : ClassUnicode :=
  ⟨⟨#[], Intervals.empty_isNonOverlapping⟩⟩

def canonicalize (cls : ClassUnicode) : ClassUnicode :=
  ⟨IntervalSet.canonicalize cls.set.intervals⟩

def union (cls1 cls2 : ClassUnicode) : ClassUnicode :=
  ⟨IntervalSet.union cls1.set cls2.set⟩

def intersection (cls1 cls2 : ClassUnicode) : ClassUnicode :=
  ⟨IntervalSet.intersection cls1.set cls2.set⟩

def difference (cls1 cls2 : ClassUnicode) : ClassUnicode :=
  ⟨IntervalSet.difference cls1.set cls2.set⟩

def symmetric_difference (cls1 cls2 : ClassUnicode) : ClassUnicode :=
  ⟨IntervalSet.symmetric_difference cls1.set cls2.set⟩

def negate (cls : ClassUnicode) : ClassUnicode :=
  ⟨IntervalSet.negate cls.set⟩

def case_fold (cls : ClassUnicode) : ClassUnicode :=
  let ranges := cls.set.intervals
  let init : Array (NonemptyInterval Char) := #[]
  let ranges := ranges |> Array.foldl (init := init) (fun acc r =>
    let folded := Unicode.case_fold_range r
    acc ++ folded)

  ⟨IntervalSet.canonicalize ranges⟩

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
  /-- Match the end of text (before optional newline). -/
  | EndWithOptionalLF : Look
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
  | .EndWithOptionalLF => s!"EndWithOptionalLF"
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

/-- The high-level intermediate representation for a look-around assertion. -/
inductive Lookaround where
  | PositiveLookahead : Hir -> Lookaround
  | NegativeLookahead : Hir -> Lookaround
  | PositiveLookbehind : Nat -> Hir -> Lookaround
  | NegativeLookbehind : Nat -> Hir -> Lookaround

/-- A concatenation of regular expressions. -/
inductive Repetition where
  | mk (min: Nat) (max: Option Nat) (greedy : Bool) (possessive : Bool) (sub: Hir) : Repetition

/-- The high-level intermediate representation for a capturing group. -/
inductive Capture where
  | mk (index: Nat) (name: Option String) (sub: Hir) : Capture

/-- The underlying kind of an arbitrary [`Hir`] expression. -/
inductive HirKind where
  /-- The empty regular expression, which matches everything, including the empty string. -/
  | Empty : HirKind
  /-- A literal string that matches exactly these bytes. -/
  | Literal : Char -> HirKind
  /-- A backrefence to a capturung group. -/
  | BackRef : Bool -> Nat -> HirKind
  /-- A single character class that matches any of the characters in the class. -/
  | Class : Class -> HirKind
  /-- A look-around assertion. A look-around match always has zero length. -/
  | Look : Look -> HirKind
  /-- A complex look-around assertion. -/
  | Lookaround : Lookaround -> HirKind
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

def fold [Inhabited α] (hir : Hir) (f : α -> Hir -> α) (init :  α): α :=
  let ⟨kind, _⟩ := hir
  match kind with
  | .Empty => f init hir
  | .Literal _ => f init hir
  | .BackRef _ _ => f init hir
  | .Class _ => f init hir
  | .Look _ => f init hir
  | .Lookaround look =>
      match look with
      | .PositiveLookahead sub => fold sub f init
      | .NegativeLookahead sub => fold sub f init
      | .PositiveLookbehind _ sub => fold sub f init
      | .NegativeLookbehind _  sub => fold sub f init
  | .Repetition ⟨_, _, _, _, sub⟩  => fold sub f init
  | .Capture _ => f init hir
  | .Concat hirs => hirs.attach |> Array.foldl (init := init)
      (fun a (h : { x // x ∈ hirs}) =>
        have : sizeOf h.val < sizeOf hirs := Array.sizeOf_lt_of_mem h.property
        fold h.val f a)
  | .Alternation hirs => hirs.attach |> Array.foldl (init := init)
      (fun a (h : { x // x ∈ hirs}) =>
        have : sizeOf h.val < sizeOf hirs := Array.sizeOf_lt_of_mem h.property
        fold h.val f a)
termination_by sizeOf hir

/-- check if an `hir` contains `look` -/
def contains (hir : Hir) (look : Look) : Bool :=
  fold (init := false) hir
    (fun acc ⟨kind, props⟩ =>
      match kind with
      | .Look _ => acc || props.look_set_prefix.contains look
      | _ => acc)

def kind (hir : Hir) : HirKind := match hir with | .mk kind _ => kind

theorem sizeOfKindOfHir (hir : Hir) : sizeOf hir.kind < sizeOf hir := by
  unfold Hir.kind; split; simp_all; omega

def properties (hir : Hir) : Properties := match hir with | .mk _ properties => properties

def toProperties (kind: HirKind) : Properties :=
  match kind with
  | .Class (.Unicode cls) =>
      /- the length, in bytes, of the smallest string matched by this character class. -/
      let min := if cls.set.intervals.size > 0 then some 1 else none
      ⟨min, none, #[]⟩
  | .Look look => ⟨none, none, #[look]⟩
  | _ => default

def toString (hir : Hir) (col : Nat): String :=
  let col := col + 2
  let pre := "\n" ++ (Char.multiple ' ' col "")
  have : sizeOf hir.kind < sizeOf hir := Hir.sizeOfKindOfHir hir
  match hk : hir.kind with
  | .Empty => s!"Empty"
  | .Literal c => s!"Literal '{UInt32.intAsString c.val}'"
  | .BackRef f n => s!"BackRef {if f then "case_insensitive" else ""}'{n}'"
  | .Class cls => s!"Class {cls}"
  | .Look look => s!"Look {look}"
  | .Lookaround lk  =>
    match hr: lk with
    | .PositiveLookahead sub =>
        have : sizeOf lk < sizeOf hir.kind := by simp [hk, hr]
        have : sizeOf sub < sizeOf lk := by simp [hr]
        s!"PositiveLookahead {toString sub col}"
    | .NegativeLookahead sub =>
        have : sizeOf lk < sizeOf hir.kind := by simp [hk, hr]
        have : sizeOf sub < sizeOf lk := by simp [hr]
        s!"NegativeLookahead {toString sub col}"
    | .PositiveLookbehind i sub =>
        have : sizeOf lk < sizeOf hir.kind := by simp [hk, hr]
        have : sizeOf sub < sizeOf lk := by simp [hr]; omega
        s!"PositiveLookbehind Length {i} {toString sub col}"
    | .NegativeLookbehind i sub =>
        have : sizeOf lk < sizeOf hir.kind := by simp [hk, hr]
        have : sizeOf sub < sizeOf lk := by simp [hr]; omega
        s!"NegativeLookbehind Length {i} {toString sub col}"
  | .Repetition rep =>
    match hr : rep with
    | .mk min max greedy possessive sub =>
        have : sizeOf rep < sizeOf hir.kind := by simp [hk, hr]
        have : sizeOf sub < sizeOf rep := by simp [hr]
        s!"Repetition {min} {max} possessive {possessive} greedy {greedy}{pre}sub {toString sub col}"
  | .Capture c =>
    match hc : c with
    | .mk index name sub =>
        have : sizeOf c < sizeOf hir.kind := by simp [hk, hc]
        have : sizeOf sub < sizeOf c := by simp [hc]; omega
        s!"Capture {index} {name}{pre}sub {toString sub col}"
  | .Concat items =>
      let hirs := Array.mapIdx items.attach (fun i s => (i, s))
      have : sizeOf items < sizeOf hir.kind := by simp [hk]
      let hirs := String.join (hirs.toList |> List.map (fun (i, ast) =>
          let iv := String.mk (Nat.toDigits 0 i.val)
          have : sizeOf ast.val < sizeOf items := Array.sizeOf_lt_of_mem ast.property
          pre ++ iv ++ ": " ++ (toString ast.val col)))
      s!"Concat {hirs}"
  | .Alternation items =>
      let hirs := Array.mapIdx items.attach (fun i s => (i, s))
      have : sizeOf items < sizeOf hir.kind := by simp [hk]
      let hirs := String.join (hirs.toList |> List.map (fun (i, ast) =>
          let iv := String.mk (Nat.toDigits 0 i.val)
          have : sizeOf ast.val < sizeOf items := Array.sizeOf_lt_of_mem ast.property
          pre ++ iv ++ ": " ++ (toString ast col)))
      s!"Alternation {hirs}"
termination_by sizeOf hir

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
      let range1 : ClassUnicodeRange := ⟨⟨'\u0000', '\u0009'⟩, by simp_arith⟩
      let range2 : ClassUnicodeRange := ⟨⟨'\u000B', ⟨0xD7FF, by simp_arith⟩⟩, by simp_arith⟩
      let range3 : ClassUnicodeRange := ⟨⟨⟨0xE000, by simp_arith⟩, ⟨0x10FFFF, by simp_arith⟩⟩, by simp_arith⟩
      let cls : ClassUnicode := ⟨IntervalSet.canonicalize #[range1, range2, range3]⟩
      let kind : HirKind := HirKind.Class (Class.Unicode cls)
      Hir.mk kind (Hir.toProperties kind)
    | Dot.AnyCharExceptCRLF =>
      let range1 : ClassUnicodeRange := ⟨⟨'\u0000', '\u0009'⟩, by simp_arith⟩
      let range2 : ClassUnicodeRange := ⟨⟨'\u000B', '\u000C'⟩, by simp_arith⟩
      let range3 : ClassUnicodeRange := ⟨⟨'\u000E', ⟨0xD7FF, by simp_arith⟩⟩, by simp_arith⟩
      let range4 : ClassUnicodeRange := ⟨⟨⟨0xE000, by simp_arith⟩, ⟨0x10FFFF, by simp_arith⟩⟩, by simp_arith⟩
      let cls : ClassUnicode := ⟨IntervalSet.canonicalize #[range1, range2, range3, range4]⟩
      let kind : HirKind := HirKind.Class (Class.Unicode cls)
      Hir.mk kind (Hir.toProperties kind)

/-- An HirFrame is a single stack frame, represented explicitly, which is
    created for each item in the Ast that we traverse.-/
inductive HirFrame where
  | Expr : Hir -> HirFrame
  | Literal : Char -> HirFrame
  | BackRef : Bool -> Nat -> HirFrame
  | ClassUnicode : ClassUnicode -> HirFrame
  | Repetition : HirFrame
  | Group : (old_flags: Syntax.Flags) -> HirFrame
  | Concat : HirFrame
  | Alternation : HirFrame

namespace HirFrame

def toString : HirFrame -> String
  | .Expr hir => s!"Expr '{hir}'"
  | .Literal c => s!"Literal {c}"
  | .BackRef f n => s!"BackRef {if f then "case_insensitive" else ""} {n}"
  | .ClassUnicode cls => s!"ClassUnicode cls set size {cls.set.intervals.size}"
  | .Repetition => "Repetition"
  | .Group flags => s!"Group {flags}"
  | .Concat => "Concat"
  | .Alternation => "Alternation"

def unwrap_expr (frame : HirFrame) : Except String Hir :=
  match frame with
  | .Expr expr => Except.ok expr
  | .Literal c => Except.ok ⟨HirKind.Literal c, default⟩
  | .BackRef f n => Except.ok ⟨HirKind.BackRef f n, default⟩
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
