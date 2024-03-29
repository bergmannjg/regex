import Lean

import Regex

open Lean System

open NFA
open Syntax
open Ast
open Regex

instance : MonadLift (Except String) IO where
  monadLift e :=
    match e with
    | Except.ok res => pure res
    | Except.error e => throw $ .userError e

namespace Test.NonemptyInterval

example : (⟨⟨'b', 'c'⟩, by simp_arith⟩ : NonemptyInterval Char)
  = Interval.intersection ⟨⟨'a', 'c'⟩, by simp_arith⟩ ⟨⟨'b', 'e'⟩, by simp_arith⟩ := by rfl

namespace Test.NonemptyInterval.Intersection

def iv1 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp_arith⟩, ⟨⟨'g', 'k'⟩, by simp_arith⟩]
def iv2 : Array $ NonemptyInterval Char :=
            #[⟨⟨'b', 'e'⟩, by simp_arith⟩, ⟨⟨'j', 'l'⟩, by simp_arith⟩, ⟨⟨'m', 'n'⟩, by simp_arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'b', 'c'⟩, by simp_arith⟩, ⟨⟨'j', 'k'⟩, by simp_arith⟩]

example : iv =
    (IntervalSet.intersection
        (IntervalSet.canonicalize iv1)
        (IntervalSet.canonicalize iv2)).intervals := by
  native_decide

end Test.NonemptyInterval.Intersection

namespace Test.NonemptyInterval.Difference

def iv1 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'e'⟩, by simp_arith⟩]
def iv2 : Array $ NonemptyInterval Char := #[⟨⟨'b', 'c'⟩, by simp_arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'a', 'a'⟩, by simp_arith⟩, ⟨⟨'d', 'e'⟩, by simp_arith⟩]

example : iv =
    (IntervalSet.difference (IntervalSet.canonicalize iv1) (IntervalSet.canonicalize iv2)).intervals := by
  native_decide

end Test.NonemptyInterval.Difference

namespace Test.NonemptyInterval.SymmetricDifference

def iv1 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp_arith⟩]
def iv2 : Array $ NonemptyInterval Char := #[⟨⟨'b', 'd'⟩, by simp_arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'a', 'a'⟩, by simp_arith⟩, ⟨⟨'d', 'd'⟩, by simp_arith⟩]

example : iv =
    (IntervalSet.symmetric_difference (IntervalSet.canonicalize iv1) (IntervalSet.canonicalize iv2)).intervals
  := by native_decide

end Test.NonemptyInterval.SymmetricDifference

namespace Test.NonemptyInterval.Canonicalize

def ivnc : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp_arith⟩, ⟨⟨'b', 'd'⟩, by simp_arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'a', 'd'⟩, by simp_arith⟩]

example : iv = (IntervalSet.canonicalize ivnc).intervals := by native_decide

def ivnc2 : Array $ NonemptyInterval Char := #[
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'B', 'B'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩]
def iv2 : Array $ NonemptyInterval Char := #[
      ⟨⟨'B', 'C'⟩, by simp_arith⟩,
      ⟨⟨'b', 'c'⟩, by simp_arith⟩]

example : iv2 = (IntervalSet.canonicalize ivnc2).intervals := by native_decide

def ivnc3 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp_arith⟩, ⟨⟨'d', 'd'⟩, by simp_arith⟩]
def iv3 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'd'⟩, by simp_arith⟩]

example : iv3 = (IntervalSet.canonicalize ivnc3).intervals := by native_decide

def ivnc4 : Array $ NonemptyInterval Char := #[
  /- 2275 2281 -/ ⟨⟨'ࣣ', 'ࣩ'⟩, by simp_arith⟩,
  /- 2275 2307 -/ ⟨⟨'ࣣ', 'ः'⟩, by simp_arith⟩,
  /- 2288 2306 -/ ⟨⟨'ࣰ', 'ं'⟩, by simp_arith⟩,
  /- 2307 2307 -/ ⟨⟨'ः', 'ः'⟩, by simp_arith⟩,
  /- 2308 2361 -/ ⟨⟨'ऄ', 'ह'⟩, by simp_arith⟩,
  /- 2362 2362 -/ ⟨⟨'ऺ', 'ऺ'⟩, by simp_arith⟩,
  /- 2362 2364 -/ ⟨⟨'ऺ', '़'⟩, by simp_arith⟩,
  /- 2363 2363 -/ ⟨⟨'ऻ', 'ऻ'⟩, by simp_arith⟩]

def iv4 : Array $ NonemptyInterval Char :=  #[⟨⟨'ࣣ', '़'⟩, by simp_arith⟩]

example : iv4 = (IntervalSet.canonicalize ivnc4).intervals := by native_decide

end Test.NonemptyInterval.Canonicalize

namespace Test.NonemptyInterval.Unique

def iv : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩]

def iv1 : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩]

example : iv = Intervals.unique iv1 := by native_decide

def iv2 : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩]

example : iv = Intervals.unique iv2 := by native_decide

def iv3 : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩]

example : iv = Intervals.unique iv3 := by native_decide

end Test.NonemptyInterval.Unique

end Test.NonemptyInterval

namespace Test.Ast

private def toString (x : Except String Ast) : String :=
  match x with
  | Except.ok ast => s!"{ast}"
  | Except.error e => s!"Error {e}"

private def astOf'a' : Ast :=
    Ast.Literal ⟨String.toSpan "a" 0 1, LiteralKind.Verbatim, 'a'⟩

private def astOf'a?' : Ast :=
    Ast.Repetition
      (Repetition.mk
        (String.toSpan "a?" 0 2)
        ⟨String.toSpan "a?" 1 2, RepetitionKind.ZeroOrOne⟩
        true
        (Ast.Literal ⟨String.toSpan "a?" 0 1, LiteralKind.Verbatim, 'a'⟩))

private def astOf'ab' : Ast :=
    Ast.Concat
      (Concat.mk
        (String.toSpan "ab" 0 2)
        #[Ast.Literal ⟨String.toSpan "ab" 0 1, LiteralKind.Verbatim, 'a'⟩,
          Ast.Literal ⟨String.toSpan "ab" 1 2, LiteralKind.Verbatim, 'b'⟩])

private def «astOf'[a]'» : Ast :=
    Ast.ClassBracketed
      (ClassBracketed.mk
        (String.toSpan "[a]" 0 3)
        false
        (ClassSet.Item (ClassSetItem.Literal ⟨String.toSpan "[a]" 1 2, LiteralKind.Verbatim, 'a'⟩)))

private def «astOf'[a-b]'» : Ast :=
    Ast.ClassBracketed
      (ClassBracketed.mk
        (String.toSpan "[a-b]" 0 5)
        false
        (ClassSet.Item (ClassSetItem.Range ⟨
            String.toSpan "[a-b]" 1 4,
            ⟨String.toSpan "[a-b]" 1 2, LiteralKind.Verbatim, 'a'⟩,
            ⟨String.toSpan "[a-b]" 3 4, LiteralKind.Verbatim, 'b'⟩,
            by simp_arith⟩)))

private def «astOf'a|b'» : Ast :=
    Ast.Alternation
      (Alternation.mk
        (String.toSpan "[a|b]" 0 3)
        #[Ast.Literal ⟨String.toSpan "a|b" 0 1, LiteralKind.Verbatim, 'a'⟩,
          Ast.Literal ⟨String.toSpan "a|b" 2 3, LiteralKind.Verbatim, 'b'⟩])

private def «astOf'(a)'» : Ast :=
    Syntax.Ast.Ast.Group
      (Syntax.Ast.Group.mk
        (String.toSpan "(a)" 0 3)
        (GroupKind.CaptureIndex 1)
        (Ast.Literal ⟨String.toSpan "(a)" 1 2, LiteralKind.Verbatim, 'a'⟩))

example : (parse "a" |> toString) = s!"{astOf'a'}" := by native_decide

example : (parse "a?" |> toString) = s!"{astOf'a?'}" := by native_decide

example : (parse "ab" |> toString) = s!"{astOf'ab'}" := by native_decide

example : (parse "[a]" |> toString) = s!"{«astOf'[a]'»}" := by native_decide

example : (parse "[a-b]" |> toString) = s!"{«astOf'[a-b]'»}" := by native_decide

example : (parse "a|b" |> toString) = s!"{«astOf'a|b'»}" := by native_decide

example : (parse "(a)" |> toString) = s!"{«astOf'(a)'»}" := by native_decide

end Test.Ast

namespace Test.Hir

def cls : Syntax.ClassUnicode :=
  let cls : ClassUnicodeRange := ⟨⟨'b', 'c'⟩, by simp_arith⟩
  ⟨IntervalSet.canonicalize #[cls]⟩

def cls_neg : Syntax.ClassUnicode :=
  let cls1 : ClassUnicodeRange := ⟨⟨'\u0000', 'a'⟩, by simp_arith⟩
  let cls2 : ClassUnicodeRange := ⟨⟨'d', ⟨0x10FFFF, by simp_arith⟩⟩, by simp_arith⟩
  ⟨IntervalSet.canonicalize #[cls1, cls2]⟩

example : (Syntax.ClassUnicode.negate cls |> toString) = (cls_neg |> toString) := by native_decide

private def toString (x : Except String Hir) : String :=
  match x with
  | Except.ok hir => s!"{hir}"
  | Except.error e => s!"Error {e}"

private def build (s : String) : Except String Hir := do
  let ast ← Syntax.Ast.parse s
  let hir ← Syntax.translate default ast
  Except.ok hir

private def hirOf'a' : Hir :=
    Hir.mk (HirKind.Literal 'a') default

private def «hirOf'(a)'» : Hir :=
    Hir.mk (HirKind.Capture (Capture.mk 1 none (Hir.mk (HirKind.Literal 'a') default))) default

example : (build "a" |> toString) = hirOf'a'.toString 0 := by native_decide

example : (build "(a)" |> toString) = «hirOf'(a)'».toString 0 := by native_decide

private def _mkCls (arr : Array $ Char × Char) : Syntax.ClassUnicode :=
  ⟨IntervalSet.canonicalize
    (arr |> Array.filterMap (fun (c1, c2) => if h : c1 ≤ c2 then some ⟨⟨ c1, c2⟩, h⟩ else none))⟩

private def mkCls (arr : Array $ Char × Char) : Hir :=
    Hir.mk (HirKind.Class
      (Class.Unicode (_mkCls arr))) default

private def mkConcat (hir : Hir) : Hir :=
  Hir.mk (HirKind.Concat #[hir]) default

example : (build "[[:alpha:]]" |> toString)
  = (mkCls #[('A', 'Z'), ('a', 'z')]).toString 0 := by native_decide

example : (build "[[:^alpha:]]" |> toString)
  = (mkCls #[('\u0000', '@'), ('[', '`'), ('{', ⟨0x10FFFF, by simp_arith⟩)]).toString 0 := by
    native_decide

example : (build "[^A-Za-z]" |> toString)
  = (mkCls #[('\u0000', '@'), ('[', '`'), ('{', ⟨0x10FFFF, by simp_arith⟩)]).toString 0 := by
    native_decide

example : (build "[x[^xyz]]" |> toString)
  = (mkCls #[('\u0000', 'x'), ('{', ⟨0x10FFFF, by simp_arith⟩)]).toString 0 := by native_decide

example : (build "[a-y&&xyz]" |> toString) = (mkCls #[('x', 'y')]).toString 0 := by native_decide

example : (build "[0-9&&[^4]]" |> toString)
  = (mkCls #[('0', '3'), ('5', '9')]).toString 0 := by native_decide

example : (build "[0-9--4]" |> toString)
  = (mkCls #[('0', '3'), ('5', '9')]).toString 0 := by native_decide

example : (build r"[\&&&&]" |> toString) = (mkCls #[('&', '&')]).toString 0 := by native_decide

example : (build "(?i)[abc&&b-c]" |> toString) =
      (mkConcat (mkCls #[('B', 'C'), ('b', 'c')])).toString 0 := by
    native_decide

example : (build "[a-z&&b-y&&c-x]" |> toString) = (mkCls #[('c', 'x')]).toString 0 := by
  native_decide

example : (build "[[:alpha:]--[:lower:]]" |> toString) = (mkCls #[('A', 'Z')]).toString 0 := by
  native_decide

example : (build "[a-g~~c-j]" |> toString) = (mkCls #[('a', 'b'), ('h', 'j')]).toString 0 := by
  native_decide

example : (build "[a&&b]" |> toString) = (mkCls #[]).toString 0 := by native_decide

end Test.Hir

namespace Test.Compiler

open BoundedBacktracker

private def toString (x : Except String Checked.NFA) : String :=
  match x with
  | Except.ok nfa => NFA.Checked.toString nfa
  | Except.error e => s!"Error {e}"

private def nfaOf'a' : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture 4 0 0 0,
    .ByteRange ⟨'a'.val, 'a'.val, 5⟩,
    .Capture 6 0 0 1,
    .Match 0
    ], 2, 0⟩

private def nfaOf'ab' : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture 4 0 0 0,
    .ByteRange ⟨'a'.val, 'a'.val, 5⟩,
    .ByteRange ⟨'b'.val, 'b'.val, 6⟩,
    .Capture 7 0 0 1,
    .Match 0
    ], 2, 0⟩

private def «nfaOf'a?'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture 4 0 0 0,
    .Union #[5, 6],
    .ByteRange ⟨'a'.val, 'a'.val, 6⟩,
    .Empty 7,
    .Capture 8 0 0 1,
    .Match 0
    ], 2, 0⟩

private def «nfaOf'ab?'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture 4 0 0 0,
    .ByteRange ⟨'a'.val, 'a'.val, 5⟩,
    .Union #[6, 7],
    .ByteRange ⟨'b'.val, 'b'.val, 7⟩,
    .Empty 8,
    .Capture 9 0 0 1,
    .Match 0
    ], 2, 0⟩

private def «nfaOf'[a-b]'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture 5 0 0 0,
    .Empty 6,
    .SparseTransitions #[⟨'a'.val, 'b'.val, 4⟩],
    .Capture 7 0 0 1,
    .Match 0
    ], 2, 0⟩

private def «nfaOf'a|b'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture 6 0 0 0,
    .ByteRange ⟨'a'.val, 'a'.val, 7⟩,
    .ByteRange ⟨'b'.val, 'b'.val, 7⟩,
    .Union #[4, 5],
    .Empty 8,
    .Capture 9 0 0 1,
    .Match 0
    ], 2, 0⟩

private def «nfaOf'(a)'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture 4 0 0 0,
    .Capture 5 0 1 2,
    .ByteRange ⟨'a'.val, 'a'.val, 6⟩,
    .Capture 7 0 1 3,
    .Capture 8 0 0 1,
    .Match 0
    ], 2, 0⟩

private def «nfaOf'[a]{0,2}'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture 4 0 0 0,
    .Empty 6,
    .Empty 12,
    .Union #[8, 5],
    .Empty 9,
    .SparseTransitions #[⟨'a'.val, 'a'.val, 7⟩],
    .Union #[11, 5],
    .Empty 5,
    .SparseTransitions #[⟨'a'.val, 'a'.val, 10⟩],
    .Capture 13 0 0 1,
    .Match 0
    ], 2, 0⟩

private def build (s : String) : Except String Checked.NFA := do
  let re ← Regex.build s
  Except.ok re.nfa

example : (build "a" |> toString) = nfaOf'a'.toString := by native_decide

example : (build "ab" |> toString) = nfaOf'ab'.toString := by native_decide

example : (build "a?" |> toString) = «nfaOf'a?'».toString := by native_decide

example : (build "ab?" |> toString) = «nfaOf'ab?'».toString := by native_decide

example : (build "[a-b]" |> toString) = «nfaOf'[a-b]'».toString := by native_decide

example : (build "a|b" |> toString) = «nfaOf'a|b'».toString := by native_decide

example : (build "(a)" |> toString) = «nfaOf'(a)'».toString := by native_decide

example : (build "[a]{0,2}" |> toString) = «nfaOf'[a]{0,2}'».toString := by native_decide

end Test.Compiler

namespace RegexTest

open Lean System

/-- A span of contiguous bytes, from start to end, represented via byte -/
structure Span where
  start: Nat
  «end»: Nat

instance : ToString Span where
  toString s := s!"{s.start} {s.end}"

/-- Captures represents a single group of captured matches from a regex search. -/
structure Captures where
  groups: Array $ Option Span

instance : ToString Captures where
  toString s := s!"Captures {s.groups}"

namespace Captures

def toList2 (json : Json) : Except String $ List (List Nat) :=
  fromJson? json

def toList3 (json : Json) : Except String $ List (List (List Nat)) :=
  fromJson? json

def toSpans (l : List (List Nat)) : Except String $ Array $ Option Span := do
  let spans ←
      l
      |> List.mapM (fun l =>
        match l with
        | [n, m] => Except.ok (some (Span.mk n m))
        | [] => Except.ok none
        | _ => Except.error s!"unexpected list {l}")
      --|> List.toArray
  Except.ok (spans.toArray)

def fromJson? (json : Json) : Except String $ Array Captures := do
  match toList3 json with
  | Except.ok l =>
      let captures  ← l
        |> List.mapM (fun l => do
          let spans ← toSpans l
          pure (Captures.mk spans))
      Except.ok (captures.toArray)
  | _ =>
    match toList2 json with
    | Except.ok l =>
      let captures  ← l
        |> List.mapM (fun l => do
          let spans ← toSpans [l]
          pure (Captures.mk spans))
      Except.ok (captures.toArray)
    | Except.error _ => Except.ok #[]

end Captures

instance : FromJson $ Array Captures := ⟨Captures.fromJson?⟩

namespace Sum

def toString (json : Json) : Except String String :=
  fromJson? json

def toArray (json : Json) : Except String $ Array String :=
  fromJson? json

def fromJson? (json : Json) : Except String $ Sum String (Array String) := do
  match toArray json with
  | Except.ok arr => Except.ok (Sum.inr arr)
  | _ =>
    match toString json with
    | Except.ok s => Except.ok (Sum.inl s)
    | Except.error e => Except.error e

def val (v : Sum String (Array String)) : String :=
    match v with
    | .inl s => s
    | .inr arr => arr[0]!

end Sum

instance : FromJson $ Sum String (Array String) := ⟨Sum.fromJson?⟩

instance : ToString $ Sum String (Array String) where
  toString v :=
    match v with
    | .inl s => s!"{s}"
    | .inr arr => s!"{arr}"

/-- A regex test describes the inputs and expected outputs of a regex match. -/
structure RegexTest where
  name : String
  regex : Sum String (Array String)
  haystack : String
  «matches» : Array Captures
  /-- An optional field whose value is a table with `start` and `end` fields-/
  bounds : Option $ Array Nat
  /--  An optional field that specifies a limit on the number of matches. -/
  «match-limit» : Option Nat
  /-- Whether to execute an anchored search or not. -/
  anchored : Option Bool
  /-- Whether to match the regex case insensitively. -/
  «case-insensitive» : Option Bool
  /-- When enabled, the haystack is unescaped. -/
  unescape : Option Bool
  compiles : Option Bool
  /-- When enabled, the regex pattern should be compiled with its
      corresponding Unicode mode enabled. -/
  unicode : Option Bool
  /-- When this is enabled, all regex match substrings should be entirely valid UTF-8. -/
  utf8 : Option Bool
  /-- May be one of `all`, `leftmost-first` or `leftmost-longest`. -/
  «match-kind» : Option String
  /-- May be one of `earliest`, `leftmost` or `overlapping`. -/
  «search-kind» : Option String
  /-- This sets the line terminator used by the multi-line assertions -/
  «line-terminator» : Option String
deriving FromJson

def isMatch (t : RegexTest) : Bool :=
  if h : 0 < t.matches.size
  then (t.matches[0]'h).groups.size > 0
  else false

structure RegexTests where
  test : Array RegexTest
deriving FromJson

namespace String

def containsSubstr (s pattern : String) : Bool :=
  (s.splitOn pattern).length > 1

end String

def checkFlagIsFalse (f : Option Bool) : Bool :=
  match f with | some v => !v | none => false

private def escape (s : String) : String :=
  (s.replace "\n" "\\n").replace "\r" "\\r"

instance : ToString RegexTest where
  toString s :=
    let str := s!"{s.name} '{s.regex}' '{escape s.haystack}' {s.matches}"
    let str := str ++ (if s.anchored.isSome then " anchored" else "")
    let str := str ++ (if s.«case-insensitive».isSome then " case-insensitive" else "")
    let str := str ++ (if s.unescape.isSome then " unescape" else "")
    let str := str ++ (if s.unicode.isSome && !s.unicode.getD true then " !unicode" else "")
    let str := str ++ (if String.containsSubstr (Sum.val s.regex) "(?" then " flags" else "")
    let str := str ++ (if checkFlagIsFalse s.compiles then " !compiles" else "")
    str

instance : ToString RegexTests where
  toString s := s!"{s.test}"

def unescape (s : String) : String :=
  ⟨loop s.data []⟩
where
  toChar (a b : Char) : Char :=
    match Char.decodeHexDigit a, Char.decodeHexDigit b with
    | some n, some m =>
      let val := 16*n+m
      if h : UInt32.isValidChar val then ⟨val, h⟩ else ⟨0, by simp_arith⟩
    | _, _ => ⟨0, by simp_arith⟩
  loop (chars : List Char) (acc : List Char) : List Char :=
    match chars with
    | [] => acc
    | '\\' :: 'x' :: a :: b :: tail => (toChar a b) :: (loop tail acc)
    | '\\' :: 'n' :: tail => '\n' :: (loop tail acc)
    | head :: tail => head :: (loop tail acc)

def compiles (t : RegexTest) : Bool :=
  let flags : Syntax.Flags := default
  let config : Compiler.Config := default
  match Regex.build (Sum.val t.regex) flags config with
  | Except.ok _ => true
  | Except.error _ => false

def captures (t : RegexTest) : Except String (Array Regex.Captures) := do
  let flags : Syntax.Flags := default
  let config : Compiler.Config := default

  let flags := {flags with case_insensitive := t.«case-insensitive»}
  let config := {config with unanchored_prefix := !t.anchored.getD false}

  let haystack := if t.unescape.getD false then unescape t.haystack else t.haystack
  let re ← Regex.build (Sum.val t.regex) flags config
  Except.ok (Regex.all_captures haystack.toSubstring re)

def checkMatches (arr : Array Regex.Captures) (t : RegexTest) : Bool :=
  let match_limit := t.«match-limit».getD 1000
  let arr := arr |> Array.toList |> List.take match_limit |> List.toArray

  if arr.size != t.matches.size then false
  else
    let idx := Array.mapIdx arr (fun i v => (i, v))
    Array.all idx (fun (i, m) =>
      if h : i.val < t.matches.size
      then
        let t_matches := (t.matches[i.val]'h).groups
        let idx := Array.mapIdx (m.matches) (fun i v => (i, v))
        Array.all idx (fun (i, v) =>
          match t_matches.get? i.val, v with
          | some (some span), some v =>
              span.start = v.startPos.byteIdx && span.end = v.stopPos.byteIdx
          | some none, none => true
          | _, _ => false)
      else false)

private def captureToString (r : Regex.Captures) : String :=
  r.matches |> Array.map (fun m =>
    match m with
    | some m => s!"({m.startPos}, {m.stopPos}), "
    | none => "none")
  |> Array.toList
  |> String.join
  |> fun s =>
    let s := if s.endsWith ", "
             then ((String.toSubstring s).dropRight 2).toString
             else s
    "[" ++ s ++ "]"

private def capturesToString (arr : Array Regex.Captures) : String :=
  arr
  |> Array.map (fun c => captureToString c ++ ", ")
  |> Array.toList
  |> String.join
  |> fun s =>
    let s := if s.endsWith ", "
             then ((String.toSubstring s).dropRight 2).toString
             else s
    "[" ++ s ++ "]"

/-- ignore test, feature not implemented -/
def ignoreTest (t : RegexTest) : Bool :=
  checkFlagIsFalse t.unicode
  || checkFlagIsFalse t.utf8
  || t.bounds.isSome -- no api
  || t.«line-terminator».isSome -- Config
  || t.«search-kind».any (· != "leftmost") -- only leftmost is valid for BoundedBacktracker
  || t.«match-kind».any (· = "all") -- Sets
  || match t.regex with | .inr _ => true | .inl _ => false -- Sets

def testItem (filename : String) (t : RegexTest) : IO (Nat × Nat × Nat) := do
  if checkFlagIsFalse t.compiles
  then
    if compiles t
    then
      IO.println s!"RegexTest: {t}"
      IO.println s!"  should not compile"
      pure (0, 1, 0)
    else pure (1, 0, 0)
  else if ignoreTest t
  then
    pure (0, 0, 1)
  else
    match captures t with
    | Except.ok result =>
      if result.size = 0
      then
        if RegexTest.isMatch t
        then
          IO.println s!"RegexTest({filename}): {t}"
          IO.println s!"  no match found, expected {t.matches}"
          pure (0, 1, 0)
        else
          pure (1, 0, 0)
      else
        if checkMatches result t
        then
            pure (1, 0, 0)
        else
          IO.println s!"RegexTest({filename}): {t}"
          IO.println s!"  expected size {t.matches.size}, actual {result.size} "
          IO.println s!"  match different, expected {t.matches}, actual {capturesToString result}"
          pure (0, 1, 0)
      | Except.error e =>
          IO.println s!"RegexTest{filename}: {t}"
          IO.println s!"  error {e}"
          pure (0, 1, 0)

def testItems (filename : String) (items : Array RegexTest) : IO (Nat × Nat× Nat) := do
  items |> Array.foldlM (init := (0, 0, 0)) (fun (succeeds, failures, ignored) RegexTest => do
    let (succeed, failure, ignore) ← testItem filename RegexTest
    pure (succeeds + succeed, failures + failure, ignore + ignored))

def toRegexTests (s : String) : Except String RegexTests := do
  Json.parse s >>= fromJson?

end RegexTest

def test (path : FilePath): IO (Nat × Nat × Nat) := do
  let filename : String := path.fileName.getD ""
  match RegexTest.toRegexTests (←IO.FS.readFile path) with
  | Except.ok tests =>
    let (succeeds, failures, ignored) ← RegexTest.testItems filename tests.test
    IO.println s!"succeeds {succeeds} failures {failures} ignored {ignored} in file {path}"
    pure (succeeds, failures, ignored)
  | Except.error e => Except.error (s!"file {path} " ++ e)

def summary (arr : Array (Nat × Nat × Nat)) : IO UInt32 := do
  let (succeeds, failures, ignored) := arr |> Array.foldl
    (fun acc v => (acc.1+v.1, acc.2.1+v.2.1, acc.2.2+v.2.2) ) (0, 0, 0)
  IO.println s!"succeeds {succeeds} failures {failures} ignored {ignored} total"
  pure (if failures > 0 then 1 else 0)

def main (args : List String): IO UInt32 := do
  let mut exitcode : UInt32 := 0
  try
    match args with
    | ["--json", path] => test path |> discard
    | ["--all", path] =>
      exitcode ←
        if ← System.FilePath.isDir path
        then
          (← System.FilePath.walkDir path)
          |> Array.filter (fun f => f.toString.endsWith "json")
          |> Array.mapM (fun file => test file)
          |> fun arr => do summary (← arr)
        else
          IO.println  s!"no such directory '{path}'"
          pure 1
    | _ => IO.println  s!"usage: Test [--json <path>] [--all path]"
  catch e =>
    IO.println s!"Error: {e}"

  pure exitcode
