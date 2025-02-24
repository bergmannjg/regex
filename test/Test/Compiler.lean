import Batteries.Data.String
import Regex

open Syntax
open NFA
open Regex

namespace Test.Compiler

open BoundedBacktracker

private def nfaOf'a'Checked : Checked.NFA :=
  Checked.NFA.mk 7
    #[.UnionReverse #[⟨2, by simp⟩, ⟨3, by simp⟩],
      .Empty ⟨0, by simp⟩,
      .SparseTransitions #[⟨0, 0xd7ff, ⟨1, by simp⟩⟩, ⟨0xe000, 0x10ffff, ⟨1, by simp⟩⟩],
      .Capture NFA.Capture.Role.Start ⟨4, by simp⟩ 0 0 0,
      .ByteRange ⟨'a'.val.val, 'a'.val.val, ⟨5, by simp⟩⟩,
      .Capture NFA.Capture.Role.End ⟨6, by simp⟩ 0 0 1,
      .Match 0
    ]
    #[]
    #[(0, 0), (1, 0)]
    false
    rfl
    rfl

private def nfaOf'a' : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture NFA.Capture.Role.Start 4 0 0 0,
    .ByteRange ⟨'a'.val, 'a'.val, 5⟩,
    .Capture NFA.Capture.Role.End 6 0 0 1,
    .Match 0
    ], #[(0, 0), (1, 0)], 2, 0⟩

example : Unchecked.toSlots (nfaOf'a'.states) = #[(0, 0), (1, 0)] := by native_decide

private def nfaOf'ab' : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture NFA.Capture.Role.Start 4 0 0 0,
    .ByteRange ⟨'a'.val, 'a'.val, 5⟩,
    .ByteRange ⟨'b'.val, 'b'.val, 6⟩,
    .Capture NFA.Capture.Role.End 7 0 0 1,
    .Match 0
    ], #[(0, 0), (1, 0)], 2, 0⟩

private def «nfaOf'a?'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture NFA.Capture.Role.Start 4 0 0 0,
    .Union #[5, 6],
    .ByteRange ⟨'a'.val, 'a'.val, 6⟩,
    .Empty 7,
    .Capture NFA.Capture.Role.End 8 0 0 1,
    .Match 0
    ], #[(0, 0), (1, 0)], 2, 0⟩

private def «nfaOf'ab?'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture NFA.Capture.Role.Start 4 0 0 0,
    .ByteRange ⟨'a'.val, 'a'.val, 5⟩,
    .Union #[6, 7],
    .ByteRange ⟨'b'.val, 'b'.val, 7⟩,
    .Empty 8,
    .Capture NFA.Capture.Role.End 9 0 0 1,
    .Match 0
    ], #[(0, 0), (1, 0)], 2, 0⟩

private def «nfaOf'[a-b]'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture NFA.Capture.Role.Start 5 0 0 0,
    .Empty 6,
    .SparseTransitions #[⟨'a'.val, 'b'.val, 4⟩],
    .Capture NFA.Capture.Role.End 7 0 0 1,
    .Match 0
    ], #[(0, 0), (1, 0)], 2, 0⟩

private def «nfaOf'a|b'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture NFA.Capture.Role.Start 6 0 0 0,
    .ByteRange ⟨'a'.val, 'a'.val, 7⟩,
    .ByteRange ⟨'b'.val, 'b'.val, 7⟩,
    .Union #[4, 5],
    .Empty 8,
    .Capture NFA.Capture.Role.End 9 0 0 1,
    .Match 0
    ], #[(0, 0), (1, 0)], 2, 0⟩

private def «nfaOf'(a)'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture NFA.Capture.Role.Start 4 0 0 0,
    .Capture NFA.Capture.Role.Start 5 0 1 2,
    .ByteRange ⟨'a'.val, 'a'.val, 6⟩,
    .Capture NFA.Capture.Role.End 7 0 1 3,
    .Capture NFA.Capture.Role.End 8 0 0 1,
    .Match 0
    ], #[(0, 0), (1, 0), (2, 1), (3, 1)], 2, 0⟩

private def «nfaOf'[a]{0,2}'» : Unchecked.NFA :=
  ⟨#[.UnionReverse #[2, 3],
    .Empty 0,
    .SparseTransitions #[⟨0, 0xd7ff, 1⟩, ⟨0xe000, 0x10ffff, 1⟩],
    .Capture NFA.Capture.Role.Start 4 0 0 0,
    .Empty 8,
    .Empty 12,
    .Empty 11,
    .SparseTransitions #[⟨'a'.val, 'a'.val, 6⟩],
    .Union #[7, 5],
    .Empty 5,
    .SparseTransitions #[⟨'a'.val, 'a'.val, 9⟩],
    .Union #[10, 5],
    .Capture NFA.Capture.Role.End 13 0 0 1,
    .Match 0
    ], #[(0, 0), (1, 0)], 2, 0⟩

open Regex.Notation

/--
error: failed to parse pattern a[, error: unclosed character class

#guard_msgs in
def re := regex% "a["
-/

example : toString nfaOf'a'Checked = toString nfaOf'a'  := by native_decide

example : toString (regex% "a").nfa = nfaOf'a'.toString := by native_decide

example : toString (regex% "ab").nfa = nfaOf'ab'.toString := by native_decide

example : toString (regex% "a?").nfa = «nfaOf'a?'».toString := by native_decide

example : toString (regex% "ab?").nfa = «nfaOf'ab?'».toString := by native_decide

example : toString (regex% "[a-b]").nfa = «nfaOf'[a-b]'».toString := by native_decide

example : toString (regex% "a|b").nfa = «nfaOf'a|b'».toString := by native_decide

example : toString (regex% "(a)").nfa = «nfaOf'(a)'».toString := by native_decide

example : toString (regex% "[a]{0,2}").nfa = «nfaOf'[a]{0,2}'».toString := by native_decide

private def capturesOf (s : String) (startPos stopPos : ValidPos s) (h : startPos.val ≤ stopPos.val)
    : Option (Captures s) :=
  some ⟨⟨⟨s, startPos.val, stopPos.val⟩,
        by exact ⟨startPos.property, stopPos.property, h⟩⟩, #[], by simp, by simp⟩

example : toString (Regex.captures "a" (regex% "a"))
          = toString (capturesOf "a"
                ⟨⟨0⟩, by simp⟩
                ⟨⟨1⟩, by exact ⟨['a'], ⟨[], by simp_all; rfl⟩⟩⟩ (by decide)) := by native_decide

example : toString (Regex.captures "ab" (regex% "a(?=b)"))
          = toString (capturesOf "ab"
                ⟨⟨0⟩, by simp⟩
                ⟨⟨1⟩, by exact ⟨['a'], ⟨['b'], by simp_all; rfl⟩⟩⟩ (by decide)) := by native_decide

example : regex% "a(?=b)" |> Regex.captures "ac" |>.isNone := by native_decide

example : toString (Regex.captures "ac" (regex% "a(?!b)"))
          = toString (capturesOf "ac"
                ⟨⟨0⟩, by simp⟩
                ⟨⟨1⟩, by exact ⟨['a'], ⟨['c'], by simp_all;rfl⟩⟩⟩ (by decide)) := by native_decide

example : regex% "a(?!b)" |> Regex.captures "ab" |>.isNone := by native_decide

private def fullMatch (s : String) (captures : Option (Captures s)) : String :=
  match captures with | some captures => captures.fullMatch.val.toString | none => ""

example : (fullMatch "∀ (n : Nat), 0 ≤ n" <| Regex.captures
            "∀ (n : Nat), 0 ≤ n"
            (regex% r"^\p{Math}\s*.(?<=\()([a-z])[^,]+,\s*(\p{Nd})\s*(\p{Math})\s*\1$"))
           = "∀ (n : Nat), 0 ≤ n" := by native_decide

/- match a double-quoted string -/
example : (fullMatch "\"αbc\"" <| Regex.captures
            "\"αbc\""
            (regex% "\"(?:[^\"\\\\]++|\\.)*+\""))
           = "\"αbc\"" := by native_decide

end Test.Compiler
