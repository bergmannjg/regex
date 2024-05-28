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
      .Capture ⟨4, by simp⟩ 0 0 0,
      .ByteRange ⟨'a'.val.val, 'a'.val.val, ⟨5, by simp⟩⟩,
      .Capture ⟨6, by simp⟩ 0 0 1,
      .Match 0
    ]
    (by simp only [Array.size_toArray, List.length_cons, List.length_nil])

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

open Regex.Notation

/--
error: failed to parse pattern a[, error: unclosed character class
-/
#guard_msgs in
def re := regex% "a["

example : NFA.Checked.toString nfaOf'a'Checked = nfaOf'a'.toString  := by native_decide

example : toString (regex% "a").nfa = nfaOf'a'.toString := by native_decide

example : toString (regex% "ab").nfa = nfaOf'ab'.toString := by native_decide

example : toString (regex% "a?").nfa = «nfaOf'a?'».toString := by native_decide

example : toString (regex% "ab?").nfa = «nfaOf'ab?'».toString := by native_decide

example : toString (regex% "[a-b]").nfa = «nfaOf'[a-b]'».toString := by native_decide

example : toString (regex% "a|b").nfa = «nfaOf'a|b'».toString := by native_decide

example : toString (regex% "(a)").nfa = «nfaOf'(a)'».toString := by native_decide

example : toString (regex% "[a]{0,2}").nfa = «nfaOf'[a]{0,2}'».toString := by native_decide

end Test.Compiler
