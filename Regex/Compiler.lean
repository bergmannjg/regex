import Init.Meta
import Batteries.Data.Array.Basic
import Batteries.Lean.Except

import Regex.Syntax.Hir
import Regex.Nfa
import Regex.Tactic.SimpLte
import Regex.Data.Nat.Basic

namespace Compiler

open Syntax
open NFA

/-!
## Compiler

Compile from a regex's high-level intermediate representation (`Syntax.Hir`)
into an NFA state graph (`NFA`).
-/

/-- The configuration used for a Thompson NFA compiler. -/
structure Config where
  /-- Whether to compile an unanchored prefix into this NFA. -/
  unanchored_prefix: Bool
  /-- Whether to simulate an unanchored prefix with the backtracker. -/
  unanchored_prefix_simulation : Bool
  /-- Max recurciosn deth in compilation -/
  fuel : Nat

instance : Inhabited Config := ⟨⟨true, false, 1000⟩⟩

/-- A value that represents the result of compiling a sub-expression of a regex's HIR.
    Specifically, this represents a sub-graph of the NFA that
    has an initial state at `start` and a final state at `end`.
-/
structure ThompsonRef where
  start: Unchecked.StateID
  «end»: Unchecked.StateID

instance : ToString ThompsonRef where
  toString s := s!"{s.start}, {s.end}"

abbrev States := { a : Array Unchecked.State // ∀ i (h : i < a.size), (a[i]'h).nextOf < a.size }

abbrev States' (states : States) :=
  { states' : States // states.val.size ≤ states'.val.size}

abbrev StateIDStates (states : States) :=
  { pairs : Unchecked.StateID × States
    // pairs.1 < pairs.2.val.size ∧ states.val.size < pairs.2.val.size}

abbrev StateIDStates' (states states' : States) :=
  { pairs : Unchecked.StateID × States
    // pairs.1 < pairs.2.val.size ∧ states.val.size < pairs.2.val.size
       ∧ states'.val.size ≤ pairs.2.val.size}

abbrev ThompsonRefStates (states : States) :=
  { pairs : ThompsonRef × States
    // pairs.1.start < pairs.2.val.size ∧ pairs.1.«end» < pairs.2.val.size
       ∧ states.val.size < pairs.2.val.size }

def ThompsonRefStates.mk {states : States} (arg1Start arg1End : Unchecked.StateID) (arg2 : States)
  (h : arg1Start < arg2.val.size
        ∧ arg1End < arg2.val.size
        ∧ states.val.size < arg2.val.size)
    : ThompsonRefStates states :=
  ⟨(⟨arg1Start, arg1End⟩ , arg2), h⟩

def ThompsonRefStates.castLt {states states' : States} (t : ThompsonRefStates states)
  (h : states'.val.size < t.val.snd.val.size) : ThompsonRefStates states' :=
  ThompsonRefStates.mk t.val.1.start t.val.1.end t.val.2 (by
    have ht := t.property
    exact And.intro ht.left (And.intro ht.right.left h))

abbrev CompilerM := StateT (Array Nat) (Except String)

private theorem all_set {n : Unchecked.StateID} {s : Unchecked.State} {states : States}
  (h : n < states.val.size) (hn : Unchecked.State.nextOf s < states.val.size)
    : ∀ i (_ : i < (states.val.set n s h).size),
     ((states.val.set n s h)[i].nextOf < (states.val.set n s h).size) := by
  have hs := Array.size_set states.val n s h
  intro i hi
  rw [hs]
  rw [hs] at hi
  have := Array.getElem_set states.val n h s i (by rw [hs]; exact hi)
  split at this
  simp_all
  rw [this]
  exact states.property i hi

private theorem all_push {s : Unchecked.State} {states : States}
  (h : Unchecked.State.nextOf s ≤ states.val.size)
    : ∀ i (_ : i < (states.val.push s).size),
      ((states.val.push s)[i].nextOf < (states.val.push s).size) := by
  intro i hi
  have := Array.getElem_push states.val s i hi
  simp_all
  split
  . rename_i h'
    exact Nat.lt_add_right 1 (states.property i h')
  . exact Nat.lt_add_one_of_le h

private theorem eat_until_lt {states : States} (h : «from» < states.val.size)
  (hm : states.val[«from»]'h = Unchecked.State.Eat (Unchecked.EatMode.Until s) n)
    : s < states.val.size ∧ n < states.val.size := by
  have := states.property «from» h
  rw [hm] at this
  simp +zetaDelta [Unchecked.State.nextOf, Nat.max, @Nat.max_def s n] at this
  exact Nat.max_lt.mp this

private theorem eat_toLast_lt {states : States} (h : «from» < states.val.size)
  (hm : states.val[«from»]'h = Unchecked.State.Eat (Unchecked.EatMode.ToLast s) n)
    : s < states.val.size ∧ n < states.val.size := by
  have := states.property «from» h
  rw [hm] at this
  simp +zetaDelta [Unchecked.State.nextOf, Nat.max, @Nat.max_def s n] at this
  exact Nat.max_lt.mp this

private theorem change_frame_step_lt {states : States} (h : «from» < states.val.size)
  (hm : states.val[«from»]'h = Unchecked.State.ChangeFrameStep f t)
    : f < states.val.size ∧ t < states.val.size := by
  have := states.property «from» h
  rw [hm] at this
  simp +zetaDelta [Unchecked.State.nextOf, Nat.max, Nat.max_lt] at this
  assumption

private theorem binary_union_lt {states : States} (h : «from» < states.val.size)
  (hm : states.val[«from»]'h = Unchecked.State.BinaryUnion alt1 alt2)
    : alt1 < states.val.size ∧ alt2 < states.val.size := by
  have := states.property «from» h
  rw [hm] at this
  simp +zetaDelta [Unchecked.State.nextOf, Nat.max, Nat.max_lt] at this
  assumption

private theorem union_lt {states : States} (h : «from» < states.val.size)
  (ht : to < states.val.size) (hm : states.val[«from»]'h = Unchecked.State.Union alternates)
    : List.maxD 0 (alternates.toList ++ [to]) < states.val.size := by
  have := states.property «from» h
  rw [hm] at this
  simp +zetaDelta [Unchecked.State.nextOf] at this
  exact List.maxD_of_append_lt this ht

private theorem union_reverse_lt {states : States} (h : «from» < states.val.size)
  (ht : to < states.val.size)
  (hm : states.val[«from»]'h = Unchecked.State.UnionReverse alternates)
    : List.maxD 0 (alternates.toList ++ [to]) < states.val.size := by
  have := states.property «from» h
  rw [hm] at this
  simp +zetaDelta [Unchecked.State.nextOf] at this
  exact List.maxD_of_append_lt this ht

/-- Add a transition from one state to another. -/
private def patch («from» «to» : Unchecked.StateID) (states : States)
  (ht : «to» < states.val.size) (h : «from» < states.val.size)
    : CompilerM { states' : States // states.val.size = states'.val.size } := do
  match hm : states.val[«from»]'h with
  | .Empty _ =>
    have hn : (Unchecked.State.Empty «to»).nextOf = «to» := by
      simp +zetaDelta [Unchecked.State.nextOf]
    pure ⟨⟨states.val.set «from» (Unchecked.State.Empty «to») h, all_set h (by simp [hn, ht])⟩,
          by simp_all⟩
  | .NextChar offset _ =>
    pure ⟨⟨states.val.set «from» (Unchecked.State.NextChar offset «to») h, by
            apply all_set; simp +zetaDelta [Unchecked.State.nextOf, ht]⟩,
          by simp_all⟩
  | .Fail =>  Except.error s!"patch states .Fail unexpected"
  | .Eat (.Until s) n =>
      if s = 0
      then pure ⟨⟨states.val.set «from» (Unchecked.State.Eat (.Until «to») n) h, by
                  apply all_set
                  simp +zetaDelta [Unchecked.State.nextOf, ht, Nat.max_lt, eat_until_lt h hm]⟩,
                by simp_all⟩
      else if n = 0
      then pure ⟨⟨states.val.set «from» (Unchecked.State.Eat (.Until s) «to») h, by
                  apply all_set
                  simp +zetaDelta [Unchecked.State.nextOf, ht, Nat.max_lt, eat_until_lt h hm]⟩,
                by simp_all⟩
      else Except.error "patch states, .Eat s and n not null"
  | .Eat (.ToLast s) n =>
      if s = 0
      then pure ⟨⟨states.val.set «from» (Unchecked.State.Eat (.ToLast «to») n) h, by
                  apply all_set
                  simp +zetaDelta [Unchecked.State.nextOf, ht, Nat.max_lt, eat_toLast_lt h hm]⟩,
                by simp_all⟩
      else if n = 0 then
      pure ⟨⟨states.val.set «from» (Unchecked.State.Eat (.ToLast s) «to») h, by
                  apply all_set
                  simp +zetaDelta [Unchecked.State.nextOf, ht, Nat.max_lt, eat_toLast_lt h hm]⟩,
                by simp_all⟩
      else Except.error "patch states, .Eat s and n not null"
  | .ChangeFrameStep f t =>
      if f = 0
      then pure ⟨⟨states.val.set «from» (Unchecked.State.ChangeFrameStep «to» t) h, by
                  apply all_set; simp +zetaDelta [Unchecked.State.nextOf,
                    change_frame_step_lt h hm, Nat.max_lt, ht]⟩,
        by simp_all⟩
      else if t = 0
      then pure ⟨⟨states.val.set «from» (Unchecked.State.ChangeFrameStep f «to»), by
                  apply all_set
                  simp +zetaDelta [Unchecked.State.nextOf, change_frame_step_lt h hm,
                                    Nat.max_lt, ht]⟩,
                by simp_all⟩
      else Except.error "patch states, .ChangeFrameStep from and to not null"
  | .RemoveFrameStep _ =>
    pure ⟨⟨states.val.set «from» (Unchecked.State.RemoveFrameStep «to») h, by
            apply all_set; simp +zetaDelta [Unchecked.State.nextOf, ht]⟩,
          by simp_all⟩
  | .Look look _ =>
    pure ⟨⟨states.val.set «from» (Unchecked.State.Look look «to»), by
            apply all_set; simp +zetaDelta [Unchecked.State.nextOf, ht]⟩,
          by simp_all⟩
  | .BackRef b f _ =>
    pure ⟨⟨states.val.set «from» (Unchecked.State.BackRef b f «to»), by
            apply all_set; simp +zetaDelta [Unchecked.State.nextOf, ht, Nat.zero_lt_of_lt ht]⟩,
          by simp_all⟩
  | .ByteRange t =>
      pure ⟨⟨states.val.set «from» (Unchecked.State.ByteRange {t with «next» := «to»}) h, by
              apply all_set; simp +zetaDelta [Unchecked.State.nextOf, ht]⟩,
            by simp_all⟩
  | .Capture role _ pattern_id group_index slot =>
      pure ⟨⟨states.val.set «from» (Unchecked.State.Capture role «to» pattern_id group_index slot),
              by apply all_set; simp +zetaDelta [Unchecked.State.nextOf, ht, Nat.zero_lt_of_lt ht]⟩,
            by simp_all⟩
  | .BinaryUnion alt1 alt2 =>
      if alt1 = 0
      then pure ⟨⟨states.val.set «from» (Unchecked.State.BinaryUnion «to» alt2) h, by
                  apply all_set; simp +zetaDelta [Unchecked.State.nextOf,
                        binary_union_lt h hm, Nat.max_lt, ht]⟩,
                by simp_all⟩
      else if alt2 = 0
      then pure ⟨⟨states.val.set «from» (Unchecked.State.BinaryUnion alt1 «to») h, by
                  apply all_set; simp +zetaDelta [Unchecked.State.nextOf,
                        binary_union_lt h hm, Nat.max_lt, ht]⟩,
                by simp_all⟩
      else Except.error "patch states, .BinaryUnion alt1 and alt2 not null"
  | .SparseTransitions _ => pure ⟨(states), by simp_all⟩
  | .Union alternates =>
      pure ⟨⟨states.val.set «from» (Unchecked.State.Union (alternates.push «to»)) h, by
              apply all_set; simp +zetaDelta [Unchecked.State.nextOf, union_lt h ht hm]⟩,
            by simp_all⟩
  | .UnionReverse alternates =>
      pure ⟨⟨states.val.set «from» (Unchecked.State.UnionReverse (alternates.push «to»)) h, by
              apply all_set; simp +zetaDelta [Unchecked.State.nextOf, union_reverse_lt h ht hm]⟩,
            by simp_all⟩
  | .Match _ => Except.error s!"patch states .Match unexpected"

private def push (s : Unchecked.State) (states : States)
  (h : NFA.Unchecked.State.nextOf s ≤ states.val.size) : CompilerM (StateIDStates states) := do
  pure ⟨(states.val.size, ⟨states.val.push s, all_push h⟩), by simp_all⟩

private def push' (s : Unchecked.State) (states : States)
  (h : NFA.Unchecked.State.nextOf s ≤ states.val.size) : CompilerM (ThompsonRefStates states) := do
  pure ⟨(⟨states.val.size, states.val.size⟩, ⟨states.val.push s, all_push h⟩),
        by exact And.intro (by simp_all) (by simp_all)⟩

private def add_match (pattern_id : PatternID) (states : States)
    : CompilerM (StateIDStates states) :=
  push (Unchecked.State.Match pattern_id) states (by
    simp +zetaDelta [Unchecked.State.nextOf])

private def add_union (states : States) : CompilerM (StateIDStates states) :=
  push (Unchecked.State.Union #[]) states (by
    simp_all +zetaDelta [Unchecked.State.nextOf, List.maxD_of_empty_eq])

private def add_union_reverse (states : States) : CompilerM (StateIDStates states) :=
  push (Unchecked.State.UnionReverse #[]) states (by
    simp_all +zetaDelta [Unchecked.State.nextOf, List.maxD_of_empty_eq])

private def add_backrefence (case_insensitive : Bool) (b : Nat) (states : States)
    : CompilerM (StateIDStates states) :=
  push (Unchecked.State.BackRef b case_insensitive 0) states (by
    simp_all +zetaDelta [Unchecked.State.nextOf])

private def c_range (start «end» : UInt32) (states : States)
    : CompilerM (ThompsonRefStates states) :=
  let trans: Unchecked.Transition := ⟨start, «end», 0⟩
  push' (Unchecked.State.ByteRange trans) states (by simp_all +zetaDelta [Unchecked.State.nextOf])

private def add_empty (states : States) : CompilerM (StateIDStates states)  :=
  push (Unchecked.State.Empty 0) states (by simp +zetaDelta [Unchecked.State.nextOf])

private def add_fail (states : States) : CompilerM (StateIDStates states) :=
  push (Unchecked.State.Fail) states (by simp +zetaDelta [Unchecked.State.nextOf])

private def add_eat (mode : Unchecked.EatMode) (states : States) (h : mode.nextOf ≤ states.val.size)
    : CompilerM (StateIDStates states) :=
  push (Unchecked.State.Eat mode 0) states (by
    simp +zetaDelta [Unchecked.State.nextOf]
    split <;> try simp_all
    · rename_i s next heq
      simp_all [Nat.max_le]
      rw [← heq.right]
      simp [Unchecked.EatMode.nextOf] at h
      exact And.intro (by assumption) (by exact Nat.zero_le states.val.size)
    · rename_i s next heq
      simp_all [Nat.max_le]
      rw [← heq.right]
      simp [Unchecked.EatMode.nextOf] at h
      exact And.intro (by assumption) (by exact Nat.zero_le states.val.size))

private def add_change_state (states : States) : CompilerM (StateIDStates states) :=
  push (Unchecked.State.ChangeFrameStep 0 0) states (by simp +zetaDelta [Unchecked.State.nextOf])

private def add_remove_state (states : States) : CompilerM (StateIDStates states) :=
  push (Unchecked.State.RemoveFrameStep 0) states (by simp +zetaDelta [Unchecked.State.nextOf])

private def add_next_char (offset : Nat) (states : States) : CompilerM (StateIDStates states) :=
  push (Unchecked.State.NextChar offset 0) states (by simp +zetaDelta [Unchecked.State.nextOf])

private def c_empty (states : States) : CompilerM (ThompsonRefStates states) :=
  push' (Unchecked.State.Empty 0) states (by simp +zetaDelta [Unchecked.State.nextOf])

private def add_sparse (trans : Array Unchecked.Transition) (states : States)
  (h : ∀ (i) (h : i < trans.size), (trans[i]'h).next ≤ states.val.size)
    : CompilerM (StateIDStates states)  :=
  push (Unchecked.State.SparseTransitions trans) states (by
    simp +zetaDelta [Unchecked.State.nextOf]
    have h : ∀ a ∈ trans.toList, a.next ≤ states.val.size := by
      intro a ha
      have ha : a ∈ trans := Array.mem_def.mpr ha
      have ⟨i, ⟨hlt, heq⟩⟩ := Array.mem_iff_getElem.mp ha
      have := h i hlt
      simp_all
    exact List.maxD_of_all_map_le h)

private def c_unicode_class (cls : ClassUnicode) (states : States)
    : CompilerM (ThompsonRefStates states) := do
  let «end» ← add_empty states
  let f : NonemptyInterval Char→Unchecked.Transition := fun r => ⟨r.fst.val, r.snd.val, «end».val.1⟩
  let trans : Array Unchecked.Transition := cls.set.intervals.map f
  let start ← add_sparse trans «end».val.2 (by
    intro i hi
    have := Array.getElem?_map f cls.set.intervals i
    simp_all +zetaDelta
    exact Nat.le_of_succ_le «end».property.left)
  pure (ThompsonRefStates.mk start.val.1 «end».val.1 start.val.2 (by
    have ⟨_, _⟩ := «end».property
    have ⟨_, _⟩ := start.property
    and_intros <;> simp_lte))

private def c_literal (c : Char) (states : States) : CompilerM (ThompsonRefStates states) :=
  c_range c.val c.val states

private def c_look (look : Syntax.Look) (states : States) : CompilerM (ThompsonRefStates states) :=
  match look with
  | .Start => push' (Unchecked.State.Look NFA.Look.Start 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .End => push' (Unchecked.State.Look NFA.Look.End 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .EndWithOptionalLF => push' (Unchecked.State.Look NFA.Look.EndWithOptionalLF 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .StartLF => push' (Unchecked.State.Look NFA.Look.StartLF 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .EndLF => push' (Unchecked.State.Look NFA.Look.EndLF 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .StartCRLF => push' (Unchecked.State.Look NFA.Look.StartCRLF 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .EndCRLF => push' (Unchecked.State.Look NFA.Look.EndCRLF 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .WordUnicode => push' (Unchecked.State.Look NFA.Look.WordUnicode 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .WordUnicodeNegate => push' (Unchecked.State.Look NFA.Look.WordUnicodeNegate 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .WordStartUnicode => push' (Unchecked.State.Look NFA.Look.WordStartUnicode 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .WordEndUnicode => push' (Unchecked.State.Look NFA.Look.WordEndUnicode 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .WordStartHalfUnicode => push' (Unchecked.State.Look NFA.Look.WordStartHalfUnicode 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .WordEndHalfUnicode => push' (Unchecked.State.Look NFA.Look.WordEndHalfUnicode 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .PreviousMatch => push' (Unchecked.State.Look NFA.Look.PreviousMatch 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])
  | .ClearMatches => push' (Unchecked.State.Look NFA.Look.ClearMatches 0) states
      (by simp +zetaDelta [Unchecked.State.nextOf])

private def c_cap' (role : Capture.Role) (pattern_id slot: Nat) (states : States)
    : CompilerM (StateIDStates states)  :=
  push (Unchecked.State.Capture role 0 0 pattern_id slot) states (by simp +zetaDelta [Unchecked.State.nextOf])

mutual

private def c_concat (hirs : Array Hir) (states : States) : CompilerM (ThompsonRefStates states) := do
  match h : hirs.head? with
  | some (head, tail) =>
    have : sizeOf head < sizeOf hirs := Array.sizeOf_head?_of_mem h
    let ⟨(⟨start, «end»⟩, states'), _⟩ ← c head states
    have : sizeOf tail < sizeOf hirs := Array.sizeOf_head?_of_tail h
    let (⟨(hir, states''), _⟩ : (StateIDStates' states states')) ← tail.attach.foldlM
      (init := ⟨(«end», states'), by simp_all⟩)
      (fun ⟨(s, states), _⟩ ⟨hir, h⟩ => do
        have : sizeOf hir < sizeOf tail := Array.sizeOf_lt_of_mem h
        let ⟨(hir, states), _⟩ ← c hir states
        let states ← patch s hir.start states (by simp_lte) (by simp_lte)
        pure ⟨(hir.end, states), by and_intros <;> simp_lte⟩)

    pure (ThompsonRefStates.mk start hir states'' (by and_intros <;> simp_lte))
  | none => c_empty states
termination_by sizeOf hirs

private def c_alt_iter (hirs : Array Hir) (states : States) : CompilerM (ThompsonRefStates states) := do
  match hHead : hirs.head? with
  | some (first, tail) =>
    have : sizeOf tail < sizeOf hirs := Array.sizeOf_head?_of_tail hHead
    match hTail : tail.head? with
    | some (second, tail') =>
      have : sizeOf first < sizeOf hirs := Array.sizeOf_head?_of_mem hHead
      let ⟨(first, states), _⟩ ← c first states
      have : sizeOf second < sizeOf tail := Array.sizeOf_head?_of_mem hTail
      let ⟨(second, states), _⟩ ← c second states
      let ⟨(union, states), _⟩ ← add_union states
      let ⟨(«end», states), _⟩ ← add_empty states

      let states ← patch union first.start states (by simp_lte) (by simp_lte)
      let states ← patch first.end «end» states (by simp_lte) (by simp_lte)
      let states ← patch union second.start states (by simp_lte) (by simp_lte)
      let states ← patch second.end «end» states (by simp_lte) (by simp_lte)

      have : sizeOf tail' < sizeOf tail := Array.sizeOf_head?_of_tail hTail
      let (⟨states', _⟩ : States' states) ← tail'.attach.foldlM (init := ⟨states, by simp_all⟩)
        (fun ⟨states, _⟩ ⟨hir, h⟩  => do
          have : sizeOf hir < sizeOf tail' := Array.sizeOf_lt_of_mem h
          let ⟨(compiled, states), _⟩ ← c hir states
          let states ← patch union compiled.start states (by simp_lte) (by simp_lte)
          let states ← patch compiled.end «end» states (by simp_lte) (by simp_lte)
          pure ⟨states, by simp_lte⟩)

      pure (ThompsonRefStates.mk union «end» states' (by and_intros <;> simp_lte))
    | none => Except.error "c_alt_iter, size > 1 expected"
  | none => Except.error "c_alt_iter, size > 0 expected"
termination_by sizeOf hirs

private def c_exactly (hir : Hir) (n : Nat) (states : States) : CompilerM (ThompsonRefStates states) := do
  if 0 < n then
    let ⟨(⟨start, «end»⟩, states'), _⟩ ← c hir states
    let (⟨(s, states''), _⟩ : (StateIDStates' states states')) ←
      (List.replicate (n-1) 0).foldlM (init := ⟨(«end», states'), by simp_all⟩)
        (fun ⟨(s, states), _⟩ _ => do
          let ⟨(ref, states), _⟩ ← c hir states
          let states ← patch s ref.start states (by simp_all) (by simp_lte)
          pure ⟨(ref.end, states), by and_intros <;> simp_lte⟩)
    pure (ThompsonRefStates.mk start s states'' (by and_intros <;> simp_lte))
  else c_empty states
termination_by sizeOf hir + sizeOf n

/-- embed `start` to `end` states in a possessive union,
    i.e. remove backtracking frames from stack if `end` state is reached
-/
private def c_possessive (tref : ThompsonRef) (states : States)
  (h1 : tref.start < states.val.size) (h2 : tref.end < states.val.size)
    : CompilerM (ThompsonRefStates states) := do
  let  ⟨(union, states), _⟩ ← add_union states
  let  ⟨(fail, states), _⟩ ← add_fail states
  let  ⟨(eat, states), _⟩ ← add_eat (Unchecked.EatMode.ToLast 0) states (by
    simp [Unchecked.EatMode.nextOf])
  let  ⟨(empty, states), _⟩ ← add_empty states

  let states ← patch union tref.start states (by simp_lte) (by simp_lte)
  let states ← patch tref.«end» eat states (by simp_lte) (by simp_lte)
  let states ← patch union fail states (by simp_lte) (by simp_lte)
  let states ← patch eat fail states (by simp_lte) (by simp_lte)
  let states ← patch eat empty states (by simp_lte) (by simp_lte)
  pure (ThompsonRefStates.mk union empty states (by and_intros <;> simp_lte))

private def is_possible_empty_repetition (hir : Hir) : Bool :=
  match hir with
  | ⟨.Repetition ⟨0, _, _, _, _⟩, _⟩ => true
  | _ => false

private def is_empty_concat (hir : Hir) : Bool :=
  match hir with
  | ⟨.Concat #[], _⟩ => true
  | _ => false

/-- collect group if `hir` is a capture group which may match with a empty string,
    it is used to build a greedy search in the Pcre flavor -/
private def get_possible_empty_capture_group (hir : Hir) : Option Nat :=
  let ⟨kind, _⟩ := hir
  match kind with
  | .Capture ⟨g, _, ⟨kind, _⟩⟩ =>
    match kind with
    | .Repetition ⟨0, _, _, _, _⟩ => some g
    | .Concat hirs => if hirs.all is_possible_empty_repetition then some g else none
    | .Alternation hirs => if (hirs.any is_empty_concat) || (hirs.any is_possible_empty_repetition)
                           then some g else none
    | _ => none
  | _ => none

/-- Compile the given expression such that it may be matched `n` or more times -/
private def c_at_least (hir : Hir) (n : Nat) (greedy : Bool) (possessive : Bool) (states : States)
    : CompilerM (ThompsonRefStates states) := do
  if n = 0 then
    /- compile x* as (x+)?, which preserves the correct preference order
        if x can match the empty string. -/
    let ⟨(compiled, states), _⟩ ← c hir states
    let ⟨(plus, states), _⟩ ← (if greedy then add_union states else add_union_reverse states)

    let states ← patch compiled.end plus states (by simp_lte) (by simp_lte)
    let states ← patch plus compiled.start states (by simp_lte) (by simp_lte)

    let groups ← get
    let groups := match (if greedy then get_possible_empty_capture_group hir else none) with
              | some g => groups.push g
              | none => groups
    set groups

    let  ⟨(question, states), _⟩ ← (if greedy then add_union states else add_union_reverse states)
    let  ⟨(empty, states), _⟩ ← add_empty states
    let states ← patch question compiled.start states (by simp_lte) (by simp_lte)
    let states ← patch question empty states (by simp_lte) (by simp_lte)
    let states ← patch plus empty states (by simp_lte) (by simp_lte)

    if possessive then
      let t ← c_possessive ⟨question, empty⟩ states (by simp_lte) (by simp_lte)
      pure (ThompsonRefStates.castLt t (by have ⟨_, _, _⟩ := t.property; simp_lte))
    else
      pure (ThompsonRefStates.mk question empty states (by and_intros <;> simp_lte))
  else if n = 1 then
    let ⟨(compiled, states), _⟩ ← c hir states
    let ⟨(union, states), _⟩ ← (if greedy then add_union states else add_union_reverse states)

    let groups ← get
    let groups := match (if greedy then get_possible_empty_capture_group hir else none) with
              | some g => groups.push g
              | none => groups
    set groups

    let states ← patch compiled.end union states (by simp_lte) (by simp_lte)
    let states ← patch union compiled.start states (by simp_lte) (by simp_lte)

    if possessive then
      let t ← c_possessive ⟨compiled.start, union⟩ states (by simp_lte) (by simp_lte)
      pure (ThompsonRefStates.castLt t (by have ⟨_, _, _⟩ := t.property; simp_lte))
    else
      pure (ThompsonRefStates.mk compiled.start union states (by and_intros <;> simp_lte))
  else
    let ⟨(«prefix», states), _⟩ ← c_exactly hir (n-1) states
    let ⟨(last, states), _⟩ ← c hir states
    let ⟨(union, states), _⟩ ← (if greedy then add_union states else add_union_reverse states)

    let states ← patch «prefix».end last.start states (by simp_lte) (by simp_lte)
    let states ← patch last.end union states (by simp_lte) (by simp_lte)
    let states ← patch union last.start states (by simp_lte) (by simp_lte)

    if possessive then
      let t ← c_possessive  ⟨«prefix».start, union⟩ states (by simp_lte) (by simp_lte)
      pure (ThompsonRefStates.castLt t (by have ⟨_, _, _⟩ := t.property; simp_lte))
    else
      pure (ThompsonRefStates.mk «prefix».start union states (by and_intros <;> simp_lte))
termination_by sizeOf hir + sizeOf n + 1

/-- Compile the given expression such that it matches at least `min` times,
    but no more than `max` times.-/
private def c_bounded (hir : Hir) (min max : Nat) (greedy : Bool) (possessive : Bool)
  (states : States) : CompilerM (ThompsonRefStates states) := do
  if 0 < max then
    let ⟨(«prefix», states), _⟩  ← c_exactly hir min states
    if min = max then
      if possessive then
        let t ← c_possessive «prefix» states (by simp_lte) (by simp_lte)
        pure (ThompsonRefStates.castLt t (by have ⟨_, _, _⟩ := t.property; simp_lte))
      else
        pure (ThompsonRefStates.mk «prefix».start «prefix».end states (by and_intros <;> simp_lte))
    else
      let ⟨(empty, states'), _⟩ ← add_empty states

      let (⟨(prev_end, states''), _⟩ : (StateIDStates' states states')) ←
        (List.replicate (max-min) 0).foldlM (init := ⟨(«prefix».end, states'),
                                                       by and_intros <;> simp_lte⟩)
          (fun ⟨(prev_end, states), _⟩ _ => do
            let ⟨(compiled, states), _⟩ ← c hir states
            let ⟨(union, states), _⟩ ←
              (if greedy then add_union states else add_union_reverse states)

            let states ← patch prev_end union states (by simp_lte) (by simp_lte)
            let states ← patch union compiled.start states (by simp_lte) (by simp_lte)

            if possessive then
              let ⟨(union, states), _⟩ ← add_union states
              let ⟨(fail, states), _⟩ ← add_fail states
              let ⟨(eat, states), _⟩ ← add_eat (Unchecked.EatMode.ToLast 0) states
                (by simp [Unchecked.EatMode.nextOf])

              let states ← patch union fail states (by simp_lte) (by simp_lte)
              let states ← patch eat fail states (by simp_lte) (by simp_lte)
              let states ← patch eat empty states (by simp_lte) (by simp_lte)

              pure ⟨(compiled.end, states), by and_intros <;> simp_lte⟩
            else
              let states ← patch union empty states (by simp_lte) (by simp_lte)
              pure ⟨(compiled.end, states), by and_intros <;> simp_lte⟩)
      let ⟨states'', _⟩ ← patch prev_end empty states'' (by simp_lte) (by simp_lte)
      pure (ThompsonRefStates.mk «prefix».start empty states'' (by and_intros <;> simp_lte))
  else c_empty states
termination_by sizeOf hir + sizeOf min + sizeOf max

private def c_back_ref (case_insensitive : Bool) (n : Nat) (states : States)
    : CompilerM (ThompsonRefStates states) := do
  let ⟨(backrefence, states), _⟩ ← add_backrefence case_insensitive n states
  let ⟨(empty, states), _⟩ ← add_empty states
  let states ← patch backrefence empty states (by simp_lte) (by simp_lte)
  pure (ThompsonRefStates.mk backrefence empty states (by and_intros <;> simp_lte))

private def c_lookaround (look : Lookaround) (states : States)
    : CompilerM (ThompsonRefStates states) := do
  match look with
  | .PositiveLookahead h =>
    let ⟨(compiled, states), _⟩ ← c h states
    let ⟨(change_state, states), _⟩ ← add_change_state states
    let ⟨(fail, states), _⟩ ← add_fail states
    let ⟨(union, states), _⟩ ← add_union states
    let ⟨(«end», states), _⟩ ← add_empty states

    let states ← patch compiled.end change_state states (by simp_lte) (by simp_lte)
    let states ← patch union compiled.start states (by simp_lte) (by simp_lte)
    let states ← patch change_state fail states (by simp_lte) (by simp_lte)
    let states ← patch change_state «end» states (by simp_lte) (by simp_lte)
    let states ← patch union fail states (by simp_lte) (by simp_lte)

    pure (ThompsonRefStates.mk union «end» states (by and_intros <;> simp_lte))
  | .NegativeLookahead h =>
    let ⟨(compiled, states), _⟩ ← c h states
    let ⟨(remove_state, states), _⟩ ← add_remove_state states
    let ⟨(empty, states), _⟩ ← add_empty states
    let ⟨(union, states), _⟩ ← add_union states
    let ⟨(«end», states), _⟩ ← add_empty states

    let states ← patch compiled.end remove_state states (by simp_lte) (by simp_lte)
    let states ← patch remove_state empty states (by simp_lte) (by simp_lte)
    let states ← patch union compiled.start states (by simp_lte) (by simp_lte)
    let states ← patch empty «end» states (by simp_lte) (by simp_lte)
    let states ← patch union empty states (by simp_lte) (by simp_lte)

    pure (ThompsonRefStates.mk union «end» states (by and_intros <;> simp_lte))
  | .PositiveLookbehind length h =>
    let ⟨(next_char, states), _⟩ ← add_next_char length states
    let ⟨(compiled, states), _⟩ ← c h states
    let ⟨(«end», states), _⟩ ← add_empty states

    let states ← patch next_char compiled.start states (by simp_lte) (by simp_lte)
    let states ← patch compiled.end «end» states (by simp_lte) (by simp_lte)

    pure (ThompsonRefStates.mk  next_char «end» states (by and_intros <;> simp_lte))
  | .NegativeLookbehind length h =>
    let ⟨(next_char, states), _⟩ ← add_next_char length states
    let ⟨(compiled, states), _⟩ ← c h states
    let ⟨(remove_state, states), _⟩ ← add_remove_state states
    let ⟨(empty, states), _⟩ ← add_empty states
    let ⟨(union, states), _⟩ ← add_union states
    let ⟨(«end», states), _⟩ ← add_empty states

    let states ← patch next_char compiled.start states (by simp_lte) (by simp_lte)
    let states ← patch compiled.end remove_state states (by simp_lte) (by simp_lte)
    let states ← patch remove_state empty states (by simp_lte) (by simp_lte)
    let states ← patch union next_char states (by simp_lte) (by simp_lte)
    let states ← patch empty «end» states (by simp_lte) (by simp_lte)
    let states ← patch union empty states (by simp_lte) (by simp_lte)

    pure (ThompsonRefStates.mk union «end» states (by and_intros <;> simp_lte))
termination_by sizeOf look

private def c_repetition (rep : Repetition) (_states : States)
    : CompilerM (ThompsonRefStates _states) := do
  match rep with
  | .mk 0 (some 1) greedy false h => do
      let ⟨(union, states), _⟩ ← if greedy then add_union _states else add_union_reverse _states
      let ⟨(compiled, states), _⟩ ← c h states
      let ⟨(empty, states), _⟩ ← add_empty states
      let states ← patch union compiled.start states (by simp_lte) (by simp_lte)
      let states ← patch union empty states (by simp_lte) (by simp_lte)
      let states ← patch compiled.end empty states (by simp_lte) (by simp_lte)
      pure (ThompsonRefStates.mk union empty states (by and_intros <;> simp_lte))
  | .mk 0 (some 1) _ true h => do
      let ⟨(union, states), _⟩ ← add_union _states
      let ⟨(compiled, states), _⟩ ← c h states
      let ⟨(eat, states), _⟩ ← add_eat (Unchecked.EatMode.Until 0) states
        (by simp [Unchecked.EatMode.nextOf])
      let ⟨(empty, states), _⟩ ← add_empty states
      let states ← patch union compiled.start states (by simp_lte) (by simp_lte)
      let states ← patch union empty states (by simp_lte) (by simp_lte)
      let states ← patch compiled.end eat states (by simp_lte) (by simp_lte)
      let states ← patch eat empty states (by simp_lte) (by simp_lte)
      let states ← patch eat empty states (by simp_lte) (by simp_lte)
      pure (ThompsonRefStates.mk union empty states (by and_intros <;> simp_lte))
  | .mk min none greedy possessive sub => do
      let cannotMatchEmptyString : Bool :=
        match sub.properties.minimum_len with
        | some n => n > 0
        | none => false
      if min = 0 && cannotMatchEmptyString
      then
        let ⟨(union, states), _⟩ ← if greedy then add_union _states else add_union_reverse _states
        let ⟨(compiled, states), _⟩ ← c sub  states
        let states ← patch union compiled.start states (by simp_lte) (by simp_lte)
        let states ← patch compiled.end union states (by simp_lte) (by simp_lte)
        pure (ThompsonRefStates.mk union union states (by and_intros <;> simp_lte))
      else c_at_least sub min greedy possessive _states
  | .mk min (some max) greedy possessive sub =>
      if min ≤ max then c_bounded sub min max greedy possessive _states else c_empty _states
termination_by sizeOf rep

private def c_cap (hir : Capture) (states : States) : CompilerM (ThompsonRefStates states) := do
  match hir with
    | .mk pattern_id _ sub =>
      let ⟨(start, states), _⟩ ← c_cap' Capture.Role.Start pattern_id (pattern_id * 2) states
      let ⟨(«inner», states), _⟩ ← c sub states
      let ⟨(«end», states), _⟩ ← c_cap' Capture.Role.End pattern_id (pattern_id * 2 + 1) states
      let states ← patch start inner.start states (by simp_lte) (by simp_lte)
      let states ← patch inner.end «end» states (by simp_lte) (by simp_lte)
      pure (ThompsonRefStates.mk start «end» states (by and_intros <;> simp_lte))
termination_by sizeOf hir

private def c (hir : Hir) (_states : States) : CompilerM (ThompsonRefStates _states) :=
  have : sizeOf hir.kind < sizeOf hir := Hir.sizeOfKindOfHir hir
  match h : hir.kind with
  | .Empty => c_empty _states
  | .Literal c => c_literal c _states
  | .Class (.Unicode cls) => c_unicode_class cls _states
  | .Look look => c_look look _states
  | .Lookaround look =>
    have : sizeOf look < sizeOf hir.kind := by simp [h]
    c_lookaround look _states
  | .BackRef f n => c_back_ref f n _states
  | .Repetition rep =>
    have : sizeOf rep < sizeOf hir.kind := by simp [h]
    c_repetition rep _states
  | .Capture cap =>
    have : sizeOf cap < sizeOf hir.kind := by simp [h]
    c_cap cap _states
  | .Concat items =>
    have : sizeOf items < sizeOf hir.kind := by simp [h]
    c_concat items _states
  | .Alternation sub =>
    have : sizeOf sub < sizeOf hir.kind := by simp [h]
    c_alt_iter sub _states
termination_by sizeOf hir

end

private def startsWithStart (hir : Hir) : Bool :=
  match hir.kind with
  | .Concat hirs =>
    match hirs.head? with
    | some (⟨HirKind.Look Syntax.Look.Start, _⟩  , _) => true
    | _ => false
  | _ => false

/-- Compile the HIR expression given. -/
private def compile' (anchored : Bool) (expr : Hir) : CompilerM States := do
  let states : States := ⟨#[], by simp_all⟩
  let ⟨(unanchored_prefix, states), _⟩ ←
    if anchored then c_empty states
    else c_repetition (Repetition.mk 0 none false false (dot Dot.AnyChar)) states
  let ⟨(one, states), _⟩ ← c_cap (Capture.mk 0 none expr) states
  let ⟨(match_state_id, states), _⟩ ← add_match 0 states
  let states ← patch one.end match_state_id states (by simp_lte) (by simp_lte)
  patch unanchored_prefix.end one.start states (by simp_lte) (by simp_lte)

/-- Compile the HIR expression given. -/
def compile (config : Config := default) (flavor : Syntax.Flavor) (expr : Hir)
    : Except String Checked.NFA := do
  let unanchored_prefix_simulation := expr.containsLookaround || config.unanchored_prefix_simulation
  let anchored := !config.unanchored_prefix || startsWithStart expr || unanchored_prefix_simulation
  let (states, groups) ← compile' anchored expr #[]
  let nfa ← NFA.toCkecked ⟨states.val, Unchecked.toSlots states, 0, 0⟩
              (match flavor with | Syntax.Flavor.Pcre => groups | _ => #[])
              states.property
  Except.ok {nfa with unanchored_prefix_in_backtrack :=
                  !startsWithStart expr && unanchored_prefix_simulation
            }
