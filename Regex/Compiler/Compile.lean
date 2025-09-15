import Init.Meta
import Batteries.Data.Array.Basic
import Batteries.Lean.Except

import Std.Tactic.Do
import Std.Tactic.Do.Syntax

import Regex.Syntax.Hir
import Regex.Nfa
import Regex.Data.Nat.Basic
import Regex.Compiler.Basic
import Regex.Compiler.Patch

namespace Compiler

open Syntax
open NFA

namespace Code

instance : MonadLiftT (StateT σ Id) (EStateM ε σ) where
  monadLift := EStateM.modifyGet

instance : MonadLiftT (StateT σ₁ Id) (EStateM ε (σ₁ × σ₂)) where
  monadLift x := fun s =>
    let x := (x.run s.1).run
    EStateM.Result.ok x.1 (x.2, s.2)

instance : MonadLiftT (EStateM ε σ₁) (EStateM ε (σ₁ × σ₂)) where
  monadLift x := fun s =>
    match (x.run s.1) with
    | EStateM.Result.ok x s' => EStateM.Result.ok x (s', s.2)
    | EStateM.Result.error e s' => EStateM.Result.error e (s', s.2)

/--
  The state consists of a pair of arrays of states and of capture groups
  with property `get_possible_empty_capture_group`.
-/
abbrev CompilerM α := EStateM String (Array Unchecked.State × Array Nat) α

abbrev StackM α := StateT (Array Unchecked.State) Id α

def push (s : Unchecked.State) : StackM Unchecked.StateID := do
  let states ← get
  set (states.push s)
  pure states.size

def push' (s : Unchecked.State) : StackM ThompsonRef := do
  let states ← get
  set (states.push s)
  pure ⟨states.size, states.size⟩

def add_match (pattern_id : PatternID) : StackM Unchecked.StateID :=
  push (Unchecked.State.Match pattern_id)

def add_union : StackM Unchecked.StateID :=
  push (Unchecked.State.Union #[])

def add_union_reverse : StackM Unchecked.StateID :=
  push (Unchecked.State.UnionReverse #[])

def add_backrefence (case_insensitive : Bool) (b : Nat) : StackM Unchecked.StateID :=
  push (Unchecked.State.BackRef b case_insensitive 0)

def c_range (start «end» : UInt32) : StackM ThompsonRef :=
  let trans: Unchecked.Transition := ⟨start, «end», 0⟩
  push' (Unchecked.State.ByteRange trans)

def add_empty : StackM Unchecked.StateID :=
  push (Unchecked.State.Empty 0)

def add_fail : StackM Unchecked.StateID :=
  push (Unchecked.State.Fail)

def add_eat (mode : Unchecked.EatMode) : StackM Unchecked.StateID :=
  push (Unchecked.State.Eat mode 0)

def add_change_state : StackM Unchecked.StateID :=
  push (Unchecked.State.ChangeFrameStep 0 0)

def add_remove_state : StackM Unchecked.StateID :=
  push (Unchecked.State.RemoveFrameStep 0)

def add_next_char (offset : Nat) : StackM Unchecked.StateID :=
  push (Unchecked.State.NextChar offset 0)

def c_empty : StackM  ThompsonRef :=
  push' (Unchecked.State.Empty 0)

def add_sparse (trans : Array Unchecked.Transition) : StackM Unchecked.StateID :=
  push (Unchecked.State.SparseTransitions trans)

def c_unicode_class (cls : ClassUnicode) : StackM ThompsonRef := do
  let «end» ← add_empty
  let trans := cls.set.intervals.map (fun r => ⟨r.fst.val, r.snd.val, «end»⟩)
  let start ← add_sparse trans
  pure (ThompsonRef.mk start «end»)

def c_literal (c : Char) : StackM ThompsonRef :=
  c_range c.val c.val

def c_look (look : Syntax.Look) : StackM ThompsonRef :=
  match look with
  | .Start => push' (Unchecked.State.Look NFA.Look.Start 0)
  | .End => push' (Unchecked.State.Look NFA.Look.End 0)
  | .EndWithOptionalLF => push' (Unchecked.State.Look NFA.Look.EndWithOptionalLF 0)
  | .StartLF => push' (Unchecked.State.Look NFA.Look.StartLF 0)
  | .EndLF => push' (Unchecked.State.Look NFA.Look.EndLF 0)
  | .StartCRLF => push' (Unchecked.State.Look NFA.Look.StartCRLF 0)
  | .EndCRLF => push' (Unchecked.State.Look NFA.Look.EndCRLF 0)
  | .WordUnicode => push' (Unchecked.State.Look NFA.Look.WordUnicode 0)
  | .WordUnicodeNegate => push' (Unchecked.State.Look NFA.Look.WordUnicodeNegate 0)
  | .WordStartUnicode => push' (Unchecked.State.Look NFA.Look.WordStartUnicode 0)
  | .WordEndUnicode => push' (Unchecked.State.Look NFA.Look.WordEndUnicode 0)
  | .WordStartHalfUnicode => push' (Unchecked.State.Look NFA.Look.WordStartHalfUnicode 0)
  | .WordEndHalfUnicode => push' (Unchecked.State.Look NFA.Look.WordEndHalfUnicode 0)
  | .PreviousMatch => push' (Unchecked.State.Look NFA.Look.PreviousMatch 0)
  | .ClearMatches => push' (Unchecked.State.Look NFA.Look.ClearMatches 0)

def c_cap' (role : Capture.Role) (group slot: Nat) : StackM Unchecked.StateID :=
  push (Unchecked.State.Capture role 0 0 group slot)

/-- embed `start` to `end` in a possessive union,
    i.e. remove backtracking frames from stack if `end` state is reached
-/
def c_possessive (tref : ThompsonRef) : PatchM ThompsonRef := do
  let  union ← add_union
  let  fail ← add_fail
  let  eat ← add_eat (Unchecked.EatMode.ToLast 0)
  let  empty ← add_empty

  Code.patch union tref.start
  Code.patch tref.«end» eat
  Code.patch union fail
  Code.patch eat fail
  Code.patch eat empty
  pure (ThompsonRef.mk union empty)

def is_possible_empty_repetition (hir : Hir) : Bool :=
  match hir with
  | ⟨.Repetition ⟨0, _, _, _, _⟩, _⟩ => true
  | _ => false

def is_empty_concat (hir : Hir) : Bool :=
  match hir with
  | ⟨.Concat #[], _⟩ => true
  | _ => false

/-- collect group if `hir` is a capture group which may match with a empty string,
    it is used to build a greedy search in the Pcre flavor -/
def get_possible_empty_capture_group (hir : Hir) : Option Nat :=
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

def c_back_ref (case_insensitive : Bool) (n : Nat) : PatchM  ThompsonRef := do
  let backrefence ← add_backrefence case_insensitive n
  let empty ← add_empty
  Code.patch backrefence empty
  pure (ThompsonRef.mk backrefence empty)

def head (hirs : Array Hir) (h : 0 < hirs.size)
    : { pair : Hir × Array Hir // pair.1 ∈ hirs ∧ pair.2.size < hirs.size
                                  ∧ sizeOf pair.2 < sizeOf hirs } :=
  let l := hirs.toList
  have : 0 < l.length := by grind
  match hm : l with | head :: tail => ⟨(head, tail.toArray), by
    simp
    have : sizeOf tail < sizeOf l := by simp_all; grind
    have : sizeOf hirs = 1 + sizeOf hirs.toList := rfl
    have : head ∈ l := by simp [*]
    and_intros <;> grind⟩

theorem head_mem_lt {hirs : Array Hir} {h : 0 < hirs.size}
  (x : { hir // hir ∈ (Code.head hirs h).val.snd })
    : sizeOf x.val < sizeOf hirs := by
  have hp := x.property
  have : sizeOf x.val < sizeOf (head hirs h).val.snd := Array.sizeOf_lt_of_mem hp
  have : sizeOf (head hirs h).val.snd < sizeOf hirs := by
    simp [head]
    split
    have : sizeOf hirs = 1 + sizeOf hirs.toList := rfl
    simp +arith [*]
  grind

theorem head_apply_lt (hirs : Array Hir) (h : 0 < hirs.size)
    : sizeOf (head hirs h).val.fst < sizeOf hirs := by
  simp [head]
  split
  have : sizeOf hirs = 1 + sizeOf hirs.toList := rfl
  simp +arith [*]

def cannotMatchEmptyString (hir : Hir) : Bool :=
  match hir.properties.minimum_len with
  | some n => n > 0
  | none => false

def c_lookaround_PositiveLookahead (compiled : ThompsonRef) : PatchM ThompsonRef := do
  let change_state ← add_change_state
  let fail ← add_fail
  let union ← add_union
  let «end» ← add_empty

  Code.patch compiled.end change_state
  Code.patch union compiled.start
  Code.patch change_state fail
  Code.patch change_state «end»
  Code.patch union fail

  pure (ThompsonRef.mk union «end»)

def c_lookaround_NegativeLookahead (compiled : ThompsonRef) : PatchM ThompsonRef := do
  let remove_state ← add_remove_state
  let empty ← add_empty
  let union ← add_union
  let «end» ← add_empty

  Code.patch compiled.end remove_state
  Code.patch remove_state empty
  Code.patch union compiled.start
  Code.patch empty «end»
  Code.patch union empty

  pure (ThompsonRef.mk union «end»)

def c_lookaround_PositiveLookbehind (next_char : Unchecked.StateID) (compiled : ThompsonRef)
    : PatchM ThompsonRef := do
  let «end» ← add_empty

  Code.patch next_char compiled.start
  Code.patch compiled.end «end»

  pure (ThompsonRef.mk  next_char «end»)

def c_lookaround_NegativeLookbehind (next_char : Unchecked.StateID) (compiled : ThompsonRef)
    : PatchM ThompsonRef := do
    let remove_state ← add_remove_state
    let empty ← add_empty
    let union ← add_union
    let «end» ← add_empty

    Code.patch next_char compiled.start
    Code.patch compiled.end remove_state
    Code.patch remove_state empty
    Code.patch union next_char
    Code.patch empty «end»
    Code.patch union empty

    pure (ThompsonRef.mk union «end»)

def c_repetition_0_some_1_false (union : Unchecked.StateID) (compiled : ThompsonRef)
    : PatchM ThompsonRef := do
  let empty ← add_empty
  Code.patch union compiled.start
  Code.patch union empty
  Code.patch compiled.end empty
  pure (ThompsonRef.mk union empty)

def c_repetition_0_some_1_true (union : Unchecked.StateID) (compiled : ThompsonRef)
    : PatchM ThompsonRef := do
  let eat ← add_eat (Unchecked.EatMode.Until 0)
  let empty ← add_empty
  Code.patch union compiled.start
  Code.patch union empty
  Code.patch compiled.end eat
  Code.patch eat empty
  Code.patch eat empty
  pure (ThompsonRef.mk union empty)

def c_repetition_0_none (union : Unchecked.StateID) (compiled : ThompsonRef)
    : PatchM ThompsonRef := do
  Code.patch union compiled.start
  Code.patch compiled.end union
  pure (ThompsonRef.mk union union)

def c_at_least_0_pre (compiled : ThompsonRef) (greedy : Bool) : PatchM Unchecked.StateID := do
  let plus ← (if greedy then add_union else add_union_reverse)
  Code.patch compiled.end plus
  Code.patch plus compiled.start
  pure plus

def c_at_least_0_post (compiled : ThompsonRef) (plus : Unchecked.StateID) (greedy : Bool)
  (possessive : Bool) : PatchM ThompsonRef := do
  let question ← (if greedy then add_union else add_union_reverse)
  let empty ← add_empty
  Code.patch question compiled.start
  Code.patch question empty
  Code.patch plus empty

  if possessive then c_possessive ⟨question, empty⟩
  else pure (ThompsonRef.mk question empty)

def c_at_least_set (possible_empty_capture_group : Option Nat) (greedy : Bool) : CompilerM Unit := do
  let (states, groups) ← get
  set (states,
        (match (if greedy then possible_empty_capture_group else none) with
         | some g => groups.push g
         | none => groups))

def c_at_least_0 (compiled : ThompsonRef) (possible_empty_capture_group : Option Nat) (greedy : Bool)
    : CompilerM Unchecked.StateID := do
  let plus ← c_at_least_0_pre compiled greedy
  c_at_least_set possible_empty_capture_group greedy
  pure plus

def c_at_least_1_pre (greedy : Bool) : PatchM Unchecked.StateID := do
  if greedy then add_union else add_union_reverse

def c_at_least_1_post (compiled : ThompsonRef) (union : Unchecked.StateID)
  (possessive : Bool) : PatchM ThompsonRef := do
  Code.patch compiled.end union
  Code.patch union compiled.start

  if possessive then c_possessive ⟨compiled.start, union⟩
  else pure (ThompsonRef.mk compiled.start union)

def c_at_least_1 (possible_empty_capture_group : Option Nat) (greedy : Bool)
    : CompilerM Unchecked.StateID := do
  let union ← c_at_least_1_pre greedy
  c_at_least_set possible_empty_capture_group greedy
  pure union

def c_at_least_2 («prefix» last : ThompsonRef) (greedy : Bool) (possessive : Bool)
      : PatchM ThompsonRef := do
  let union ← (if greedy then add_union else add_union_reverse)

  Code.patch «prefix».end last.start
  Code.patch last.end union
  Code.patch union last.start

  if possessive then c_possessive  ⟨«prefix».start, union⟩
  else pure (ThompsonRef.mk «prefix».start union)

def c_bounded.fold.patch.pre (compiled: ThompsonRef) (prev_end : Unchecked.StateID)
  (greedy : Bool)
    : PatchM Unchecked.StateID := do
  let union ← (if greedy then add_union else add_union_reverse)
  Code.patch prev_end union
  Code.patch union compiled.start
  pure union

def c_bounded.fold.patch.possessive (compiled: ThompsonRef) (empty : Unchecked.StateID)
    : PatchM Unchecked.StateID := do
  let union ← add_union
  let fail ← add_fail
  let eat ← add_eat (Unchecked.EatMode.ToLast 0)

  Code.patch union fail
  Code.patch eat fail
  Code.patch eat empty

  pure compiled.end

def c_bounded.fold.patch.post (compiled: ThompsonRef) (union empty : Unchecked.StateID)
    : PatchM Unchecked.StateID := do
  Code.patch union empty
  pure compiled.end

def c_bounded.fold.patch (compiled: ThompsonRef) (prev_end empty : Unchecked.StateID)
  (greedy : Bool) (possessive : Bool)
    : PatchM Unchecked.StateID := do
  let union ← c_bounded.fold.patch.pre compiled prev_end greedy
  if possessive
  then c_bounded.fold.patch.possessive compiled empty
  else c_bounded.fold.patch.post compiled union empty

def c_alt_iter_step (first second : ThompsonRef)
    : PatchM (Unchecked.StateID × Unchecked.StateID) := do
  let union ← add_union
  let «end» ← add_empty

  Code.patch union first.start
  Code.patch first.end «end»
  Code.patch union second.start
  Code.patch second.end «end»

  pure (union, «end»)

def c_rep_pre (greedy : Bool) : PatchM Unchecked.StateID := do
  if greedy then add_union else add_union_reverse

mutual

def c_concat.fold (hirs : Array Hir) (s : Unchecked.StateID) : CompilerM Unchecked.StateID := do
  let go (pair : Unchecked.StateID) (hirM : { hir : Hir // hir ∈ hirs }) := do
    have := Array.sizeOf_lt_of_mem hirM.property
    let hir ← c hirM.val
    Code.patch pair hir.start
    pure hir.end
  hirs.attach.foldlM go s
termination_by sizeOf hirs

def c_concat (hirs : Array Hir) : CompilerM ThompsonRef := do
  match h : hirs.head? with
  | some (head, tail) =>
    have : sizeOf head < sizeOf hirs := Array.sizeOf_head?_of_mem h
    let ⟨start, «end»⟩ ← c head
    have : sizeOf tail < sizeOf hirs := Array.sizeOf_head?_of_tail h
    let hir ← c_concat.fold tail «end»
    pure (ThompsonRef.mk start hir)
  | none => c_empty
termination_by sizeOf hirs

def c_alt_iter.fold (hirs : Array Hir) (union «end» : Unchecked.StateID)
    : CompilerM Unit := do
  hirs.attach.foldlM (init := ())
    (fun s ⟨hir, h⟩  => do
      have : sizeOf hir < sizeOf hirs := Array.sizeOf_lt_of_mem h
      let compiled ← c hir
      Code.patch union compiled.start
      Code.patch compiled.end «end»
      pure s)
termination_by sizeOf hirs

def c_alt_iter (hirs : Array Hir) : CompilerM ThompsonRef := do
  match hHead : hirs.head? with
  | some (first, tail) =>
    have : sizeOf tail < sizeOf hirs := Array.sizeOf_head?_of_tail hHead
    match hTail : tail.head? with
    | some (second, tail') =>
      have : sizeOf first < sizeOf hirs := Array.sizeOf_head?_of_mem hHead
      let first ← c first
      have : sizeOf second < sizeOf tail := Array.sizeOf_head?_of_mem hTail
      let second ← c second
      let (union, «end») ← c_alt_iter_step first second
      have : sizeOf tail' < sizeOf tail := Array.sizeOf_head?_of_tail hTail
      c_alt_iter.fold tail' union «end»
      pure (ThompsonRef.mk union «end»)
    | none => .error "c_alt_iter, size > 1 expected"
  | none => .error "c_alt_iter, size > 0 expected"
termination_by sizeOf hirs

def c_exactly.fold (hir : Hir) (n : Nat) («end» : Unchecked.StateID)
    : CompilerM Unchecked.StateID := do
  if 0 < n then
    (List.replicate n 0).foldlM (init := («end»))
      (fun s _ => do
        let ref ← c hir
        Code.patch s ref.start
        pure ref.end)
  else pure («end»)
termination_by sizeOf hir + sizeOf n

def c_exactly (hir : Hir) (n : Nat) : CompilerM ThompsonRef := do
  if 0 < n then
    let ⟨start, «end»⟩ ← c hir
    let s ← c_exactly.fold hir (n-1) «end»
    pure (ThompsonRef.mk start s)
  else c_empty
termination_by sizeOf hir + sizeOf n

/-- Compile the given expression such that it may be matched `n` or more times -/
def c_at_least (hir : Hir) (n : Nat) (greedy : Bool) (possessive : Bool)
    : CompilerM ThompsonRef := do
  let possible_empty_capture_group := get_possible_empty_capture_group hir
  if n = 0 then
    /- compile x* as (x+)?, which preserves the correct preference order if x can match the empty string. -/
    let compiled ← c hir
    let plus ← c_at_least_0 compiled possible_empty_capture_group greedy
    c_at_least_0_post compiled plus greedy possessive
  else if n = 1 then
    let compiled ← c hir
    let union ← c_at_least_1 possible_empty_capture_group greedy
    c_at_least_1_post compiled union possessive
  else
    let «prefix» ← c_exactly hir (n-1)
    let last ← c hir
    c_at_least_2 «prefix» last greedy possessive
termination_by sizeOf hir + sizeOf n + 1

def c_bounded.fold (hir : Hir) (n : Nat) («prefix» : ThompsonRef) (empty : Unchecked.StateID)
  (greedy : Bool) (possessive : Bool)
    : CompilerM Unchecked.StateID := do
  if 0 < n then
    (List.replicate n 0).foldlM (init := «prefix».end)
      (fun prev_end _ => do
        let compiled ← c hir
        c_bounded.fold.patch compiled prev_end empty greedy possessive)
  else pure «prefix».end
termination_by sizeOf hir + sizeOf n

/-- Compile the given expression such that it matches at least `min` times,
    but no more than `max` times.-/
def c_bounded (hir : Hir) (min max : Nat) (greedy : Bool) (possessive : Bool)
    : CompilerM ThompsonRef := do
  if 0 < max then
    let «prefix»  ← c_exactly hir min
    if min = max then
      if possessive then c_possessive «prefix»
      else pure (ThompsonRef.mk «prefix».start «prefix».end)
    else
      let empty ← add_empty
      let prev_end ← c_bounded.fold hir (max-min) «prefix» empty greedy possessive
      Code.patch prev_end empty
      pure (ThompsonRef.mk «prefix».start empty)
  else c_empty
termination_by sizeOf hir + sizeOf min + sizeOf (max - min) + 1

def c_lookaround (look : Lookaround) : CompilerM ThompsonRef := do
  match look with
  | .PositiveLookahead h =>
    let compiled ← c h
    c_lookaround_PositiveLookahead compiled
  | .NegativeLookahead h =>
    let compiled ← c h
    c_lookaround_NegativeLookahead compiled
  | .PositiveLookbehind length h =>
    let next_char ← add_next_char length
    let compiled ← c h
    c_lookaround_PositiveLookbehind next_char compiled
  | .NegativeLookbehind length h =>
    let next_char ← add_next_char length
    let compiled ← c h
    c_lookaround_NegativeLookbehind next_char compiled
termination_by sizeOf look

def c_repetition (rep : Repetition) : CompilerM ThompsonRef := do
  match rep with
  | .mk 0 (some 1) greedy false h => do
      let union ← c_rep_pre greedy
      let compiled ← c h
      c_repetition_0_some_1_false union compiled
  | .mk 0 (some 1) _ true h => do
      let union ← add_union
      let compiled ← c h
      c_repetition_0_some_1_true union compiled
  | .mk min none greedy possessive sub => do
      if min = 0 && cannotMatchEmptyString sub
      then
        let union ← c_rep_pre greedy
        let compiled ← c sub
        c_repetition_0_none union compiled
      else c_at_least sub min greedy possessive
  | .mk min (some max) greedy possessive sub =>
      if min ≤ max then c_bounded sub min max greedy possessive else c_empty
termination_by sizeOf rep

def c_cap (hir : Capture) : CompilerM ThompsonRef := do
  match hir with
    | .mk group _ sub =>
      let start ← c_cap' Capture.Role.Start group (group * 2)
      let «inner» ← c sub
      let «end» ← c_cap' Capture.Role.End group (group * 2 + 1)
      Code.patch start inner.start
      Code.patch inner.end «end»
      pure (ThompsonRef.mk start «end»)
termination_by sizeOf hir

def c (hir : Hir) : CompilerM ThompsonRef :=
  have : sizeOf hir.kind < sizeOf hir := Hir.sizeOfKindOfHir hir
  match h : hir.kind with
  | .Empty => c_empty
  | .Literal c => c_literal c
  | .Class (.Unicode cls) => c_unicode_class cls
  | .Look look => c_look look
  | .Lookaround look =>
    have : sizeOf look < sizeOf hir.kind := by simp [h]
    c_lookaround look
  | .BackRef f n => c_back_ref f n
  | .Repetition rep =>
    have : sizeOf rep < sizeOf hir.kind := by simp [h]
    c_repetition rep
  | .Capture cap =>
    have : sizeOf cap < sizeOf hir.kind := by simp [h]
    c_cap cap
  | .Concat items =>
    have : sizeOf items < sizeOf hir.kind := by simp [h]
    c_concat items
  | .Alternation sub =>
    have : sizeOf sub < sizeOf hir.kind := by simp [h]
    c_alt_iter sub
termination_by sizeOf hir

end

def init (anchored : Bool) : CompilerM ThompsonRef := do
  let unanchored_prefix ←
    if anchored then c_empty
    else c_repetition (Repetition.mk 0 none false false (dot Dot.AnyChar))
  pure unanchored_prefix

/-- Compile the HIR expression given. -/
def compile (anchored : Bool) (expr : Hir) : CompilerM Unit := do
  let unanchored_prefix ← init anchored
  let one ← c_cap (Capture.mk 0 none expr)
  let match_state_id ← add_match 0
  patch one.end match_state_id
  patch unanchored_prefix.end one.start

end Code
