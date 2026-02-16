
import Std.Tactic.Do
import Std.Tactic.Do.Syntax

import Regex.Data.Nat.Basic
import Regex.Compiler.Basic
import Regex.Compiler.Patch
import Regex.Compiler.Lemmas.Basic

namespace Compiler

open Syntax
open NFA

namespace Lemmas

open Std.Do

set_option mvcgen.warning false

@[simp] def State.patchAssignable (state : Unchecked.State)  : Prop :=
  match state with
  | .Empty _
  | .NextChar _ _
  | .RemoveFrameStep _
  | .Look _ _
  | .BackRef _ _ _
  | .ByteRange _
  | .Capture _ _ _ _
  | .SparseTransitions _
  | .Union _
  | .UnionReverse _ => True
  | _ => False

def patchAssignable (s : Array Unchecked.State) (sid : Unchecked.StateID) : Prop :=
  if h : sid < s.size then State.patchAssignable (s[sid]'h)
  else False

@[simp] def State.patch2Assignable (state : Unchecked.State) : Prop :=
  match state with
  | .Eat (.Until _)  _
  | .Eat (.ToLast _)  _
  | .BinaryUnion  _ _
  | .ChangeFrameStep _ _ => True
  | _ => False

@[simp, grind .] theorem State.patchAssignable_of_empty
    : State.patchAssignable (Unchecked.State.Empty 0) := by
  simp

@[simp, grind .] theorem State.patchAssignable_of_next_char (offset : Nat)
    : State.patchAssignable (Unchecked.State.NextChar offset 0) := by
  simp

@[simp, grind .] theorem State.patchAssignable_of_look
    : State.patchAssignable (Unchecked.State.Look look 0) := by
  simp

@[simp, grind .] theorem State.patchAssignable_of_remove_frame_step
    : State.patchAssignable (Unchecked.State.RemoveFrameStep 0) := by
  simp

@[simp, grind .] theorem State.patchAssignable_of_byte_range (trans : NFA.Unchecked.Transition)
    : State.patchAssignable (Unchecked.State.ByteRange trans) := by
  simp

@[simp, grind .] theorem State.patchAssignable_of_sparse_transistions (trans : Array Unchecked.Transition)
    : State.patchAssignable (Unchecked.State.SparseTransitions trans) := by
  simp

@[simp, grind .] theorem State.patchAssignable_of_union
    : State.patchAssignable (Unchecked.State.Union #[]) := by
  simp

@[simp, grind .] theorem State.patchAssignable_of_union_reverse
    : State.patchAssignable (Unchecked.State.UnionReverse #[]) := by
  simp

@[simp, grind .] theorem State.patchAssignable_of_capture (role : Capture.Role) (group : Nat)
    : State.patchAssignable (Unchecked.State.Capture role 0 0 group) := by
  simp

@[simp, grind .] theorem State.patch2Assignable_of_changeframe_step
    : State.patch2Assignable (Unchecked.State.ChangeFrameStep 0 0) := by
  simp

def patch2Assignable (s : Array Unchecked.State) (sid : Unchecked.StateID) : Prop :=
  if h : sid < s.size then State.patch2Assignable (s[sid]'h)
  else False

@[simp, grind .] theorem State.patchAssignable_of_backRef {b : Nat} {case_insensitive : Bool}
    : State.patchAssignable (Unchecked.State.BackRef b case_insensitive 0) := by
  simp

@[simp, grind .] def assignableIf (s1 s2 : Array Unchecked.State) :=
  (∀ sid : Fin s1.size, patchAssignable s1 sid → patchAssignable s2 sid)
  ∧ (∀ sid : Fin s1.size, patch2Assignable s1 sid → patch2Assignable s2 sid)

@[simp, grind .] theorem patchAssignable_of_some {s : Array Unchecked.State} (hlt : f < s.size)
  {state : Unchecked.State} (h : s[f]? = some state) (hp : State.patchAssignable state)
    : patchAssignable s f := by
  simp [getElem?] at h
  obtain ⟨_, h⟩ := h
  simp [patchAssignable]
  exact ⟨hlt, by rw [h]; simp_all⟩

@[simp, grind .] theorem patchAssignable_of_eq (s1 s2 : Array Unchecked.State)
  (h1 : patchAssignable s1 sid) (h2 : sid < s1.size) (h3 : sid < s2.size)  (h4 : s1[sid] = s2[sid])
    : patchAssignable s2 sid := by
  simp [patchAssignable]
  simp [patchAssignable] at h1
  exact ⟨h3, by split<;> simp_all⟩

@[simp, grind →] theorem patchAssignable_of_append (s1 s2 : Array Unchecked.State)
  (h1 : patchAssignable s1 sid) (h2 : isAppend s1 s2)
    : patchAssignable s2 sid := by
  simp [patchAssignable]
  simp [patchAssignable] at h1
  obtain ⟨h1, hm⟩ := h1
  obtain ⟨s3, _⟩ := h2
  have hlt : sid < s2.size := by grind
  exact ⟨hlt, by simp_all⟩

@[simp, grind .] theorem assignableIf_trans (s1 s2 : Array Unchecked.State)
  (h1 : assignableIf s1 s2) (h2 : assignableIf s2 s3)
    : assignableIf s1 s3 := by
  simp_all
  and_intros
  · intros sid h
    have h1 := h1.left sid h
    exact h2.left ⟨sid, by grind [= patchAssignable]⟩ h1
  · intros sid h
    have h1 := h1.right sid h
    exact h2.right ⟨sid, by grind [= patch2Assignable]⟩ h1

@[simp, grind .] theorem patchAssignable_of_assignableIf (s1 s2 : Array Unchecked.State)
  (h1 : patchAssignable s1 sid) (h2 : assignableIf s1 s2)
    : patchAssignable s2 sid := by
  simp at h2
  exact h2.left ⟨sid, by grind [= patchAssignable]⟩ h1

@[simp, grind .] theorem patch2Assignable_of_assignableIf (s1 s2 : Array Unchecked.State)
  (h1 : patch2Assignable s1 sid) (h2 : assignableIf s1 s2)
    : patch2Assignable s2 sid := by
  simp at h2
  exact h2.right ⟨sid, by grind [= patch2Assignable]⟩ h1

@[simp, grind .] theorem not_patchAssignable_if_patch_eq_error {s1 s2 : Array Unchecked.State}
  (h : Code.patch f t s1 = EStateM.Result.error e s2) (hlt : f < s1.size)
    : ¬patchAssignable s1 f := by
  simp [Code.patch] at h
  dsimp only [get, getThe, MonadStateOf.get,EStateM.instMonadStateOf, EStateM.get,
              bind, Monad.toBind, EStateM.bind] at h
  split at h
  simp [patchAssignable]
  intros
  split
  case h_11 | isFalse => simp_all
  all_goals (rename_i heq; rw [heq] at h; dsimp [EStateM.set] at h; simp at h)

@[simp, grind .] theorem patch2Assignable_of_eq (s1 s2 : Array Unchecked.State)
  (h1 : patch2Assignable s1 sid) (h2 : sid < s1.size) (h3 : sid < s2.size)  (h4 : s1[sid] = s2[sid])
    : patch2Assignable s2 sid := by
  simp [patch2Assignable]
  simp [patch2Assignable] at h1
  exact ⟨h3, by split<;> simp_all⟩

@[simp, grind →] theorem patch2Assignable_of_append (s1 s2 : Array Unchecked.State)
  (h1 : patch2Assignable s1 sid) (h2 :isAppend s1 s2)
    : patch2Assignable s2 sid := by
  simp [patch2Assignable]
  simp [patch2Assignable] at h1
  obtain ⟨h1, hm⟩ := h1
  obtain ⟨s3, h3⟩ := h2
  have hlt : sid < s2.size := by
    have : s1.size ≤ (s1.append s3).size := by simp_all
    rw [h3]
    exact Nat.lt_of_lt_of_le h1 this
  exact ⟨hlt, by
    split
    case h_4 => split at hm <;> simp_all
    case h_5 => split at hm <;> simp_all
    all_goals grind⟩

@[simp, grind .] theorem not_patch2Assignable_if_patch2_eq_error {s1 s2 : Array Unchecked.State}
  (h : Code.patch2 f t1 t2 s1 = EStateM.Result.error e s2) (hlt : f < s1.size)
    : ¬patch2Assignable s1 f := by
  simp [Code.patch2] at h
  dsimp only [get,getThe, EStateM.instMonadStateOf, EStateM.get,
              bind, Monad.toBind, EStateM.bind] at h
  split at h
  simp [patch2Assignable]
  intros
  split
  case h_5 | isFalse => simp_all
  all_goals (rename_i heq; rw [heq] at h; dsimp [EStateM.set] at h; simp at h)

@[simp, grind .] theorem not_patch2Assignable_if_patch_eq (s1 s2 : Array Unchecked.State)
  (h : Code.patch f t s1 = EStateM.Result.ok () s2)
    : ¬patch2Assignable s1 f := by
  simp [patch2Assignable]
  intro hlt
  simp [Code.patch] at h
  dsimp [bind, EStateM.bind] at h
  split at h
  split at h
  · expose_names
    have : s1 = a := by
      dsimp only [get, getThe, MonadStateOf.get, EStateM.get] at heq
      simp_all
    have : s1[f] = a[f] := by grind
    rw [this]
    split <;> simp_all
    all_goals (expose_names; rw [heq_1] at h; simp at h)
  · simp_all
  · simp_all

theorem patch_spec_constant («from»: Unchecked.StateID) («to»: Unchecked.StateID)
  (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ «from» < states.size ∧ «to» < states.size⌝⦄
      Code.patch «from» «to»
      ⦃post⟨fun _ r => ⌜stateIdNextOfEqLt states «to» r
                        ∧ (∀ sid : Fin r.size, (_ : sid < states.size) →
                           sid.val ≠ «from» → r[sid] = states[sid])⌝, fun _ => ⌜True⌝ ⟩⦄ := by
  mintro _
  simp [Code.patch]
  intros
  mvcgen
  all_goals grind

theorem patch_spec_assignable («from»: Unchecked.StateID) («to»: Unchecked.StateID)
  (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ «from» < states.size ∧ «to» < states.size⌝⦄
      Code.patch «from» «to»
      ⦃post⟨fun _ r => ⌜patchAssignable r «from»⌝, fun _ => ⌜True⌝ ⟩⦄ := by
  mintro _
  simp [Code.patch]
  intros
  mvcgen
  all_goals simp_all [patchAssignable]

@[simp, grind .] theorem patchAssignable_of_patch_eq (s1 s2 : Array Unchecked.State)
  (h : Code.patch f t s1 = EStateM.Result.ok e s2) (hf : f < s1.size) (ht : t < s1.size)
    : patchAssignable s2 f := by
  have hpatch := patch_spec_assignable f t s1
  simp [Triple] at hpatch
  have hpatch := hpatch hf ht
  simp [wp] at hpatch
  split at hpatch
  all_goals grind

@[spec] theorem patch_spec («from»: Unchecked.StateID) {«to»: Unchecked.StateID}
  {states : Array Unchecked.State}
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ «from» < states.size ∧ «to» < states.size
                ∧ patchAssignable states «from»⌝⦄
      Code.patch «from» «to»
      ⦃post⟨fun _ r => ⌜stateIdNextOfEqLt states «to» r ∧ assignableIf states r⌝, fun _ => ⌜False⌝ ⟩⦄ := by
  simp [Triple]
  intros h f t
  simp [wp]
  have hpatch := patch_spec_constant «from» to states
  simp [Triple] at hpatch
  have hpatch := hpatch h f t
  simp [wp] at hpatch
  split
  · intros
    and_intros
    all_goals grind
  · grind

@[spec] theorem patch_lift_spec («from»: Unchecked.StateID) {«to»: Unchecked.StateID}
  {states : Array Unchecked.State}
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states ∧ «from» < states.size ∧ «to» < states.size
                ∧ patchAssignable states «from») ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.patch «from» «to» : Code.CompilerM Unit)
      ⦃post⟨fun _ s => ⌜(stateIdNextOfEqLt states «to» s.1 ∧ assignableIf states s.1)
                        ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝ ⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (patch_spec _)

theorem patch2_spec_constant («from»: Unchecked.StateID) (to₁ to₂: Unchecked.StateID)
  (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ «from» < states.size ∧ to₁ < states.size
                  ∧ to₂ < states.size⌝⦄
      Code.patch2 «from» to₁ to₂
      ⦃post⟨fun _ r => ⌜stateIdNextOfEqLt states to₁ r
                        ∧ (∀ sid : Fin r.size, (_ : sid < states.size) →
                           sid.val ≠ «from» → r[sid] = states[sid])⌝, fun _ => ⌜True⌝ ⟩⦄ := by
  mintro _
  simp [Code.patch2]
  intros
  mvcgen
  all_goals grind

theorem patch2_spec_assignable («from»: Unchecked.StateID) (to₁ to₂ : Unchecked.StateID)
  (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ «from» < states.size ∧ to₁ < states.size ∧ to₂ < states.size⌝⦄
      Code.patch2 «from» to₁ to₂
      ⦃post⟨fun _ r => ⌜patch2Assignable r «from»⌝, fun _ => ⌜True⌝ ⟩⦄ := by
  mintro _
  simp [Code.patch2]
  intros
  mvcgen
  all_goals simp_all [patch2Assignable]

@[simp, grind .] theorem patch2Assignable_of_patch_eq (s1 s2 : Array Unchecked.State)
  (h : Code.patch2 f t1 t2 s1 = EStateM.Result.ok e s2) (hf : f < s1.size)
    (ht1 : t1 < s1.size) (ht2 : t2 < s1.size)
    : patch2Assignable s2 f := by
  have hpatch := patch2_spec_assignable f t1 t2 s1
  simp [Triple] at hpatch
  have hpatch := hpatch hf ht1
  simp [wp] at hpatch
  split at hpatch
  all_goals grind

@[simp, grind .] theorem not_patchAssignable_if_patch2_eq (s1 s2 : Array Unchecked.State)
  (h : Code.patch2 f t1 t2 s1 = EStateM.Result.ok () s2)
    : ¬patchAssignable s1 f := by
  simp [patchAssignable]
  intro hlt
  simp [Code.patch2] at h
  dsimp only [bind, EStateM.bind] at h
  split at h
  split at h
  · expose_names
    have : s1 = a := by
      dsimp only [get, getThe, MonadStateOf.get, EStateM.get] at heq
      simp_all
    have : s1[f] = a[f] := by grind
    rw [this]
    split <;> simp_all
  · simp_all
  · simp_all

@[spec] theorem patch2_spec («from»: Unchecked.StateID) {to₁ to₂ : Unchecked.StateID}
  {states : Array Unchecked.State}
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ «from» < states.size ∧ to₁ < states.size
                  ∧ to₂ < states.size ∧ patch2Assignable states «from»⌝⦄
      Code.patch2 «from» to₁ to₂
      ⦃post⟨fun _ r => ⌜stateIdNextOfEqLt states to₁ r ∧ to₂ < r.size ∧ assignableIf states r⌝, fun _ => ⌜False⌝ ⟩⦄ := by
  simp [Triple]
  intros h f t
  simp [wp]
  have hpatch := patch2_spec_constant «from» to₁ to₂ states
  simp [Triple] at hpatch
  have hpatch := hpatch h f t
  simp [wp] at hpatch
  split
  · intros
    and_intros
    all_goals grind
  · grind
