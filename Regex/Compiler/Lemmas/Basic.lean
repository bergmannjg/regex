module

public import Std.Tactic.Do
public import Std.Tactic.Do.Syntax

public import Regex.Compiler.Basic
public import Regex.Compiler.Compile

@[expose] public section

namespace Compiler

open Regex.Syntax
open NFA

namespace Lemmas

@[simp, grind] def isAppend (s1 s2 : Array Unchecked.State) :=
  ∃ s', s2 = s1 ++ s'

@[simp, grind .] theorem isAppend_trans (h1 : isAppend s1 s2) (h2 : isAppend s2 s3)
    : isAppend s1 s3 := by
  grind

@[grind .] theorem all_push {sid : Unchecked.State} (states : Array Unchecked.State)
  (h : Unchecked.State.nextOf sid ≤ states.size)
  (hlt : ∀ (i : Nat) _, states[i].nextOf < states.size)
    : ∀ (i : Nat) _, ((states.push sid)[i].nextOf < (states.push sid).size) := by
  intro i hi
  have := @Array.getElem_push _ states sid i hi
  simp_all
  split
  . rename_i h'
    exact Nat.lt_add_right 1 (hlt i h')
  . exact Nat.lt_add_one_of_le h

open Std.WP

set_option linter.deprecated.syntax false

@[simp, grind] def tRefLt (t : ThompsonRef) (r : Array Unchecked.State) :=
  t.1 < r.size ∧ t.2 < r.size

@[simp, grind] def statesNextOfLeLt (prevs : Array Unchecked.State) (s : Array Unchecked.State) :=
  prevs.size ≤ s.size ∧ NextOfLt s

@[simp, grind] def stateIdNextOfLt (prevs : Array Unchecked.State) (sid : Unchecked.StateID) (s : Array Unchecked.State) :=
  prevs.size < s.size ∧ sid < s.size ∧ NextOfLt s

@[simp, grind] def stateIdNextOfLeLt (prevs : Array Unchecked.State) (sid : Unchecked.StateID) (s : Array Unchecked.State) :=
  prevs.size ≤ s.size ∧ sid < s.size ∧ NextOfLt s

@[simp, grind] def stateIdNextOfEqLt (prevs : Array Unchecked.State) (sid : Unchecked.StateID) (s : Array Unchecked.State) :=
  prevs.size = s.size ∧ sid < s.size ∧ NextOfLt s

@[simp, grind] def tRefNextOfLt (prevs : Array Unchecked.State) (t : ThompsonRef) (s : Array Unchecked.State) :=
  prevs.size < s.size ∧ tRefLt t s ∧ NextOfLt s

@[simp, grind] def tRefNextOfLeLt (prevs : Array Unchecked.State) (t : ThompsonRef) (s : Array Unchecked.State) :=
  prevs.size ≤ s.size ∧ tRefLt t s ∧ NextOfLt s

def cValid (caps : Array NFA.Capture) :=
  NFA.Capture.Valid caps

def cMemAndValid (prev caps : Array NFA.Capture) :=
  (∀ a ∈ prev, a ∈ caps) ∧ NFA.Capture.Valid caps

def cValidFunc (captures : Array NFA.Capture) : Array NFA.Capture → Prop :=
    fun (curr : Array NFA.Capture) => curr = captures ∧ cValid captures

def cMemAndValidFunc (captures : Array NFA.Capture) : Array NFA.Capture → Prop :=
    fun (curr : Array NFA.Capture) => curr = captures ∧ cMemAndValid captures curr

@[grind .] theorem cap_exists_of_cap_role_end_of_cValid (caps : Array NFA.Capture) (h : cValid caps)
  (a : NFA.Capture)  (h1 : a ∈ caps) (h2 : a.role = Capture.Role.End)
    : ∃ (a' : NFA.Capture), a' ∈ caps ∧ a'.role = Capture.Role.Start ∧ a.group = a'.group := by
  dsimp only [cValid] at h
  have := Capture.Valid.forall h
  simp_all

@[grind .] theorem cValid_of_empty (captures : Array NFA.Capture) (h : captures.size = 0)
    : cValid captures := by
  dsimp only [cValid]
  grind

@[grind .] theorem cValid_of_cMemAndValid (prevs caps : Array NFA.Capture)
  (h : cMemAndValid prevs caps)
    : cValid caps := by
  dsimp [cMemAndValid] at h
  grind [= cValid]

@[simp] theorem cMemAndValid_of_cValid_of_eq (captures : Array NFA.Capture)
    : ∀ (s : Array NFA.Capture), s = captures ∧ cValid captures → cMemAndValid captures s := by
  intro s h
  unfold cValid at h
  unfold cMemAndValid
  rw [h.left]
  simp_all

@[simp, grind .] theorem valid_of_push_of_role_start (captures : Array NFA.Capture)
  (capture : NFA.Capture) (hr : capture.role = Capture.Role.Start) (hc :  NFA.Capture.Valid  captures)
    :  NFA.Capture.Valid (captures.push capture) := by
  apply Capture.Valid.mk
  intro c
  have ⟨c', _⟩ := Capture.Valid.forall hc ⟨c, by grind⟩
  exact ⟨c', by grind⟩

@[simp] theorem cMemAndValid_of_push_of_role_start (captures : Array NFA.Capture)
  (capture : NFA.Capture) (hr : capture.role = Capture.Role.Start) (hc : cValid captures)
    : cMemAndValid captures (captures.push capture) := by
  simp [cMemAndValid]
  simp [cValid] at hc
  and_intros
  · grind
  · apply Capture.Valid.mk
    intro c
    have ⟨c', _⟩ := Capture.Valid.forall hc ⟨c, by grind⟩
    exact ⟨c', by grind⟩

@[grind .] theorem cMemAndValid_of_push_of_role_end (captures : Array NFA.Capture)
  (capture : NFA.Capture) (hc : cValid captures)
  (h : ∃ c ∈ captures, c.role = Capture.Role.Start ∧ c.group = capture.group)
    : cMemAndValid captures (captures.push capture) := by
  simp [cMemAndValid]
  simp [cValid] at hc
  and_intros
  · grind
  · apply Capture.Valid.mk
    intro c
    cases Array.mem_or_eq_of_mem_push c.property.left
    · have ⟨c', _⟩ := Capture.Valid.forall hc ⟨c, by grind⟩
      exact ⟨c', by grind⟩
    · have ⟨c', _⟩ := h
      exact ⟨c', by grind⟩

@[simp] theorem cMemAndValidFunc_of_cValidFunc (captures : Array NFA.Capture)
    : ∀ (s : Array NFA.Capture), cValidFunc captures s → cMemAndValidFunc captures s := by
  intro s h
  simp [cValidFunc] at h
  dsimp only [cMemAndValidFunc]
  simp_all

theorem lift_spec_StateT_to_PatchM {v : StateT (Array Unchecked.State) Id α}
  {P : (Array Unchecked.State) → Prop} {Q : α → (Array Unchecked.State) → Prop}
  (h : ⦃P⦄ v ⦃Q⦄) : ⦃P⦄ (v : Code.PatchM α) ⦃Q; fun _ _ => False⦄ := by
  refine ⟨fun s hs => ?_⟩
  have := h.le_wp s hs
  simp only [WP.wp, WP.trans, liftM, monadLift, MonadLiftT.monadLift, EStateM.modifyGet] at this ⊢
  exact this

theorem lift_spec_PatchM_to_CompilerM {captures : Array NFA.Capture}
  {v : Code.PatchM α} {P : (Array Unchecked.State) → Prop} {Q : α → (Array Unchecked.State) → Prop}
  (h : ⦃P⦄ v ⦃Q; fun _ _ => False⦄)
    : ⦃fun s => P s.1 ∧ s.2.1 = captures ∧ cValid captures⦄
      (v : Code.CompilerM α)
      ⦃fun r s => Q r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  refine ⟨fun s ⟨hp, hc, hv⟩ => ?_⟩
  have := h.le_wp s.1 hp
  simp only [WP.wp, WP.trans, liftM, monadLift, MonadLiftT.monadLift, EStateM.run] at this ⊢
  cases hx : v s.1 <;> simp only [hx] at this ⊢
  exact ⟨this, hc, cMemAndValid_of_cValid_of_eq captures _ ⟨hc, hv⟩⟩

theorem lift_spec_StateT_to_CompilerM {captures : Array NFA.Capture}
  {v : StateT (Array Unchecked.State) Id α} {P : (Array Unchecked.State) → Prop}
  {Q : α → (Array Unchecked.State) → Prop}
  (h : ⦃P⦄ v ⦃Q⦄)
    : ⦃fun s => P s.1 ∧ s.2.1 = captures ∧ cValid captures⦄
      (v : Code.CompilerM α)
      ⦃fun r s => Q r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  refine ⟨fun s ⟨hp, hc, hv⟩ => ?_⟩
  have := h.le_wp s.1 hp
  simp only [WP.wp, WP.trans, liftM, monadLift, MonadLiftT.monadLift, StateT.run, Id.run] at this ⊢
  exact ⟨this, hc, cMemAndValid_of_cValid_of_eq captures _ ⟨hc, hv⟩⟩

@[grind .] theorem nextOf_look_eq : (Unchecked.State.Look look 0).nextOf = 0 := by
  simp_all [Unchecked.State.nextOf]

@[grind .] theorem nextOf_union_eq : (Unchecked.State.Union #[]).nextOf = 0 := by
  simp_all [Unchecked.State.nextOf, List.maxD]

@[grind .] theorem nextOf_union_reverse_eq : (Unchecked.State.UnionReverse #[]).nextOf = 0 := by
  simp_all [Unchecked.State.nextOf, List.maxD]

@[grind .] theorem nextOf_transition_le_of_le (states: Array Unchecked.State) (trans : Array Unchecked.Transition)
  (h : ∀ (i : Nat) (x : i < trans.size), trans[i].next ≤ states.size)
    : (Unchecked.State.SparseTransitions trans).nextOf ≤ states.size := by
  simp_all [Unchecked.State.nextOf]
  have h : ∀ a ∈ trans.toList, a.next ≤ states.size := by
    intro a ha
    have ha : a ∈ trans := Array.mem_def.mpr ha
    have ⟨i, ⟨hlt, heq⟩⟩ := Array.mem_iff_getElem.mp ha
    have := h i hlt
    simp_all
  exact List.maxD_of_all_map_le h
