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
import Regex.Compiler.Compile

namespace Compiler

open Syntax
open NFA

namespace Lemmas

/-!
## Lemmas

Proof that `Compiler.Code.compile` gives an array with the `Compiler.NextOfLt` and `NFA.Capture.valid` property

- `c_compile_spec`: main result
-/

/-- instantiate mvar,
    mspec with a precondition like `fun s => s = states ∧ P` gives a uninstantiated mvar
-/
syntax "inst_mvar" : tactic
macro_rules | `(tactic|inst_mvar) => `(tactic| simp; (try and_intros; rfl); try simp_all)

/-- instantiate mvars,
    mspec with a precondition like `fun s => s = states ∧ P` gives a uninstantiated mvar
-/
syntax "inst_mvars" : tactic
macro_rules | `(tactic|inst_mvars) => `(tactic| simp; and_intros; all_goals try rfl)

@[grind] private theorem all_push {sid : Unchecked.State} (states : Array Unchecked.State)
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

open Std.Do

set_option mvcgen.warning false

@[spec] theorem lift_StackT_to_EStateM_spec
  (v : StateT σ Id α)
  {P : σ → Prop}
  (Q : σ → α → σ → Prop)
  (hspec : ⦃fun s => ⌜s = n ∧ P n⌝⦄ v ⦃post⟨fun a s => ⌜Q n a s⌝⟩⦄)
    : ⦃fun s => ⌜s = n ∧ P n⌝⦄
      (v : (EStateM ε σ α))
      ⦃post⟨fun a s => ⌜Q n a s⌝, fun _ => ⌜True⌝ ⟩⦄ := by
  assumption

def coe_spec_StackT_to_EStateM
  {v : StateT σ Id α}
  {P : σ → Prop}
  {Q : α → σ → Prop}
  (hspec : ⦃fun s => ⌜P s⌝⦄ v ⦃post⟨fun a s => ⌜Q a s⌝⟩⦄)
    : ⦃fun s => ⌜P s⌝⦄
      (v : (EStateM ε σ α))
      ⦃post⟨fun a s => ⌜Q a s⌝, fun _ _ => ⌜True⌝ ⟩⦄ := by
  assumption

instance {v : StateT σ Id α} {P : σ → Prop} {Q : α → σ → Prop}
  : Coe (⦃fun s => ⌜P s⌝⦄ v ⦃post⟨fun a s => ⌜Q a s⌝⟩⦄)
      (⦃fun s => ⌜P s⌝⦄ (v : (EStateM ε σ α)) ⦃post⟨fun a s => ⌜Q a s⌝, fun _ _ => ⌜True⌝ ⟩⦄)
  where coe := coe_spec_StackT_to_EStateM

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

@[grind] theorem cap_exists_of_cap_role_end_of_cValid (caps : Array NFA.Capture) (h : cValid caps)
  (a : NFA.Capture)  (h1 : a ∈ caps) (h2 : a.role = Capture.Role.End)
    : ∃ (a' : NFA.Capture), a' ∈ caps ∧ a'.role = Capture.Role.Start ∧ a.group = a'.group := by
  dsimp only [cValid] at h
  have := Capture.Valid.forall h
  simp_all

@[grind] theorem cValid_of_empty (captures : Array NFA.Capture) (h : captures.size = 0)
    : cValid captures := by
  dsimp only [cValid]
  apply Capture.Valid.mk
  grind

@[grind] theorem cValid_of_cMemAndValid (prevs caps : Array NFA.Capture)
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

@[grind] theorem cMemAndValid_of_push_of_role_end (captures : Array NFA.Capture)
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

private theorem coe_spec_EStateM_to_EStateM_Prod
  (σ₃ : Type)
  {v₁ : EStateM ε σ₁ α}
  {P₁ : σ₁ → Prop}
  {Q₁  : α → σ₁ → Prop}
  (hspec₁ : ⦃fun s => ⌜P₁ s⌝⦄ v₁ ⦃post⟨fun a s => ⌜Q₁ a s⌝, fun _ => ⌜True⌝⟩⦄)
  (P₂ : σ₂ → Prop)
  (Q₂ : σ₂ → Prop)
  (hpq : ∀ s : σ₂, P₂ s → Q₂ s)
    : ⦃fun s => ⌜P₁ s.1 ∧ P₂ s.2.1⌝⦄
      (v₁ : EStateM ε (σ₁ × σ₂ × σ₃) α)
      ⦃post⟨fun r s => ⌜Q₁ r s.1 ∧ Q₂ s.2.1⌝, fun _ _ => ⌜True⌝ ⟩⦄ := by
  simp_all [Triple, wp, liftM, monadLift, SPred.entails, EStateM.run]
  grind

private theorem coe_spec_EStateM_to_CompilerM
  {captures : Array NFA.Capture}
  {v₁ : EStateM ε σ₁ α}
  {P₁ : σ₁ → Prop}
  {Q₁  : α → σ₁ → Prop}
  (hspec₁ : ⦃fun s => ⌜P₁ s⌝⦄ v₁ ⦃post⟨fun a s => ⌜Q₁ a s⌝, fun _ => ⌜True⌝⟩⦄)
    : ⦃fun s => ⌜P₁ s.1 ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (v₁ : EStateM ε (σ₁ × (Array NFA.Capture) × (Array Nat)) α)
      ⦃post⟨fun r s => ⌜Q₁ r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ _ => ⌜True⌝ ⟩⦄ := by
  exact coe_spec_EStateM_to_EStateM_Prod (Array Nat) hspec₁
          (cValidFunc captures) (cMemAndValidFunc captures) (by simp_all)

private theorem coe_spec_StateT_to_CompilerM
  {captures : Array NFA.Capture}
  {v : StateT σ₁ Id α}
  {P₁: σ₁ → Prop}
  {Q₁ : α → σ₁ → Prop}
  (hspec : ⦃fun s => ⌜P₁ s⌝⦄ v ⦃post⟨fun a s => ⌜Q₁ a s⌝⟩⦄)
    : ⦃fun s => ⌜P₁ s.1 ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (v : EStateM ε (σ₁ × (Array NFA.Capture) × (Array Nat)) α)
      ⦃post⟨fun r s => ⌜Q₁ r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ _ => ⌜True⌝⟩⦄ :=
  coe_spec_EStateM_to_EStateM_Prod (Array Nat) (coe_spec_StackT_to_EStateM hspec)
          (cValidFunc captures) (cMemAndValidFunc captures) (by simp_all)

theorem lift_CompilerM_bind_pure [MonadLiftT (EStateM ε σ) Code.CompilerM] (x : EStateM ε σ α)
    : liftM x >>= EStateM.pure = (x : Code.CompilerM α) := by
  apply bind_pure

theorem pure_of_imp_spec {x : α} {P1 P2 : α → σ → Prop} (h : ∀ a s, P1 a s → P2 a s)
    : ⦃fun s => ⌜P1 x s⌝⦄
      (EStateM.pure x : EStateM ε σ α)
      ⦃post⟨fun r s => ⌜P2 r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  simp [Triple, wp, EStateM.pure]
  grind

@[spec] theorem patch_spec («from»: Unchecked.StateID) {«to» : Unchecked.StateID}
  {states : Array Unchecked.State}
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ «from» < states.size ∧ «to» < states.size⌝⦄
      Code.patch «from» «to»
      ⦃post⟨fun _ r => ⌜stateIdNextOfEqLt states «to» r⌝, fun _ => ⌜True⌝ ⟩⦄ := by
  mvcgen [Code.patch]
  with grind

@[spec] theorem patch_lift_spec («from»: Unchecked.StateID) {«to» : Unchecked.StateID}
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states ∧ «from» < states.size ∧ «to» < states.size)
                 ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.patch «from» «to» : Code.CompilerM Unit)
      ⦃post⟨fun _ s => ⌜stateIdNextOfEqLt states «to» s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝,
           fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (patch_spec _)

@[spec] theorem push_spec (sid : Unchecked.State) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size⌝⦄
      Code.push sid
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.push]
  with grind

@[spec] theorem push_lift_spec (sid : Unchecked.State) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size⌝⦄
      (Code.push sid : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝ ⟩⦄ := by
  exact ↑(push_spec sid states)

@[spec] theorem push_run_spec (sid : Unchecked.State) (states : Array Unchecked.State)
  (h1 : NextOfLt states) (h2 : NFA.Unchecked.State.nextOf sid ≤ states.size)
    : ⦃⌜True⌝⦄
      ((Code.push sid).run states : Id (Unchecked.StateID × Array Unchecked.State))
      ⦃post⟨fun r => ⌜stateIdNextOfLt states r.1 r.2⌝⟩⦄ := by
  mintro _
  mvcgen [Code.push]
  dsimp only [bind, StateT.bind, Functor.map, StateT.map, wp, Id.run]
  split
  rename_i heq
  dsimp only [MonadStateOf.get, StateT.get, pure] at heq
  dsimp only [set, StateT.set, StateT.pure, pure]
  simp only [stateIdNextOfLt, PredTrans.pure_apply, Array.size_push, Nat.lt_add_one, true_and,
    SPred.down_pure]
  and_intros <;> grind

@[spec] theorem push_run_lift_spec (sid : Unchecked.State) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s.1 = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size⌝⦄
      (Code.push sid states : Code.CompilerM (Unchecked.StateID × Array Unchecked.State))
      ⦃post⟨fun r _ => ⌜stateIdNextOfLt states r.1 r.2⌝, fun _ => ⌜True⌝ ⟩⦄ := by
  mvcgen
  intros
  generalize h : (Code.push sid).run states = x
  apply Id.of_wp_run_eq h
  apply push_run_spec sid states <;> simp_all

@[spec] theorem push'_spec (sid : Unchecked.State) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size⌝⦄
      Code.push' sid
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.push']
  with grind

@[spec] theorem add_match_spec (pattern_id : PatternID) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_match pattern_id
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.add_match]
  with grind

@[spec] theorem add_match_lift_spec (pattern_id : PatternID) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.add_match pattern_id : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝ , fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (add_match_spec _ _)

@[spec] theorem add_union_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_union
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.add_union]
  and_intros <;> simp_all [Unchecked.State.nextOf, List.maxD]

@[spec] theorem add_union_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_union : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact ↑(add_union_spec states)

@[spec] theorem add_union_lift'_spec (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.add_union : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (add_union_spec _)

@[spec] theorem add_union_reverse_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_union_reverse
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.add_union_reverse]
  and_intros <;> simp_all [Unchecked.State.nextOf, List.maxD]

@[spec] theorem add_union_reverse_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_union_reverse : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact ↑(add_union_reverse_spec states)

@[spec] theorem add_backrefence_spec (case_insensitive : Bool) (b : Nat) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_backrefence case_insensitive b
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.add_backrefence]
  and_intros <;> grind

@[spec] theorem add_backrefence_lift_spec (case_insensitive : Bool) (b : Nat) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_backrefence case_insensitive b : (EStateM String (Array Unchecked.State) Unchecked.StateID))
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.add_backrefence]

@[spec] theorem c_range_spec (start «end» : UInt32) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_range start «end»
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.c_range]
  with grind

@[spec] theorem add_empty_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_empty
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.add_empty]
  with grind

@[spec] theorem add_empty_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_empty : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact ↑(add_empty_spec states)

theorem add_empty_lift'_spec (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.add_empty : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (add_empty_spec _)

@[spec] theorem add_fail_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_fail
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.add_fail]
  with grind

@[spec] theorem add_fail_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_fail : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact ↑(add_fail_spec states)

theorem eat_next_of_le (states : Array Unchecked.State) (h : mode.nextOf < states.size)
    : (Unchecked.State.Eat mode 0).nextOf ≤ states.size := by
  simp [Unchecked.State.nextOf]
  split
  all_goals simp_all
    <;> rename_i s next heq
    <;> simp_all [Nat.max_le]
    <;> rw [← heq.right]
    <;> simp [Unchecked.EatMode.nextOf] at h
    <;> exact And.intro (by grind) (by exact Nat.zero_le states.size)

@[spec] theorem add_eat_spec (mode : Unchecked.EatMode) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ (mode.nextOf < states.size)⌝⦄
      Code.add_eat mode
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.add_eat]
  simp_all [@eat_next_of_le mode states (by simp_all)]

@[spec] theorem add_change_state_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_change_state
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.add_change_state]
  with grind

@[spec] theorem add_change_state_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_change_state : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact ↑(add_change_state_spec states)

@[spec] theorem add_remove_state_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_remove_state
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.add_remove_state]
  with grind

@[spec] theorem add_next_char_spec (offset : Nat) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_next_char offset
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.add_next_char]
  with grind

@[spec] theorem add_next_char_lift_spec (offset : Nat) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.add_next_char offset : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (add_next_char_spec _ _)

@[spec] theorem c_empty_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_empty
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.c_empty]
  with grind

@[spec] theorem c_empty_lift_spec (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_empty : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (c_empty_spec _)

@[simp] theorem transition_lt_of_lt (states: Array Unchecked.State) (trans : Array Unchecked.Transition)
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

@[spec] theorem add_sparse_spec (trans : Array Unchecked.Transition) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ ∀ (i : Nat) _, trans[i].next ≤ states.size⌝⦄
      Code.add_sparse trans
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.add_sparse]
  and_intros <;> simp_all

@[spec] theorem c_unicode_class_spec (cls : ClassUnicode) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_unicode_class cls
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.c_unicode_class]
  with grind

@[spec] theorem c_unicode_class_lift_spec (cls : ClassUnicode) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_unicode_class cls : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (c_unicode_class_spec _ _)

@[spec] theorem c_literal_spec (c : Char) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_literal c
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s⌝⟩⦄ := by
  mvcgen [Code.c_literal]

@[spec] theorem c_literal_lift_spec (c : Char) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_literal c : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (c_literal_spec _ _)

@[spec] theorem c_look_spec (look : Syntax.Look) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_look look
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s⌝ ⟩⦄ := by
  mvcgen [Code.c_look]
  with grind

@[spec] theorem c_look_lift_spec (look : Syntax.Look) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_look look : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (c_look_spec _ _)

@[spec] theorem c_possessive_spec (tref : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tref.start < states.size
                      ∧ tref.end < states.size ∧ NextOfLt states⌝⦄
      Code.c_possessive tref
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_possessive]
  with grind

@[spec] theorem c_possessive_lift_spec (tref : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tref.start < states.size ∧ tref.end < states.size ∧ NextOfLt states)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_possessive tref : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_possessive_spec _ _)

theorem tref_le_of_lt_spec (states : Array Unchecked.State)
    : ∀ (tref : ThompsonRef),
      ⦃fun s => ⌜tRefNextOfLt states tref s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝⦄
      (EStateM.pure tref : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  intro tref
  apply pure_of_imp_spec (by grind)

-- relax postcondition of c_possessive_lift_spec
theorem c_possessive_le_lift_spec (tref : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tref.start < states.size ∧ tref.end < states.size ∧ NextOfLt states)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_possessive tref : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  have := Triple.bind _ _ (c_possessive_lift_spec tref states captures) (tref_le_of_lt_spec states)
  rwa [lift_CompilerM_bind_pure (Code.c_possessive tref)] at this

@[spec] theorem c_cap'_start_spec (group : Nat) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_cap' Capture.Role.Start group
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1
                        ∧ cMemAndValid captures s.2.1
                        ∧ (NFA.Capture.mk Capture.Role.Start group) ∈ s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_cap']
  with grind
  simp_all

@[spec] theorem c_cap'_end_spec (group : Nat) (states : Array Unchecked.State)
  (captures : Array NFA.Capture) (h : ∃ c ∈ captures, c.role = Capture.Role.Start ∧ c.group = group)
    : ⦃fun s => ⌜s.1 = states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_cap' Capture.Role.End group
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_cap']
  with grind

@[spec] theorem c_back_ref_spec (case_insensitive : Bool) (n : Nat)  (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_back_ref case_insensitive n
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_back_ref]
  with grind

@[spec] theorem c_back_ref_lift_spec (case_insensitive : Bool) (n : Nat)  (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_back_ref case_insensitive n : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_back_ref_spec _ _ _)

@[spec] theorem c_lookaround_PositiveLookahead_spec (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states ∧ NextOfLt states⌝⦄
      Code.c_lookaround_PositiveLookahead compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_lookaround_PositiveLookahead]
  with grind

@[spec] theorem c_lookaround_PositiveLookahead_lift_spec (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_lookaround_PositiveLookahead compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_lookaround_PositiveLookahead_spec _ _)

@[spec] theorem c_lookaround_NegativeLookahead_spec (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states ∧ NextOfLt states⌝⦄
      Code.c_lookaround_NegativeLookahead compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_lookaround_NegativeLookahead]
  with grind

@[spec] theorem c_lookaround_NegativeLookahead_lift_spec (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_lookaround_NegativeLookahead compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_lookaround_NegativeLookahead_spec _ _)

@[spec] theorem c_lookaround_PositiveLookbehind_spec (next_char : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states⌝⦄
      Code.c_lookaround_PositiveLookbehind next_char compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_lookaround_PositiveLookbehind]
  with grind

@[spec] theorem c_lookaround_PositiveLookbehind_lift_spec (next_char : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_lookaround_PositiveLookbehind next_char compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_lookaround_PositiveLookbehind_spec _ _ _)

@[spec] theorem c_lookaround_NegativeLookbehind_spec (next_char : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states⌝⦄
      Code.c_lookaround_NegativeLookbehind next_char compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_lookaround_NegativeLookbehind]
  with grind

@[spec] theorem c_lookaround_NegativeLookbehind_lift_spec (next_char : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_lookaround_NegativeLookbehind next_char compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_lookaround_NegativeLookbehind_spec _ _ _)

@[spec] theorem c_repetition_0_some_1_false_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states⌝⦄
      Code.c_repetition_0_some_1_false union compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_repetition_0_some_1_false]
  with grind

@[spec] theorem c_repetition_0_some_1_false_lift_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_repetition_0_some_1_false union compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_repetition_0_some_1_false_spec _ _ _)

@[spec] theorem c_repetition_0_some_1_true_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states⌝⦄
      Code.c_repetition_0_some_1_true union compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_repetition_0_some_1_true]
  with grind

@[spec] theorem c_repetition_0_some_1_true_lift_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_repetition_0_some_1_true union compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_repetition_0_some_1_true_spec _ _ _)

@[spec] theorem c_repetition_0_none_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states⌝⦄
      Code.c_repetition_0_none union compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_repetition_0_none]
  with grind

@[spec] theorem c_repetition_0_none_lift_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_repetition_0_none union compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_repetition_0_none_spec _ _ _)

@[spec] theorem greedy_union_spec (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (if greedy then Code.add_union else Code.add_union_reverse : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  split <;> mvcgen

@[spec] theorem c_at_least_0_pre_spec (compiled : ThompsonRef) (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states ∧ NextOfLt states⌝⦄
      Code.c_at_least_0_pre compiled greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_at_least_0_pre]
  with grind

@[spec] theorem c_at_least_0_pre_lift_spec (compiled : ThompsonRef) (greedy : Bool) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_at_least_0_pre compiled greedy : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_at_least_0_pre_spec _ _ _)

@[spec] theorem c_at_least_set_spec (possible_empty_capture_group : Option Nat) (greedy : Bool)
  (states : Array Unchecked.State) {groups : Array Nat}
    : ⦃fun s => ⌜s.1 = states ∧ s.2.2 = groups⌝⦄
      Code.c_at_least_set possible_empty_capture_group greedy
      ⦃post⟨fun _ s => ⌜states = s.1  ∧ groups.size ≤ s.2.2.size⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_at_least_set]
  with grind

@[spec] theorem c_at_least_0_post_spec (compiled : ThompsonRef) (plus : Unchecked.StateID) (greedy : Bool)
  (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ plus < states.size ∧ compiled.start < states.size ∧ NextOfLt states⌝⦄
      Code.c_at_least_0_post compiled plus greedy possessive
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_at_least_0_post]
  case vc11 =>
    and_intros
    rfl
    all_goals grind
  case vc25 =>
    and_intros
    rfl
    all_goals grind
  all_goals grind

@[spec] theorem c_at_least_0_post_lift_spec (compiled : ThompsonRef) (plus : Unchecked.StateID) (greedy : Bool)
  (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ plus < states.size ∧ compiled.start < states.size ∧ NextOfLt states)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_at_least_0_post compiled plus greedy possessive : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_at_least_0_post_spec _ _ _ _ _)

@[spec] theorem c_at_least_0_spec (compiled : ThompsonRef) (possible_empty_capture_group : Option Nat) (greedy : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_at_least_0 compiled possible_empty_capture_group greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_at_least_0]
  with grind

@[spec] theorem c_at_least_1_pre_spec (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_at_least_1_pre greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_at_least_1_pre]

@[spec] theorem c_at_least_1_pre_lift_spec (greedy : Bool) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_at_least_1_pre greedy : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_at_least_1_pre_spec _ _)

@[spec] theorem c_at_least_1_post_spec (compiled : ThompsonRef) (union : Unchecked.StateID)
  (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states⌝⦄
      Code.c_at_least_1_post compiled union possessive
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_at_least_1_post]
  case vc5.post.success =>
    and_intros
    rfl
    grind
    grind
    apply NextOfLt.mk
    grind
  all_goals grind

@[spec] theorem c_at_least_1_post_lift_spec (compiled : ThompsonRef) (union : Unchecked.StateID)
  (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_at_least_1_post compiled union possessive : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_at_least_1_post_spec _ _ _ _)

@[spec] theorem c_at_least_1_spec (possible_empty_capture_group : Option Nat) (greedy : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_at_least_1 possible_empty_capture_group greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_at_least_1]

@[spec] theorem c_at_least_2_spec («prefix» last : ThompsonRef) (greedy : Bool)
  (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt «prefix» states ∧ tRefLt last states ∧ NextOfLt states⌝⦄
      Code.c_at_least_2 «prefix» last greedy possessive
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_at_least_2]
  case vc9 =>
    and_intros
    rfl
    all_goals grind
  case vc21 =>
    and_intros
    rfl
    all_goals grind
  all_goals grind

@[spec] theorem c_at_least_2_lift_spec («prefix» last : ThompsonRef) (greedy : Bool)
  (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt «prefix» states ∧ tRefLt last states ∧ NextOfLt states)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_at_least_2 «prefix» last greedy possessive : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_at_least_2_spec _ _ _ _ _)

@[spec] theorem c_bounded.fold.patch.pre_spec (compiled: ThompsonRef) (prev_end : Unchecked.StateID)
  (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states
                      ∧ prev_end < states.size ∧ NextOfLt states⌝⦄
      Code.c_bounded.fold.patch.pre compiled prev_end greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_bounded.fold.patch.pre]
  all_goals grind

@[spec] theorem c_bounded.fold.patch.possessive_spec (compiled: ThompsonRef) (empty : Unchecked.StateID)
  (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states
                      ∧ empty < states.size ∧ NextOfLt states⌝⦄
      Code.c_bounded.fold.patch.possessive compiled empty
      ⦃post⟨fun r s => ⌜stateIdNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_bounded.fold.patch.possessive]
  with grind

@[spec] theorem c_bounded.fold.patch.post_spec (compiled: ThompsonRef) (union empty : Unchecked.StateID) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ compiled.end < states.size
                      ∧ union < states.size ∧ empty < states.size ∧ NextOfLt states⌝⦄
      Code.c_bounded.fold.patch.post compiled union empty
      ⦃post⟨fun r s => ⌜stateIdNextOfLeLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_bounded.fold.patch.post]
  with grind

@[spec] theorem c_bounded.fold.patch_spec (compiled: ThompsonRef) (prev_end empty : Unchecked.StateID)
  (greedy : Bool) (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states
                      ∧ prev_end < states.size ∧ empty < states.size ∧ NextOfLt states⌝⦄
      Code.c_bounded.fold.patch compiled prev_end empty greedy possessive
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_bounded.fold.patch]
  case vc3 =>
    inst_mvar
    all_goals grind
  case vc6 =>
    and_intros
    rfl
    all_goals grind
  all_goals grind

@[spec] theorem c_bounded.fold.patch_lift_spec  (compiled: ThompsonRef) (prev_end empty : Unchecked.StateID)
  (greedy : Bool) (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt compiled states
                      ∧ prev_end < states.size ∧ empty < states.size ∧ NextOfLt states)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_bounded.fold.patch compiled prev_end empty greedy possessive : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_bounded.fold.patch_spec _ _ _ _ _ _)

@[spec] theorem c_alt_iter_step_spec (first second: ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt first states
                      ∧ tRefLt second states ∧ NextOfLt states⌝⦄
      Code.c_alt_iter_step first second
      ⦃post⟨fun r s => ⌜tRefNextOfLt states ⟨r.1, r.2⟩ s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_alt_iter_step]
  with grind

@[spec] theorem c_alt_iter_step_lift_spec (first second: ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt first states ∧ tRefLt second states ∧ NextOfLt states)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_alt_iter_step first second : Code.CompilerM (Unchecked.StateID × Unchecked.StateID))
      ⦃post⟨fun r s => ⌜tRefNextOfLt states ⟨r.1, r.2⟩ s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_alt_iter_step_spec _ _ _)

@[spec] theorem c_rep_pre_spec (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_rep_pre greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [Code.c_rep_pre]

@[spec] theorem c_rep_pre_lift_spec (greedy : Bool) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_rep_pre greedy : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_rep_pre_spec _ _)

set_option maxHeartbeats 4000000

mutual

@[spec] theorem c_bounded_spec (hir : Hir) (min max : Nat) (greedy : Bool) (possessive : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_bounded hir min max greedy possessive
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_bounded
  split
  mspec c_exactly_spec
  split
  case isTrue.post.success.isTrue =>
    split
    · mspec c_possessive_le_lift_spec
      inst_mvars
      case post.success => mvcgen with grind
      all_goals grind
    · simp_all
  case isTrue.post.success.isFalse =>
      mspec add_empty_lift'_spec
      inst_mvars
      case post.success =>
        mspec c_bounded_fold_spec
        inst_mvars
        case post.success =>
          mspec patch_lift_spec
          · inst_mvars
            all_goals grind
          · mvcgen with grind [= cValid, = cMemAndValid]
        all_goals grind
      all_goals grind
  case isFalse =>
    mspec c_empty_lift_spec
    inst_mvars
    case post.success => mvcgen with grind
    all_goals grind
termination_by sizeOf hir + sizeOf min + sizeOf (max - min) + 1

@[spec] theorem c_lookaround_spec (look : Lookaround) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_lookaround look
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_lookaround
  split
  case h_1 | h_2 =>
    mspec c_spec
    mspec
    inst_mvars
    all_goals simp_all
    all_goals grind
  case h_3 | h_4 =>
    mspec add_next_char_lift_spec
    inst_mvars
    case post.success =>
      mspec c_spec
      inst_mvars
      case post.success =>
        mspec
        inst_mvars
        case post.success => simp; intros; grind
        all_goals simp_all
        all_goals grind
      all_goals grind
    all_goals grind
termination_by sizeOf look

@[spec] theorem c_repetition_spec (rep : Repetition) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_repetition rep
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_repetition
  split
  case h_1 | h_2 =>
    mspec
    inst_mvars
    case post.success =>
      mspec c_spec
      inst_mvars
      case post.success =>
        mspec
        inst_mvars
        case post.success => mvcgen with grind
        all_goals grind
      all_goals grind
    all_goals grind
  case h_3 =>
    split
    · mspec
      inst_mvars
      case post.success =>
        mspec c_spec
        inst_mvars
        case post.success =>
          mspec
          inst_mvars
          case post.success => mvcgen with grind
          all_goals grind
        all_goals grind
      all_goals grind
    · mspec c_at_least_spec
  case h_4 =>
    split
    mspec c_bounded_spec
    inst_mvars
    intros
    mvcgen with grind
termination_by sizeOf rep

@[spec] theorem c_exactly_spec (hir : Hir) (n : Nat) (states : Array Unchecked.State)
   (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_exactly hir n
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_exactly
  split
  · mspec c_spec
    mspec c_exactly_fold_spec
    inst_mvars
    case isTrue.post.success.post.success => mvcgen with grind [= cValid, = cMemAndValid]
    all_goals grind
  · mspec c_empty_lift_spec
    inst_mvars
    case isFalse.post.success => mvcgen with grind
    all_goals grind
termination_by sizeOf hir + sizeOf n

@[spec] theorem c_concat_fold_spec (tail : Array Hir) (sid : Unchecked.StateID)
 (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ sid < states.size ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_concat.fold tail sid
      ⦃post⟨fun r s => ⌜stateIdNextOfLeLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_concat.fold
  mspec Spec.foldlM_array
  case inv =>
    exact (fun (xs, r) s => ⌜states.size ≤ s.1.size ∧ sid < s.1.size ∧ r < s.1.size ∧ NextOfLt s.1
                              ∧ cMemAndValid captures s.2.1⌝, fun e => ⌜true⌝, ())
  case step =>
    intros
    expose_names
    have := Array.sizeOf_lt_of_mem cur.property
    mintro _
    mspec c_spec
    inst_mvars
    case post.success =>
      mspec patch_lift_spec
      · inst_mvars
        all_goals grind
      · mvcgen
        grind [= cMemAndValid]
    all_goals grind
  case pre => simp_all
  simp_all
termination_by sizeOf tail

@[spec] theorem c_concat_spec (hirs : Array Hir) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_concat hirs
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_concat
  split
  expose_names
  have := Array.sizeOf_head?_of_mem heq
  have := Array.sizeOf_head?_of_tail heq
  mspec c_spec
  inst_mvars
  case h_1.post.success =>
    mspec c_concat_fold_spec
    inst_mvars
    case post.success =>
      mvcgen with grind [= cValid, = cMemAndValid]
    all_goals grind
  case h_2 =>
    mvcgen with grind
  all_goals grind
termination_by sizeOf hirs

@[spec] theorem c_alt_iter_fold_spec (hirs : Array Hir) (union «end» : Unchecked.StateID)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ union < states.size ∧ «end» < states.size ∧ NextOfLt states
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_alt_iter.fold hirs union «end»
      ⦃post⟨fun _ s => ⌜statesNextOfLeLt states s.1  ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_alt_iter.fold
  mspec Spec.foldlM_array
  case inv =>
    exact (fun (_, xs) s => ⌜states.size ≤ s.1.size ∧ union < s.1.size ∧ «end» < s.1.size
                              ∧ NextOfLt s.1 ∧ cMemAndValid captures s.2.1⌝, fun e => ⌜true⌝, ())
  case step =>
    intros
    expose_names
    have := Array.sizeOf_lt_of_mem cur.property
    mintro _
    mspec c_spec
    inst_mvars
    case post.success =>
      mspec patch_lift_spec
      inst_mvars
      case post.success =>
        mspec patch_lift_spec
        inst_mvars
        case post.success =>
          mvcgen with grind [= cMemAndValid]
        all_goals grind
      all_goals grind
    all_goals grind
  case pre =>
    simp_all
  case post =>
    simp_all
termination_by sizeOf hirs

@[spec] theorem c_alt_iter_spec (hirs : Array Hir) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_alt_iter hirs
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_alt_iter
  split
  case h_1 =>
    expose_names
    have := Array.sizeOf_head?_of_mem heq
    have := Array.sizeOf_head?_of_tail heq
    split
    case h_1 =>
      expose_names
      mspec c_spec
      have := Array.sizeOf_head?_of_mem heq_1
      have := Array.sizeOf_head?_of_tail heq_1
      mspec c_spec
      inst_mvars
      case post.success.post.success =>
        mspec c_alt_iter_step_lift_spec
        inst_mvars
        case post.success =>
          mspec c_alt_iter_fold_spec
          inst_mvars
          case post.success => mvcgen with grind [= cMemAndValid]
          all_goals grind
        all_goals grind
      all_goals grind
    case h_2 =>
      simp_all [wp]
  case h_2 =>
    simp_all [wp]
termination_by sizeOf hirs

@[spec] theorem c_exactly_fold_spec (hir : Hir) (n : Nat) («end» : Unchecked.StateID)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ «end» < states.size ∧  NextOfLt states
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_exactly.fold hir n «end»
      ⦃post⟨fun r s => ⌜stateIdNextOfLeLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_exactly.fold
  split
  mspec Spec.foldlM_list
  case inv =>
    exact (fun (xs, r) s => ⌜states.size ≤ s.1.size ∧ r < s.1.size ∧ «end» < s.1.size
                              ∧ NextOfLt s.1 ∧ cMemAndValid captures s.2.1⌝, fun e => ⌜true⌝, ())
  case step =>
    intros
    mintro _
    mspec c_spec
    inst_mvars
    case post.success =>
      mspec patch_lift_spec
      inst_mvars
      case post.success => mvcgen with grind [= cMemAndValid]
      all_goals grind
    all_goals grind
  all_goals simp_all
termination_by sizeOf hir + sizeOf n

@[spec] theorem c_at_least_spec (hir : Hir) (n : Nat) (greedy : Bool) (possessive : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_at_least hir n greedy possessive
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_at_least
  split
  case isTrue =>
    mspec c_spec
    mspec c_at_least_0_spec
    inst_mvars
    case post.success.post.success =>
      mspec c_at_least_0_post_lift_spec
      inst_mvars
      case post.success => mvcgen with grind
      all_goals grind
    all_goals grind
  case isFalse =>
    split
    mspec c_spec
    mspec c_at_least_1_spec
    inst_mvars
    case isTrue.post.success.post.success =>
      mspec c_at_least_1_post_lift_spec
      inst_mvars
      case post.success => simp; intros; grind
      all_goals grind
    case isFalse =>
      mspec c_exactly_spec
      mspec c_spec
      inst_mvars
      case post.success.post.success =>
        mspec c_at_least_2_lift_spec
        inst_mvars
        case post.success => simp; intros; grind [= cMemAndValid]
        all_goals grind
      all_goals grind
    all_goals grind
termination_by sizeOf hir + sizeOf n + 1

@[spec] theorem c_bounded_fold_spec  (hir : Hir) (n : Nat) («prefix» : ThompsonRef) (empty : Unchecked.StateID)
  (greedy : Bool) (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ tRefLt «prefix» states ∧ empty < states.size ∧ NextOfLt states
                 ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_bounded.fold hir n «prefix» empty greedy possessive
      ⦃post⟨fun r s => ⌜stateIdNextOfLeLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_bounded.fold
  split
  mspec Spec.foldlM_list
  case inv =>
    exact (fun (xs, r) s => ⌜states.size ≤ s.1.size ∧ r < s.1.size ∧ empty < s.1.size
                            ∧ NextOfLt s.1 ∧ cMemAndValid captures s.2.1⌝, fun e => ⌜true⌝, ())
  case step =>
    intros
    mintro _
    mspec c_spec
    inst_mvars
    case post.success =>
      mspec c_bounded.fold.patch_lift_spec
      inst_mvars
      case post.success => mvcgen with grind [= cMemAndValid]
      all_goals grind
    all_goals grind
  case pre =>
    intro _
    simp_all
  case isTrue =>
    intro _
    simp_all
  case isFalse =>
    intro _
    simp_all
termination_by sizeOf hir + sizeOf n

@[spec] theorem c_cap_spec (hir : Syntax.Capture) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_cap hir
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.c_cap
  split
  mspec c_cap'_start_spec
  mspec c_spec
  inst_mvars
  case h_1.post.success.post.success =>
    intros
    mspec c_cap'_end_spec
    inst_mvars
    case post.success =>
      mspec patch_lift_spec
      inst_mvars
      case post.success =>
        mspec patch_lift_spec
        inst_mvars
        case post.success => mvcgen with grind [= cValid, = cMemAndValid]
        all_goals grind
      all_goals grind
    simp_all
    all_goals grind [= cMemAndValid]
  all_goals grind
termination_by sizeOf hir

@[spec] theorem c_spec (hir : Hir) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c hir
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  have : sizeOf hir.kind < sizeOf hir := Hir.sizeOfKindOfHir hir
  mintro _
  unfold Code.c
  split
  · mspec c_empty_lift_spec
    inst_mvars; grind; grind; mvcgen with grind
  · mspec c_literal_lift_spec
    inst_mvars; grind; grind; mvcgen with grind
  · mspec c_unicode_class_lift_spec
    inst_mvars; grind; grind; mvcgen with grind
  · mspec c_look_lift_spec
    inst_mvars; grind; grind; mvcgen with grind
  · expose_names
    have : sizeOf look < sizeOf hir.kind := by simp [heq]
    mspec c_lookaround_spec
  · mspec c_back_ref_lift_spec
    inst_mvars; grind; grind; mvcgen with grind
  · expose_names
    have : sizeOf rep < sizeOf hir.kind := by simp [heq]
    mspec c_repetition_spec
  · expose_names
    have : sizeOf cap < sizeOf hir.kind := by simp [heq]
    mspec c_cap_spec
  · expose_names
    have : sizeOf items < sizeOf hir.kind := by simp [heq]
    mspec c_concat_spec
    grind
  · expose_names
    have : sizeOf sub < sizeOf hir.kind := by simp [heq]
    mspec c_alt_iter_spec
termination_by sizeOf hir

end

@[spec] theorem c_init_spec (anchored : Bool)
    : ⦃fun s => ⌜s.1.size = 0 ∧ s.2.1.size = 0⌝⦄
      Code.init anchored
      ⦃post⟨fun r s => ⌜tRefLt r s.1 ∧ NextOfLt s.1 ∧ cValid s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  mvcgen [Code.init] with exact #[]
  all_goals grind

@[spec] theorem c_compile_spec (anchored : Bool) (hir : Hir)
    : ⦃fun s => ⌜s.1.size = 0 ∧ s.2.1.size = 0⌝⦄
      Code.compile anchored hir
      ⦃post⟨fun _ s => ⌜NextOfLt s.1 ∧ cValid s.2.1⌝, fun _ => ⌜True⌝⟩⦄ := by
  mintro _
  unfold Code.compile
  mspec c_init_spec
  mspec c_cap_spec
  inst_mvars
  case success.post.success =>
    mspec add_match_lift_spec
    inst_mvars
    case post.success =>
      mspec patch_lift_spec
      inst_mvars
      case post.success =>
        mvcgen [patch_lift_spec]
        and_intros; rfl
        apply NextOfLt.mk
        all_goals (try rfl) <;> grind
      all_goals grind
    all_goals grind
  all_goals grind

theorem compile_nextOf_lt {anchored : Bool} {expr : Hir}
  (h : Code.compile anchored expr (#[], #[], #[]) = EStateM.Result.ok () (states, captures, groups))
    : NextOfLt states := by
  have heq := c_compile_spec anchored expr (#[], #[], #[])
  simp [wp] at heq
  split at heq <;> simp_all

theorem compile_captures_valid {anchored : Bool} {expr : Hir}
  (h : Code.compile anchored expr (#[], #[], #[]) = EStateM.Result.ok () (states, captures, groups))
    : Capture.Valid captures := by
  have heq := c_compile_spec anchored expr (#[], #[], #[])
  simp [wp] at heq
  split at heq <;> grind [= cValid]
