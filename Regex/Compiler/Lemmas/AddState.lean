import Std.Tactic.Do
import Std.Tactic.Do.Syntax

import Regex.Compiler.Basic
import Regex.Compiler.Patch
import Regex.Compiler.Compile
import Regex.Compiler.Lemmas.Basic
import Regex.Compiler.Lemmas.Patch

namespace Compiler

open Syntax
open NFA

namespace Lemmas

open Std.Do

set_option mvcgen.warning false

@[simp, grind] def isAppendOfState (sid : Unchecked.StateID) (state : Unchecked.State) (s1 s2 : Array Unchecked.State) :=
  s2 = s1 ++ #[state] ∧ s2[sid]? = some state

@[simp, grind] def isAppendOfStateID (sid : Unchecked.StateID) (s1 s2 : Array Unchecked.State) :=
  ∃ state, isAppendOfState sid state s1 s2

@[simp, grind] def assignableP (sid : Unchecked.StateID) (s1 s2 : Array Unchecked.State) :=
  patchAssignable s2 sid ∧ isAppendOfStateID sid s1 s2

@[simp, grind] def assignableP2 (sid : Unchecked.StateID) (s1 s2 : Array Unchecked.State) :=
  patch2Assignable s2 sid ∧ isAppendOfStateID sid s1 s2

@[simp, grind .] def pushPostCond (prevsid : Unchecked.State) (prevs : Array Unchecked.State) (sid : Unchecked.StateID) (s : Array Unchecked.State) :=
  stateIdNextOfLt prevs sid s ∧ isAppendOfState sid prevsid prevs s ∧ sid = prevs.size

@[simp, grind .] def pushPostCond' (prevsid : Unchecked.State) (prevs : Array Unchecked.State) (r : ThompsonRef) (s : Array Unchecked.State) :=
  tRefNextOfLt prevs r s ∧ isAppendOfState r.end prevsid prevs s ∧ r.end = prevs.size

@[simp, grind →] theorem isAppend_of_isAppendOfState (h : isAppendOfStateID sid1 s1 s2)
    : isAppend s1 s2 := by
  obtain ⟨state, h⟩ := h
  exact ⟨#[state], by grind⟩

@[simp, grind →] theorem isAppend_of_assignableP (h : assignableP sid1 s1 s2)
    : isAppend s1 s2 := by
  obtain ⟨state, h⟩ := h.right
  exact ⟨#[state], by grind⟩

@[simp, grind →] theorem isAppend_of_assignableP2 (h : assignableP2 sid1 s1 s2)
    : isAppend s1 s2 := by
  obtain ⟨state, h⟩ := h.right
  exact ⟨#[state], by grind⟩

@[spec] theorem push_spec (sid : Unchecked.State) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size⌝⦄
      Code.push sid
      ⦃post⟨fun r s => ⌜pushPostCond sid states r s⌝⟩⦄ := by
  mvcgen [Code.push] with grind

@[spec] theorem push_lift_spec (sid : Unchecked.State) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size⌝⦄
      (Code.push sid : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜pushPostCond sid states r s⌝, fun _ => ⌜False⌝ ⟩⦄ := by
  exact ↑(push_spec sid states)

@[spec] theorem push_run_spec (sid : Unchecked.State) (states : Array Unchecked.State)
  (h1 : NextOfLt states) (h2 : NFA.Unchecked.State.nextOf sid ≤ states.size)
  (h3 : State.patchAssignable sid)
    : ⦃⌜True⌝⦄
      ((Code.push sid).run states : Id (Unchecked.StateID × Array Unchecked.State))
      ⦃post⟨fun r => ⌜stateIdNextOfLt states r.1 r.2
                      ∧ assignableIf states r.2 ∧ assignableP r.1 states r.2⌝⟩⦄ := by
  mvcgen [Code.push]
  dsimp only [bind, StateT.bind, Functor.map, StateT.map, wp, Id.run]
  split
  rename_i heq
  dsimp only [MonadStateOf.get, StateT.get, pure] at heq
  dsimp only [set, StateT.set, StateT.pure, pure,stateIdNextOfLt, PredTrans.pure_apply,
    Array.size_push, Nat.lt_add_one, true_and, SPred.down_pure]
  simp
  and_intros
  case h_1.refine_2.refine_2.refine_1 => simp_all
  all_goals grind

@[spec] theorem push_run_lift_spec (sid : Unchecked.State) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s.1 = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size
                ∧ State.patchAssignable sid⌝⦄
      (Code.push sid states : Code.CompilerM (Unchecked.StateID × Array Unchecked.State))
      ⦃post⟨fun r _ => ⌜stateIdNextOfLt states r.1 r.2
                        ∧ assignableIf states r.2 ∧ assignableP r.1 states r.2⌝, fun _ => ⌜False⌝ ⟩⦄ := by
  mvcgen
  intros
  generalize h : (Code.push sid).run states = x
  apply Id.of_wp_run_eq h
  apply push_run_spec sid states <;> simp_all

@[simp, grind .]theorem push'_lt (state : Unchecked.State) (states : Array Unchecked.State)
    : states.size < (Code.push' state states).snd.size := by
  simp [Code.push']
  simp only [get, getThe, MonadStateOf.get, set, Functor.map, bind, StateT.bind, StateT.get, pure,
    StateT.map, StateT.set, Array.size_push, Nat.lt_add_one]

@[spec] theorem push'_spec (sid : Unchecked.State) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size⌝⦄
      Code.push' sid
      ⦃post⟨fun r s => ⌜pushPostCond' sid states r s⌝⟩⦄ := by
  mvcgen [Code.push'] with grind

@[simp, grind .]theorem append_of_push (s s_1 : Array Unchecked.State)
  (r : Unchecked.StateID) (h_1 : r < s_1.size)
  (h_2 : s_1 = s.push state) (h_3 : s_1[r]? = some state)
    : ∃ state, s_1 = s.push state ∧ s_1[r]? = some state := by
  exact ⟨s_1[r], by grind⟩

@[simp, grind .]theorem assignableIfP_of_push (s s_1 : Array Unchecked.State)
  (r : Unchecked.StateID) (h_1 : r < s_1.size) (hs : State.patchAssignable state)
  (h_2 : s_1 = s.push state) (h_3 : s_1[r]? = some state)
    : (∃ state, s_1 = s.push state ∧ s_1[r]? = some state) ∧
       (∀ (sid : Fin s_1.size), patchAssignable s ↑sid → patchAssignable s_1 ↑sid) ∧
        ∀ (sid : Fin s_1.size), ¬↑sid = s.size
            → patch2Assignable s ↑sid → patch2Assignable s_1 ↑sid := by
  and_intros <;> grind

@[simp, grind .]theorem assignableIfP_of_push' (s s_1 : Array Unchecked.State)
  (r : ThompsonRef) (h_2 : r.end < s_1.size) (hs : State.patchAssignable state)
  (h_4 : s_1 = s.push state) (h_5 : s_1[r.end]? = some state)
    : (∃ state, s_1 = s.push state ∧ s_1[r.end]? = some state) ∧
       (∀ (sid : Fin s_1.size), patchAssignable s ↑sid → patchAssignable s_1 ↑sid) ∧
        ∀ (sid : Fin s_1.size), ¬↑sid = s.size
            → patch2Assignable s ↑sid → patch2Assignable s_1 ↑sid := by
  exact assignableIfP_of_push s s_1 r.end h_2 hs h_4 h_5

@[spec] theorem add_match_spec (pattern_id : PatternID) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_match pattern_id
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s⌝⟩⦄ := by
  mvcgen [Code.add_match]
  with grind

@[spec] theorem add_match_lift_spec (pattern_id : PatternID) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.add_match pattern_id : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜(stateIdNextOfLt states r s.1 ∧ assignableIf states s.1) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝ , fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (add_match_spec _ _)

@[spec] theorem add_union_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_union
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s⌝⟩⦄ := by
  mvcgen [Code.add_union]
  with grind

@[spec] theorem add_union_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_union : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact ↑(add_union_spec states)

@[spec] theorem add_union_lift_spec' (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.add_union : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜(stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ assignableP r states s.1) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (add_union_spec _)

@[spec] theorem add_union_reverse_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_union_reverse
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableP r states s⌝⟩⦄ := by
  mvcgen [Code.add_union_reverse]
  with grind

@[spec] theorem add_union_reverse_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_union_reverse : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableP r states s⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact ↑(add_union_reverse_spec states)

@[spec] theorem add_backrefence_spec (case_insensitive : Bool) (b : Nat) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_backrefence case_insensitive b
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s⌝⟩⦄ := by
  mvcgen [Code.add_backrefence]
  with grind

@[spec] theorem add_backrefence_lift_spec (case_insensitive : Bool) (b : Nat) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_backrefence case_insensitive b : (EStateM String (Array Unchecked.State) Unchecked.StateID))
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact ↑(add_backrefence_spec case_insensitive b states)

@[spec] theorem c_range_spec (start «end» : UInt32) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_range start «end»
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s ∧ assignableIf states s ∧ assignableP r.end states s⌝⟩⦄ := by
  mvcgen [Code.c_range]
  with grind

@[spec] theorem add_empty_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_empty
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s⌝⟩⦄ := by
  mvcgen [Code.add_empty]
  with grind

@[spec] theorem add_empty_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_empty : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact ↑(add_empty_spec states)

theorem add_empty_lift_spec' (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.add_empty : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜(stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ assignableP r states s.1)
          ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (add_empty_spec _)

@[spec] theorem add_fail_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_fail
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ isAppendOfStateID r states s⌝⟩⦄ := by
  mvcgen [Code.add_fail]
  with grind

@[spec] theorem add_fail_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_fail : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ isAppendOfStateID r states s⌝, fun _ => ⌜False⌝⟩⦄ := by
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

@[simp, grind .] theorem patch2Assignable_of_eat_state (states : Array Unchecked.State)
  (sid sid': Unchecked.StateID) (hlt : sid < states.size)
  (heq : states[sid]? = some (Unchecked.State.Eat mode sid'))
    : patch2Assignable states sid := by
  simp [patch2Assignable]
  exact ⟨hlt, by
    split; grind; grind; simp_all; simp_all
    cases mode <;> simp_all⟩

@[spec] theorem add_eat_spec (mode : Unchecked.EatMode) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ (mode.nextOf < states.size)⌝⦄
      Code.add_eat mode
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP2 r states s⌝⟩⦄ := by
  mvcgen [Code.add_eat]
  with grind
  simp_all [@eat_next_of_le mode states (by simp_all)]

@[spec] theorem add_eat_lift_spec (mode : Unchecked.EatMode) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ (mode.nextOf < states.size)⌝⦄
      (Code.add_eat mode : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP2 r states s⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact ↑(add_eat_spec mode states)

@[simp, grind .] theorem patch2Assignable_of_state (states : Array Unchecked.State)
  (sid: Unchecked.StateID) (hlt : sid < states.size) (h : State.patch2Assignable state)
  (heq : states[sid]? = some (state))
    : patch2Assignable states sid := by
  simp [patch2Assignable]
  exact ⟨hlt, by split; grind; grind; simp_all; simp_all; simp_all⟩

@[simp, grind .] theorem patch2Assignable_of_add_change_state (states : Array Unchecked.State)
  (sid: Unchecked.StateID) (hlt : sid < states.size)
  (heq : states[sid]? = some (Unchecked.State.ChangeFrameStep 0 0))
    : patch2Assignable states sid := by
  exact @patch2Assignable_of_state (Unchecked.State.ChangeFrameStep 0 0) states sid hlt (by grind) heq

@[spec] theorem add_change_state_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ 0 < states.size⌝⦄
      Code.add_change_state
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP2 r states s⌝⟩⦄ := by
  mvcgen [Code.add_change_state]
  with grind

@[spec] theorem add_change_state_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ 0 < states.size⌝⦄
      (Code.add_change_state : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP2 r states s⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact ↑(add_change_state_spec states)

@[spec] theorem add_remove_state_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_remove_state
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s⌝⟩⦄ := by
  mvcgen [Code.add_remove_state]
  with grind

@[spec] theorem add_remove_state_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (Code.add_remove_state : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact ↑(add_remove_state_spec states)

@[spec] theorem add_next_char_spec (offset : Nat) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.add_next_char offset
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s⌝⟩⦄ := by
  mvcgen [Code.add_next_char]
  with grind

@[spec] theorem add_next_char_lift_spec (offset : Nat) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.add_next_char offset : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜(stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ assignableP r states s.1)
              ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (add_next_char_spec _ _)

@[spec] theorem c_empty_spec (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_empty
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s ∧ assignableP r.end states s⌝⟩⦄ := by
  mvcgen [Code.c_empty]
  with grind

@[spec] theorem c_empty_lift_spec (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_empty : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLt states r s.1 ∧ assignableP r.end states s.1)
              ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (c_empty_spec _)

@[spec] theorem add_sparse_spec (trans : Array Unchecked.Transition) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states ∧ ∀ (i : Nat) _, trans[i].next ≤ states.size⌝⦄
      Code.add_sparse trans
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r⌝⟩⦄ := by
  mvcgen [Code.add_sparse] with grind
  and_intros; grind; grind
  exact nextOf_transition_le_of_le _ trans (by grind)

@[spec] theorem c_unicode_class_spec (cls : ClassUnicode) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_unicode_class cls
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝⟩⦄ := by
  mvcgen [Code.c_unicode_class] with grind

@[spec] theorem c_unicode_class_lift_spec (cls : ClassUnicode) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_unicode_class cls : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (c_unicode_class_spec _ _)

@[spec] theorem c_literal_spec (c : Char) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_literal c
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s ∧ assignableIf states s ∧ assignableP r.end states s⌝⟩⦄ := by
  mvcgen [Code.c_literal]

@[spec] theorem c_literal_lift_spec (c : Char) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_literal c : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ assignableP r.end states s.1)
            ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (c_literal_spec _ _)

@[spec] theorem c_look_spec (look : Syntax.Look) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_look look
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s ∧ assignableP r.end states s⌝ ⟩⦄ := by
  cases look <;> (mvcgen [Code.c_look]; and_intros; grind; grind; grind; simp; all_goals grind)

@[spec] theorem c_look_lift_spec (look : Syntax.Look) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_look look : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLt states r s.1 ∧ assignableP r.end states s.1)
             ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_StateT_to_CompilerM (c_look_spec _ _)

@[spec] theorem c_possessive_spec (tref : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tref.start < states.size
                      ∧ tref.end < states.size ∧ NextOfLt states
                      ∧ patchAssignable states tref.end⌝⦄
      Code.c_possessive tref
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_possessive] with grind

@[spec] theorem c_possessive_lift_spec (tref : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tref.start < states.size ∧ tref.end < states.size
                    ∧ NextOfLt states ∧ patchAssignable states tref.end)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_possessive tref : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end)
            ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_possessive_spec _ _)

theorem tref_le_of_lt_spec (states : Array Unchecked.State)
    : ∀ (tref : ThompsonRef),
      ⦃fun s => ⌜(tRefNextOfLt states tref s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 tref.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝⦄
      (EStateM.pure tref : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  intro tref
  apply pure_of_imp_spec (by grind)

-- relax postcondition of c_possessive_lift_spec
theorem c_possessive_le_lift_spec (tref : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tref.start < states.size ∧ tref.end < states.size
                    ∧ NextOfLt states ∧ patchAssignable states tref.end)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_possessive tref : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  have := Triple.bind _ _ (c_possessive_lift_spec tref states captures) (tref_le_of_lt_spec states)
  rwa [lift_CompilerM_bind_pure (Code.c_possessive tref)] at this

@[spec] theorem c_cap'_start_spec (group : Nat) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_cap' Capture.Role.Start group
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1
                        ∧ assignableIf states s.1 ∧ assignableP r states s.1
                        ∧ cMemAndValid captures s.2.1
                        ∧ (NFA.Capture.mk Capture.Role.Start group) ∈ s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_cap']
  and_intros; all_goals grind

@[spec] theorem c_cap'_end_spec (group : Nat) (states : Array Unchecked.State)
  (captures : Array NFA.Capture) (h : ∃ c ∈ captures, c.role = Capture.Role.Start ∧ c.group = group)
    : ⦃fun s => ⌜s.1 = states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_cap' Capture.Role.End group
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1
                      ∧ assignableIf states s.1 ∧ assignableP r states s.1
                      ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_cap'] with grind

@[spec] theorem c_back_ref_spec (case_insensitive : Bool) (n : Nat)  (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_back_ref case_insensitive n
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_back_ref] with grind

@[spec] theorem c_back_ref_lift_spec (case_insensitive : Bool) (n : Nat)  (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_back_ref case_insensitive n : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end)
                        ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_back_ref_spec _ _ _)

@[spec] theorem c_lookaround_PositiveLookahead_spec (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states ∧ NextOfLt states ∧ patchAssignable states compiled.end⌝⦄
      Code.c_lookaround_PositiveLookahead compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_lookaround_PositiveLookahead] with grind

@[spec] theorem c_lookaround_PositiveLookahead_lift_spec (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states ∧ patchAssignable states compiled.end)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_lookaround_PositiveLookahead compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_lookaround_PositiveLookahead_spec _ _)

@[spec] theorem c_lookaround_NegativeLookahead_spec (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states ∧ NextOfLt states ∧ patchAssignable states compiled.end⌝⦄
      Code.c_lookaround_NegativeLookahead compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_lookaround_NegativeLookahead] with grind

@[spec] theorem c_lookaround_NegativeLookahead_lift_spec (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states ∧ patchAssignable states compiled.end)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_lookaround_NegativeLookahead compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end)
            ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_lookaround_NegativeLookahead_spec _ _)

@[spec] theorem c_lookaround_PositiveLookbehind_spec (next_char : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                   ∧ patchAssignable states next_char ∧ patchAssignable states compiled.end⌝⦄
      Code.c_lookaround_PositiveLookbehind next_char compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s ∧ assignableIf states s  ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_lookaround_PositiveLookbehind] with grind

@[spec] theorem c_lookaround_PositiveLookbehind_lift_spec (next_char : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                  ∧ patchAssignable states next_char ∧ patchAssignable states compiled.end) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_lookaround_PositiveLookbehind next_char compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1  ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_lookaround_PositiveLookbehind_spec _ _ _)

set_option maxHeartbeats 500000 in
@[spec] theorem c_lookaround_NegativeLookbehind_spec (next_char : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                  ∧ patchAssignable states next_char ∧ patchAssignable states compiled.end⌝⦄
      Code.c_lookaround_NegativeLookbehind next_char compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_lookaround_NegativeLookbehind] with grind
  and_intros
  all_goals grind only [→ isAppend_of_assignableP, assignableP, → patchAssignable_of_append,
      patchAssignable_of_assignableIf, assignableIf_trans,
      = stateIdNextOfLt.eq_1, = stateIdNextOfEqLt.eq_1,
      patch2Assignable_of_assignableIf]

@[spec] theorem c_lookaround_NegativeLookbehind_lift_spec (next_char : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                    ∧ patchAssignable states next_char ∧ patchAssignable states compiled.end)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_lookaround_NegativeLookbehind next_char compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_lookaround_NegativeLookbehind_spec _ _ _)

@[spec] theorem c_repetition_0_some_1_false_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                    ∧ patchAssignable states union ∧ patchAssignable states compiled.end⌝⦄
      Code.c_repetition_0_some_1_false union compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_repetition_0_some_1_false] with grind

@[spec] theorem c_repetition_0_some_1_false_lift_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                  ∧ patchAssignable states union ∧ patchAssignable states compiled.end)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_repetition_0_some_1_false union compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_repetition_0_some_1_false_spec _ _ _)

@[spec] theorem c_repetition_0_some_1_true_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                  ∧ patchAssignable states union ∧ patchAssignable states compiled.end⌝⦄
      Code.c_repetition_0_some_1_true union compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_repetition_0_some_1_true] with grind

@[spec] theorem c_repetition_0_some_1_true_lift_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                    ∧ patchAssignable states union ∧ patchAssignable states compiled.end)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_repetition_0_some_1_true union compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_repetition_0_some_1_true_spec _ _ _)

@[spec] theorem c_repetition_0_none_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                  ∧ patchAssignable states union ∧ patchAssignable states compiled.end⌝⦄
      Code.c_repetition_0_none union compiled
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_repetition_0_none] with grind

@[spec] theorem c_repetition_0_none_lift_spec (union : Unchecked.StateID) (compiled : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                    ∧ patchAssignable states union ∧ patchAssignable states compiled.end)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_repetition_0_none union compiled : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_repetition_0_none_spec _ _ _)

@[spec] theorem greedy_union_spec (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      (if greedy then Code.add_union else Code.add_union_reverse : Code.PatchM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  dsimp [Code.add_union, Code.add_union_reverse]
  intros
  split <;> (mspec push_lift_spec; grind; simp; intros; and_intros; all_goals grind)

@[spec] theorem c_at_least_0_pre_spec (compiled : ThompsonRef) (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states ∧ NextOfLt states ∧ patchAssignable states compiled.end⌝⦄
      Code.c_at_least_0_pre compiled greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_at_least_0_pre]
  case vc12 => and_intros; all_goals grind
  all_goals grind

@[spec] theorem c_at_least_0_pre_lift_spec (compiled : ThompsonRef) (greedy : Bool) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states ∧ patchAssignable states compiled.end)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_at_least_0_pre compiled greedy : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜(stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_at_least_0_pre_spec _ _ _)

@[spec] theorem c_at_least_set_spec (possible_empty_capture_group : Option Nat) (greedy : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture) {groups : Array Nat}
    : ⦃fun s => ⌜s.1 = states ∧ s.2.1 = captures ∧ s.2.2 = groups⌝⦄
      Code.c_at_least_set possible_empty_capture_group greedy
      ⦃post⟨fun _ s => ⌜states = s.1 ∧ s.2.1 = captures ∧ groups.size ≤ s.2.2.size ∧ assignableIf states s.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_at_least_set]
  with grind

@[spec] theorem c_at_least_0_post_spec (compiled : ThompsonRef) (plus : Unchecked.StateID) (greedy : Bool)
  (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ plus < states.size ∧ compiled.start < states.size ∧ NextOfLt states
                 ∧ patchAssignable states compiled.end  ∧ patchAssignable states plus⌝⦄
      Code.c_at_least_0_post compiled plus greedy possessive
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_at_least_0_post]
  case vc23 => intros; and_intros; all_goals grind
  case vc24 => and_intros; all_goals grind
  all_goals grind

@[spec] theorem c_at_least_0_post_lift_spec (compiled : ThompsonRef) (plus : Unchecked.StateID) (greedy : Bool)
  (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ plus < states.size ∧ compiled.start < states.size ∧ NextOfLt states
                      ∧ patchAssignable states compiled.end  ∧ patchAssignable states plus)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_at_least_0_post compiled plus greedy possessive : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_at_least_0_post_spec _ _ _ _ _)

@[spec] theorem c_at_least_0_spec (compiled : ThompsonRef) (possible_empty_capture_group : Option Nat) (greedy : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states ∧ patchAssignable states compiled.end ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_at_least_0 compiled possible_empty_capture_group greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_at_least_0]
  with grind

@[spec] theorem c_at_least_1_pre_spec (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_at_least_1_pre greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  dsimp [Code.c_at_least_1_pre]
  intros
  mspec greedy_union_spec

@[spec] theorem c_at_least_1_pre_lift_spec (greedy : Bool) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_at_least_1_pre greedy : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜(stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_at_least_1_pre_spec _ _)

@[spec] theorem c_at_least_1_post_spec (compiled : ThompsonRef) (union : Unchecked.StateID)
  (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
              ∧ patchAssignable states compiled.end ∧ patchAssignable states union⌝⦄
      Code.c_at_least_1_post compiled union possessive
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_at_least_1_post] with grind

@[spec] theorem c_at_least_1_post_lift_spec (compiled : ThompsonRef) (union : Unchecked.StateID)
  (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                   ∧ patchAssignable states compiled.end ∧ patchAssignable states union)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_at_least_1_post compiled union possessive : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_at_least_1_post_spec _ _ _ _)

@[spec] theorem c_at_least_1_spec (possible_empty_capture_group : Option Nat) (greedy : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_at_least_1 possible_empty_capture_group greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_at_least_1]
  with grind

@[spec] theorem c_at_least_2_spec («prefix» last : ThompsonRef) (greedy : Bool)
  (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt «prefix» states ∧ tRefLt last states ∧ NextOfLt states
                ∧ patchAssignable states «prefix».end ∧ patchAssignable states last.end⌝⦄
      Code.c_at_least_2 «prefix» last greedy possessive
      ⦃post⟨fun r s => ⌜tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_at_least_2]
  case vc17 => intros; and_intros; all_goals grind
  case vc18 => and_intros; all_goals grind
  all_goals grind

@[spec] theorem c_at_least_2_lift_spec («prefix» last : ThompsonRef) (greedy : Bool)
  (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt «prefix» states ∧ tRefLt last states ∧ NextOfLt states
                  ∧ patchAssignable states «prefix».end ∧ patchAssignable states last.end)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_at_least_2 «prefix» last greedy possessive : Code.CompilerM ThompsonRef)
      ⦃post⟨fun r s => ⌜(tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_at_least_2_spec _ _ _ _ _)
