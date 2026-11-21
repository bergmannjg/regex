module

public import Std.WP

public import Regex.Compiler.Basic
public import Regex.Compiler.Patch
public import Regex.Compiler.Compile
public import Regex.Compiler.Lemmas.Basic
public import Regex.Compiler.Lemmas.Patch

@[expose] public section

namespace Compiler

open NFA

namespace Lemmas

open Std.WP

set_option experimental.vcgen true

@[simp, grind] def isAppendOfState (sid : Unchecked.StateID) (state : Unchecked.State)
    (s1 s2 : Array Unchecked.State) :=
  s2 = s1 ++ #[state] ∧ s2[sid]? = some state

@[simp, grind] def isAppendOfStateID (sid : Unchecked.StateID) (s1 s2 : Array Unchecked.State) :=
  ∃ state, isAppendOfState sid state s1 s2

@[simp, grind] def assignableP (sid : Unchecked.StateID) (s1 s2 : Array Unchecked.State) :=
  patchAssignable s2 sid ∧ isAppendOfStateID sid s1 s2

@[simp, grind] def assignableP2 (sid : Unchecked.StateID) (s1 s2 : Array Unchecked.State) :=
  patch2Assignable s2 sid ∧ isAppendOfStateID sid s1 s2

@[simp, grind .] def pushPostCond (prevsid : Unchecked.State) (prevs : Array Unchecked.State)
    (sid : Unchecked.StateID) (s : Array Unchecked.State) :=
  stateIdNextOfLt prevs sid s ∧ isAppendOfState sid prevsid prevs s ∧ sid = prevs.size

@[simp, grind .] def pushPostCond' (prevsid : Unchecked.State) (prevs : Array Unchecked.State)
    (r : ThompsonRef) (s : Array Unchecked.State) :=
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
    : ⦃fun s => s = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size⦄
      Code.push sid
      ⦃fun r s => pushPostCond sid states r s⦄ := by
  vcgen [Code.push]
  simp
  and_intros
  all_goals try grind only [all_push]
  simp [NextOfLt.iff]
  grind

@[spec] theorem push_lift_spec (sid : Unchecked.State) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size⦄
      (Code.push sid : Code.PatchM Unchecked.StateID)
      ⦃fun r s => pushPostCond sid states r s; fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_PatchM (push_spec sid states)
@[simp] theorem push_run_eq (sid : Unchecked.State) (states : Array Unchecked.State)
    : (Code.push sid).run states = (states.size, states.push sid) := rfl

@[simp, grind =] theorem push_run_run_eq (sid : Unchecked.State) (states : Array Unchecked.State)
    : ((Code.push sid).run states).run = (states.size, states.push sid) := rfl

@[simp, grind =] theorem push_apply_run_eq (sid : Unchecked.State)
  (states : Array Unchecked.State)
    : (Code.push sid states).run = (states.size, states.push sid) := rfl

private theorem assignable_of (sid : Unchecked.State) (states : Array Unchecked.State)
  (h1 : NextOfLt states) (h2 : NFA.Unchecked.State.nextOf sid ≤ states.size)
  (h3 : State.patchAssignable sid)
    : stateIdNextOfLt states states.size (states.push sid)
      ∧ assignableIf states (states.push sid)
      ∧ assignableP states.size states (states.push sid) := by
  simp only [stateIdNextOfLt, assignableIf, assignableP, isAppendOfStateID, isAppendOfState,
    Array.append_singleton, Array.size_push, Nat.lt_add_one, true_and, getElem?_pos,
    Array.getElem_push_eq]
  and_intros
  all_goals grind [patchAssignable]

@[spec] theorem push_run_spec (sid : Unchecked.State) (states : Array Unchecked.State)
  (h1 : NextOfLt states) (h2 : NFA.Unchecked.State.nextOf sid ≤ states.size)
  (h3 : State.patchAssignable sid)
    : ⦃True⦄
      ((Code.push sid).run states : Id (Unchecked.StateID × Array Unchecked.State))
      ⦃fun r => stateIdNextOfLt states r.1 r.2
                      ∧ assignableIf states r.2 ∧ assignableP r.1 states r.2⦄ := by
  refine ⟨fun _ => ?_⟩
  simp only [WP.wp, WP.trans, push_run_eq]
  exact assignable_of sid states h1 h2 h3

@[spec] theorem push_run_lift_spec (sid : Unchecked.State) (states : Array Unchecked.State)
    : ⦃fun s => s.1 = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size
                ∧ State.patchAssignable sid⦄
      (Code.push sid states : Code.CompilerM (Unchecked.StateID × Array Unchecked.State))
      ⦃fun r _ => stateIdNextOfLt states r.1 r.2
                        ∧ assignableIf states r.2 ∧ assignableP r.1 states r.2;
                  fun _ _ => False⦄ := by
  vcgen with finish [assignable_of]

@[simp, grind .]theorem push'_lt (state : Unchecked.State) (states : Array Unchecked.State)
    : states.size < (Code.push' state states).snd.size := by
  simp [Code.push']
  simp only [get, getThe, MonadStateOf.get, set, Functor.map, bind, StateT.bind, StateT.get, pure,
    StateT.map, StateT.set, Array.size_push, Nat.lt_add_one]

@[spec] theorem push'_spec (sid : Unchecked.State) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states ∧ NFA.Unchecked.State.nextOf sid ≤ states.size⦄
      Code.push' sid
      ⦃fun r s => pushPostCond' sid states r s⦄ := by
  vcgen [Code.push']
  simp
  grind

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
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.add_match pattern_id
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s⦄ := by
  vcgen [Code.add_match] with finish [Unchecked.State.nextOf]

@[spec] theorem add_match_lift_spec (pattern_id : PatternID) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.add_match pattern_id : Code.CompilerM Unchecked.StateID)
      ⦃fun r s => (stateIdNextOfLt states r s.1 ∧ assignableIf states s.1)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_CompilerM (add_match_spec _ _)

@[spec] theorem add_union_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.add_union
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s
                  ∧ assignableP r states s⦄ := by
  vcgen [Code.add_union] with finish [Unchecked.State.nextOf]

@[spec] theorem add_union_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      (Code.add_union : Code.PatchM Unchecked.StateID)
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s;
                  fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_PatchM (add_union_spec states)
@[spec] theorem add_union_lift_spec' (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.add_union : Code.CompilerM Unchecked.StateID)
      ⦃fun r s => (stateIdNextOfLt states r s.1 ∧ assignableIf states s.1
                    ∧ assignableP r states s.1)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_CompilerM (add_union_spec _)

@[spec] theorem add_union_reverse_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.add_union_reverse
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s
                  ∧ assignableP r states s⦄ := by
  vcgen [Code.add_union_reverse] with finish [Unchecked.State.nextOf]

@[spec] theorem add_union_reverse_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      (Code.add_union_reverse : Code.PatchM Unchecked.StateID)
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s;
                  fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_PatchM (add_union_reverse_spec states)
@[spec] theorem add_backrefence_spec (case_insensitive : Bool) (b : Nat)
  (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.add_backrefence case_insensitive b
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s
                  ∧ assignableP r states s⦄ := by
  vcgen [Code.add_backrefence] with finish [Unchecked.State.nextOf]

@[spec] theorem add_backrefence_lift_spec (case_insensitive : Bool) (b : Nat)
  (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      (Code.add_backrefence case_insensitive b
        : (EStateM String (Array Unchecked.State) Unchecked.StateID))
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s;
                  fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_PatchM (add_backrefence_spec case_insensitive b states)
@[spec] theorem c_range_spec (start «end» : UInt32) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.c_range start «end»
      ⦃fun r s => tRefNextOfLt states r s ∧ assignableIf states s
                  ∧ assignableP r.end states s⦄ := by
  vcgen [Code.c_range] with finish [Unchecked.State.nextOf]

@[spec] theorem add_empty_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.add_empty
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s
                  ∧ assignableP r states s⦄ := by
  vcgen [Code.add_empty] with finish [Unchecked.State.nextOf]

@[spec] theorem add_empty_lift_PatchM_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      (Code.add_empty : Code.PatchM Unchecked.StateID)
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s;
                  fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_PatchM (add_empty_spec states)

theorem add_empty_lift_CompilerM_spec (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.add_empty : Code.CompilerM Unchecked.StateID)
      ⦃fun r s => (stateIdNextOfLt states r s.1 ∧ assignableIf states s.1
                    ∧ assignableP r states s.1)
          ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_CompilerM (add_empty_spec _)

@[spec] theorem add_fail_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.add_fail
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s
                  ∧ isAppendOfStateID r states s⦄ := by
  vcgen [Code.add_fail] with finish [Unchecked.State.nextOf]

@[spec] theorem add_fail_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      (Code.add_fail : Code.PatchM Unchecked.StateID)
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s
                  ∧ isAppendOfStateID r states s; fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_PatchM (add_fail_spec states)
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
    : ⦃fun s => s = states ∧ NextOfLt states ∧ (mode.nextOf < states.size)⦄
      Code.add_eat mode
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s
                  ∧ assignableP2 r states s⦄ := by
  vcgen [Code.add_eat]
  case vc2 => rename_i h; obtain ⟨rfl, -, h⟩ := h; exact eat_next_of_le _ h
  all_goals grind [Unchecked.State.nextOf]

@[spec] theorem add_eat_lift_spec (mode : Unchecked.EatMode) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states ∧ (mode.nextOf < states.size)⦄
      (Code.add_eat mode : Code.PatchM Unchecked.StateID)
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP2 r states s;
                  fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_PatchM (add_eat_spec mode states)
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
  exact @patch2Assignable_of_state (Unchecked.State.ChangeFrameStep 0 0) states sid hlt
    (by grind) heq

@[spec] theorem add_change_state_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states ∧ 0 < states.size⦄
      Code.add_change_state
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s
                  ∧ assignableP2 r states s⦄ := by
  vcgen [Code.add_change_state] with finish [Unchecked.State.nextOf]

@[spec] theorem add_change_state_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states ∧ 0 < states.size⦄
      (Code.add_change_state : Code.PatchM Unchecked.StateID)
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP2 r states s;
                  fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_PatchM (add_change_state_spec states)
@[spec] theorem add_remove_state_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.add_remove_state
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s
                  ∧ assignableP r states s⦄ := by
  vcgen [Code.add_remove_state] with finish [Unchecked.State.nextOf]

@[spec] theorem add_remove_state_lift_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      (Code.add_remove_state : Code.PatchM Unchecked.StateID)
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ assignableP r states s;
                  fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_PatchM (add_remove_state_spec states)
@[spec] theorem add_next_char_spec (offset : Nat) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.add_next_char offset
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s
                  ∧ assignableP r states s⦄ := by
  vcgen [Code.add_next_char] with finish [Unchecked.State.nextOf]

@[spec] theorem add_next_char_lift_spec (offset : Nat) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.add_next_char offset : Code.CompilerM Unchecked.StateID)
      ⦃fun r s => (stateIdNextOfLt states r s.1 ∧ assignableIf states s.1
                    ∧ assignableP r states s.1)
              ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_CompilerM (add_next_char_spec _ _)

@[spec] theorem c_empty_spec (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.c_empty
      ⦃fun r s => tRefNextOfLt states r s ∧ assignableP r.end states s⦄ := by
  vcgen [Code.c_empty] with finish [Unchecked.State.nextOf]

@[spec] theorem c_empty_lift_spec (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_empty : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLt states r s.1 ∧ assignableP r.end states s.1)
              ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_CompilerM (c_empty_spec _)

@[spec] theorem add_sparse_spec (trans : Array Unchecked.Transition)
  (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states ∧ ∀ (i : Nat) _, trans[i].next ≤ states.size⦄
      Code.add_sparse trans
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r⦄ := by
  vcgen [Code.add_sparse]
  case vc2 => rename_i h; obtain ⟨rfl, -, h⟩ := h; exact nextOf_transition_le_of_le _ trans h
  all_goals grind [Unchecked.State.nextOf]

@[spec] theorem c_unicode_class_spec (cls : Regex.Syntax.ClassUnicode)
  (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.c_unicode_class cls
      ⦃fun r s => tRefNextOfLt states r s ∧ assignableIf states s
                  ∧ patchAssignable s r.end⦄ := by
  vcgen [Code.c_unicode_class] with finish [Unchecked.State.nextOf]

@[spec] theorem c_unicode_class_lift_spec (cls : Regex.Syntax.ClassUnicode)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_unicode_class cls : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_CompilerM (c_unicode_class_spec _ _)

@[spec] theorem c_literal_spec (c : Char) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.c_literal c
      ⦃fun r s => tRefNextOfLt states r s ∧ assignableIf states s
                  ∧ assignableP r.end states s⦄ := by
  vcgen [Code.c_literal] with finish [Unchecked.State.nextOf]

@[spec] theorem c_literal_lift_spec (c : Char) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_literal c : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLt states r s.1 ∧ assignableIf states s.1
                    ∧ assignableP r.end states s.1)
            ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_CompilerM (c_literal_spec _ _)

@[spec] theorem c_look_spec (look : Regex.Syntax.Look) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.c_look look
      ⦃fun r s => tRefNextOfLt states r s ∧ assignableP r.end states s⦄ := by
  vcgen [Code.c_look] with finish [Unchecked.State.nextOf]

@[spec] theorem c_look_lift_spec (look : Regex.Syntax.Look) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_look look : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLt states r s.1 ∧ assignableP r.end states s.1)
             ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_StateT_to_CompilerM (c_look_spec _ _)

@[spec] theorem c_possessive_spec (tref : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ tref.start < states.size
                      ∧ tref.end < states.size ∧ NextOfLt states
                      ∧ patchAssignable states tref.end⦄
      Code.c_possessive tref
      ⦃fun r s => tRefNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_possessive] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_possessive_lift_spec (tref : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ tref.start < states.size ∧ tref.end < states.size
                    ∧ NextOfLt states ∧ patchAssignable states tref.end)
                  ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_possessive tref : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end)
            ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_possessive_spec _ _)

-- relax postcondition of c_possessive_lift_spec
theorem c_possessive_le_lift_spec (tref : ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ tref.start < states.size ∧ tref.end < states.size
                    ∧ NextOfLt states ∧ patchAssignable states tref.end)
                ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_possessive tref : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact ⟨Triple.entails_wp_of_post (c_possessive_lift_spec tref states captures)
    (fun _ _ h => by grind)⟩

@[spec] theorem c_cap'_start_spec (group : Nat) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_cap' Capture.Role.Start group
      ⦃fun r s => stateIdNextOfLt states r s.1
                        ∧ assignableIf states s.1 ∧ assignableP r states s.1
                        ∧ cMemAndValid captures s.2.1
                        ∧ (NFA.Capture.mk Capture.Role.Start group) ∈ s.2.1;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_cap'] with finish [assignable_of, cMemAndValid]

@[spec] theorem c_cap'_end_spec (group : Nat) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
  (h : ∃ c ∈ captures, c.role = Capture.Role.Start ∧ c.group = group)
    : ⦃fun s => s.1 = states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_cap' Capture.Role.End group
      ⦃fun r s => stateIdNextOfLt states r s.1
                      ∧ assignableIf states s.1 ∧ assignableP r states s.1
                      ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  vcgen [Code.c_cap'] with finish [assignable_of, cMemAndValid]

@[spec] theorem c_back_ref_spec (case_insensitive : Bool) (n : Nat)
  (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.c_back_ref case_insensitive n
      ⦃fun r s => tRefNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_back_ref] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_back_ref_lift_spec (case_insensitive : Bool) (n : Nat)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_back_ref case_insensitive n : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end)
                        ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_back_ref_spec _ _ _)

@[spec] theorem c_lookaround_PositiveLookahead_spec (compiled : ThompsonRef)
  (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ tRefLt compiled states ∧ NextOfLt states
                ∧ patchAssignable states compiled.end⦄
      Code.c_lookaround_PositiveLookahead compiled
      ⦃fun r s => tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_lookaround_PositiveLookahead] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_lookaround_PositiveLookahead_lift_spec (compiled : ThompsonRef)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states
                    ∧ patchAssignable states compiled.end)
                  ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_lookaround_PositiveLookahead compiled : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_lookaround_PositiveLookahead_spec _ _)

@[spec] theorem c_lookaround_NegativeLookahead_spec (compiled : ThompsonRef)
  (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ tRefLt compiled states ∧ NextOfLt states
                ∧ patchAssignable states compiled.end⦄
      Code.c_lookaround_NegativeLookahead compiled
      ⦃fun r s => tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_lookaround_NegativeLookahead] with finish only [patchAssignable_of_assignableIf,
    = stateIdNextOfLt.eq_1, assignableIf_trans, → isAppend_of_assignableP, assignableP,
    = stateIdNextOfEqLt.eq_1, → patchAssignable_of_append, patch2Assignable_of_assignableIf,
    = assignableIf.eq_1, = tRefNextOfLeLt.eq_1, = tRefLt.eq_1, = tRefNextOfLt.eq_1]

@[spec] theorem c_lookaround_NegativeLookahead_lift_spec (compiled : ThompsonRef)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states
                    ∧ patchAssignable states compiled.end)
                  ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_lookaround_NegativeLookahead compiled : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_lookaround_NegativeLookahead_spec _ _)

@[spec] theorem c_lookaround_PositiveLookbehind_spec (next_char : Unchecked.StateID)
  (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                   ∧ patchAssignable states next_char ∧ patchAssignable states compiled.end⦄
      Code.c_lookaround_PositiveLookbehind next_char compiled
      ⦃fun r s => tRefNextOfLeLt states r s ∧ assignableIf states s  ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_lookaround_PositiveLookbehind] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_lookaround_PositiveLookbehind_lift_spec (next_char : Unchecked.StateID)
  (compiled : ThompsonRef) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                  ∧ patchAssignable states next_char ∧ patchAssignable states compiled.end)
                  ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_lookaround_PositiveLookbehind next_char compiled : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLeLt states r s.1  ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_lookaround_PositiveLookbehind_spec _ _ _)

@[spec] theorem c_lookaround_NegativeLookbehind_spec (next_char : Unchecked.StateID)
  (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                  ∧ patchAssignable states next_char ∧ patchAssignable states compiled.end⦄
      Code.c_lookaround_NegativeLookbehind next_char compiled
      ⦃fun r s => tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_lookaround_NegativeLookbehind] with finish only [patchAssignable_of_assignableIf,
    = stateIdNextOfLt.eq_1, assignableIf_trans, → isAppend_of_assignableP, assignableP,
    = stateIdNextOfEqLt.eq_1, → patchAssignable_of_append, patch2Assignable_of_assignableIf,
    = assignableIf.eq_1, = tRefNextOfLeLt.eq_1, = tRefLt.eq_1, = tRefNextOfLt.eq_1]

@[spec] theorem c_lookaround_NegativeLookbehind_lift_spec (next_char : Unchecked.StateID)
  (compiled : ThompsonRef) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ next_char < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                    ∧ patchAssignable states next_char ∧ patchAssignable states compiled.end)
                ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_lookaround_NegativeLookbehind next_char compiled : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_lookaround_NegativeLookbehind_spec _ _ _)

@[spec] theorem c_repetition_0_some_1_false_spec (union : Unchecked.StateID)
  (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                    ∧ patchAssignable states union ∧ patchAssignable states compiled.end⦄
      Code.c_repetition_0_some_1_false union compiled
      ⦃fun r s => tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_repetition_0_some_1_false] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_repetition_0_some_1_false_lift_spec (union : Unchecked.StateID)
  (compiled : ThompsonRef) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                  ∧ patchAssignable states union ∧ patchAssignable states compiled.end)
                  ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_repetition_0_some_1_false union compiled : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_repetition_0_some_1_false_spec _ _ _)

@[spec] theorem c_repetition_0_some_1_true_spec (union : Unchecked.StateID)
  (compiled : ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                  ∧ patchAssignable states union ∧ patchAssignable states compiled.end⦄
      Code.c_repetition_0_some_1_true union compiled
      ⦃fun r s => tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_repetition_0_some_1_true] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_repetition_0_some_1_true_lift_spec (union : Unchecked.StateID)
  (compiled : ThompsonRef) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                    ∧ patchAssignable states union ∧ patchAssignable states compiled.end)
                ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_repetition_0_some_1_true union compiled : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_repetition_0_some_1_true_spec _ _ _)

@[spec] theorem c_repetition_0_none_spec (union : Unchecked.StateID) (compiled : ThompsonRef)
  (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                  ∧ patchAssignable states union ∧ patchAssignable states compiled.end⦄
      Code.c_repetition_0_none union compiled
      ⦃fun r s => tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_repetition_0_none] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_repetition_0_none_lift_spec (union : Unchecked.StateID)
  (compiled : ThompsonRef) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                    ∧ patchAssignable states union ∧ patchAssignable states compiled.end)
                  ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_repetition_0_none union compiled : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_repetition_0_none_spec _ _ _)

@[spec] theorem greedy_union_spec (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      (if greedy then Code.add_union else Code.add_union_reverse : Code.PatchM Unchecked.StateID)
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r;
                  fun _ _ => False⦄ := by
  vcgen with finish [Unchecked.State.nextOf, Unchecked.EatMode.nextOf, assignableP, assignableP2,
    isAppend_of_isAppendOfState, isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_at_least_0_pre_spec (compiled : ThompsonRef) (greedy : Bool)
  (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ tRefLt compiled states ∧ NextOfLt states
                ∧ patchAssignable states compiled.end⦄
      Code.c_at_least_0_pre compiled greedy
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_at_least_0_pre] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_at_least_0_pre_lift_spec (compiled : ThompsonRef) (greedy : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states
                    ∧ patchAssignable states compiled.end)
                ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_at_least_0_pre compiled greedy : Code.CompilerM Unchecked.StateID)
      ⦃fun r s => (stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_at_least_0_pre_spec _ _ _)

@[spec] theorem c_at_least_set_spec (possible_empty_capture_group : Option Nat) (greedy : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture) {groups : Array Nat}
    : ⦃fun s => s.1 = states ∧ s.2.1 = captures ∧ s.2.2 = groups⦄
      Code.c_at_least_set possible_empty_capture_group greedy
      ⦃fun _ s => states = s.1 ∧ s.2.1 = captures ∧ groups.size ≤ s.2.2.size
                  ∧ assignableIf states s.1; fun _ _ => False⦄ := by
  vcgen [Code.c_at_least_set] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_at_least_0_post_spec (compiled : ThompsonRef) (plus : Unchecked.StateID)
  (greedy : Bool) (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ plus < states.size ∧ compiled.start < states.size ∧ NextOfLt states
                 ∧ patchAssignable states compiled.end  ∧ patchAssignable states plus⦄
      Code.c_at_least_0_post compiled plus greedy possessive
      ⦃fun r s => tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_at_least_0_post] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_at_least_0_post_lift_spec (compiled : ThompsonRef) (plus : Unchecked.StateID)
  (greedy : Bool) (possessive : Bool) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ plus < states.size ∧ compiled.start < states.size
                      ∧ NextOfLt states ∧ patchAssignable states compiled.end
                      ∧ patchAssignable states plus)
                ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_at_least_0_post compiled plus greedy possessive : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_at_least_0_post_spec _ _ _ _ _)

@[spec] theorem c_at_least_0_spec (compiled : ThompsonRef)
  (possible_empty_capture_group : Option Nat) (greedy : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧ tRefLt compiled states ∧ NextOfLt states
                ∧ patchAssignable states compiled.end ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_at_least_0 compiled possible_empty_capture_group greedy
      ⦃fun r s => stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  vcgen [Code.c_at_least_0] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_at_least_1_pre_spec (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.c_at_least_1_pre greedy
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_at_least_1_pre] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_at_least_1_pre_lift_spec (greedy : Bool) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_at_least_1_pre greedy : Code.CompilerM Unchecked.StateID)
      ⦃fun r s => (stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_at_least_1_pre_spec _ _)

@[spec] theorem c_at_least_1_post_spec (compiled : ThompsonRef) (union : Unchecked.StateID)
  (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
              ∧ patchAssignable states compiled.end ∧ patchAssignable states union⦄
      Code.c_at_least_1_post compiled union possessive
      ⦃fun r s => tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_at_least_1_post] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_at_least_1_post_lift_spec (compiled : ThompsonRef) (union : Unchecked.StateID)
  (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ union < states.size ∧ tRefLt compiled states ∧ NextOfLt states
                   ∧ patchAssignable states compiled.end ∧ patchAssignable states union)
                  ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_at_least_1_post compiled union possessive : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_at_least_1_post_spec _ _ _ _)

@[spec] theorem c_at_least_1_spec (possible_empty_capture_group : Option Nat) (greedy : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_at_least_1 possible_empty_capture_group greedy
      ⦃fun r s => stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  vcgen [Code.c_at_least_1] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_at_least_2_spec («prefix» last : ThompsonRef) (greedy : Bool)
  (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ tRefLt «prefix» states ∧ tRefLt last states ∧ NextOfLt states
                ∧ patchAssignable states «prefix».end ∧ patchAssignable states last.end⦄
      Code.c_at_least_2 «prefix» last greedy possessive
      ⦃fun r s => tRefNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r.end;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_at_least_2] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, patchAssignable_of_append]

@[spec] theorem c_at_least_2_lift_spec («prefix» last : ThompsonRef) (greedy : Bool)
  (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ tRefLt «prefix» states ∧ tRefLt last states ∧ NextOfLt states
                  ∧ patchAssignable states «prefix».end ∧ patchAssignable states last.end)
                  ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_at_least_2 «prefix» last greedy possessive : Code.CompilerM ThompsonRef)
      ⦃fun r s => (tRefNextOfLeLt states r s.1 ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.end)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_at_least_2_spec _ _ _ _ _)
