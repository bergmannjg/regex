import Std.Tactic.Do
import Std.Tactic.Do.Syntax

import Regex.Compiler.Basic
import Regex.Compiler.Patch
import Regex.Compiler.Compile
import Regex.Compiler.Lemmas.Basic
import Regex.Compiler.Lemmas.Patch
import Regex.Compiler.Lemmas.AddState

namespace Compiler

open Syntax
open NFA

namespace Lemmas

/-!
## Lemmas

Proof that `Compiler.Code.compile` gives an array with the `Compiler.NextOfLt` and `Capture.Valid` property
and has no exceptions

- `c_compile_spec`: main result
-/

open Std.Do

set_option mvcgen.warning false

set_option trace.profiler.threshold 2000

@[spec] theorem c_bounded.fold.patch.pre_spec (compiled: ThompsonRef) (prev_end : Unchecked.StateID)
  (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states
                      ∧ prev_end < states.size ∧ NextOfLt states
                      ∧ patchAssignable states prev_end⌝⦄
      Code.c_bounded.fold.patch.pre compiled prev_end greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r⌝, fun _ => ⌜False⌝⟩⦄ := by
  dsimp [Code.c_bounded.fold.patch.pre]
  mintro _
  mspec greedy_union_spec; grind
  mvcgen with grind

@[spec] theorem c_bounded.fold.patch.possessive_spec (compiled: ThompsonRef) (empty : Unchecked.StateID)
  (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states
                      ∧ empty < states.size ∧ NextOfLt states ∧ patchAssignable states compiled.end⌝⦄
      Code.c_bounded.fold.patch.possessive compiled empty
      ⦃post⟨fun r s => ⌜stateIdNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r⌝, fun _ => ⌜False⌝⟩⦄ := by
  dsimp [Code.c_bounded.fold.patch.possessive]
  mintro _
  mspec add_union_lift_spec; grind only [← SPred.entails.refl]
  mspec add_fail_lift_spec; grind only [= stateIdNextOfLt.eq_1, = SPred.entails_nil]
  mspec add_eat_lift_spec; grind only [= stateIdNextOfLt.eq_1, ← SPred.pure_mono,
    = Unchecked.EatMode.nextOf.eq_2]
  mvcgen
  grind only [= stateIdNextOfLt.eq_1, = assignableP.eq_1, → isAppend_of_isAppendOfState,
    → patchAssignable_of_append, patchAssignable_of_assignableIf]
  grind only [= stateIdNextOfLt.eq_1, = assignableP2.eq_1, = stateIdNextOfEqLt.eq_1,
    patch2Assignable_of_assignableIf]
  grind only [patchAssignable_of_assignableIf, = stateIdNextOfLt.eq_1, assignableIf_trans,
    → isAppend_of_assignableP, = stateIdNextOfEqLt.eq_1, = assignableIf.eq_1,
    → patchAssignable_of_append]

@[spec] theorem c_bounded.fold.patch.post_spec (compiled: ThompsonRef) (union empty : Unchecked.StateID) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ compiled.end < states.size
                      ∧ union < states.size ∧ empty < states.size ∧ NextOfLt states
                      ∧ patchAssignable states union ∧ patchAssignable states compiled.end⌝⦄
      Code.c_bounded.fold.patch.post compiled union empty
      ⦃post⟨fun r s => ⌜stateIdNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_bounded.fold.patch.post] with grind

@[spec] theorem c_bounded.fold.patch_spec (compiled: ThompsonRef) (prev_end empty : Unchecked.StateID)
  (greedy : Bool) (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt compiled states
                      ∧ prev_end < states.size ∧ empty < states.size ∧ NextOfLt states
                      ∧ patchAssignable states prev_end ∧ patchAssignable states compiled.end⌝⦄
      Code.c_bounded.fold.patch compiled prev_end empty greedy possessive
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [Code.c_bounded.fold.patch] with grind

@[spec] theorem c_bounded.fold.patch_lift_spec  (compiled: ThompsonRef) (prev_end empty : Unchecked.StateID)
  (greedy : Bool) (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt compiled states
                      ∧ prev_end < states.size ∧ empty < states.size ∧ NextOfLt states
                      ∧ patchAssignable states prev_end ∧ patchAssignable states compiled.end)
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_bounded.fold.patch compiled prev_end empty greedy possessive : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜(stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_bounded.fold.patch_spec _ _ _ _ _ _)

@[spec] theorem c_alt_iter_step_spec (first second: ThompsonRef) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ tRefLt first states
                      ∧ tRefLt second states ∧ NextOfLt states
                      ∧ patchAssignable states first.end ∧ patchAssignable states second.end⌝⦄
      Code.c_alt_iter_step first second
      ⦃post⟨fun r s => ⌜tRefNextOfLt states ⟨r.1, r.2⟩ s ∧ assignableIf states s ∧ patchAssignable s r.1 ∧ patchAssignable s r.2⌝, fun _ => ⌜False⌝⟩⦄ := by
  dsimp [Code.c_alt_iter_step]
  mintro _
  mspec add_union_lift_spec; grind only [← SPred.entails.refl]
  mspec add_empty_lift_spec; grind only [= stateIdNextOfLt.eq_1, = SPred.entails_nil]
  mvcgen
  grind only [= stateIdNextOfLt.eq_1, = assignableP.eq_1, patchAssignable_of_assignableIf]
  grind only [patchAssignable_of_assignableIf, = stateIdNextOfLt.eq_1, = stateIdNextOfEqLt.eq_1,
    assignableIf_trans]
  grind only [= stateIdNextOfLt.eq_1, → isAppend_of_assignableP, = assignableP.eq_1,
    = stateIdNextOfEqLt.eq_1, → patchAssignable_of_append, patchAssignable_of_assignableIf,
    assignableIf_trans]
  grind only [patchAssignable_of_assignableIf, = stateIdNextOfLt.eq_1, assignableIf_trans,
    = stateIdNextOfEqLt.eq_1]
  grind only [patchAssignable_of_assignableIf, = stateIdNextOfLt.eq_1, assignableIf_trans,
    = assignableP.eq_1, = stateIdNextOfEqLt.eq_1, = assignableIf.eq_1]

@[spec] theorem c_alt_iter_step_lift_spec (first second: ThompsonRef) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ tRefLt first states ∧ tRefLt second states ∧ NextOfLt states
                    ∧ patchAssignable states first.end ∧ patchAssignable states second.end)
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_alt_iter_step first second : Code.CompilerM (Unchecked.StateID × Unchecked.StateID))
      ⦃post⟨fun r s => ⌜(tRefNextOfLt states ⟨r.1, r.2⟩ s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.1 ∧ patchAssignable s.1 r.2)
                        ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_alt_iter_step_spec _ _ _)

@[spec] theorem c_rep_pre_spec (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => ⌜s = states ∧ NextOfLt states⌝⦄
      Code.c_rep_pre greedy
      ⦃post⟨fun r s => ⌜stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  dsimp [Code.c_rep_pre]
  intros
  mspec greedy_union_spec

@[spec] theorem c_rep_pre_lift_spec (greedy : Bool) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      (Code.c_rep_pre greedy : Code.CompilerM Unchecked.StateID)
      ⦃post⟨fun r s => ⌜(stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r) ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  exact coe_spec_EStateM_to_CompilerM (c_rep_pre_spec _ _)

@[simp, grind =] theorem cMemAndValid_iff (prev caps : Array NFA.Capture) :
    cMemAndValid prev caps ↔ (∀ a ∈ prev, a ∈ caps) ∧ NFA.Capture.Valid caps := by
  rfl

set_option maxHeartbeats 4000000

mutual

@[spec] theorem c_alt_iter_fold_spec (hirs : Array Hir) (union «end» : Unchecked.StateID)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ union < states.size ∧ «end» < states.size ∧ NextOfLt states
                ∧ patchAssignable states union
                ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_alt_iter.fold hirs union «end»
      ⦃post⟨fun _ s => ⌜statesNextOfLeLt states s.1 ∧ assignableIf states s.1 ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  unfold Code.c_alt_iter.fold
  mspec Spec.foldlM_array
  case inv =>
    exact (fun (_, xs) s => ⌜states.size ≤ s.1.size ∧ union < s.1.size ∧ «end» < s.1.size
                              ∧ assignableIf states s.1 ∧ patchAssignable states union
                              ∧ NextOfLt s.1 ∧ cMemAndValid captures s.2.1⌝, fun e => ⌜False⌝, ())
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
          mvcgen
          grind only [assignableIf_trans, = tRefNextOfLt.eq_1, = stateIdNextOfEqLt.eq_1,
            cMemAndValid, #ab8902846395062a, #8e27c298286ff11c]
        grind only [= stateIdNextOfEqLt.eq_1]
        grind only [= tRefNextOfLt.eq_1, = stateIdNextOfEqLt.eq_1, = tRefLt.eq_1]
        grind only [= tRefNextOfLt.eq_1, = stateIdNextOfEqLt.eq_1]
        grind only [patchAssignable_of_assignableIf]
        grind only [cValid_of_cMemAndValid]
      grind only [= tRefNextOfLt.eq_1]
      grind only [= tRefNextOfLt.eq_1]
      grind only [= tRefNextOfLt.eq_1, = tRefLt.eq_1]
      grind only [patchAssignable_of_assignableIf, assignableIf_trans]
      grind only [cValid_of_cMemAndValid]
    all_goals grind only [cValid_of_cMemAndValid]
  case pre =>
    simp_all only [assignableIf, SPred.entails_1,
      SPred.down_pure, Std.le_refl, implies_true, and_self, cMemAndValid_of_cValid_of_eq]
  case post =>
    simp only [assignableIf, statesNextOfLeLt,
      SPred.entails_1, SPred.down_pure, and_imp, Prod.forall, forall_const]
    grind only
  simp only [ExceptConds.entails.refl]
termination_by sizeOf hirs

@[spec] theorem c_concat_fold_spec (tail : Array Hir) (sid : Unchecked.StateID)
 (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ sid < states.size ∧ NextOfLt states ∧ patchAssignable states sid) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_concat.fold tail sid
      ⦃post⟨fun r s => ⌜stateIdNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  unfold Code.c_concat.fold
  mspec Spec.foldlM_array
  case inv =>
    exact (fun (xs, r) s => ⌜states.size ≤ s.1.size ∧ sid < s.1.size ∧ r < s.1.size ∧ NextOfLt s.1
                              ∧ assignableIf states s.1 ∧ patchAssignable s.1 r
                              ∧ cMemAndValid captures s.2.1⌝, fun e => ⌜False⌝, ())
  case pre => simp_all only [assignableIf,
    and_self_left, SPred.entails_1, SPred.down_pure, Std.le_refl, implies_true, and_self,
    cMemAndValid_of_cValid_of_eq]
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
        grind
    all_goals grind
  simp only [assignableIf, stateIdNextOfLeLt,
    SPred.entails_1, SPred.down_pure, and_imp, Prod.forall, forall_const]
  grind only
  rfl
termination_by sizeOf tail

@[spec] theorem c_alt_iter_spec (alt : Syntax.Alternation) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_alt_iter alt
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  unfold Code.c_alt_iter
  split
  expose_names
  have : sizeOf first < sizeOf (Syntax.Alternation.mk first second tail) := by simp +arith
  have : sizeOf second < sizeOf (Syntax.Alternation.mk first second tail) := by simp +arith
  have : sizeOf tail < sizeOf (Syntax.Alternation.mk first second tail) := by simp +arith
  mspec c_spec
  inst_mvars; grind; grind
  mspec c_spec
  inst_mvars
  case post.success.post.success =>
    mspec c_alt_iter_step_lift_spec
    inst_mvars
    case post.success =>
      mspec c_alt_iter_fold_spec
      inst_mvars
      case post.success =>
        mvcgen with grind
      all_goals grind
    all_goals grind
  all_goals grind
termination_by sizeOf alt

@[spec] theorem c_bounded_spec (hir : Hir) (min max : Nat) (greedy : Bool) (possessive : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_bounded hir min max greedy possessive
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  unfold Code.c_bounded
  split
  mspec c_exactly_spec
  inst_mvars; grind; grind
  split
  case isTrue.post.success.isTrue =>
    split
    · mspec c_possessive_le_lift_spec
      inst_mvars
      case post.success => mvcgen with grind
      all_goals grind
    · simp only [tRefNextOfLt, tRefLt, assignableIf,
        WP.pure, SPred.entails_1, SPred.down_pure, and_imp, Prod.forall, forall_const]
      intros
      and_intros
      all_goals grind
  case isTrue.post.success.isFalse =>
      mspec add_empty_lift_spec'
      inst_mvars
      case post.success =>
        mspec c_bounded_fold_spec
        inst_mvars
        case post.success =>
          mspec patch_lift_spec
          · inst_mvars; all_goals grind
          · simp only [stateIdNextOfEqLt, assignableIf,
              tRefNextOfLt, tRefLt, WP.pure, SPred.entails_1, SPred.down_pure, and_imp, Prod.forall,
              forall_const]
            intros
            and_intros
            grind only [tRefNextOfLt, = stateIdNextOfLt.eq_1, = stateIdNextOfLeLt.eq_1]
            grind only [tRefNextOfLt, = stateIdNextOfLt.eq_1, = stateIdNextOfLeLt.eq_1, tRefLt]
            assumption
            assumption
            grind only [patchAssignable_of_assignableIf, assignableIf_trans, assignableIf]
            grind only [patch2Assignable_of_assignableIf, assignableIf_trans, assignableIf]
            grind only [= assignableP.eq_1, patchAssignable_of_assignableIf, assignableIf_trans,
              assignableIf]
            grind
            rename_i h; exact h.right
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
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  unfold Code.c_lookaround
  split
  case h_1 |  h_2 =>
    mspec c_spec
    inst_mvars; grind; grind
    mspec
    inst_mvars; grind; grind; grind; grind; grind
    simp only [tRefNextOfLeLt, tRefLt, assignableIf,
      tRefNextOfLt, SPred.entails_1, SPred.down_pure, and_imp, Prod.forall, forall_const]
    grind only [= stateIdNextOfLt.eq_1, tRefNextOfLt, patchAssignable_of_assignableIf,
            assignableIf_trans, assignableIf, patch2Assignable_of_assignableIf]
  case h_3 | h_4 =>
    mspec add_next_char_lift_spec
    inst_mvars
    case post.success =>
      mspec c_spec
      inst_mvars
      case post.success =>
        mspec
        inst_mvars
        case post.success =>
          simp only [tRefNextOfLeLt, tRefLt, assignableIf, tRefNextOfLt, SPred.entails_1,
            SPred.down_pure, and_imp, Prod.forall, forall_const]
          intros
          grind only [= stateIdNextOfLt.eq_1, tRefNextOfLt, patchAssignable_of_assignableIf,
            assignableIf_trans, assignableIf, patch2Assignable_of_assignableIf]
        all_goals grind
      all_goals grind
    all_goals grind
termination_by sizeOf look

@[spec] theorem c_repetition_spec (rep : Repetition) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_repetition rep
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
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
    mspec c_empty_lift_spec
    inst_mvars; grind; grind
    simp only [tRefNextOfLt, tRefLt, assignableP, isAppendOfStateID, isAppendOfState,
      Array.append_singleton, assignableIf,
      SPred.entails_1, SPred.down_pure, and_imp, forall_exists_index, Prod.forall, forall_const]
    intros
    grind only [patchAssignable_of_eq, = Array.getElem_push, patch2Assignable_of_eq]
termination_by sizeOf rep

@[spec] theorem c_exactly_spec (hir : Hir) (n : Nat) (states : Array Unchecked.State)
   (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_exactly hir n
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  unfold Code.c_exactly
  split
  · mspec c_spec
    inst_mvars; grind; grind
    mspec c_exactly_fold_spec
    inst_mvars
    case isTrue.post.success.post.success => mvcgen with grind [= cValid, = cMemAndValid]
    all_goals grind
  · mspec c_empty_lift_spec
    inst_mvars
    case isFalse.post.success => mvcgen with grind
    all_goals grind
termination_by sizeOf hir + sizeOf n

@[spec] theorem c_concat_spec (hirs : Array Hir) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜(s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_concat hirs
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
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
    mvcgen
    inst_mvars
    all_goals grind [= cValid, = cMemAndValid]
  all_goals grind
termination_by sizeOf hirs

@[spec] theorem c_exactly_fold_spec (hir : Hir) (n : Nat) («end» : Unchecked.StateID)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ «end» < states.size ∧  NextOfLt states
                  ∧ patchAssignable states «end»
                  ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_exactly.fold hir n «end»
      ⦃post⟨fun r s => ⌜stateIdNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  unfold Code.c_exactly.fold
  split
  mspec Spec.foldlM_list
  case inv =>
    exact (fun (xs, r) s => ⌜states.size ≤ s.1.size ∧ r < s.1.size ∧ «end» < s.1.size
                              ∧ assignableIf states s.1 ∧ patchAssignable s.1 r ∧ patchAssignable states «end»
                              ∧ NextOfLt s.1 ∧ cMemAndValid captures s.2.1⌝, fun e => ⌜False⌝, ())
  case step =>
    intros
    mintro _
    mspec c_spec
    inst_mvars
    case post.success =>
      mspec patch_lift_spec
      inst_mvars
      case post.success => mvcgen with grind
      all_goals grind
    all_goals grind
  case pre | isFalse =>
    simp_all only [Nat.not_lt, Nat.le_zero_eq, stateIdNextOfLeLt, assignableIf, WP.pure,
      SPred.entails_1, SPred.down_pure, Std.le_refl,
      and_self, implies_true, cMemAndValid_of_cValid_of_eq]
  case isTrue.post =>
    simp only [assignableIf,  stateIdNextOfLeLt,
      SPred.entails_1, SPred.down_pure, and_imp, Prod.forall, forall_const]
    all_goals grind
  simp
termination_by sizeOf hir + sizeOf n

@[spec] theorem c_at_least_spec (hir : Hir) (n : Nat) (greedy : Bool) (possessive : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_at_least hir n greedy possessive
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ assignableIf states s.1
            ∧ patchAssignable s.1 r.end ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  unfold Code.c_at_least
  split
  case isTrue =>
    mspec c_spec
    inst_mvars; grind; grind
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
    inst_mvars; grind; grind
    mspec c_at_least_1_spec
    inst_mvars
    case isTrue.post.success.post.success =>
      mspec c_at_least_1_post_lift_spec
      inst_mvars
      case post.success =>
        simp only [tRefNextOfLeLt, tRefLt, assignableIf,
          tRefNextOfLt, SPred.entails_1, SPred.down_pure, and_imp, Prod.forall, forall_const]
        intros
        grind only [tRefNextOfLt, = stateIdNextOfLt.eq_1, patchAssignable_of_assignableIf,
          assignableIf_trans, assignableIf, patch2Assignable_of_assignableIf]
      all_goals grind
    case isFalse =>
      mspec c_exactly_spec
      inst_mvars; grind; grind
      mspec c_spec
      inst_mvars
      case post.success.post.success =>
        mspec c_at_least_2_lift_spec
        inst_mvars
        case post.success =>
          simp only [tRefNextOfLeLt, tRefLt, assignableIf, tRefNextOfLt, SPred.entails_1,
            SPred.down_pure, and_imp, Prod.forall, forall_const]
          intros
          grind only [tRefNextOfLt, = cMemAndValid_iff, patchAssignable_of_assignableIf,
            assignableIf_trans, assignableIf, patch2Assignable_of_assignableIf]
        all_goals grind
      all_goals grind
    all_goals grind
termination_by sizeOf hir + sizeOf n + 1

@[spec] theorem c_bounded_fold_spec  (hir : Hir) (n : Nat) («prefix» : ThompsonRef) (empty : Unchecked.StateID)
  (greedy : Bool) (possessive : Bool) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧ tRefLt «prefix» states ∧ empty < states.size ∧ NextOfLt states
                 ∧ patchAssignable states «prefix».end
                 ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_bounded.fold hir n «prefix» empty greedy possessive
      ⦃post⟨fun r s => ⌜stateIdNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  unfold Code.c_bounded.fold
  split
  mspec Spec.foldlM_list
  case inv =>
    exact (fun (xs, r) s => ⌜states.size ≤ s.1.size ∧ r < s.1.size ∧ empty < s.1.size
                            ∧ assignableIf states s.1 ∧ patchAssignable s.1 r ∧ patchAssignable states «prefix».end
                            ∧ NextOfLt s.1 ∧ cMemAndValid captures s.2.1⌝, fun e => ⌜False⌝, ())
  case step =>
    intros
    mintro _
    mspec c_spec
    inst_mvars
    case post.success =>
      mspec c_bounded.fold.patch_lift_spec
      inst_mvars
      case post.success => mvcgen with grind
      all_goals grind
    all_goals grind
  case pre =>
    intro _
    simp_all only [tRefLt, assignableIf,
      cMemAndValid_iff, SPred.entails_nil, SPred.down_pure, Std.le_refl, implies_true, and_self,
      true_and, and_imp]
    grind only [= Capture.Valid.iff, cap_exists_of_cap_role_end_of_cValid, #0000, #f40e, #25d2]
  case isTrue =>
    simp only [assignableIf,  cMemAndValid_iff,
      stateIdNextOfLeLt, SPred.entails_1, SPred.down_pure, and_imp, Prod.forall, forall_const]
    all_goals grind
  case isFalse =>
    intro _
    simp_all only [Nat.not_lt, Nat.le_zero_eq, tRefLt, stateIdNextOfLeLt, assignableIf,
      cMemAndValid_iff, WP.pure, SPred.entails_nil,
      SPred.down_pure, Std.le_refl, and_self, implies_true, true_and, and_imp]
    grind only [= Capture.Valid.iff, cap_exists_of_cap_role_end_of_cValid]
  simp
termination_by sizeOf hir + sizeOf n

@[spec] theorem c_cap_spec (hir : Syntax.Capture) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c_cap hir
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  mintro _
  unfold Code.c_cap
  split
  mspec c_cap'_start_spec
  inst_mvars; grind; grind
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
        case post.success => mvcgen with grind
        all_goals grind
      all_goals grind
    simp_all only [stateIdNextOfLt, assignableIf, assignableP, isAppendOfStateID, isAppendOfState,
      Array.append_singleton, cMemAndValid_iff, tRefNextOfLt, tRefLt]
    all_goals grind
  all_goals grind
termination_by sizeOf hir

@[spec] theorem c_spec (hir : Hir) (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => ⌜s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⌝⦄
      Code.c hir
      ⦃post⟨fun r s => ⌜tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end ∧ cMemAndValid captures s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
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
      ⦃post⟨fun r s => ⌜tRefLt r s.1 ∧ NextOfLt s.1 ∧ patchAssignable s.1 r.end ∧ cValid s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
  dsimp [Code.init]
  mintro _
  split
  mspec; simp; and_intros; grind; rfl; grind; simp; grind only [cValid_of_empty]
  mspec; simp; and_intros; grind; rfl; grind
  simp only [tRefNextOfLt, tRefLt, assignableIf, cMemAndValid_iff, WP.pure, SPred.entails_1,
    SPred.down_pure, and_imp, Prod.forall, forall_const]
  intros
  and_intros
  case isFalse.post.success.refine_2.refine_2.refine_2 => assumption
  all_goals grind

@[spec] theorem c_compile_spec (anchored : Bool) (hir : Hir)
    : ⦃fun s => ⌜s.1.size = 0 ∧ s.2.1.size = 0⌝⦄
      Code.compile anchored hir
      ⦃post⟨fun _ s => ⌜NextOfLt s.1 ∧ cValid s.2.1⌝, fun _ => ⌜False⌝⟩⦄ := by
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
        mvcgen
        and_intros
        simp
        apply NextOfLt.mk
        case vc1.pre.refine_2.refine_1 => rfl
        all_goals grind
      all_goals grind
    all_goals grind
  all_goals grind

theorem compile_nextOf_lt {anchored : Bool} {expr : Hir}
  (h : Code.compile anchored expr (#[], #[], #[]) = EStateM.Result.ok () (states, captures, groups))
    : NextOfLt states := by
  have heq := c_compile_spec anchored expr (#[], #[], #[])
  simp [wp] at heq
  dsimp [PredTrans.apply] at heq
  split at heq <;> simp_all
  expose_names
  dsimp [EStateM.run] at heq_1
  simp_all

theorem compile_captures_valid {anchored : Bool} {expr : Hir}
  (h : Code.compile anchored expr (#[], #[], #[]) = EStateM.Result.ok () (states, captures, groups))
    : Capture.Valid captures := by
  have heq := c_compile_spec anchored expr (#[], #[], #[])
  simp [wp] at heq
  dsimp [PredTrans.apply] at heq
  split at heq
  · expose_names
    dsimp [EStateM.run] at heq_1
    grind
  · grind [= cValid]

theorem compile_eq_ok {anchored : Bool} {expr : Hir}
   : ∃ s, Code.compile anchored expr (#[], #[], #[]) = EStateM.Result.ok () s := by
  have heq := c_compile_spec anchored expr (#[], #[], #[])
  simp [wp] at heq
  dsimp [PredTrans.apply] at heq
  split at heq <;> simp_all
  expose_names
  dsimp [EStateM.run] at heq_1
  grind
