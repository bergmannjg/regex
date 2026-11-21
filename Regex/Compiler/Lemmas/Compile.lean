module

public import Std.WP

public import Regex.Compiler.Basic
public import Regex.Compiler.Patch
public import Regex.Compiler.Compile
public import Regex.Compiler.Lemmas.Basic
public import Regex.Compiler.Lemmas.Patch
public import Regex.Compiler.Lemmas.AddState

public section

namespace Compiler

open Regex.Syntax
open NFA

namespace Lemmas

/-!
## Lemmas

Proof that `Compiler.Code.compile` gives an array with the `Compiler.NextOfLt` and `Capture.Valid`
property and has no exceptions

- `c_compile_spec`: main result
-/

open Std.WP

set_option experimental.vcgen true

@[spec] private theorem c_bounded.fold.patch.pre_spec (compiled: ThompsonRef)
  (prev_end : Unchecked.StateID) (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ tRefLt compiled states
                      ∧ prev_end < states.size ∧ NextOfLt states
                      ∧ patchAssignable states prev_end⦄
      Code.c_bounded.fold.patch.pre compiled prev_end greedy
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_bounded.fold.patch.pre] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, isAppend_of_assignableP, patchAssignable_of_append]

@[spec] private theorem c_bounded.fold.patch.possessive_spec (compiled: ThompsonRef)
  (empty : Unchecked.StateID) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ tRefLt compiled states
                      ∧ empty < states.size ∧ NextOfLt states ∧ patchAssignable states compiled.end⦄
      Code.c_bounded.fold.patch.possessive compiled empty
      ⦃fun r s => stateIdNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_bounded.fold.patch.possessive] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, isAppend_of_assignableP, patchAssignable_of_append]

@[spec] private theorem c_bounded.fold.patch.post_spec (compiled: ThompsonRef)
  (union empty : Unchecked.StateID) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ compiled.end < states.size
                      ∧ union < states.size ∧ empty < states.size ∧ NextOfLt states
                      ∧ patchAssignable states union ∧ patchAssignable states compiled.end⦄
      Code.c_bounded.fold.patch.post compiled union empty
      ⦃fun r s => stateIdNextOfLeLt states r s ∧ assignableIf states s ∧ patchAssignable s r;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_bounded.fold.patch.post] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, isAppend_of_assignableP, patchAssignable_of_append]

@[spec] private theorem c_bounded.fold.patch_spec (compiled: ThompsonRef)
  (prev_end empty : Unchecked.StateID)
  (greedy : Bool) (possessive : Bool) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ tRefLt compiled states
                      ∧ prev_end < states.size ∧ empty < states.size ∧ NextOfLt states
                      ∧ patchAssignable states prev_end ∧ patchAssignable states compiled.end⦄
      Code.c_bounded.fold.patch compiled prev_end empty greedy possessive
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_bounded.fold.patch] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, isAppend_of_assignableP, patchAssignable_of_append]

@[spec] private theorem c_bounded.fold.patch_lift_spec  (compiled: ThompsonRef)
  (prev_end empty : Unchecked.StateID) (greedy : Bool) (possessive : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ tRefLt compiled states
                      ∧ prev_end < states.size ∧ empty < states.size ∧ NextOfLt states
                      ∧ patchAssignable states prev_end ∧ patchAssignable states compiled.end)
                  ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_bounded.fold.patch compiled prev_end empty greedy possessive
        : Code.CompilerM Unchecked.StateID)
      ⦃fun r s => (stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_bounded.fold.patch_spec _ _ _ _ _ _)

@[spec] private theorem c_alt_iter_step_spec (first second: ThompsonRef)
  (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ tRefLt first states
                      ∧ tRefLt second states ∧ NextOfLt states
                      ∧ patchAssignable states first.end ∧ patchAssignable states second.end⦄
      Code.c_alt_iter_step first second
      ⦃fun r s => tRefNextOfLt states ⟨r.1, r.2⟩ s ∧ assignableIf states s ∧ patchAssignable s r.1
                  ∧ patchAssignable s r.2; fun _ _ => False⦄ := by
  vcgen [Code.c_alt_iter_step] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, isAppend_of_assignableP, patchAssignable_of_append]

@[spec] private theorem c_alt_iter_step_lift_spec (first second: ThompsonRef)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ tRefLt first states ∧ tRefLt second states ∧ NextOfLt states
                    ∧ patchAssignable states first.end ∧ patchAssignable states second.end)
                ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_alt_iter_step first second : Code.CompilerM (Unchecked.StateID × Unchecked.StateID))
      ⦃fun r s => (tRefNextOfLt states ⟨r.1, r.2⟩ s.1 ∧ assignableIf states s.1
                    ∧ patchAssignable s.1 r.1 ∧ patchAssignable s.1 r.2)
                        ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_alt_iter_step_spec _ _ _)

@[spec] private theorem c_rep_pre_spec (greedy : Bool) (states : Array Unchecked.State)
    : ⦃fun s => s = states ∧ NextOfLt states⦄
      Code.c_rep_pre greedy
      ⦃fun r s => stateIdNextOfLt states r s ∧ assignableIf states s ∧ patchAssignable s r;
                  fun _ _ => False⦄ := by
  vcgen [Code.c_rep_pre] with finish [Unchecked.State.nextOf,
    Unchecked.EatMode.nextOf, assignableP, assignableP2, isAppend_of_isAppendOfState,
    isAppend_of_assignableP2, isAppend_of_assignableP, patchAssignable_of_append]

@[spec] private theorem c_rep_pre_lift_spec (greedy : Bool) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      (Code.c_rep_pre greedy : Code.CompilerM Unchecked.StateID)
      ⦃fun r s => (stateIdNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r)
                  ∧ s.2.1 = captures ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  exact lift_spec_PatchM_to_CompilerM (c_rep_pre_spec _ _)

@[simp, grind =] private theorem cMemAndValid_iff (prev caps : Array NFA.Capture) :
    cMemAndValid prev caps ↔ (∀ a ∈ prev, a ∈ caps) ∧ NFA.Capture.Valid caps := by
  rfl

mutual

@[spec] private theorem c_alt_iter_fold_spec (hirs : Array Hir) (union «end» : Unchecked.StateID)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧ union < states.size ∧ «end» < states.size ∧ NextOfLt states
                ∧ patchAssignable states union
                ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_alt_iter.fold hirs union «end»
      ⦃fun _ s => statesNextOfLeLt states s.1 ∧ assignableIf states s.1
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  have ih := fun hir (_ : sizeOf hir < sizeOf hirs) st cap => c_spec hir st cap
  unfold Code.c_alt_iter.fold
  vcgen [ih, patch_lift_spec] invariants
  · fun _ _ _ s => states.size ≤ s.1.size ∧ union < s.1.size ∧ «end» < s.1.size
                              ∧ assignableIf states s.1 ∧ patchAssignable states union
                              ∧ NextOfLt s.1 ∧ cMemAndValid captures s.2.1
  with finish [tRefNextOfLt, tRefLt, stateIdNextOfEqLt, statesNextOfLeLt, cMemAndValid,
      assignableIf]
termination_by sizeOf hirs

@[spec] private theorem c_concat_fold_spec (tail : Array Hir) (sid : Unchecked.StateID)
 (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ sid < states.size ∧ NextOfLt states ∧ patchAssignable states sid)
                  ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_concat.fold tail sid
      ⦃fun r s => stateIdNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  have ih := fun hir (_ : sizeOf hir < sizeOf tail) st cap => c_spec hir st cap
  unfold Code.c_concat.fold
  vcgen [ih] invariants
  · fun _ _ r s => states.size ≤ s.1.size ∧ sid < s.1.size ∧ r < s.1.size ∧ NextOfLt s.1
                    ∧ assignableIf states s.1 ∧ patchAssignable s.1 r ∧ cMemAndValid captures s.2.1
  with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf tail

@[spec] private theorem c_alt_iter_spec (alt : Regex.Syntax.Alternation)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_alt_iter alt
      ⦃fun r s => tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  obtain ⟨first, second, tail⟩ := alt
  have : sizeOf first < sizeOf (Regex.Syntax.Alternation.mk first second tail) := by simp +arith
  have : sizeOf second < sizeOf (Regex.Syntax.Alternation.mk first second tail) := by simp +arith
  have : sizeOf tail < sizeOf (Regex.Syntax.Alternation.mk first second tail) := by simp +arith
  have h1 := fun st cap => c_spec first st cap
  have h2 := fun st cap => c_spec second st cap
  have h3 := fun u e st cap => c_alt_iter_fold_spec tail u e st cap
  unfold Code.c_alt_iter
  vcgen [h1, h2, h3] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf alt

@[spec] private theorem c_bounded_spec (hir : Hir) (min max : Nat) (greedy : Bool)
  (possessive : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_bounded hir min max greedy possessive
      ⦃fun r s => tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  have h1 := fun st cap => c_exactly_spec hir min st cap
  have h2 := fun p e st cap => c_bounded_fold_spec hir (max - min) p e greedy possessive st cap
  unfold Code.c_bounded
  vcgen [h1, h2, c_possessive_le_lift_spec, add_empty_lift_CompilerM_spec]
    with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf hir + sizeOf min + sizeOf (max - min) + 1

@[spec] private theorem c_lookaround_spec (look : Lookaround) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_lookaround look
      ⦃fun r s => tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  cases look with
  | PositiveLookahead h | NegativeLookahead h | PositiveLookbehind _ h | NegativeLookbehind _ h =>
    have ih := fun st cap => c_spec h st cap
    unfold Code.c_lookaround
    vcgen [ih] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf look

@[spec] private theorem c_repetition_spec (rep : Repetition) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧ NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_repetition rep
      ⦃fun r s => tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  unfold Code.c_repetition
  split
  next _ sub =>
    have h1 := fun st cap => c_spec sub st cap
    vcgen [h1] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  next _ sub =>
    have h1 := fun st cap => c_spec sub st cap
    vcgen [h1] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  next min greedy possessive sub =>
    have h1 := fun st cap => c_spec sub st cap
    have h2 := fun st cap => c_at_least_spec sub min greedy possessive st cap
    vcgen [h1, h2] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  next min max greedy possessive sub _ _ =>
    have h2 := fun st cap => c_bounded_spec sub min max greedy possessive st cap
    vcgen [h2] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf rep

@[spec] private theorem c_exactly_spec (hir : Hir) (n : Nat) (states : Array Unchecked.State)
   (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_exactly hir n
      ⦃fun r s => tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  unfold Code.c_exactly
  split
  · have h1 := fun st cap => c_spec hir st cap
    have h2 := fun e st cap => c_exactly_fold_spec hir (n - 1) e st cap
    vcgen [h1, h2] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  · vcgen with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf hir + sizeOf n

@[spec] private theorem c_concat_spec (hirs : Array Hir) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => (s.1 = states ∧ NextOfLt states) ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_concat hirs
      ⦃fun r s => tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  unfold Code.c_concat
  split
  · rename_i head tail heq
    have := Array.sizeOf_head?_of_mem heq
    have := Array.sizeOf_head?_of_tail heq
    have h1 := fun st cap => c_spec head st cap
    have h2 := fun e st cap => c_concat_fold_spec tail e st cap
    vcgen [h1, h2] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  · vcgen with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf hirs

@[spec] private theorem c_exactly_fold_spec (hir : Hir) (n : Nat) («end» : Unchecked.StateID)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧ «end» < states.size ∧  NextOfLt states
                  ∧ patchAssignable states «end»
                  ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_exactly.fold hir n «end»
      ⦃fun r s => stateIdNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  unfold Code.c_exactly.fold
  split
  · have ih := fun st cap => c_spec hir st cap
    vcgen [ih] invariants
    · fun _ _ r s => states.size ≤ s.1.size ∧ r < s.1.size ∧ «end» < s.1.size
                      ∧ assignableIf states s.1 ∧ patchAssignable s.1 r
                      ∧ patchAssignable states «end»
                      ∧ NextOfLt s.1 ∧ cMemAndValid captures s.2.1
    with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  · vcgen with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf hir + sizeOf n

@[spec] private theorem c_at_least_spec (hir : Hir) (n : Nat) (greedy : Bool) (possessive : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_at_least hir n greedy possessive
      ⦃fun r s => tRefNextOfLt states r s.1 ∧ assignableIf states s.1
            ∧ patchAssignable s.1 r.end ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  have h1 := fun st cap => c_spec hir st cap
  have h2 := fun st cap => c_exactly_spec hir (n - 1) st cap
  unfold Code.c_at_least
  vcgen [h1, h2] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf hir + sizeOf n + 1

@[spec] private theorem c_bounded_fold_spec  (hir : Hir) (n : Nat) («prefix» : ThompsonRef)
  (empty : Unchecked.StateID) (greedy : Bool) (possessive : Bool)
  (states : Array Unchecked.State) (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧ tRefLt «prefix» states ∧ empty < states.size ∧ NextOfLt states
                 ∧ patchAssignable states «prefix».end
                 ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_bounded.fold hir n «prefix» empty greedy possessive
      ⦃fun r s => stateIdNextOfLeLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  unfold Code.c_bounded.fold
  split
  · have ih := fun st cap => c_spec hir st cap
    vcgen [ih, c_bounded.fold.patch_lift_spec] invariants
    · fun _ _ r s => states.size ≤ s.1.size ∧ r < s.1.size ∧ empty < s.1.size
                      ∧ assignableIf states s.1 ∧ patchAssignable s.1 r
                      ∧ patchAssignable states «prefix».end
                      ∧ NextOfLt s.1 ∧ cMemAndValid captures s.2.1
    with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  · vcgen with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf hir + sizeOf n

@[spec] private theorem c_cap_spec (hir : Regex.Syntax.Capture) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c_cap hir
      ⦃fun r s => tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  obtain ⟨group, _, sub⟩ := hir
  have ih := fun st cap => c_spec sub st cap
  unfold Code.c_cap
  vcgen [ih] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf hir

@[spec] private theorem c_spec (hir : Hir) (states : Array Unchecked.State)
  (captures : Array NFA.Capture)
    : ⦃fun s => s.1 = states ∧  NextOfLt states ∧ s.2.1 = captures ∧ cValid captures⦄
      Code.c hir
      ⦃fun r s => tRefNextOfLt states r s.1 ∧ assignableIf states s.1 ∧ patchAssignable s.1 r.end
                  ∧ cMemAndValid captures s.2.1; fun _ _ => False⦄ := by
  have : sizeOf hir.kind < sizeOf hir := Hir.sizeOfKindOfHir hir
  unfold Code.c
  split
  any_goals vcgen with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  all_goals rename_i x heq
  · vcgen [fun st cap => c_lookaround_spec x st cap] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  · vcgen [fun st cap => c_repetition_spec x st cap] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  · vcgen [fun st cap => c_cap_spec x st cap] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  · vcgen [fun st cap => c_concat_spec x st cap] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
  · vcgen [fun st cap => c_alt_iter_spec x st cap] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]
termination_by sizeOf hir

end

@[spec] private theorem c_init_spec (anchored : Bool)
    : ⦃fun s => s.1.size = 0 ∧ s.2.1.size = 0⦄
      Code.init anchored
      ⦃fun r s => tRefLt r s.1 ∧ NextOfLt s.1 ∧ patchAssignable s.1 r.end ∧ cValid s.2.1;
                  fun _ _ => False⦄ := by
  vcgen [Code.init] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]

@[spec] theorem c_compile_spec (anchored : Bool) (hir : Hir)
    : ⦃fun s => s.1.size = 0 ∧ s.2.1.size = 0⦄
      Code.compile anchored hir
      ⦃fun _ s => NextOfLt s.1 ∧ cValid s.2.1; fun _ _ => False⦄ := by
  vcgen [Code.compile] with finish [tRefNextOfLt, tRefLt,
      tRefNextOfLeLt, stateIdNextOfEqLt, stateIdNextOfLeLt, stateIdNextOfLt, cMemAndValid,
      assignableIf, assignableP, assignableP2, isAppendOfStateID, isAppendOfState]

theorem compile_nextOf_lt {anchored : Bool} {expr : Hir}
  (h : Code.compile anchored expr (#[], #[], #[]) = EStateM.Result.ok () (states, captures, groups))
    : NextOfLt states := by
  have := (c_compile_spec anchored expr).le_wp (#[], #[], #[]) ⟨rfl, rfl⟩
  simp only [WP.wp, WP.trans, h] at this
  exact this.1

theorem compile_captures_valid {anchored : Bool} {expr : Hir}
  (h : Code.compile anchored expr (#[], #[], #[]) = EStateM.Result.ok () (states, captures, groups))
    : Capture.Valid captures := by
  have := (c_compile_spec anchored expr).le_wp (#[], #[], #[]) ⟨rfl, rfl⟩
  simp only [WP.wp, WP.trans, h] at this
  grind [= cValid]

theorem compile_eq_ok {anchored : Bool} {expr : Hir}
   : ∃ s, Code.compile anchored expr (#[], #[], #[]) = EStateM.Result.ok () s := by
  have := (c_compile_spec anchored expr).le_wp (#[], #[], #[]) ⟨rfl, rfl⟩
  simp only [WP.wp, WP.trans] at this
  split at this
  · rename_i a s' heq
    exact ⟨s', heq⟩
  · exact this.elim
