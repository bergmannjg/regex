import Std.Tactic.Do
import Std.Tactic.Do.Syntax

import Regex.Do.Triple.SpecLemmas
import Regex.Compiler.Basic

namespace Compiler

open Syntax
open NFA

namespace Code

abbrev PatchM α := EStateM String (Array Unchecked.State) α

/-- Add a transition from one state to another. -/
def patch («from» «to» : Unchecked.StateID) : PatchM Unit := do
  let states ← get
  if h : «from» < states.size then
    match hm : states[«from»]'h with
    | .Empty _ => set (states.set «from» (Unchecked.State.Empty «to») h)
    | .NextChar offset _ => set (states.set «from» (Unchecked.State.NextChar offset «to») h)
    | .Fail =>  EStateM.Result.error s!"patch states .Fail unexpected"
    | .Eat (.Until s) n =>
        if s = 0
        then set (states.set «from» (Unchecked.State.Eat (.Until «to») n) h)
        else if n = 0
        then set (states.set «from» (Unchecked.State.Eat (.Until s) «to») h)
        else EStateM.Result.error "patch states, .Eat s and n not null"
    | .Eat (.ToLast s) n =>
        if s = 0
        then set (states.set «from» (Unchecked.State.Eat (.ToLast «to») n) h)
        else if n = 0 then
        set (states.set «from» (Unchecked.State.Eat (.ToLast s) «to») h)
        else EStateM.Result.error "patch states, .Eat s and n not null"
    | .ChangeFrameStep f t =>
        if f = 0
        then set (states.set «from» (Unchecked.State.ChangeFrameStep «to» t) h)
        else if t = 0
        then set (states.set «from» (Unchecked.State.ChangeFrameStep f «to»))
        else EStateM.Result.error "patch states, .ChangeFrameStep from and to not null"
    | .RemoveFrameStep _ =>
      set (states.set «from» (Unchecked.State.RemoveFrameStep «to») h)
    | .Look look _ =>
      set (states.set «from» (Unchecked.State.Look look «to»))
    | .BackRef b f _ =>
      set (states.set «from» (Unchecked.State.BackRef b f «to»))
    | .ByteRange t =>
        set (states.set «from» (Unchecked.State.ByteRange {t with «next» := «to»}) h)
    | .Capture role _ pattern_id group_index slot =>
        set (states.set «from» (Unchecked.State.Capture role «to» pattern_id group_index slot))
    | .BinaryUnion alt1 alt2 =>
        if alt1 = 0
        then set (states.set «from» (Unchecked.State.BinaryUnion «to» alt2) h)
        else if alt2 = 0
        then set (states.set «from» (Unchecked.State.BinaryUnion alt1 «to») h)
        else EStateM.Result.error "patch states, .BinaryUnion alt1 and alt2 not null"
    | .SparseTransitions _ => set states
    | .Union alternates =>
        set (states.set «from» (Unchecked.State.Union (alternates.push «to»)) h)
    | .UnionReverse alternates =>
        set (states.set «from» (Unchecked.State.UnionReverse (alternates.push «to»)) h)
    | .Match _ => EStateM.Result.error s!"patch states .Match unexpected"
  else EStateM.Result.error s!"patch index error"

end Code

namespace Lemmas

private theorem all_set_next_of_lt (n : Unchecked.StateID) (s : Unchecked.State)
  (states : Array Unchecked.State)
  (h : n < states.size) (hn : Unchecked.State.nextOf s < states.size)
  (hlt : ∀ (i : Nat) _, states[i].nextOf < states.size)
    : ∀ (i : Nat) (hi : i < states.size), (((states.set n s h)[i]'(by grind)).nextOf < states.size) := by
  grind

private theorem eat_lt («from» s : Nat) (n : Unchecked.StateID) (m : Unchecked.EatMode)
  (states : Array Unchecked.State) (h : «from» < states.size)
  (hmode : Unchecked.EatMode.nextOf m = s)
  (hm : states[«from»]'h = Unchecked.State.Eat m n)
  (hlt : states[«from»].nextOf < states.size)
    : s < states.size ∧ n < states.size := by
  rw [hm] at hlt
  simp [Unchecked.EatMode.nextOf] at hmode
  unfold Unchecked.State.nextOf at hlt
  split at hlt <;> try simp_all [Nat.max_lt]

private theorem change_frame_step_lt («from» : Nat) (f t : Unchecked.StateID)
  (states : Array Unchecked.State) (h : «from» < states.size)
  (hm : states[«from»]'h = Unchecked.State.ChangeFrameStep f t)
  (hlt : states[«from»].nextOf < states.size)
    : f < states.size ∧ t < states.size := by
  rw [hm] at hlt
  unfold Unchecked.State.nextOf at hlt
  grind

private theorem binary_union_lt («from» : Nat) (alt1 alt2 : Unchecked.StateID)
  (states : Array Unchecked.State) (h : «from» < states.size)
  (hm : states[«from»]'h = Unchecked.State.BinaryUnion alt1 alt2)
  (hlt : states[«from»].nextOf < states.size)
    : alt1 < states.size ∧ alt2 < states.size := by
  rw [hm] at hlt
  unfold Unchecked.State.nextOf at hlt
  grind

private theorem union_lt («from» to : Nat) (alternates : Array Unchecked.StateID)
  (states : Array Unchecked.State) (h : «from» < states.size)
  (ht : to < states.size) (hm : states[«from»]'h = Unchecked.State.Union alternates)
  (hlt : states[«from»].nextOf < states.size)
    : List.maxD 0 (alternates.toList ++ [to]) < states.size := by
  rw [hm] at hlt
  simp +zetaDelta [Unchecked.State.nextOf] at hlt
  exact List.maxD_of_append_lt hlt ht

private theorem union_reverse_lt («from» to : Nat) (alternates : Array Unchecked.StateID)
  (states : Array Unchecked.State) (h : «from» < states.size)
  (ht : to < states.size)
  (hm : states[«from»]'h = Unchecked.State.UnionReverse alternates)
  (hlt : states[«from»].nextOf < states.size)
    : List.maxD 0 (alternates.toList ++ [to]) < states.size := by
  rw [hm] at hlt
  simp +zetaDelta [Unchecked.State.nextOf] at hlt
  exact List.maxD_of_append_lt hlt ht

open Std.Do

set_option mvcgen.warning false

@[spec] theorem patch_spec («from»: Unchecked.StateID) {«to» : Unchecked.StateID}
  {states : Array Unchecked.State}
    : ⦃fun s => ⌜s = states ∧ nextOfLt states ∧ «from» < states.size ∧ «to» < states.size⌝⦄
      Code.patch «from» «to»
      ⦃post⟨fun _ r => ⌜states.size = r.size ∧ «to» < r.size ∧ nextOfLt r⌝, fun _ => ⌜True⌝ ⟩⦄ := by
  mintro _
  unfold Code.patch
  mvcgen
  all_goals simp_all
  all_goals try intro _ _; expose_names
  all_goals try (apply all_set_next_of_lt «from» _ states h_2.right.right.left ?_ (h.right.left)); try assumption
  all_goals try simp_all [Unchecked.State.nextOf, h_2.right.right.right, Nat.max_lt]
  all_goals try simp [wp]
  all_goals try simp [nextOfLt] at h
  expose_names
  · simp [eat_lt «from» s_1 n (Unchecked.EatMode.Until s_1)
      states (by grind) (by simp_all [Unchecked.EatMode.nextOf]) (by simp_all) (by grind)]
  · simp [eat_lt «from» s_1 n (Unchecked.EatMode.Until s_1)
      states (by grind) (by simp_all [Unchecked.EatMode.nextOf]) (by simp_all) (by grind)]
  · simp [eat_lt «from» s_1 n (Unchecked.EatMode.ToLast 0)
      states (by grind) (by simp_all [Unchecked.EatMode.nextOf]) (by simp_all) (by grind)]
  · simp [eat_lt «from» s_1 n (Unchecked.EatMode.ToLast s_1)
      states (by grind) (by simp_all [Unchecked.EatMode.nextOf]) (by simp_all) (by grind)]
  · simp [change_frame_step_lt «from» f t states (by grind) (by simp_all) (by grind)]
  · simp [change_frame_step_lt «from» f t states (by grind) (by simp_all) (by grind)]
  · simp [binary_union_lt «from» alt1 alt2 states (by grind) (by simp_all) (by grind)]
  · simp [binary_union_lt «from» alt1 alt2 states (by grind) (by simp_all) (by grind)]
  · simp [union_lt «from» «to» alternates states (by simp_all) (by grind) (by grind) (by grind)]
  · simp [union_reverse_lt «from» «to» alternates states (by simp_all) (by grind) (by grind) (by grind)]
end Lemmas
