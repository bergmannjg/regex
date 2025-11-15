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
    | .Capture role _ pattern_id group_index =>
        set (states.set «from» (Unchecked.State.Capture role «to» pattern_id group_index))
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

@[grind .] theorem all_set_next_of_lt (n : Unchecked.StateID) (s : Unchecked.State)
  (states : Array Unchecked.State)
  (h : n < states.size) (hn : Unchecked.State.nextOf s < states.size)
  (hlt : ∀ (i : Nat) _, states[i].nextOf < states.size)
    : ∀ (i : Nat) (hi : i < states.size), (((states.set n s h)[i]'(by grind)).nextOf < states.size) := by
  grind

private theorem maxD_of_union_lt («from» : Nat) (s : Array Unchecked.State) (alternates : Array Unchecked.StateID)
  (h1 : «from» < s.size) (h3 : NextOfLt s)
  (hm : s[«from»] = Unchecked.State.Union alternates)
    : List.maxD 0 alternates.toList < s.size := by
  have h3 := NextOfLt.forall h3
  have hn := h3 «from» h1
  rw [hm] at hn
  unfold  Unchecked.State.nextOf at hn
  split at hn
  all_goals grind

private theorem maxD_of_union_reverse_lt («from» : Nat) (s : Array Unchecked.State) (alternates : Array Unchecked.StateID)
  (h1 : «from» < s.size) (h3 : NextOfLt s)
  (hm : s[«from»] = Unchecked.State.UnionReverse alternates)
    : List.maxD 0 alternates.toList < s.size := by
  have h3 := NextOfLt.forall h3
  have hn := h3 «from» h1
  rw [hm] at hn
  unfold  Unchecked.State.nextOf at hn
  split at hn
  all_goals grind

@[grind .] theorem nextOfLt_of_union («from» to : Nat) (s : Array Unchecked.State) (alternates : Array Unchecked.StateID)
  (h1 : «from» < s.size) (h2 : to < s.size) (h3 : NextOfLt s)
  (hm : s[«from»] = Unchecked.State.Union alternates)
    : NextOfLt (s.set «from» (Unchecked.State.Union (alternates.push to)) h1) := by
  apply NextOfLt.mk
  intros i _
  by_cases hi : i = «from»
  · unfold Unchecked.State.nextOf
    split
    case h_12 =>
      expose_names
      have : alternates.toList ++ [to] = alts.toList := by grind
      have : List.maxD 0 alts.toList < s.size := by
        rw [← this]
        exact List.maxD_of_append_lt (maxD_of_union_lt «from» s alternates h1 h3 hm) (by grind)
      grind
    all_goals grind
  · grind

@[grind .] theorem nextOfLt_of_union_reverse («from» to : Nat) (s : Array Unchecked.State) (alternates : Array Unchecked.StateID)
  (h1 : «from» < s.size) (h2 : to < s.size) (h3 : NextOfLt s)
  (hm : s[«from»] = Unchecked.State.UnionReverse alternates)
    : NextOfLt (s.set «from» (Unchecked.State.UnionReverse (alternates.push to)) h1) := by
  apply NextOfLt.mk
  intros i _
  by_cases hi : i = «from»
  · unfold Unchecked.State.nextOf
    split
    case h_13 =>
      expose_names
      have : alternates.toList ++ [to] = alts.toList := by grind
      have : List.maxD 0 alts.toList < s.size := by
        rw [← this]
        exact List.maxD_of_append_lt (maxD_of_union_reverse_lt «from» s alternates h1 h3 hm) (by grind)
      grind
    all_goals grind
  · grind

end Lemmas
