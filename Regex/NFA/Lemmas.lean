import Batteries.Data.Fin.Basic
import Regex.Utils
import Regex.Data.List.Lemmas
import Regex.Data.Array.Basic
import Regex.Data.Array.Lemmas
import Regex.NFA.Basic

namespace NFA

@[grind] theorem valid_sorted_of_valid (captures : Array NFA.Capture) (h : NFA.Capture.Valid captures)
    : NFA.Capture.Valid (captures.mergeSort (fun a b => decide (a ≤ b))) := by
  apply NFA.Capture.Valid.mk
  have := NFA.Capture.Valid.forall h
  simp_all

@[grind] theorem valid_unique_of_valid (captures : Array NFA.Capture) (h : NFA.Capture.Valid captures)
    : NFA.Capture.Valid (captures.unique) := by
  apply NFA.Capture.Valid.mk
  have := NFA.Capture.Valid.forall h
  simp_all

theorem CapturesValidOfRangeMap (captures : Array NFA.Capture)
  (h : (List.range captures.size).map (fun i =>
          if i % 2 = 0 then ⟨Capture.Role.Start, i.div 2⟩ else ⟨Capture.Role.End, i.div 2⟩)
        = captures.toList)
    : NFA.Capture.Valid captures := by
  apply NFA.Capture.Valid.mk
  generalize hf : (fun (i : Nat) => ((if i % 2 = 0 then ⟨Capture.Role.Start, i.div 2⟩
                                else ⟨Capture.Role.End, i.div 2⟩) : NFA.Capture)) = f at h
  intro ⟨a, _⟩
  exact ⟨⟨Capture.Role.Start, a.group⟩, by
    and_intros
    · have h : a ∈ List.map f (List.range captures.size) := by grind
      have ⟨i, ⟨h1, h2⟩⟩ : ∃ i, i ∈ (List.range captures.size) ∧ f i = a := List.mem_map.mp h
      rw [← hf] at h2
      simp at h2
      split at h2
      · grind
      · have h : i % 2 = 1 := by grind
        have : f (i - 1) ∈ List.map f (List.range captures.size) := by grind
        have : f (i - 1) ∈ captures := by grind
        have : f (i - 1) = { role := Capture.Role.Start, group := a.group } := by
          rw [←hf]
          simp
          split
          · simp
            have : a.group = i.div 2 := by grind
            rw [this, ←h]
            exact Nat.div_eq_sub_mod_div.symm
          · grind
        simp_all
    · rfl
    · rfl⟩
