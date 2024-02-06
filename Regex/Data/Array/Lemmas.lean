import Regex.Data.List.Lemmas
import Regex.Data.Array.Basic

namespace Array

theorem size_one (a : α) : (#[a] : Array α).size = 1 := rfl

theorem default_size_zero (arr : Array α) (h : arr = default) : arr.size = 0 := by
  unfold Array.size List.length
  split <;> try simp_all
  contradiction

theorem non_empty_of_last? (arr : Array α) (h: Array.last? arr = some last) : 0 < arr.size := by
  unfold Array.last? at h
  split at h <;> simp_all

theorem pop?_of_last? (arr : Array α) (h: Array.last? arr = some last)
    : ∃ (arr' : Array α), Array.pop? arr = some (last, arr') := by
  unfold Array.pop?
  unfold Array.last? at h
  split <;> simp_all

theorem pop?_of_non_empty (arr : Array α) (h : 0 < arr.size)
    : ∃ (arr' : Array α) (last : α), Array.pop? arr = some (last, arr') := by
  unfold Array.pop?
  split <;> simp_all

theorem last?_eq_getLast (a : Array α) (h1: Array.last? a = some last) (h2 : a.data ≠ [])
    : List.getLast a.data h2 = last := by
  unfold Array.last? at h1
  split at h1 <;> simp_all
  rw [← List.getLast_eq_get a.data h2] at h1
  simp [h1]

theorem lt_of_pop?_eq_last? {arr : Array α} (h : Array.pop? arr = some (last, arr'))
    : 0 < arr.data.length := by
  unfold Array.pop? at h
  split at h <;> simp_all

theorem get_last_of_pop? {arr : Array α} (h1 : Array.pop? arr = some (last, arr'))
  (h2 : arr.data.length - 1 < arr.data.length)
    : List.get arr.data ⟨arr.data.length - 1, h2⟩ = last := by
  unfold Array.pop? at h1
  split at h1 <;> try simp_all

theorem concat_of_pop? {arr : Array α} (h : Array.pop? arr = some (last, arr'))
    : arr.data = arr'.data ++ [last] := by
  have hlt : 0 < arr.data.length := by simp_all[Array.lt_of_pop?_eq_last? h]
  have hlt : arr.data.length - 1 < arr.data.length := Nat.pred_lt' hlt
  have hlast : List.get arr.data ⟨arr.data.length - 1, hlt⟩ = last :=
     Array.get_last_of_pop? h hlt
  unfold Array.pop? at h
  split at h <;> simp_all
  have hr : Array.pop arr = arr' := h
  have hr : (Array.pop arr).data = arr'.data := by simp_all
  have hx : (Array.pop arr).data = List.dropLast arr.data := Array.pop_data arr
  rw [hx] at hr
  have hy : List.dropLast (arr'.data ++ [last]) = arr'.data := by apply List.dropLast_concat
  have hz : List.dropLast arr.data = List.dropLast (arr'.data ++ [last]) := by
    rw [← hy] at hr
    rw [hr]
  simp [List.eq_of_dropLast_eq_last_eq hz hlt (by simp_all)
          (by rw [List.get_last_of_concat _]; rw [hlast])]
