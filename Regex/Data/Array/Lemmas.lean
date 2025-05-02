import Init.Data.List.Lemmas
import Init.Data.Array.Mem

import Regex.Data.List.Lemmas
import Regex.Data.Array.Basic

namespace Array

theorem sizeOf_head?_of_mem [SizeOf α] {as : Array α} (h : Array.head? as = some (a, as'))
    : sizeOf a < sizeOf as := by
  unfold Array.head? at h
  split at h <;> simp_all
  exact Array.sizeOf_lt_of_mem <| (@Array.mem_def α a as).mpr (by simp_all)

theorem sizeOf_head?_of_tail [SizeOf α] {as : Array α} (h : Array.head? as = some (a, as'))
    : sizeOf as' < sizeOf as := by
  unfold Array.head? at h
  split at h <;> simp_all
  cases as with | _ as =>
  cases as' with | _ as' =>
  simp_all
  simp +arith

theorem sizeOf_dropLast_cons [SizeOf α] (a : α) (as : List α)
    : sizeOf (a :: as).dropLast < sizeOf (a :: as) := by
  induction as generalizing a with
  | nil => simp +arith
  | cons a' as ih => apply Nat.add_lt_add_left _; exact ih a'

theorem sizeOf_dropLast_non_empty [SizeOf α] (as : List α) (h : 0 < as.length)
    : sizeOf as.dropLast < sizeOf as := by
  unfold List.length at h
  split at h <;> simp_all
  exact sizeOf_dropLast_cons _ _

theorem sizeOf_pop_non_empty [SizeOf α] (as : Array α) (h : 0 < as.toList.length)
    : sizeOf as.pop < sizeOf as := by
  unfold Array.pop
  cases as with | _ as =>
  simp
  exact sizeOf_dropLast_non_empty _ h

theorem sizeOf_pop? [SizeOf α] {as : Array α} (h : Array.pop? as = some (a, as'))
    : sizeOf as' < sizeOf as := by
  unfold Array.pop? at h
  split at h <;> simp_all
  rename_i hl
  rw [← h.right]
  exact sizeOf_pop_non_empty as hl

theorem size_one (a : α) : (#[a] : Array α).size = 1 := rfl

theorem default_size_zero (arr : Array α) (h : arr = default) : arr.size = 0 :=
  size_eq_zero_iff.mpr h

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

theorem last?_eq_getLast (a : Array α) (h1: Array.last? a = some last) (h2 : a.toList ≠ [])
    : List.getLast a.toList h2 = last := by
  unfold Array.last? at h1
  split at h1 <;> simp_all
  rw [← h1]
  have := @List.getLast_eq_getElem α a.toList h2
  simp_all

theorem lt_of_pop?_eq_last? {arr : Array α} (h : Array.pop? arr = some (last, arr'))
    : 0 < arr.toList.length := by
  unfold Array.pop? at h
  split at h <;> simp_all

theorem get_last_of_pop? {arr : Array α} (h1 : Array.pop? arr = some (last, arr'))
  (h2 : arr.toList.length - 1 < arr.toList.length)
    : List.get arr.toList ⟨arr.toList.length - 1, h2⟩ = last := by
  unfold Array.pop? at h1
  split at h1 <;> try simp_all

theorem concat_of_pop? {arr : Array α} (h : Array.pop? arr = some (last, arr'))
    : arr.toList = arr'.toList ++ [last] := by
  have hlt : 0 < arr.toList.length := lt_of_pop?_eq_last? h
  have hlt : arr.toList.length - 1 < arr.toList.length := Nat.pred_lt_of_lt hlt
  have hlast : List.get arr.toList ⟨arr.toList.length - 1, hlt⟩ = last :=
     Array.get_last_of_pop? h hlt
  unfold Array.pop? at h
  split at h <;> simp_all
  have hr : Array.pop arr = arr' := h
  have hr : (Array.pop arr).toList = arr'.toList := congrArg toList h
  have hx : (Array.pop arr).toList = List.dropLast arr.toList := @Array.toList_pop α arr
  rw [hx] at hr
  have hy : List.dropLast (arr'.toList ++ [last]) = arr'.toList := List.dropLast_concat
  have hz : List.dropLast arr.toList = List.dropLast (arr'.toList ++ [last]) := by
    rw [← hy] at hr
    exact hr
  simp [List.eq_of_dropLast_eq_last_eq hz hlt (by simp_all)
          (by rw [List.get_last_of_concat _]; exact hlast)]

theorem get_eq_get?_some {as : Array α} (hlt : i < as.size) (h : a = as[i]'hlt)
    : as[i]? = some a := by
  simp_all
