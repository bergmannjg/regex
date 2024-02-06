import Init.Data.Ord
import Std.Logic
import Std.Data.Nat.Lemmas
import Std.Data.Fin.Lemmas
import Std.Data.Int.Lemmas
import Std.Data.List.Basic
import Std.Data.Array.Init.Lemmas
import Mathlib.Data.List.Chain
import Regex.Utils
import Regex.Bound
import Regex.Data.UInt.Basic
import Regex.Data.Char.Basic
import Regex.Data.List.Lemmas
import Regex.Data.Array.Basic
import Regex.Data.Array.Lemmas
import Regex.Interval.Basic

namespace Ranges

theorem empty_isNonOverlapping {α : Type u} [Ord α] [LT α] [LE α] [Bound α] [HSub α α Nat]
    : nonOverlapping (#[] : Array (Range α)) := by
  unfold nonOverlapping dataIsNonOverlapping
  split <;> simp_all

theorem single_isNonOverlapping (ranges : Array (Range Char)) (h : ranges.size = 1)
    : nonOverlapping ranges  := by
  unfold nonOverlapping dataIsNonOverlapping
  split <;> try simp_all
  unfold Array.size at h
  unfold List.length at h
  split at h <;> try simp_all
  unfold List.length at h
  split at h <;> try simp_all

end Ranges

instance (α : Type u) [Ord α] [LT α] [LE α] [Bound α] [HSub α α Nat]
    [(a b : α) → Decidable (a < b)] [(a b : α) → Decidable (a = b)]
    : Inhabited $ IntervalSet α where
  default := ⟨#[], Ranges.empty_isNonOverlapping⟩

namespace Interval

def singleton (r : Range Char) : IntervalSet Char :=
  let arr := #[r]
  ⟨arr, by simp [Ranges.single_isNonOverlapping arr (Array.size_one r)]⟩

theorem pred_lt' {n m : Nat} (h : m < n) : Nat.pred n < n :=
  Nat.pred_lt (Nat.not_eq_zero_of_lt h)

theorem Fin.pred {i : Fin n} (h : 0 < i.val) : LT.lt (i.val-1) n := by
  have h1 : i.val-1 < i.val := pred_lt' h
  have h2 : i.val < n := i.isLt
  simp [Nat.lt_trans h1 h2]

theorem isNonOverlapping (l r : Range Char)
  (h1 : ¬(r.start.toNat - l.end.toNat) = 1) (h2 : ¬r.start < l.end) (h3 : ¬l.end = r.start)
    : Range.nonOverlapping l r := by
  have h1 : ¬1 = (r.start.toNat - l.end.toNat) := fun h => h1 (h.symm)
  have h2 : l.end ≤  r.start := Nat.not_lt.mp h2
  have h3 : ¬l.end.val.val = r.start.val.val := UInt32.val_ne_of_ne (Char.val_ne_of_ne h3)
  have h : l.end.toNat < r.start.toNat := Nat.lt_of_le_of_ne h2 (Fin.val_ne_of_ne h3)
  have h : l.end.toNat+1 ≤ r.start.toNat := Nat.succ_le_of_lt h
  have h : 1 + l.end.toNat ≤ r.start.toNat := by rw [Nat.add_comm]; simp [h]
  have h : 1 < r.start.toNat - l.end.toNat := Nat.lt_of_le_of_ne (Nat.le_sub_of_add_le h) h1
  unfold Range.nonOverlapping
  rw [← Range.Char.sub_def]
  unfold Range.Char.sub
  simp [h]

theorem nonOverlappingWithLast_of_empty (ranges : Array $ Range Char) (next : Option (Range Char))
    (h2 : ranges.size = 0) : nonOverlappingWithLast ranges next  := by
  unfold nonOverlappingWithLast
  split <;> try simp_all
  · unfold Array.size List.length at h2
    split at h2 <;> try simp_all
    rename_i heq' x heq
    unfold Array.last? at heq'
    split at heq' <;> try simp_all
    rename_i h
    unfold List.length at h
    split at h <;> try simp_all
  · unfold Array.size List.length at h2
    split at h2 <;> try simp_all
    rename_i heq' x heq
    unfold Array.last? at heq'
    split at heq' <;> try simp_all
    rename_i h
    unfold List.length at h
    split at h <;> try simp_all

theorem nonOverlappingWithLast_with_none_eq_empty (acc : Acc) (h : acc.next.isNone)
    : acc.set.ranges.size = 0 := by
  have hx : nonOverlappingWithLast acc.set.ranges acc.next := acc.nonOverlapping
  unfold nonOverlappingWithLast at hx
  split at hx <;> try simp_all

  rename_i heq _
  unfold Array.last? at heq
  split at heq <;> try simp_all

theorem nonOverlappingWithLast_of_none (acc : Acc) (n : Range Char) (h : acc.next.isNone)
    : nonOverlappingWithLast acc.set.ranges n  := by
  have hx : acc.set.ranges.size = 0 := nonOverlappingWithLast_with_none_eq_empty acc h
  simp [nonOverlappingWithLast_of_empty acc.set.ranges n hx]

theorem nonOverlappingWithLast_of_val (acc : Acc) (n : Range Char) (h : is_start_eq acc.next n)
    : nonOverlappingWithLast acc.set.ranges n  := by
  have hx : nonOverlappingWithLast acc.set.ranges acc.next := acc.nonOverlapping
  unfold nonOverlappingWithLast
  unfold nonOverlappingWithLast at hx
  unfold is_start_eq at h
  simp_all
  split <;> try simp_all
  unfold Range.nonOverlapping
  split at hx <;> try simp_all
  unfold Range.nonOverlapping at hx
  simp_all

theorem is_start_eq_of_val (next : Option (Range Char)) (n: Range Char)
  (hm : next = some l) (hx : l.start = n.start) : is_start_eq next n := by
  unfold is_start_eq
  simp_all

theorem is_start_eq_of_none (next : Option (Range Char)) (n: Range Char)
  (hm : next = none) : is_start_eq next n := by
  unfold is_start_eq
  simp_all

theorem nonOverlappingWithLast_of_singleton (l r : Range Char) (h : Range.nonOverlapping l r)
    : nonOverlappingWithLast (singleton l).ranges (some r)  := by
  unfold singleton nonOverlappingWithLast
  split <;> simp_all
  unfold Range.nonOverlapping
  rename_i heq _
  unfold Array.last? at heq
  split at heq <;> simp_all
  unfold Range.nonOverlapping  at h
  rename_i last' _ _ _
  have heq' : List.get #[l].data ⟨0, by simp⟩ = l := List.singleton_val l (by simp)
  simp_all

theorem nonOverlapping_of_push (acc : Acc) (next : Range Char)
  (h1: Array.last? acc.set.ranges = some last) (h2 : acc.next = some next)
    : Ranges.nonOverlapping (Array.push acc.set.ranges next) := by
  unfold Array.push Ranges.nonOverlapping
  simp
  have ⟨acc', hp⟩ := Array.pop?_of_last? acc.set.ranges h1
  have h1 : acc.set.ranges.data = acc'.data ++ [last] := Array.concat_of_pop? hp
  have h2 : Range.nonOverlapping last next := by
    have hx : nonOverlappingWithLast acc.set.ranges acc.next := acc.nonOverlapping
    unfold nonOverlappingWithLast at hx
    split at hx <;> simp_all
  have h5 : Ranges.dataIsNonOverlapping (acc'.data ++ [last] ++ [next]) := by
    have hn : Ranges.nonOverlapping acc.set.ranges := acc.set.isNonOverlapping
    unfold Ranges.nonOverlapping at hn
    unfold Ranges.dataIsNonOverlapping
    split <;> simp_all
    rename_i heq
    cases h : acc'.data
    · rw [h] at heq
      simp_all
      rw [← heq.left, ← heq.right]
      rw [← heq.left] at h2
      have hx : List.Chain Range.nonOverlapping next [] := by simp_all
      simp [List.chain_cons.mpr ⟨h2, hx⟩]
      simp [h2]
    · rw [h] at heq
      rename_i head' tail' _ head tail
      have hh : head = head' := List.head_eq_of_cons_eq heq
      have ht : tail ++ [last] ++ [next] = tail' := by simp_all [List.tail_eq_of_cons_eq heq]
      have hn : List.Chain Range.nonOverlapping head (tail ++ [last]) := by
        unfold Ranges.dataIsNonOverlapping at hn
        simp_all [hn]
      have hy : List.Chain Range.nonOverlapping head (tail ++ [last]  ++ [next]) := by
        simp [List.chain_append_cons_cons.mpr]
        simp [h2]
        simp [hn]
      rw [←hh, ←ht]
      simp_all [hy]
  simp_all [h5]

theorem List.eq_head_of_get_first (arr : List α) (h1 : 0 < arr.length)
  (h2 : arr = head :: tail) : head = arr.get ⟨0, h1⟩ := by
  cases arr
  · contradiction
  · unfold List.get
    rename_i head' tail'
    simp [List.head_eq_of_cons_eq h2]

theorem Array.eq_head_of_get_first (arr : Array α) (h1 : 0 < arr.size)
  (h2 : arr.data = head :: tail) : head = arr.get ⟨0, h1⟩ :=
  List.eq_head_of_get_first arr.data h1 h2

theorem List.eq_succ_of_tail_nth (arr : List α) (h1 : i+1 < arr.length)
  (h2 : arr = head :: tail) (h3 : i < tail.length)
    : tail.get ⟨i, h3⟩ = arr.get ⟨i+1, h1⟩ := by
  cases h2
  have h : (head :: tail).get ⟨i+1, h1⟩ = tail.get ⟨i, h3⟩ := List.get_cons_succ
  exact h.symm

theorem Array.eq_succ_of_tail_nth (arr : Array α) (h1 : i+1 < arr.size)
  (h2 : arr.data = head :: tail) (h3 : i < tail.length)
    : tail.get ⟨i, h3⟩ = arr.get ⟨i+1, h1⟩ :=
  List.eq_succ_of_tail_nth arr.data h1 h2 h3

theorem nonOverlapping_of_nth (ranges : Array $ Range Char) (n : Nat)
  (h1 : 0 < n) (h2 : n+1 < Array.size ranges) (h3: ranges.data = head :: tail)
  (h4 : ∀ (i : ℕ) (h : i < List.length tail-1),
    Range.nonOverlapping (tail.get ⟨i, Nat.lt_of_lt_pred h⟩) (tail.get ⟨i+1, Nat.lt_pred_iff.mp h⟩))
    : Range.nonOverlapping (ranges.get ⟨n, Nat.lt_of_succ_lt h2⟩) (ranges.get ⟨n+1, h2⟩) := by
  have hlt : n < Array.size ranges := Nat.lt_of_succ_lt h2
  have hf : n+1 < ranges.data.length := by unfold Array.size at h2; simp_all [h2]
  have hne : ¬n = 0 := (Nat.ne_of_lt h1).symm
  have hps : n-1+1 = n := Nat.succ_pred (by simp_all)
  have ht0 : n < tail.length := by
    have h : n < ranges.data.length-1 := Nat.pred_lt_pred (by simp [Nat.lt_of_le_of_ne]) hf
    have h : n < tail.length := Nat.lt_of_lt_of_eq h (by simp_all)
    simp [h]
  have ht1 : n-1 < tail.length-1 := Nat.pred_lt_pred (by simp_all) ht0
  have ht2 : n-1 < tail.length := Nat.lt_of_lt_pred ht1
  have ht3 : n-1+1 < tail.length := by simp [hps, ht0]
  have : Range.nonOverlapping (tail.get ⟨n-1, ht2⟩) (tail.get ⟨n-1+1, ht3⟩) := h4 (n-1) ht1
  have : tail.get ⟨n-1, ht2⟩ = ranges.get ⟨n, hlt⟩ := by
    let i := n-1
    have h : i+1 < ranges.size := by simp [hps, hlt]
    simp [Array.eq_succ_of_tail_nth ranges h h3 ht2]
    simp [hps]
  have : tail.get ⟨n-1+1, ht3⟩ = ranges.get ⟨n+1, hf⟩ := by
    let i := n-1+1
    have h : i < tail.length := by simp [hps, ht0]
    simp [Array.eq_succ_of_tail_nth ranges (by simp [hps, hf]) h3 h]
    simp [hps]
  simp_all

theorem nonOverlapping_of_pred (ranges : Array $ Range Char) (i : Fin (Array.size ranges))
  (x y : Range Char) (h : 0 < i.val)
  (hx : x = Array.get ranges ⟨i-1, Fin.pred h⟩) (hy : y = Array.get ranges i)
  (hr : Ranges.nonOverlapping ranges)
   : Range.nonOverlapping x y := by
  unfold Ranges.nonOverlapping at hr
  unfold Ranges.dataIsNonOverlapping at hr
  split at hr <;> try simp_all
  · rename_i heq
    have : 0 = ranges.size := by unfold Array.size List.length; split <;> try simp_all
    have : 0 ≠ ranges.size := by simp [Nat.ne_of_lt (Nat.lt_trans h i.isLt)]
    contradiction
  · rename_i heq
    have : ¬1 < ranges.size := by unfold Array.size List.length; split <;> try simp_all
    have : 1 < ranges.size := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt h) i.isLt
    contradiction
  · rename_i head tail _ heq
    let ⟨h1, h2⟩ := List.chain_iff_get.mp hr
    match hm : i with
    | ⟨0, h⟩ => contradiction
    | ⟨1, hf⟩ =>
      rename_i xt
      have hx1 : 0 < ranges.size := by simp [Nat.lt_trans h hf]
      have hx2 : 0 < tail.length := by cases tail <;> simp_all
      have : Range.nonOverlapping head (List.get tail { val := 0, isLt := hx2}) := h1 hx2
      have : head = ranges.get ⟨0, hx1⟩  := Array.eq_head_of_get_first ranges hx1 heq
      have : tail.get ⟨0, hx2⟩  = ranges.get ⟨1, hf⟩ := Array.eq_succ_of_tail_nth ranges hf heq hx2
      simp_all
    | ⟨n+2, hf⟩ =>
      have hx1 : n+1 < ranges.size := by simp [Nat.lt_trans _ hf]
      have hx2 : Range.nonOverlapping ranges[n+1] ranges[n+2] :=
        nonOverlapping_of_nth ranges (n+1) (by simp) hf heq h2
      simp [hx2]

theorem nonOverlappingWithLast_of_push(acc : Acc) (h1 : acc.next = some l)
  (h2 : Ranges.nonOverlapping (Array.push acc.set.ranges l)) (h3 : Range.nonOverlapping l r)
    : nonOverlappingWithLast (Acc.push acc l h2).ranges (some r) := by
  unfold Acc.push Array.push nonOverlappingWithLast
  split <;> try simp_all
  rename_i last next heq _
  unfold Array.last? at heq
  split at heq <;> try simp_all
  have hne : acc.set.ranges.data ++ [l] ≠ [] := by simp_all
  have h : List.getLast (acc.set.ranges.data ++ [l]) hne
      = List.get (acc.set.ranges.data ++ [l]) ⟨acc.set.ranges.data.length, (by simp_all)⟩ := by
      have h : List.get (acc.set.ranges.data ++ [l]) ⟨acc.set.ranges.data.length, (by simp_all)⟩
              = List.get (acc.set.ranges.data ++ [l])
                  ⟨(acc.set.ranges.data ++ [l]).length-1, (by simp_all)⟩ := by
        simp_all
      rw [h]
      rw [List.getLast_eq_get (acc.set.ranges.data ++ [l]) hne]
  rw [← h] at heq
  simp [List.getLast_append] at heq
  rw [heq] at h3
  simp [h3]
