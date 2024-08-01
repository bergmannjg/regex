import Init.Data.Ord
import Batteries.Logic
import Batteries.Data.Nat.Lemmas
import Batteries.Data.Fin.Lemmas
import Batteries.Data.Int.Lemmas
import Batteries.Data.List.Basic
import Batteries.Data.Array.Lemmas
import Regex.Utils
import Regex.Data.UInt.Basic
import Regex.Data.Char.Basic
import Regex.Data.List.Lemmas
import Regex.Data.Array.Basic
import Regex.Data.Array.Lemmas
import Regex.Interval.Basic

namespace Intervals

open Interval

theorem empty_isNonOverlapping {α : Type} [LE α] [HSub α α Nat]
    : nonOverlapping (#[] : Array (NonemptyInterval α)) := by
  unfold nonOverlapping dataIsNonOverlapping
  split <;> simp_all

theorem single_isNonOverlapping (ranges : Array (NonemptyInterval Char)) (h : ranges.size = 1)
    : nonOverlapping ranges  := by
  unfold nonOverlapping dataIsNonOverlapping
  split <;> try simp_all
  unfold Array.size at h
  unfold List.length at h
  split at h <;> try simp_all

instance (α : Type) [LT α] [LE α] [HSub α α Nat]
    [(a b : α) → Decidable (a < b)] [(a b : α) → Decidable (a = b)]
    : Inhabited $ IntervalSet α where
  default := ⟨#[], Intervals.empty_isNonOverlapping⟩

def singleton (r : NonemptyInterval Char) : IntervalSet Char :=
  let arr := #[r]
  ⟨arr, by simp [Intervals.single_isNonOverlapping arr (Array.size_one r)]⟩

theorem pred_lt' {n m : Nat} (h : m < n) : Nat.pred n < n :=
  Nat.pred_lt (Nat.not_eq_zero_of_lt h)

theorem Fin.pred {i : Fin n} (h : 0 < i.val) : LT.lt (i.val-1) n := by
  have h1 : i.val-1 < i.val := pred_lt' h
  have h2 : i.val < n := i.isLt
  simp [Nat.lt_trans h1 h2]

theorem isNonOverlapping (l r : NonemptyInterval Char)
  (h1 : ¬(r.fst.toNat - l.snd.toNat) = 1) (h2 : ¬r.fst < l.snd) (h3 : ¬l.snd = r.fst)
    : Interval.nonOverlapping l r := by
  have h1 : ¬1 = (r.fst.toNat - l.snd.toNat) := fun h => h1 (h.symm)
  have h2 : l.snd ≤  r.fst := Nat.not_lt.mp h2
  have h3 : ¬l.snd.val.val = r.fst.val.val := UInt32.val_ne_of_ne (Char.val_ne_of_ne h3)
  have h : l.snd.toNat < r.fst.toNat := Nat.lt_of_le_of_ne h2 (Fin.val_ne_of_ne h3)
  have h : l.snd.toNat+1 ≤ r.fst.toNat := Nat.succ_le_of_lt h
  have h : 1 + l.snd.toNat ≤ r.fst.toNat := by rw [Nat.add_comm]; simp [h]
  have h : 1 < r.fst.toNat - l.snd.toNat := Nat.lt_of_le_of_ne (Nat.le_sub_of_add_le h) h1
  unfold Interval.nonOverlapping
  rw [← Interval.Char.sub_def]
  unfold Interval.Char.sub
  simp [h]

theorem nonOverlappingWithLast_of_empty (ranges : Array $ NonemptyInterval Char)
  (next : Option (NonemptyInterval Char)) (h2 : ranges.size = 0)
    : nonOverlappingWithLast ranges next  := by
  unfold nonOverlappingWithLast
  split <;> try simp_all
  · rename_i heq'
    unfold Array.last? at heq'
    split at heq' <;> try simp_all
    rename_i h
    unfold List.length at h
    split at h <;> try simp_all
  · rename_i heq'
    unfold Array.last? at heq'
    split at heq' <;> try simp_all
    rename_i h
    unfold List.length at h
    split at h <;> try simp_all

theorem nonOverlappingWithLast_with_none_eq_empty (acc : Acc) (h : acc.next.isNone)
    : acc.set.intervals.size = 0 := by
  have hx : nonOverlappingWithLast acc.set.intervals acc.next := acc.nonOverlapping
  unfold nonOverlappingWithLast at hx
  split at hx <;> try simp_all

  rename_i heq _
  unfold Array.last? at heq
  split at heq <;> try simp_all

theorem nonOverlappingWithLast_of_none (acc : Interval.Acc) (n : NonemptyInterval Char) (h : acc.next.isNone)
    : nonOverlappingWithLast acc.set.intervals n  := by
  have hx : acc.set.intervals.size = 0 := nonOverlappingWithLast_with_none_eq_empty acc h
  simp [nonOverlappingWithLast_of_empty acc.set.intervals n hx]

theorem nonOverlappingWithLast_of_val (acc : Acc) (n : NonemptyInterval Char)
  (h : is_start_eq acc.next n) : nonOverlappingWithLast acc.set.intervals n  := by
  have hx : nonOverlappingWithLast acc.set.intervals acc.next := acc.nonOverlapping
  unfold nonOverlappingWithLast
  unfold nonOverlappingWithLast at hx
  unfold is_start_eq at h
  simp_all
  split <;> try simp_all
  unfold Interval.nonOverlapping
  split at hx <;> try simp_all
  unfold Interval.nonOverlapping at hx
  simp_all

theorem is_start_eq_of_val (next : Option (NonemptyInterval Char)) (n: NonemptyInterval Char)
  (hm : next = some l) (hx : l.fst = n.fst) : is_start_eq next n := by
  unfold is_start_eq
  simp_all

theorem is_start_eq_of_none (next : Option (NonemptyInterval Char)) (n: NonemptyInterval Char)
  (hm : next = none) : is_start_eq next n := by
  unfold is_start_eq
  simp_all

theorem nonOverlappingWithLast_of_singleton (l r : NonemptyInterval Char) (h : Interval.nonOverlapping l r)
    : nonOverlappingWithLast (singleton l).intervals (some r)  := by
  unfold singleton nonOverlappingWithLast
  split <;> simp_all
  unfold Interval.nonOverlapping
  rename_i heq _
  unfold Array.last? at heq
  split at heq <;> simp_all
  unfold Interval.nonOverlapping  at h
  rename_i last' _ _ _
  simp_all

theorem nonOverlapping_of_push (acc : Acc) (next : NonemptyInterval Char)
  (h1: Array.last? acc.set.intervals = some last) (h2 : acc.next = some next)
    : Intervals.nonOverlapping (Array.push acc.set.intervals next) := by
  unfold Array.push Intervals.nonOverlapping
  simp
  have ⟨acc', hp⟩ := Array.pop?_of_last? acc.set.intervals h1
  have h1 : acc.set.intervals.data = acc'.data ++ [last] := Array.concat_of_pop? hp
  have h2 : Interval.nonOverlapping last next := by
    have hx : nonOverlappingWithLast acc.set.intervals acc.next := acc.nonOverlapping
    unfold nonOverlappingWithLast at hx
    split at hx <;> simp_all
  have h5 : Intervals.dataIsNonOverlapping (acc'.data ++ [last] ++ [next]) := by
    have hn : Intervals.nonOverlapping acc.set.intervals := acc.set.isNonOverlapping
    unfold Intervals.nonOverlapping at hn
    unfold Intervals.dataIsNonOverlapping
    split <;> simp_all
    rename_i heq
    cases h : acc'.data
    · rw [h] at heq
      simp_all
      rw [← heq.left, ← heq.right]
      rw [← heq.left] at h2
      have hx : List.Chain Interval.nonOverlapping next [] := by simp_all
      simp [List.chain_cons.mpr ⟨h2, hx⟩]
    · rw [h] at heq
      rename_i head' tail' _ head tail
      have hh : head = head' := List.head_eq_of_cons_eq heq
      have ht : tail ++ [last] ++ [next] = tail' := by simp_all [List.tail_eq_of_cons_eq heq]
      have hn : List.Chain Interval.nonOverlapping head (tail ++ [last]) := by
        unfold Intervals.dataIsNonOverlapping at hn
        simp_all [hn]
      have hy : List.Chain Interval.nonOverlapping head (tail ++ [last]  ++ [next]) := by
        simp [List.append_assoc, List.singleton_append, List.chain_append_cons_cons,
              List.Chain.nil, and_true]
        simp_all [h2]
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

theorem nonOverlapping_of_nth (ranges : Array $ NonemptyInterval Char) (n : Nat)
  (h1 : 0 < n) (h2 : n+1 < Array.size ranges) (h3: ranges.data = head :: tail)
  (h4 : ∀ (i : Nat) (h : i < List.length tail-1),
    Interval.nonOverlapping (tail.get ⟨i, by omega⟩) (tail.get ⟨i+1, Nat.add_lt_of_lt_sub h⟩))
    : Interval.nonOverlapping (ranges.get ⟨n, Nat.lt_of_succ_lt h2⟩) (ranges.get ⟨n+1, h2⟩) := by
  have hlt : n < Array.size ranges := Nat.lt_of_succ_lt h2
  have hf : n+1 < ranges.data.length := by unfold Array.size at h2; simp_all [h2]
  have hne : ¬n = 0 := (Nat.ne_of_lt h1).symm
  have hps : n-1+1 = n := Nat.succ_pred (by simp_all)
  have ht0 : n < tail.length := by
    have h : n < ranges.data.length-1 := Nat.pred_lt_pred (by simp [Nat.lt_of_le_of_ne]) hf
    have h : n < tail.length := Nat.lt_of_lt_of_eq h (by simp_all)
    simp [h]
  have ht1 : n-1 < tail.length-1 := Nat.pred_lt_pred (by simp_all) ht0
  have ht2 : n-1 < tail.length := by omega
  have ht3 : n-1+1 < tail.length := by simp [hps, ht0]
  have : Interval.nonOverlapping (tail.get ⟨n-1, ht2⟩) (tail.get ⟨n-1+1, ht3⟩) := h4 (n-1) ht1
  have : tail.get ⟨n-1, ht2⟩ = ranges.get ⟨n, hlt⟩ :=
    List.eq_succ_of_tail_nth_pred ranges.data hne hlt h3 ht2
  have : tail.get ⟨n, ht0⟩ = ranges.get ⟨n+1, hf⟩ :=
    List.eq_succ_of_tail_nth ranges.data (by simp [h2]) h3 ht0
  simp_all

theorem nonOverlapping_of_pred (ranges : Array $ NonemptyInterval Char) (i : Fin (Array.size ranges))
  (x y : NonemptyInterval Char) (h : 0 < i.val)
  (hx : x = Array.get ranges ⟨i-1, Fin.pred h⟩) (hy : y = Array.get ranges i)
  (hr : Intervals.nonOverlapping ranges)
   : Interval.nonOverlapping x y := by
  unfold Intervals.nonOverlapping at hr
  unfold Intervals.dataIsNonOverlapping at hr
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
    match i with
    | ⟨0, h⟩ => contradiction
    | ⟨1, hf⟩ =>
      rename_i xt
      have hx1 : 0 < ranges.size := by simp [Nat.lt_trans h hf]
      have hx2 : 0 < tail.length := by cases tail <;> simp_all
      have : head = ranges.get ⟨0, hx1⟩  := Array.eq_head_of_get_first ranges hx1 heq
      have : tail.get ⟨0, hx2⟩  = ranges.get ⟨1, hf⟩ := List.eq_succ_of_tail_nth ranges.data hf heq hx2
      simp_all
    | ⟨n+2, hf⟩ =>
      have hx1 : n+1 < ranges.size := by simp [Nat.lt_trans _ hf]
      have hx2 : Interval.nonOverlapping ranges[n+1] ranges[n+2] :=
        nonOverlapping_of_nth ranges (n+1) (by simp) hf heq h2
      simp [hx2]

theorem nonOverlappingWithLast_of_push(acc : Acc)
  (h2 : Intervals.nonOverlapping (Array.push acc.set.intervals l)) (h3 : Interval.nonOverlapping l r)
    : nonOverlappingWithLast (Acc.push acc l h2).intervals (some r) := by
  unfold Acc.push Array.push nonOverlappingWithLast
  split <;> try simp_all
  rename_i last next heq _
  unfold Array.last? at heq
  split at heq <;> try simp_all
