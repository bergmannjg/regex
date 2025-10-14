import Init.Data.List.Lemmas
import Init.Data.Order.Lemmas
import Init.Data.Array.Mem
import Batteries.Data.Array.Basic

import Std.Tactic.Do
import Std.Tactic.Do.Syntax

import Regex.Data.List.Lemmas
import Regex.Data.Ord.Basic
import Regex.Data.Nat.Basic
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
  rename_i h'
  exact h'

theorem pop?_of_last? (arr : Array α) (h: Array.last? arr = some last)
    : ∃ (arr' : Array α), Array.pop? arr = some (last, arr') := by
  unfold Array.pop?
  unfold Array.last? at h
  split <;> simp_all
  · let ⟨_, hm⟩ := h
    exact hm
  · let ⟨_, _⟩ := h
    contradiction

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
  rename_i h'
  exact h'

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
  exact List.eq_of_dropLast_eq_last_eq hz (by omega) (by simp_all)
          (by rw [List.get_last_of_concat _]; exact hlast)
  omega

theorem get_eq_get?_some {as : Array α} (hlt : i < as.size) (h : a = as[i]'hlt)
    : as[i]? = some a := by
  simp_all

@[simp] theorem size_of_head?_lt (as : Array α) (h : as.toList.head? = some a) : 0 < as.size := by
  unfold Array.size
  unfold List.head? at h
  split at h <;> simp_all

private theorem unique.acc_mem_snd [DecidableEq α]
    : ∀ (acc : (α × Array α)) (r : α), 0 < acc.snd.size
      → acc.fst ∈ acc.snd
      → (unique.acc acc r).snd.toList.head? = acc.snd.toList.head?
        ∧ (unique.acc acc r).fst ∈ (unique.acc acc r).snd.toList
        ∧ ∀ a ∈ acc.snd, a ∈ (unique.acc acc r).snd
        ∧ r ∈ (unique.acc acc r).snd := by
    unfold unique.acc
    have (x : (α × Array α)) (r : α) : (if x.fst = r then (r, x.snd) else (r, x.snd.push r))
        = (if x.fst = r then (r, x.snd) else (r, x.snd ++ #[r])) := by
      rfl
    intros
    and_intros
    · simp [List.head?]; split <;> rename_i heq <;> split at heq <;> split <;> simp_all
    all_goals simp_all <;> split <;> simp_all

private theorem unique.mem_foldl [DecidableEq α]
  (l : List α) (a head : α) (init : α × Array α) (ha : a ∈ l || a ∈ init.snd.toList)
  (hi1 : init.snd.toList.head? = some head) (hi2 : init.fst ∈ init.snd)
    : a ∈ (List.foldl unique.acc init l).snd := by
  have hf := @unique.acc_mem_snd α
  induction l generalizing init with
  | nil =>
    simp_all
  | cons a' l ih =>
    simp at ih
    simp [List.foldl_cons]
    expose_names
    simp at ha
    cases ha
    · rename_i ha
      cases ha
      · have := @ih (unique.acc init a').fst (unique.acc init a').snd
            (by exact Or.inr (by have := hf init a' (by simp_all) (by grind); grind))
            (by have := hf init a (by simp_all) (by grind); grind)
            (by grind)
        simp_all
      · have := @ih (unique.acc init a').fst (unique.acc init a').snd
            (by exact Or.inl (by simp_all))
            (by have := hf init a (by simp_all) (by grind); grind)
            (by grind)
        simp_all
    · expose_names
      have := @ih (unique.acc init a').fst (unique.acc init a').snd
            (by exact Or.inr (by have := hf init a' (by simp_all); grind))
            (by have := hf init a (by simp_all) (by grind); grind)
            (by grind)
      simp_all

private theorem unique.mem_of_foldl [DecidableEq α]
  (l : List α) (a : α) (init : α × Array α) (ha1 : a ∈ (List.foldl unique.acc init l).snd)
  (ha2 : ¬a ∈ init.snd) (hne : ¬l = [])
    : a ∈ l := by
  induction l generalizing init with
  | nil => contradiction
  | cons a' l ih =>
    by_cases a = a'
    · grind
    · simp [List.foldl_cons] at ha1
      by_cases h : a ∈ (unique.acc init a').snd
      · have hf : ∀ a a' (acc : α × Array α), a ∈ (unique.acc acc a').snd → a ∈ acc.snd ∨ a ∈ acc.snd ++ #[a'] := by
          intro a a acc h
          unfold unique.acc at h
          grind
        have := hf a a' init h
        simp_all
      · by_cases l = []
        · simp_all
        · have := ih (unique.acc init a') ha1 (by grind) (by grind)
          simp_all

protected theorem unique.mem_of_mem_unqiue [DecidableEq α] [LE α] (as : Array α)
    : a ∈ as.unique → a ∈ as := by
  simp [Array.unique]
  split
  · grind
  · grind
  · expose_names
    generalize hi : (head, #[head]) = init
    by_cases a = head
    · intro ha
      apply Array.mem_toList_iff.mp
      grind
    · intro ha
      have := unique.mem_of_foldl tail a init ha (by grind)
      apply Array.mem_toList_iff.mp
      simp_all

private theorem unique.mem_unique_of_mem [DecidableEq α] [LE α] (as : Array α)
  : a ∈ as → a ∈ as.unique := by
  simp [Array.unique]
  cases as
  rename_i l
  split
  · simp_all
  · simp_all
  · intro ha
    expose_names
    generalize hi : (head, #[head]) = init
    have hi : init.snd.toList.head? = some head := by rw [← hi]; simp [List.head?]
    simp at heq
    simp at ha
    rw [heq] at ha
    cases ha
    · unfold List.head? at hi
      split at hi
      · grind
      · expose_names
        exact unique.mem_foldl tail a a init
              (by simp_all) (by unfold List.head?; split <;> grind) (by grind)
    · exact unique.mem_foldl tail a head init
              (by simp_all; expose_names; exact Or.symm (Or.inr h_1)) (by grind)  (by grind)

@[simp] theorem mem_unique [DecidableEq α] [LE α] (as : Array α) : a ∈ as.unique ↔ a ∈ as :=
  ⟨by intro h; exact unique.mem_of_mem_unqiue as h, by intro h; exact unique.mem_unique_of_mem as h⟩

private theorem nodup.nodup_acc_if_nodup [DecidableEq α] [LE α] [LT α] [Std.IsPreorder α]
  [Std.LawfulOrderLT α] [Std.Antisymm fun (x1 x2 : α) => x1 ≤ x2]
    : ∀ a (acc : α × Array α), acc.fst ≤ a → (∀ a' ∈ acc.snd.toList, a' ≤ acc.fst)
        → acc.snd.toList.Nodup → (unique.acc acc a).snd.toList.Nodup := by
  intros
  expose_names
  unfold List.Nodup at h_2
  unfold List.Nodup unique.acc
  split
  assumption
  simp_all
  apply List.pairwise_append.mpr
  have := @Std.LawfulOrderLT.lt_iff α _ _ _ -- for grind
  have : ∀ (a b c : α), a ≤ b ∧ b ≤ c ∧ ¬b = c → a < c := by -- for grind
    intro a b c h
    exact Std.lt_of_le_of_lt h.left (Std.lt_of_le_of_ne h.right.left h.right.right)
  and_intros <;> grind

private theorem nodup.nodup_of_foldl [DecidableEq α] [LE α] [LT α] [Std.IsPreorder α]
  [Std.LawfulOrderLT α] [Std.Antisymm fun (x1 x2 : α) => x1 ≤ x2]
  (l : List α) (init : α × Array α)
  (h : l.Pairwise LE.le)
  (ha1 : (∀ (a' : α), a' ∈ init.snd.toList → a' ≤ init.fst))
  (ha2 : init.snd.toList.Nodup)
  (ha3 : (∀ (a : α), a ∈ l → init.fst ≤ a))
    : (List.foldl unique.acc init l).snd.toList.Nodup := by
  have := @Std.IsPreorder.le_trans α _ _ -- for grind
  have := @Std.IsPreorder.le_refl α -- for grind
  have := @nodup_acc_if_nodup α
  have : ∀ a a' (acc : α × Array α), acc.fst ≤ a → (∀ a' ∈ acc.snd.toList, a' ≤ acc.fst)
         → a' ∈ (unique.acc acc a).snd → a' ≤ (unique.acc acc a).fst := by
    intro _ _ _ _ _ h
    unfold unique.acc at h
    unfold unique.acc
    split <;> grind
  have : ∀ a (acc : α × Array α), (unique.acc acc a).fst ≤ a := by unfold unique.acc; grind
  induction l generalizing init with
  | nil => simp_all
  | cons a l ih =>
    simp [List.foldl_cons]
    expose_names
    by_cases l = []
    · simp_all
    · expose_names
      have ih := ih (unique.acc init a) (by grind) (by simp_all) (by grind) (by
        intros
        simp_all
        grind)
      simp_all

@[simp] theorem nodup_unique [DecidableEq α] [LE α] [LT α] [Std.IsPreorder α]
  [Std.LawfulOrderLT α] [Std.Antisymm fun (x1 x2 : α) => x1 ≤ x2] (as : Array α)
  (h : as.toList.Pairwise LE.le)
    : List.Nodup as.unique.toList := by
  have := @Std.IsPreorder.le_trans α _ _ -- for grind
  have := @Std.IsPreorder.le_refl α -- for grind
  simp [Array.unique]
  cases as
  rename_i l
  split
  · simp_all
  · simp_all
  · expose_names
    generalize hi : (head, #[head]) = init
    have : ∀ (a : α), a ∈ tail → init.fst ≤ a := by rw [← hi]; simp_all
    apply nodup.nodup_of_foldl tail init
    all_goals grind

@[simp] theorem mergeSort_toList_eq (as bs: Array α) (le : α → α → Bool := by exact fun a b => a ≤ b)
  (h : bs = as.mergeSort le) : as.toList.mergeSort le = bs.toList := by
  unfold Array.mergeSort at h
  grind

@[simp] theorem mem_mergeSort [LT α] (as : Array α) (le : α → α → Bool := by exact (· ≤ ·))
    : a ∈ as.mergeSort le ↔ a ∈ as := by
  unfold Array.mergeSort
  simp_all only [List.mem_toArray, List.mem_mergeSort, mem_toList_iff]

open Std.Do

theorem minWith_spec [ord : Ord α] [Std.TransOrd α] (as : Array α) (init : α)
  (f : α → α → α) (hf : (fun min x => if @compare α ord x min = Ordering.lt then x else min) = f)
  (lt_iff : ∀ a b : α, (Ord.toLT ord).lt a b ↔ (Ord.toLE ord).le a b ∧ ¬ (Ord.toLE ord).le b a)
  (le_notLt : ∀ a b : α, ¬(Ord.toLT ord).lt a b ↔ (Ord.toLE ord).le b a)
    : ⦃⌜True⌝⦄
      (Array.foldlM f init as : Id α)
      ⦃⇓r => ⌜(Ord.toLE ord).le r init ∧ ∀ a ∈ as, (Ord.toLE ord).le r a⌝⦄ := by
  have le_refl : ∀ a : α, (Ord.toLE ord).le a a := by grind
  have le_trans : ∀ a b c : α, letI le := (Ord.toLE ord).le; le a b → le b c → le a c := by
    apply Std.TransOrd.isLE_trans
  mintro _
  mspec Spec.foldlM_array
  case inv => exact (⇓ (xs, r) => ⌜(Ord.toLE ord).le r init
                                    ∧ ∀ a ∈ xs.prefix, (Ord.toLE ord).le r a⌝)
  case pre => simp_all
  case post.success => simp_all
  case step =>
    simp_all
    intro pref curr suff h r
    mintro _
    simp_all
    intro hb ha
    rw [← hf]
    simp_all
    split
    · simp [wp, Id.run]
      and_intros
      · expose_names
        have : @LT.lt α ltOfOrd curr r := by assumption
        have := (lt_iff curr r).mp (by grind)
        grind
      · expose_names
        intro a ha
        cases ha
        · expose_names
          have : @LT.lt α ltOfOrd curr r := by assumption
          have := (lt_iff curr r).mp (by grind)
          have ha := ha a h_2
          grind
        · grind
    · simp [wp, Id.run]
      and_intros
      · grind
      · intro a ha
        cases ha
        · expose_names
          exact le_trans r r a (by grind) (ha a h_2)
        · expose_names
          have : (Ord.toLE ord).le r curr := by
            have h : ¬@LT.lt α ltOfOrd curr r := by assumption
            have h := le_notLt curr r
            cases h <;> simp_all
          grind

theorem min_le_mem [ord : Ord α] [Std.TransOrd α]
  (xs : Array α) (h : xs.min? = some m)
  (lt_iff : ∀ a b : α, (Ord.toLT ord).lt a b ↔ (Ord.toLE ord).le a b ∧ ¬ (Ord.toLE ord).le b a)
  (le_notLt : ∀ a b : α, ¬(Ord.toLT ord).lt a b ↔ (Ord.toLE ord).le b a)
    : ∀ a ∈ xs, (Ord.toLE ord).le m a := by
  unfold Array.min? Array.minD Array.minWith at h
  split at h
  · simp at h
    generalize hf : (fun min x => if @compare α ord x min = Ordering.lt then x else min) = f at h
    unfold Array.foldl at h
    let xs' := xs.extract 1 xs.size
    have hex : xs' = xs.extract 1 := by simp +zetaDelta
    have heq := (minWith_spec xs' xs[0] f hf (by grind) (by grind)) (by simp_all)
    simp [wp] at heq
    have hm : foldl (fun x1 x2 => Id.run (f x1 x2)) xs[0] xs' = m := by
      simp [Id.run, pure] at h
      simp [Id.run]
      rw [hex, ← h]
      exact id (Eq.symm (@Array.foldlM_start_stop α α Id Id.instMonad xs f xs[0] 1 xs.size))
    intro a ha
    by_cases h: a = xs[0]
    · have heq := heq.left
      rwa [hm, ← h] at heq
    · have heq := heq.right a (by
        rw [hex]
        apply Array.mem_extract_iff_getElem.mpr
        have ⟨i, ⟨hi, hmem⟩⟩ := Array.mem_iff_getElem.mp ha
        exact ⟨i-1, by grind⟩)
      rwa [hm] at heq
  · simp_all

theorem mem_le_max [ord : Ord α] [Std.TransOrd α] (xs : Array α)
  (h : xs.max? = some m)
  (lt_iff : ∀ a b : α, (Ord.toLT ord).lt a b ↔ (Ord.toLE ord).le a b ∧ ¬ (Ord.toLE ord).le b a)
  (le_iff : ∀ a b : α, ¬(Ord.toLT ord).lt a b ↔ (Ord.toLE ord).le b a)
    : ∀ a ∈ xs, (Ord.toLE ord).le a m := by
  unfold Array.max? at h
  exact @min_le_mem α m ord.opposite _ xs h (by simp_all) (by intro a b; exact le_iff b a)
