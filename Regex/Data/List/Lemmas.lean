import Batteries.Data.Nat.Lemmas
import Batteries.Data.Fin.Lemmas
import Init.Data.Int.Lemmas
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas

import Regex.Data.Nat.Basic

namespace List

def maxD [Max α] (d : α) (l : List α) : α :=
  match l.max? with | some m => m | none => d

theorem maxD_of_empty_eq {α : Type} [Max α] {d : α}: [].maxD d = d := by
  simp [maxD]

theorem all_le_maxD {l : List Nat} (d : Nat) : ∀ a ∈ l, a ≤ l.maxD d := by
  intro a ha
  simp [maxD]
  split <;> try simp_all
  rename_i a' heq
  have := (@max?_eq_some_iff' a' l).mp heq
  simp_all

theorem maxD_of_append_lt {l : List Nat} (h : l.maxD 0 < m) (ha : a < m)
    : (l ++ [a]).maxD 0 < m := by
  simp [maxD]
  split <;> try simp_all
  rename_i a' heq
  have := (@max?_eq_some_iff' a' (l ++ [a])).mp heq
  have : a' ∈ l ∨ a' = a := by simp_all [List.mem_append.mp this.left]
  cases this
  · rename_i h'
    exact Nat.lt_of_le_of_lt (all_le_maxD 0 a' h') h
  · rename_i h'
    exact lt_of_eq_of_lt h' ha

theorem maxD_le_of_all_le {l : List Nat} (h : ∀ a ∈ l, a ≤ m) : l.maxD 0 ≤ m := by
  simp [maxD]
  split <;> try simp_all
  rename_i a' heq
  have h1 := (@max?_eq_some_iff' a' l).mp heq
  exact h a' h1.left

theorem maxD_all_lt_of_lt {l : List Nat} {d m : Nat} (h : l.maxD d < m) : ∀ a ∈ l, a < m := by
  intro a ha
  have := all_le_maxD d a ha
  exact Nat.lt_of_le_of_lt this h

theorem maxD_of_map_all_lt {l : List α} {d m : Nat} (f : α → Nat) (h : (l.map f).maxD d < m)
  (hmem : ∀ a ∈ l, f a ∈ (l.map f)) : ∀ a ∈ l, f a < m := by
  intro a ha
  exact maxD_all_lt_of_lt h (f a) (hmem a ha)

theorem maxD_of_all_map_le {α : Type} {l : List α} {f : α → Nat}
  (h : ∀ a ∈ l, f a ≤ m) : (l.map f).maxD 0 ≤ m := by
  exact @maxD_le_of_all_le m (l.map f) (by
    intro i hi
    simp_all
    let ⟨a, ha⟩ := hi
    have := h a ha.left
    rw [← ha.right]
    exact this)

theorem singleton_val_of (a : α) (arr : List α) (h1 : arr = [a]) (h2 : 0 < List.length arr)
    : List.get arr ⟨0, h2⟩ = a  := by
  simp_all [List.get]

theorem singleton_val (a : α) (h : 0 < List.length [a])
    : List.get [a] ⟨0, h⟩ = a  := by
  rfl

theorem get_of_fun_eq {l1 l2 : List α} {f : List α → List α} (h : f l1 = f l2)
  (n : Fin (f l1).length) : (f l1).get n = (f l2).get ⟨n, h ▸ n.2⟩ :=
  List.get_of_eq h n

theorem eq_of_dropLast_eq_last_eq {l1 l2 : List α} (hd : List.dropLast l1 = List.dropLast l2)
  (hl1 : l1.length - 1 < l1.length) (hl2 : l2.length - 1 < l2.length)
  (heq : List.get l1 ⟨l1.length - 1, hl1⟩  = List.get l2 ⟨l2.length - 1, hl2⟩) : l1 = l2 :=
  have hdl : l1.dropLast.length = l2.dropLast.length := by rw [hd]
  have hn1 : 0 < l1.length := Nat.zero_lt_of_lt hl1
  have hn2 : 0 < l2.length := Nat.zero_lt_of_lt hl2
  have hl : l1.length = l2.length := by
    have : l1.dropLast.length = l1.length - 1 := @List.length_dropLast α l1
    have : l2.dropLast.length = l2.length - 1 := @List.length_dropLast α l2
    omega
  List.ext_get hl fun n h1 h2 =>
    if hx1 : n < l1.dropLast.length then by
      have hx2 : n < l2.dropLast.length := Nat.lt_of_lt_of_eq hx1 hdl
      have hy1 : l1.dropLast.get ⟨n, hx1⟩ = l1.get ⟨n, h1⟩ := @List.getElem_dropLast α l1 n hx1
      have hy2 : l2.dropLast.get ⟨n, hx2⟩ = l2.get ⟨n, h2⟩ := @List.getElem_dropLast α l2 n hx2
      have hy3 : l1.dropLast.get ⟨n, hx1⟩ = l2.dropLast.get ⟨n, hx2⟩ := List.get_of_fun_eq hd ⟨n, hx1⟩
      rw [hy3, hy2] at hy1
      rw [hy1]
    else by
      rw [@List.length_dropLast α l1] at hx1
      simp [Nat.le_of_not_gt] at hx1
      have hn1 : n = l1.length - 1 := by
        simp [Nat.eq_pred_of_le_of_lt_succ hn1 hx1 h1]
      have hn2 : n = l2.length - 1 := by omega
      simp [← hn1, ← hn2] at heq
      exact heq

theorem get_last_of_concat {l : List α} (h : (l ++ [last]).length - 1 < (l ++ [last]).length)
    : List.get (l ++ [last]) ⟨(l ++ [last]).length - 1, h⟩ = last  := by
  simp

theorem eq_succ_of_tail_nth {head : α} {tail : List α} (data : List α) (h1 : n+1 < data.length)
  (h2 : data = head :: tail) (h3 : n < tail.length)
    : tail.get ⟨n, h3⟩ = data.get ⟨n+1, h1⟩ := by
  cases h2
  rfl

theorem eq_succ_of_tail_nth_pred {head : α} {tail : List α} (data : List α) (h0 : n ≠ 0)
  (h1 : n < data.length) (h2 : data = head :: tail) (h3 : n - 1 < tail.length)
    : tail.get ⟨n - 1, h3⟩ = data.get ⟨n, h1⟩ := by
  have hps : n - 1 + 1 = n := Nat.succ_pred h0
  have hpl : n - 1 + 1 < data.length := lt_of_eq_of_lt hps h1
  have : data.get ⟨n, h1⟩ = data.get ⟨n - 1 + 1, hpl⟩ := by simp_all
  rw [this]
  exact List.eq_succ_of_tail_nth data hpl h2 h3

/- see Mathlib/Data/List/Chain.lean -/
theorem chain_split {a b : α} {l₁ l₂ : List α} :
    Chain R a (l₁ ++ b :: l₂) ↔ Chain R a (l₁ ++ [b]) ∧ Chain R b l₂ := by
  induction l₁ generalizing a with
  | nil => simp
  | cons x l₁ IH => simp only [cons_append, chain_cons, and_assoc, IH]

/- see Mathlib/Data/List/Chain.lean -/
theorem chain_append_cons_cons {a b c : α} {l₁ l₂ : List α} :
    Chain R a (l₁ ++ b :: c :: l₂) ↔ Chain R a (l₁ ++ [b]) ∧ R b c ∧ Chain R c l₂ := by
  rw [chain_split, chain_cons]

/- see Mathlib/Data/List/Chain.lean -/
theorem chain_iff_get {R} : ∀ {a : α} {l : List α}, Chain R a l ↔
    (∀ h : 0 < length l, R a (get l ⟨0, h⟩)) ∧
      ∀ (i : Nat) (h : i < l.length - 1),
        R (get l ⟨i, by omega⟩) (get l ⟨i+1, by omega⟩)
  | a, [] => iff_of_true (Chain.nil) ⟨fun h => by simp at h, fun _ h => by simp at h⟩
  | a, b :: t => by
    rw [chain_cons, @chain_iff_get _ _ _ t]
    constructor
    · rintro ⟨R, ⟨h0, h⟩⟩
      constructor
      · intro _
        exact R
      intro i w
      cases i
      · apply h0
      · rename_i i
        exact h i (Nat.lt_sub_of_add_lt w)
    rintro ⟨h0, h⟩; constructor
    · apply h0
      exact Nat.zero_lt_succ t.length
    constructor
    · apply h 0
    intro i w
    exact h (i+1) (Nat.add_lt_of_lt_sub w)
