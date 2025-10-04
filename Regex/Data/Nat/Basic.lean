import Batteries.Data.Nat.Lemmas

namespace Nat

theorem mod_sub_eq_of_lt {i j n : Nat} (h : i ≤ j) (h1 : j - i < n) (h2 : i ≤ n)
    : (j + (n - i)) % n = j - i := by
  rw [← Nat.add_sub_assoc h2 j]
  rw [Nat.sub_add_comm h]
  have : (j - i) % n = j - i := Nat.mod_eq_of_lt h1
  simp_all

theorem le_lt_sub_lt {i j n : Nat} (h1 : i ≤ j) (h2 : j < n) :  j - i < n := by
  have hy : n ≤ i + n := Nat.le_add_left n i
  have hx : j < i + n := Nat.lt_of_lt_of_le h2 hy
  simp [Nat.sub_lt_left_of_lt_add h1 hx]

theorem eq_pred_of_le_of_lt_succ {n m : Nat} (h0 : 0 < n) (h1 : n.pred ≤ m) (h2 : m < n)
    : m = n.pred := by
  have h : m ≤ n.pred := by
    have : n = Nat.succ (n.pred) := by cases h0 <;> rfl
    rw [this] at h2
    apply Nat.le_of_lt_succ h2
  simp [Nat.le_antisymm h h1]

theorem succ_lt_lt {c1 c2 : Nat} (h : 1 + c1 < c2) : c1 < c2 := by
  have h1 : c1 < 1 + c1 := by
    rw [Nat.add_comm]
    simp[Nat.lt_succ_self _]
  simp[Nat.lt_trans h1 h]

theorem lt_trans_trans {a b c d : Nat}
  (h₁ : LT.lt a b) (h₂ : LT.lt b c) (h₃ : LT.lt c d) : LT.lt a d  :=
  Nat.lt_trans (Nat.lt_trans h₁ h₂) h₃

theorem lt_trans_trans_trans {a b c d e : Nat}
  (h₁ : LT.lt a b) (h₂ : LT.lt b c) (h₃ : LT.lt c d) (h₄ : LT.lt d e) : LT.lt a e  :=
  Nat.lt_trans (Nat.lt_trans (Nat.lt_trans h₁ h₂) h₃) h₄

theorem toLE_iff_le : ∀ (a b : Nat), (Ord.toLE instOrdNat).le a b ↔ a ≤ b := by
  unfold Ord.toLE instOrdNat
  intro a b
  rw [iff_def]
  and_intros
  · intro h
    exact Nat.isLE_compare.mp h
  · intro h
    exact Nat.isLE_compare.mpr h

theorem toLT_iff_lt : ∀ (a b : Nat), (Ord.toLT instOrdNat).lt a b ↔ a < b := by
  unfold Ord.toLT instOrdNat
  intro a b
  rw [iff_def]
  and_intros
  · intro h
    exact Nat.compare_eq_lt.mp h
  · intro h
    exact Nat.compare_eq_lt.mpr h

theorem toLT_iff : ∀ (a b : Nat), (Ord.toLT instOrdNat).lt a b
    ↔ (Ord.toLE instOrdNat).le a b ∧ ¬(Ord.toLE instOrdNat).le b a  := by
  intro a b
  rw [toLT_iff_lt a b, toLE_iff_le a b, toLE_iff_le b a]
  exact Nat.lt_iff_le_not_le

theorem toLT_notLt : ∀ (a b : Nat), ¬(Ord.toLT instOrdNat).lt a b
    ↔ (Ord.toLE instOrdNat).le b a  := by
  intro a b
  rw [toLT_iff_lt a b, toLE_iff_le b a]
  exact Nat.not_lt
