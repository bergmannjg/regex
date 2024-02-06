import Std.Data.Nat.Lemmas

namespace Nat

theorem mod_sub_eq_of_lt {i j n : Nat} (h : i ≤ j) (h1 : j - i < n) (h2 : i ≤ n)
    : (j + (n - i)) % n = j - i := by
  rw [← Nat.add_sub_assoc h2 j]
  rw [Nat.sub_add_comm h]
  have hy : ((j - i) + n) % n = (j - i) % n := Nat.add_mod_right (j - i) n
  have h1 : (j - i) % n = j - i := Nat.mod_eq_of_lt h1
  simp_all [hy]

theorem le_lt_sub_lt {i j n : Nat} (h1 : i ≤ j) (h2 : j < n) :  j - i < n := by
  have hy : n ≤ i + n := Nat.le_add_left n i
  have hx : j < i + n := Nat.lt_of_lt_of_le h2 hy
  simp [Nat.sub_lt_left_of_lt_add h1 hx]

theorem eq_pred_of_le_of_lt_succ {n m : Nat} (h0 : 0 < n) (h1 : n.pred ≤ m) (h2 : m < n)
    : m = n.pred := by
  have h : m ≤ n.pred := by
    have : n = Nat.succ (n.pred) := by cases h0 <;> rfl
    rw [this] at h2
    simp [Nat.le_of_lt_succ h2]
  simp [Nat.le_antisymm h1 h]