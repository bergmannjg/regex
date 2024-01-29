import Init.Data.Ord
import Std.Data.Nat.Lemmas
import Std.Data.Fin.Lemmas
import Std.Data.Int.Lemmas

import Regex.Utils
import Regex.Data.Fin.Basic
import Regex.Data.Nat.Basic
import Regex.Data.UInt.Basic
import Regex.Data.Char.Basic

/-!
## Bound

This file defines a `Bound` of type Char.
A bound defines a bounded set of values with a min_value, max_value and increment
and decrement operators. A `Range` is defined by a bound.
-/

namespace Bound

theorem UInt32.isValidChar_lt_0x110000 (u : UInt32) (h : UInt32.isValidChar u)
    : u.val.val < 0x110000 := by
  unfold UInt32.isValidChar at h
  unfold Nat.isValidChar at h
  unfold UInt32.toNat at h
  cases h
  · rename_i h
    have hy : u.val.val < 0x110000 := Nat.lt_trans h (by simp_arith)
    simp_all [hy]
  · rename_i h
    simp_all [ h.right]

theorem UInt32.isValidChar_lt_uintSize (u : UInt32) (h : UInt32.isValidChar u)
    : u.val.val < UInt32.size := by
  have hx : u.val.val < 0x110000 := UInt32.isValidChar_lt_0x110000 u h
  have hy : u.val.val + 1 < 0x110000 + 1 := Nat.add_lt_add_right hx 1
  have hz : 0x110000 + 1 < UInt32.size := by simp_arith
  simp [Nat.lt_trans hy hz]

theorem UInt32.isValidChar_succ_lt_uintSize (u : UInt32) (h : UInt32.isValidChar u)
    : u.val.val + 1 < UInt32.size := by
  have hx : u.val.val < 0x110000 := UInt32.isValidChar_lt_0x110000 u h
  have hy : u.val.val + 1 < 0x110000 + 1 := Nat.add_lt_add_right hx 1
  have hz : 0x110000 + 1 < UInt32.size := by simp_arith
  simp [Nat.lt_trans hy hz]

theorem UInt32.isValidChar_pred_lt_uintSize (u : UInt32) (h2 : UInt32.isValidChar u) (h3 : 1 ≤ u)
    : u.val - 1 < UInt32.size := by

  have hx1 : u.val.val < 0x110000 := UInt32.isValidChar_lt_0x110000 u h2
  have hx2 : u.val < 0x110000 := UInt32.lt_def.mp hx1
  have hx3 : 0x110000 < UInt32.size := by simp_arith
  have hx4 : u.val < UInt32.size := Nat.lt_trans hx2 hx3

  have h3 : u.val - 1 < UInt32.size := Nat.le_lt_sub_lt h3 hx4
  simp [h3]

theorem Nat.succ_lt_lt {c1 c2 : Nat} (h : 1 + c1 < c2) : c1 < c2 := by
  have h1 : c1 < 1 + c1 := by
    rw [Nat.add_comm]
    simp[Nat.lt_succ_self _]
  simp[Nat.lt_trans h1 h]

theorem UInt32.lt_succ_le {c1 c2 : UInt32} (h : c1 < c2) (hsucc : c1.val + 1 < UInt32.size)
    : c1 + 1 ≤ c2 := by
  have hx : c1.val < c2.val := UInt32.lt_def.mp h
  have heq : c1.val.val + 1 ≤ c2.val.val := Nat.succ_le_of_lt hx
  have ht : c1.val.val + 1 = (c1 + 1).val.val := UInt32.toNat_add_toNat c1 1 hsucc
  rw [ht] at heq
  simp [UInt32.le_def.mpr heq]

theorem UInt32.toNatUnfold (c1 c2 : UInt32) (heq : c2.toNat - c1.toNat = (c2 - c1).toNat)
    : c2.val.val - c1.val.val = (c2 - c1).val.val := by
  unfold UInt32.toNat at heq
  simp_all [heq]

theorem UInt32.lt_pred_le {c1 c2 : UInt32} (h : c1 < c2) (h2 : c2.val < UInt32.size)
    : c1 ≤ c2 - 1  := by
  have hx : c1.val < c2.val := UInt32.lt_def.mp h
  have heq : c1.val.val ≤ c2.val.val - 1 := Nat.le_pred_of_lt hx
  let hnm : 1 ≤ c2 := UInt32.one_le_of_lt h
  have ht' : c2.toNat - 1 = (c2 - 1).toNat := UInt32.toNat_sub_toNat hnm h2
  have ht : c2.val.val - 1 = (c2 - 1).val.val := UInt32.toNatUnfold 1 c2 ht'
  rw [ht] at heq
  simp [UInt32.le_def.mpr heq]

theorem Char.succ_lt_lt {c1 c2 : Char} (h : 1 + Char.toNat c1 < Char.toNat c2) : c1 < c2 := by
  have h : Char.toNat c1 < Char.toNat c2 := Nat.succ_lt_lt h
  exact h

theorem Char.succ_lt_succ_lt {c1 c2 : Char} (h : 1 + Char.toNat c1 < Char.toNat c2)
    (hs: UInt32.isValidChar (c1.val + 1)) : ⟨c1.val + 1, hs⟩ < c2 := by
  rw [Char.lt_def]
  have h : c1.toNat + 1 < Char.toNat c2 := by
    rw [Nat.add_comm]
    simp [h]
  have hx : Char.toNat c1 + 1 < UInt32.size := UInt32.isValidChar_succ_lt_uintSize c1.val c1.valid
  have hy : c1.toNat + 1 = (c1.val + 1).toNat := UInt32.toNat_add_toNat c1.val 1 hx
  rw [hy] at h
  have hz : c1.val + 1 < c2.val := h
  simp [hz]

theorem Char.lt_pred_le {c1 c2 : Char} (h : c1 < c2) : c1.val ≤ c2.val - 1 := by
  have h : c1.val < c2.val := Char.lt_def.mp h
  have h2 : c2.val.val < UInt32.size := UInt32.isValidChar_lt_uintSize c2.val c2.valid
  simp [UInt32.lt_pred_le h h2]

theorem Char.lt_succ_le {c1 c2 : Char} (h : c1 < c2) : c1.val + 1 ≤ c2.val := by
  have h : c1.val < c2.val := Char.lt_def.mp h
  have hsucc : c1.val.val + 1 < UInt32.size := UInt32.isValidChar_succ_lt_uintSize c1.val c1.valid
  simp [UInt32.lt_succ_le h hsucc]

theorem Char.succ_add_le__pred {c1 c2 : Char} (h : 1 + c1.toNat < c2.toNat)
  (hs: UInt32.isValidChar (c1.val + 1)) : c1.val + 1 ≤ c2.val - 1 := by
  have h : ⟨c1.val + 1, hs⟩ < c2 := Char.succ_lt_succ_lt h hs
  have h : c1.val + 1 ≤ c2.val - 1 := Char.lt_pred_le h
  simp [h]

theorem Char.incr_le_decr {c1 c2 : Char} (h : 1 + Char.toNat c1 < Char.toNat c2)
    : Char.increment c1 ≤ Char.decrement c2 := by
  unfold Char.increment
  unfold Char.decrement
  split <;> try simp_all
  · split <;> try simp_all
    · rename_i hs hp
      let cs : Char := ⟨c1.val + 1, hs⟩
      have hseq : cs = ⟨c1.val + 1, hs⟩ := by simp
      let cp : Char := ⟨c2.val - 1, hp⟩
      let hpeq : cp = ⟨c2.val - 1, hp⟩ := by simp
      rw [← hseq, ← hpeq]
      have h : cs.val ≤ cp.val := Char.succ_add_le__pred h hs
      apply h
    · rename_i hv _
      have h : c1 < c2 := Char.succ_lt_lt h
      have h : c1.val + 1 ≤ c2.val := by simp [Char.lt_succ_le h]
      apply h
  · split <;> try simp_all
    · rename_i hv
      have h : c1 < c2 := Char.succ_lt_lt h
      have h : c1.val ≤ c2.val - 1 := by simp [Char.lt_pred_le h]
      apply h
    · have h : c1 < c2 := Char.succ_lt_lt h
      simp [Char.lt_le h]

end Bound

/-- a Bound has a min_value, max_value and increment and decrement operators -/
class Bound (α : Type u) [Ord α] [LE α] where
  min_value : α
  max_value : α
  increment : α -> α
  decrement : α -> α
  min_value_le_max_value : min_value ≤ max_value
  min_value_le_decrement c : min_value ≤ decrement c
  increment_le_max_value c : increment c ≤ max_value

/-- a Bound of type Char -/
instance : Bound Char where
  min_value := Char.min
  max_value := Char.max
  increment (c : Char) := Char.increment c
  decrement (c : Char) := Char.decrement c
  min_value_le_max_value := by simp_arith
  increment_le_max_value c := by
    unfold Char.increment; simp_all; split <;> try simp_all
    · simp [Char.le_max]
    · simp [Char.le_max]
  min_value_le_decrement c := by
    unfold Char.decrement; simp_all; split <;> try simp_all
    · simp [Char.min_le]
    · simp [Char.min_le]
