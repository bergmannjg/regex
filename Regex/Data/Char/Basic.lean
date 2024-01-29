import Std.Data.Nat.Lemmas
import Regex.Data.UInt.Basic

namespace Char

/-- max valid char -/
def max : Char := ⟨0x10FFFF, by simp_arith⟩

/-- incr char up to max valid char `Char.max` -/
def increment (c : Char) : Char :=
  if h : UInt32.isValidChar (c.val + 1) then ⟨c.val + 1, h⟩ else c

/-- min valid char -/
def min : Char := '\u0000'

/-- decr char to min valid char `Char.min` -/
def decrement (c : Char) : Char :=
  if h : UInt32.isValidChar (c.val - 1) then ⟨c.val - 1, h⟩ else c

theorem eq_le {c1 c2 : Char} (h : c1 = c2) : c1 ≤ c2 := by
  have h₁ : c1.val.toNat ≤ c2.val.toNat := by simp[h]
  exact h₁

theorem lt_le {c1 c2 : Char} (h : c1 < c2) : c1 ≤ c2 := by
  have h₁ : c1.val.toNat < c2.val.toNat := h
  have h₂ : c1.val.toNat ≤ c2.val.toNat := by simp [Nat.le_of_lt h₁]
  exact h₂

theorem succ_lt {c1 c2 : Char} (h : (c2.val.toNat - c1.val.toNat) = 1) : c1 < c2 := by
  have hx : c1.val.toNat < c2.val.toNat := by simp_all [Nat.lt_of_sub_eq_succ h]
  exact hx

theorem le_trans {c1 c2 c3 : Char} (h₁ : c1 ≤ c2) (h₂ : c2 ≤ c3) : c1 ≤ c3 := by
  have h : c1.val.toNat ≤ c3.val.toNat := by exact Nat.le_trans h₁ h₂
  exact h

theorem min_le (c : Char) : Char.min ≤ c := by
  have h : 0 ≤ c.val.toNat := by simp_all
  exact h

theorem le_max (c : Char) : c ≤ Char.max := by
  cases c.valid
  · rename_i h
    have hx : 0xd800 < 0x10FFFF := by simp_arith
    have hy : c.val.toNat < 0x10FFFF := by simp [Nat.lt_trans h hx]
    have hz : c < Char.max := by exact hy
    simp [Char.lt_le hz]
  · rename_i h
    have hx : c.val.toNat < 0x10FFFF.succ := h.right
    have hy : c.val.toNat ≤ 0x10FFFF := Nat.le_of_lt_succ hx
    exact hy

theorem lt_def {a b : Char} : a < b ↔ a.val < b.val := .rfl

theorem one_le_of_lt {c1 c2 : Char} (h : c1 < c2) : 1 ≤ c2.val :=
  have h : c1.val < c2.val := Char.lt_def.mp h
  UInt32.one_le_of_lt h

theorem toNat_eq (c : Char) : c.val.toNat.toUInt32 = c.val := by
  simp [UInt32.toNat_toUInt_eq c.val]
