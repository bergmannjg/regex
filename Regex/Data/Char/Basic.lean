import Batteries.Data.Nat.Lemmas
import Regex.Data.UInt.Basic
import Batteries.Data.Char.Basic

namespace Char

/-- max valid char -/
def maxChar : Char := ⟨Char.max.toUInt32, by simp +arith +decide⟩

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
  have h₂ : c1.val.toNat ≤ c2.val.toNat := by grind
  exact h₂

theorem succ_lt {c1 c2 : Char} (h : (c2.val.toNat - c1.val.toNat) = 1) : c1 < c2 := by
  have hx : c1.val.toNat < c2.val.toNat := by grind
  exact hx

theorem min_le (c : Char) : Char.min ≤ c := by
  have h : 0 ≤ c.val.toNat := by simp_all
  exact h

theorem le_max (c : Char) : c ≤ Char.maxChar := by
  cases c.valid
  · rename_i h
    have hx : 0xd800 < 0x10FFFF := by simp +arith
    have hy : c.val.toNat < 0x10FFFF := by grind
    have hz : c < Char.maxChar := by exact hy
    simp [Char.lt_le hz]
  · rename_i h
    have hx : c.val.toNat < 0x10FFFF.succ := h.right
    have hy : c.val.toNat ≤ 0x10FFFF := Nat.le_of_lt_succ hx
    exact hy

theorem one_le_of_lt {c1 c2 : Char} (h : c1 < c2) : 1 ≤ c2.val :=
  have h : c1.val < c2.val := Char.lt_def.mp h
  UInt32.one_le_of_lt h

theorem toNat_eq (c : Char) : c.val.toNat.toUInt32 = c.val := by
  exact UInt32.ofNat_toNat

theorem succ_lt_lt {c1 c2 : Char} (h : 1 + Char.toNat c1 < Char.toNat c2) : c1 < c2 := by
  have h : Char.toNat c1 < Char.toNat c2 := Nat.succ_lt_lt h
  exact h

theorem succ_lt_succ_lt {c1 c2 : Char} (h : 1 + Char.toNat c1 < Char.toNat c2)
    (hs: UInt32.isValidChar (c1.val + 1)) : ⟨c1.val + 1, hs⟩ < c2 := by
  rw [Char.lt_def]
  have h : c1.toNat + 1 < Char.toNat c2 := by
    rw [Nat.add_comm]
    simp [h]
  have hx : Char.toNat c1 + 1 < UInt32.size := UInt32.isValidChar_succ_lt_uintSize c1.val c1.valid
  have hy : c1.toNat + 1 = (c1.val + 1).toNat := UInt32.toNat_add_toNat c1.val 1 hx
  rw [hy] at h
  exact h

theorem lt_pred_le {c1 c2 : Char} (h : c1 < c2) : c1.val ≤ c2.val - 1 := by
  have h : c1.val < c2.val := Char.lt_def.mp h
  have h2 : c2.val.toFin < UInt32.size := UInt32.isValidChar_lt_uintSize c2.val
  simp [UInt32.lt_pred_le h h2]

theorem lt_succ_le {c1 c2 : Char} (h : c1 < c2) : c1.val + 1 ≤ c2.val := by
  have h : c1.val < c2.val := Char.lt_def.mp h
  have hsucc : c1.val.toFin + 1 < UInt32.size := UInt32.isValidChar_succ_lt_uintSize c1.val c1.valid
  simp [UInt32.lt_succ_le h hsucc]

theorem succ_add_le__pred {c1 c2 : Char} (h : 1 + c1.toNat < c2.toNat)
  (hs: UInt32.isValidChar (c1.val + 1)) : c1.val + 1 ≤ c2.val - 1 := by
  have h : ⟨c1.val + 1, hs⟩ < c2 := Char.succ_lt_succ_lt h hs
  have h : c1.val + 1 ≤ c2.val - 1 := Char.lt_pred_le h
  simp [h]

theorem incr_le_decr {c1 c2 : Char} (h : 1 + Char.toNat c1 < Char.toNat c2)
    : Char.increment c1 ≤ Char.decrement c2 := by
  unfold Char.increment
  unfold Char.decrement
  split <;> try simp_all
  · split <;> try simp_all
    · rename_i hs hp
      let cs : Char := ⟨c1.val + 1, hs⟩
      have hseq : cs = ⟨c1.val + 1, hs⟩ := rfl
      let cp : Char := ⟨c2.val - 1, hp⟩
      let hpeq : cp = ⟨c2.val - 1, hp⟩ := rfl
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
