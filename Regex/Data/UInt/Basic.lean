import Batteries.Data.Fin.Lemmas
import Batteries.Data.Nat.Lemmas
import Regex.Data.Fin.Basic
import Regex.Data.Nat.Basic
import Init.Data.UInt.Lemmas
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas

namespace UInt32

theorem add_def' {a b : UInt32} : UInt32.add a b = a + b := rfl

theorem sub_def' {a b : UInt32} : UInt32.sub a b = a - b := rfl

theorem val_ne_of_ne {c d : UInt32} (h : Not (Eq c d)) : Not (Eq c.val d.val) :=
  fun h' => absurd (UInt32.eq_of_val_eq h') h

theorem one_le_of_lt {c1 c2 : UInt32} (h : c1 < c2) : 1 ≤ c2 :=
  Nat.zero_lt_of_lt h

theorem lt_toNat_lt {a b : UInt32} (h : a < b) : a.toNat < b.toNat := by
  unfold UInt32.toNat
  simp [UInt32.lt_def] at h
  exact BitVec.lt_def.mpr h

theorem toNat_toUInt_eq (u : UInt32) : u.toNat.toUInt32 = u := by
  unfold UInt32.toNat
  unfold Nat.toUInt32
  unfold UInt32.ofNat
  have h : (Fin.ofNat' UInt32.size (u.val)) = u.val := Fin.toNat_ofNat_eq u.val
  simp [h]

theorem ofNat_eq (n : Nat) (h : n < UInt32.size) : (UInt32.ofNat n).val = ⟨n, h⟩ := by
  simp_all [UInt32.ofNat, BitVec.ofNat_eq_ofNat, Fin.instOfNat]
  rw [← Fin.ofNat_eq n h]

@[simp] theorem toBitVecToNat_eq_val {u : UInt32} : u.toBitVec.toNat = u.val.val := rfl

theorem toBitVec_add_ofNat_eq {n m : Nat}
    : (ofNat n).toBitVec + (ofNat m).toBitVec
    = BitVec.ofNat 32 ((ofNat n).val + (ofNat m).val) := by
  unfold HAdd.hAdd instHAdd
  simp_all
  unfold Add.add BitVec.instAdd BitVec.add instAddNat
  simp_all

theorem ofNat_add_ofNat (n m : Nat) (hnm : n + m < UInt32.size)
    : (UInt32.ofNat n) + (UInt32.ofNat m) = UInt32.ofNat (n + m) := by
  simp only [← UInt32.add_def', UInt32.add, toBitVec_add_ofNat_eq, UInt32.mk_ofNat]

  apply UInt32.eq_of_val_eq
  have hn : n < UInt32.size := by omega
  have hm : m < UInt32.size := by omega
  rw [UInt32.ofNat_eq (n + m) hnm, UInt32.ofNat_eq n hn, UInt32.ofNat_eq m hm]
  have h : (⟨n, hn⟩ : Fin UInt32.size) + ⟨m, hm⟩ = ⟨n + m, hnm⟩ := by
    rw [Fin.add_def]
    simp [Nat.mod_eq_of_lt hnm]
  exact h

theorem toNat_add_toNat (n m : UInt32) (hnm : n.val + m.val < UInt32.size)
    : n.toNat + m.toNat = (n + m).toNat := by
  rw [← UInt32.add_def']
  unfold UInt32.add
  unfold UInt32.toNat
  simp_all [Fin.add_def]
  have h : (n.toBitVec.toNat + m.toBitVec.toNat) % UInt32.size
         = n.toBitVec.toNat + m.toBitVec.toNat := Nat.mod_eq_of_lt hnm
  simp_all [h]

theorem toNat_sub_toNat {n m : UInt32} (hmn : m.val ≤ n.val) (h2 : n.val < UInt32.size)
    : n.toNat - m.toNat = (n - m).toNat := by
  have h1 : n.val - m.val < UInt32.size := Nat.le_lt_sub_lt hmn h2
  have h2 : m.val < UInt32.size := Nat.lt_of_le_of_lt hmn h2
  rw [← UInt32.sub_def']
  unfold UInt32.sub
  unfold UInt32.toNat
  simp [Fin.sub_def]
  have h : (n.toBitVec.toNat + (UInt32.size - m.toBitVec.toNat)) % UInt32.size
            = n.toBitVec.toNat - m.toBitVec.toNat := Nat.mod_sub_eq_of_lt hmn h1 (Nat.le_of_lt h2)
  simp_all [h]
  have : n.toBitVec.toNat + (UInt32.size - m.toBitVec.toNat)
       = (UInt32.size - m.toBitVec.toNat) +  n.toBitVec.toNat := by simp_arith
  simp_all [h]

theorem toUInt32_add_toUInt32 (n m : Nat) (hnm : n + m < UInt32.size)
    : n.toUInt32 + m.toUInt32 = (n + m).toUInt32 := by
  unfold Nat.toUInt32
  simp [UInt32.ofNat_add_ofNat n m hnm]

theorem toUInt32_one_add (c : Nat) (h : c + 1 < UInt32.size)
    : c.toUInt32 + 1 = (c + 1).toUInt32 :=
  toUInt32_add_toUInt32 c 1 h

theorem isValidChar_lt_0x110000 (u : UInt32) (h : UInt32.isValidChar u)
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

theorem isValidChar_lt_uintSize (u : UInt32) : u.val.val < UInt32.size := by
  exact u.val.isLt

theorem isValidChar_succ_lt_uintSize (u : UInt32) (h : UInt32.isValidChar u)
    : u.val.val + 1 < UInt32.size := by
  have hx : u.val.val < 0x110000 := UInt32.isValidChar_lt_0x110000 u h
  have hy : u.val.val + 1 < 0x110000 + 1 := Nat.add_lt_add_right hx 1
  have hz : 0x110000 + 1 < UInt32.size := by simp_arith
  exact Nat.lt_trans hy hz

theorem isValidChar_pred_lt_uintSize (u : UInt32) : u.val - 1 < UInt32.size := by
  omega

theorem lt_succ_le {c1 c2 : UInt32} (h : c1 < c2) (hsucc : c1.val + 1 < UInt32.size)
    : c1 + 1 ≤ c2 := by
  have hx : c1.val < c2.val := UInt32.lt_def.mp h
  have heq : c1.val.val + 1 ≤ c2.val.val := Nat.succ_le_of_lt hx
  have ht : c1.val.val + 1 = (c1 + 1).val.val := UInt32.toNat_add_toNat c1 1 hsucc
  rw [ht] at heq
  simp [UInt32.le_def.mpr heq]

theorem toNatUnfold (c1 c2 : UInt32) (heq : c2.toNat - c1.toNat = (c2 - c1).toNat)
    : c2.val.val - c1.val.val = (c2 - c1).val.val := by
  unfold UInt32.toNat BitVec.toNat at heq
  simp_all [heq]
  rfl

theorem lt_pred_le {c1 c2 : UInt32} (h : c1 < c2) (h2 : c2.val < UInt32.size)
    : c1 ≤ c2 - 1  := by
  have hx : c1.val < c2.val := UInt32.lt_def.mp h
  have heq : c1.val.val ≤ c2.val.val - 1 := Nat.le_pred_of_lt hx
  let hnm : 1 ≤ c2 := UInt32.one_le_of_lt h
  have ht' : c2.toNat - 1 = (c2 - 1).toNat := UInt32.toNat_sub_toNat hnm h2
  have ht : c2.val.val - 1 = (c2 - 1).val.val := UInt32.toNatUnfold 1 c2 ht'
  rw [ht] at heq
  simp [UInt32.le_def.mpr heq]
