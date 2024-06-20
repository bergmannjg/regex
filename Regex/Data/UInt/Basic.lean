import Batteries.Data.Fin.Lemmas
import Batteries.Data.Nat.Lemmas
import Regex.Data.Fin.Basic
import Regex.Data.Nat.Basic

namespace UInt32

theorem lt_def {a b : UInt32} : a < b ↔ a.val < b.val := .rfl

theorem le_def {a b : UInt32} : a ≤ b ↔ a.val ≤ b.val := .rfl

theorem add_def {a b : UInt32} : UInt32.add a b = a + b := rfl

theorem sub_def {a b : UInt32} : UInt32.sub a b = a - b := rfl

theorem eq_of_val_eq : ∀ {i j : UInt32}, Eq i.val j.val → Eq i j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem val_eq_of_eq {i j : UInt32} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

theorem val_ne_of_ne {c d : UInt32} (h : Not (Eq c d)) : Not (Eq c.val d.val) :=
  fun h' => absurd (eq_of_val_eq h') h

theorem one_le_of_lt {c1 c2 : UInt32} (h : c1 < c2) : 1 ≤ c2 :=
  Nat.zero_lt_of_lt h

theorem toNat_toUInt_eq (u : UInt32) : u.toNat.toUInt32 = u := by
  unfold UInt32.toNat
  unfold Nat.toUInt32
  unfold UInt32.ofNat
  have h : (Fin.ofNat (u.val)) = u.val := Fin.toNat_ofNat_eq u.val
  rw [h]

theorem ofNat_eq (n : Nat) (h : n < UInt32.size) : (UInt32.ofNat n).val = ⟨n, h⟩ := by
  unfold UInt32.ofNat
  simp [Fin.ofNat_eq n h]

theorem ofNat_add_ofNat (n m : Nat) (hn : n < UInt32.size) (hm : m < UInt32.size)
  (hnm : n + m < UInt32.size) : (UInt32.ofNat n) + (UInt32.ofNat m) = UInt32.ofNat (n + m) := by
  rw [← UInt32.add_def]
  unfold UInt32.add
  have hx : (UInt32.ofNat n).val = ⟨n, hn⟩ := UInt32.ofNat_eq n hn
  have hy : (UInt32.ofNat m).val = ⟨m, hm⟩ := UInt32.ofNat_eq m hm
  have hxy : (UInt32.ofNat (n + m)).val = ⟨n + m, hnm⟩ := UInt32.ofNat_eq (n + m) hnm
  apply UInt32.eq_of_val_eq
  rw [hxy, hx, hy]
  have hxy : (⟨n, hn⟩ : Fin UInt32.size) + ⟨m, hm⟩ = ⟨n + m, hnm⟩ := by
    rw [Fin.add_def]
    have hx : (⟨n, hn⟩ : Fin UInt32.size).val = n := by simp
    have hy : (⟨m, hm⟩ : Fin UInt32.size).val = m := by simp
    rw [hx, hy]
    have h : (n + m) % UInt32.size = n + m := Nat.mod_eq_of_lt hnm
    simp [h]
  rw [hxy]

theorem toNat_add_toNat (n m : UInt32) (hnm : n.val + m.val < UInt32.size)
    : n.toNat + m.toNat = (n + m).toNat := by
  rw [← UInt32.add_def]
  unfold UInt32.add
  unfold UInt32.toNat
  rw [Fin.add_def]
  have h : (n.val.val + m.val.val) % UInt32.size = n.val.val + m.val.val := Nat.mod_eq_of_lt hnm
  simp [h]

theorem toNat_sub_toNat {n m : UInt32} (hmn : m.val ≤ n.val) (h2 : n.val < UInt32.size)
    : n.toNat - m.toNat = (n - m).toNat := by
  have h1 : n.val - m.val < UInt32.size := Nat.le_lt_sub_lt hmn h2
  have h2 : m.val < UInt32.size := Nat.lt_of_le_of_lt hmn h2
  rw [← UInt32.sub_def]
  unfold UInt32.sub
  unfold UInt32.toNat
  rw [Fin.sub_def]
  have h : (n.val.val + (UInt32.size - m.val.val)) % UInt32.size
            = n.val.val - m.val.val := Nat.mod_sub_eq_of_lt hmn h1 (Nat.le_of_lt h2)
  simp [h]

theorem toUInt32_add_toUInt32 (n m : Nat) (hn : n < UInt32.size) (hm : m < UInt32.size)
  (hnm : n + m < UInt32.size) : n.toUInt32 + m.toUInt32 = (n + m).toUInt32 := by
  unfold Nat.toUInt32
  simp [UInt32.ofNat_add_ofNat n m hn hm hnm]

theorem toUInt32_one_add (c : Nat) (h : c + 1 < UInt32.size)
    : c.toUInt32 + 1 = (c + 1).toUInt32 :=
  toUInt32_add_toUInt32 c 1 (by simp [Nat.lt_of_succ_lt h]) (by simp_arith) h

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
  simp [Nat.lt_trans _ _]

theorem isValidChar_succ_lt_uintSize (u : UInt32) (h : UInt32.isValidChar u)
    : u.val.val + 1 < UInt32.size := by
  have hx : u.val.val < 0x110000 := UInt32.isValidChar_lt_0x110000 u h
  have hy : u.val.val + 1 < 0x110000 + 1 := Nat.add_lt_add_right hx 1
  have hz : 0x110000 + 1 < UInt32.size := by simp_arith
  simp [Nat.lt_trans hy hz]

theorem isValidChar_pred_lt_uintSize (u : UInt32) (h2 : UInt32.isValidChar u) (h3 : 1 ≤ u)
    : u.val - 1 < UInt32.size := by

  have hx1 : u.val.val < 0x110000 := UInt32.isValidChar_lt_0x110000 u h2
  have hx2 : u.val < 0x110000 := UInt32.lt_def.mp hx1
  have hx3 : 0x110000 < UInt32.size := by simp_arith
  have hx4 : u.val < UInt32.size := Nat.lt_trans hx2 hx3

  have h3 : u.val - 1 < UInt32.size := Nat.le_lt_sub_lt h3 hx4
  simp [h3]

theorem lt_succ_le {c1 c2 : UInt32} (h : c1 < c2) (hsucc : c1.val + 1 < UInt32.size)
    : c1 + 1 ≤ c2 := by
  have hx : c1.val < c2.val := UInt32.lt_def.mp h
  have heq : c1.val.val + 1 ≤ c2.val.val := Nat.succ_le_of_lt hx
  have ht : c1.val.val + 1 = (c1 + 1).val.val := UInt32.toNat_add_toNat c1 1 hsucc
  rw [ht] at heq
  simp [UInt32.le_def.mpr heq]

theorem toNatUnfold (c1 c2 : UInt32) (heq : c2.toNat - c1.toNat = (c2 - c1).toNat)
    : c2.val.val - c1.val.val = (c2 - c1).val.val := by
  unfold UInt32.toNat at heq
  simp_all [heq]

theorem lt_pred_le {c1 c2 : UInt32} (h : c1 < c2) (h2 : c2.val < UInt32.size)
    : c1 ≤ c2 - 1  := by
  have hx : c1.val < c2.val := UInt32.lt_def.mp h
  have heq : c1.val.val ≤ c2.val.val - 1 := Nat.le_pred_of_lt hx
  let hnm : 1 ≤ c2 := UInt32.one_le_of_lt h
  have ht' : c2.toNat - 1 = (c2 - 1).toNat := UInt32.toNat_sub_toNat hnm h2
  have ht : c2.val.val - 1 = (c2 - 1).val.val := UInt32.toNatUnfold 1 c2 ht'
  rw [ht] at heq
  simp [UInt32.le_def.mpr heq]
