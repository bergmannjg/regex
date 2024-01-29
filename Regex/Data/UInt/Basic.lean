import Std.Data.Fin.Lemmas
import Std.Data.Nat.Lemmas
import Regex.Data.Fin.Basic
import Regex.Data.Nat.Basic

namespace UInt32

theorem lt_def {a b : UInt32} : a < b ↔ a.val < b.val := .rfl

theorem le_def {a b : UInt32} : a ≤ b ↔ a.val ≤ b.val := .rfl

theorem add_def {a b : UInt32} : UInt32.add a b = a + b := rfl

theorem sub_def {a b : UInt32} : UInt32.sub a b = a - b := rfl

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

theorem eq_of_val_eq : ∀ {i j : UInt32}, Eq i.val j.val → Eq i j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem val_eq_of_eq {i j : UInt32} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

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
