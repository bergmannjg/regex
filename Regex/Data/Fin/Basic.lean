import Batteries.Data.Fin.Lemmas

namespace Fin

theorem ofNat_eq (n : Nat) (h : n < UInt32.size)
    : Fin.ofNat' UInt32.size n = ⟨n, h⟩  := by
  have hu : UInt32.size = 4294967295 + 1 := by simp_arith
  rw [hu] at h
  unfold Fin.ofNat'
  simp [Fin.val_mk h]
  simp_all [Nat.mod_eq_of_lt h]

theorem ofNat_val_eq (n : Nat) (h : n < UInt32.size)
    : (Fin.ofNat'  UInt32.size n).val = n := by
  simp [Fin.ofNat_eq n h]

theorem ofNat_add (n m : Nat) (h : n + m < UInt32.size)
    : (Fin.ofNat'  UInt32.size (n + m)).val = n + m := by
  have hu : UInt32.size = 4294967295 + 1 := by simp_arith
  rw [hu] at h
  unfold Fin.ofNat'
  simp [Fin.val_mk h]
  simp_all [Nat.mod_eq_of_lt h]

theorem toNat_ofNat_eq (n : Fin UInt32.size) : (Fin.ofNat' UInt32.size (n.val)) = n := by
  unfold Fin.ofNat'
  have heq : n.val % UInt32.size = n.val := by simp_all [Nat.mod_eq_of_lt n.isLt]
  have hn : n.val % UInt32.size < UInt32.size := by rw[heq]; simp [n.isLt]
  let m : Fin UInt32.size := { val := n.val % UInt32.size, isLt := hn }
  have hm : m = { val := n.val % UInt32.size, isLt := hn } := by simp +zetaDelta
  rw [← hm]
  simp_all [heq]

theorem ofNat_val_add (n m : Fin UInt32.size) (h : n.val + m.val < UInt32.size)
    : (Fin.ofNat'  UInt32.size (n.val + m.val)) = n + m := by
  unfold Fin.ofNat'
  have heq : (n.val + m.val) % UInt32.size = n.val + m.val := by simp_all [Nat.mod_eq_of_lt h]
  have hnm : (n.val + m.val) % UInt32.size < UInt32.size := by rw[heq]; simp [h]
  let nm : Fin UInt32.size := { val := (n.val + m.val) % UInt32.size, isLt := hnm }
  have hm : nm = { val := (n.val + m.val) % UInt32.size, isLt := hnm } := by simp +zetaDelta
  rw [← hm]
  rw [Fin.add_def]
