import Batteries.Data.String

namespace String

theorem valid_prev {p : Pos} (h : p.Valid s) : (prev s p).Valid s := by
  match s, p, h with
  | ⟨_⟩, ⟨_⟩, ⟨[], cs, rfl, rfl⟩ => simp_all
  | ⟨_⟩, ⟨_⟩, ⟨cs, cs', rfl, rfl⟩ =>
    match cs, cs.eq_nil_or_concat with
    | _, .inl rfl => simp_all
    | _, .inr ⟨cs'', c, rfl⟩ =>
      simp [String.Pos.Valid]
      have := prev_of_valid cs'' c cs'
      simp_all
      exact ⟨cs'', And.intro ⟨c:: cs', rfl⟩ rfl⟩

theorem Pos.lt_def {a b : String.Pos} : a < b  ↔ a.byteIdx < b.byteIdx := Iff.rfl

theorem Pos.sub_lt_sub_left {k m n : String.Pos} (h1 : k < m) (h2 : k < n)
    : m - n < m - k := by
  have : m.byteIdx - n.byteIdx < m.byteIdx - k.byteIdx := Nat.sub_lt_sub_left h1 h2
  exact (String.Pos.lt_def.mpr this)

theorem Pos.sizeof_lt_of_lt {a b : String.Pos} (h : a < b) : sizeOf a < sizeOf b := by
  have sizeOf_string_pos {s : String.Pos} : sizeOf (s) = 1 + sizeOf s.byteIdx := rfl
  simp at h
  rw [sizeOf_string_pos, sizeOf_string_pos, sizeOf_nat, sizeOf_nat]
  omega
