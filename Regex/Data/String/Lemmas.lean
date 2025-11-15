import Batteries.Data.String

namespace String

theorem valid_prev {p : Pos.Raw} (h : p.Valid s) : (Pos.Raw.prev s p).Valid s := by
  match hm : s, p, h with
  | _, ⟨_⟩, ⟨[], cs, _⟩ => simp_all
  | _, ⟨_⟩, ⟨cs, cs', _⟩ =>
    match cs, cs.eq_nil_or_concat with
    | _, .inl rfl => simp_all
    | cs, .inr ⟨cs'', c, h⟩ =>
      have := prev_of_valid cs'' c cs'
      exact Pos.Raw.Valid.intro ⟨cs'', ⟨c :: cs', by and_intros <;> simp_all⟩⟩

theorem Pos.lt_def {a b : String.Pos.Raw} : a < b  ↔ a.byteIdx < b.byteIdx := Iff.rfl

theorem Pos.sub_lt_sub_left {k m n : String.Pos.Raw} (h1 : k < m) (h2 : k < n)
    : m.byteIdx - n.byteIdx < m.byteIdx - k.byteIdx := by
  have : m.byteIdx - n.byteIdx < m.byteIdx - k.byteIdx := Nat.sub_lt_sub_left h1 h2
  exact (String.Pos.lt_def.mpr this)

theorem Pos.sizeof_lt_of_lt {a b : String.Pos.Raw} (h : a < b) : sizeOf a < sizeOf b := by
  have sizeOf_string_pos {s : String.Pos.Raw} : sizeOf (s) = 1 + sizeOf s.byteIdx := rfl
  rw [sizeOf_string_pos, sizeOf_string_pos, sizeOf_nat, sizeOf_nat]
  exact Nat.add_lt_add_left h 1
