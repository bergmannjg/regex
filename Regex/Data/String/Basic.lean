import Batteries.Data.String

namespace String.Slice

/-- Slice `s` is a subslice of Slice `t`, if the underlying strings are equal
  and t.startInclusive ≤ s.startInclusive and s.endExclusive ≤ t.endExclusive.  -/
def isSubslice (s t : String.Slice) := s.str = t.str
                  ∧ t.startInclusive.offset ≤ s.startInclusive.offset
                  ∧ s.endExclusive.offset ≤ t.endExclusive.offset

@[simp] theorem replaceStartEnd_is_subslice_of {s : String.Slice} {p0 p1 : s.Pos} {h : p0 ≤ p1}
    : isSubslice (String.Slice.replaceStartEnd s p0 p1 h) s := by
  and_intros
  · rfl
  · simp [String.Pos.Raw.offsetBy, String.Pos.Raw.le_iff]
  · rw [@String.Slice.endExclusive_replaceStartEnd s p0 p1 h]
    exact String.Slice.Pos.offset_str_le_offset_endExclusive

/-- cast `p : s.Pos` to `t.Pos` -/
def castPosOfSubslice {s t : String.Slice} (p: s.Pos) (h : isSubslice s t) : t.Pos :=
  ⟨⟨p.offset.byteIdx + s.startInclusive.offset.byteIdx - t.startInclusive.offset.byteIdx⟩, by
    simp [isSubslice] at h
    generalize heq : p.offset.byteIdx + s.startInclusive.offset.byteIdx - t.startInclusive.offset.byteIdx = byteIdx
    have le : ⟨byteIdx⟩ ≤ t.rawEndPos := by
      rw [← heq]
      simp [String.Slice.rawEndPos, String.Slice.utf8ByteSize_eq]

      have := t.startInclusive_le_endExclusive
      rw [String.ValidPos.le_iff, String.Pos.Raw.le_iff] at this
      simp_all only [Nat.sub_add_cancel]

      have := p.isValidForSlice.le_utf8ByteSize
      simp [Slice.rawEndPos, Slice.utf8ByteSize, Pos.Raw.byteDistance, String.Pos.Raw.le_iff] at this

      have := s.startInclusive_le_endExclusive
      simp [String.ValidPos.le_iff, String.Pos.Raw.le_iff] at this

      exact Nat.le_trans (by grind) h.right.right
    have isValid : ((⟨byteIdx⟩ : String.Pos.Raw).offsetBy t.startInclusive.offset).IsValid t.str := by
      rw [← heq]
      simp [String.Pos.Raw.offsetBy]
      rw [Nat.add_sub_cancel' (by have := String.Pos.Raw.le_iff.mp h.right.left; grind)]
      rw [← h.left]
      have := p.isValidForSlice.isValid_offsetBy
      simp [Pos.Raw.offsetBy] at this
      grind
    exact { le_utf8ByteSize := le, isValid_offsetBy := isValid }⟩

/-- `s.startPos : s.Pos` as `t.Pos` -/
def startPosOfSubslice {s t : String.Slice} (h : isSubslice s t) : t.Pos :=
  castPosOfSubslice s.startPos h

theorem startPosOfSubslice_eq {s t : String.Slice} (h : isSubslice s t)
    : ⟨s.startInclusive.offset.byteIdx - t.startInclusive.offset.byteIdx⟩
      = (startPosOfSubslice h).offset := by
  simp [castPosOfSubslice, startPosOfSubslice]

/-- `s.endPos : s.Pos` as `t.Pos` -/
def endPosOfSubslice {s t : String.Slice} (h : isSubslice s t) : t.Pos :=
  castPosOfSubslice s.endPos h

theorem endPosOfSubslice_eq {s t : String.Slice} (h : isSubslice s t)
    : ⟨s.endExclusive.offset.byteIdx - t.startInclusive.offset.byteIdx⟩
      = (endPosOfSubslice h).offset := by
  simp [castPosOfSubslice, endPosOfSubslice]
  have : s.startInclusive.offset.byteIdx + s.utf8ByteSize = s.endExclusive.offset.byteIdx := by
    exact Nat.add_sub_of_le s.startInclusive_le_endExclusive
  grind

@[simp] theorem byteDistance_of_next_lt {s : String.Slice} {pos : s.Pos} (h : pos ≠ s.endPos)
    : (pos.next h).offset.byteDistance s.rawEndPos < pos.offset.byteDistance s.rawEndPos := by
  simp [String.Pos.Raw.byteDistance]
  rw [← @String.Slice.Pos.byteIdx_offset_next s pos h]
  have : pos.offset.byteIdx < (pos.next h).offset.byteIdx := by
    have := @String.Slice.Pos.lt_next s pos h
    rwa [String.Slice.Pos.lt_iff, String.Pos.Raw.lt_iff] at this
  have : (pos.next h).offset.byteIdx ≤ s.utf8ByteSize :=
    (pos.next h).isValidForSlice.le_utf8ByteSize
  grind

@[simp] theorem byteDistance_of_offset_and_char_lt {s : String.Slice} {pos : s.Pos} (h : pos ≠ s.endPos)
    : (pos.offset + pos.get h).byteDistance s.rawEndPos < pos.offset.byteDistance s.rawEndPos := by
  rw [← @String.Slice.Pos.offset_next s pos h]
  exact byteDistance_of_next_lt h
