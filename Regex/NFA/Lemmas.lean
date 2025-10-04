import Batteries.Data.Fin.Basic
import Regex.Utils
import Regex.Data.List.Lemmas
import Regex.Data.Array.Basic
import Regex.Data.Array.Lemmas
import Regex.NFA.Basic

namespace NFA

theorem SlotsValidOfRangeMap (slots : Array Capture.SlotGroup)
  (h : (List.range slots.size).map (fun i => (i, i.div 2)) = slots.toList)
    : Slots.Valid slots := by
  simp
  and_intros
  · intros
    expose_names
    have hMem (a : Capture.SlotGroup) (h : a ∈ (List.range slots.size).map (fun i => (i, i.div 2)))
        : a.2 = a.1.div 2 := by
      grind
    have := hMem (a, b) (by grind)
    simp_all
    rw [Nat.mul_comm]
    have := @Nat.div_add_mod a 2
    rw [h_2] at this
    exact id (Eq.symm this)
  · intros
    expose_names
    have hMem (a : Capture.SlotGroup) (h : a ∈ (List.range slots.size).map (fun i => (i, i.div 2)))
        : a.2 = a.1.div 2 := by
      grind
    have := hMem (a, b) (by grind)
    simp_all
    rw [Nat.mul_comm]
    have := @Nat.div_add_mod a 2
    rw [h_2] at this
    exact id (Eq.symm this)
  · intros
    expose_names
    exact ⟨a - 1, ⟨b, by
    and_intros
    · have : (a, b) ∈ (List.range slots.size).map (fun i => (i, i.div 2)) := by grind
      have h : b = (a - 1).div 2 := by
        rw [h_2]
        exact Eq.symm (@Nat.div_eq_of_eq_mul_left 2 (b * 2) b (by grind) rfl)
      have hMem (a : Capture.SlotGroup) (h : a.1 < slots.size ∧ a.2 = a.1.div 2)
          : a ∈ (List.range slots.size).map (fun i => (i, i.div 2)) := by
        grind
      have := hMem (a - 1, b) (And.intro (by grind) h)
      grind
    · rfl
    · grind⟩⟩

instance instLEProdNat : LE Capture.SlotGroup where le := Prod.Lex (· < ·) (· ≤ ·)
instance instLTProdNat : LT Capture.SlotGroup where lt := Prod.Lex (· < ·) (· < ·)

private theorem mem_toSlots_capture_exists (captures : Array NFA.Capture) (slots : Array Capture.SlotGroup)
  (h : slots = NFA.Capture.toSlots captures)
    : ∀ slot ∈ slots, ∃ capture : NFA.Capture, capture ∈ captures ∧ NFA.Capture.toSlots.f capture = slot := by
  unfold NFA.Capture.toSlots at h
  simp at h
  generalize hf : (Array.map NFA.Capture.toSlots.f captures) = filtered at h
  generalize hs : (filtered.mergeSort NFA.Capture.toSlots.le) = sorted at h
  intro slot hSlot
  rw [h] at hSlot
  have hMemSorted := (Array.mem_unique sorted).mp hSlot
  rw [← hs] at hMemSorted
  have hMemFiltered := (Array.mem_mergeSort filtered NFA.Capture.toSlots.le).mp hMemSorted
  rw [← hf] at hMemFiltered
  have ⟨state, ⟨hmem, heq⟩⟩ := Array.mem_map.mp hMemFiltered
  exact ⟨state, by simp [*]⟩

private theorem mem_toSlots_slot_exists (captures : Array NFA.Capture) (slots : Array Capture.SlotGroup)
  (h : slots = NFA.Capture.toSlots captures)
    : ∀ capture ∈ captures, (∃ slot ∈ slots, NFA.Capture.toSlots.f capture = slot) := by
  unfold NFA.Capture.toSlots at h
  simp at h
  generalize hf : (Array.map NFA.Capture.toSlots.f captures) = filtered at h
  generalize hs : (filtered.mergeSort NFA.Capture.toSlots.le) = sorted at h
  intro capture hCapture
  let slot := NFA.Capture.toSlots.f capture
  let hSlot : slot = NFA.Capture.toSlots.f capture := by simp +zetaDelta
  exact ⟨slot, by
    have hMemMap := (@Array.mem_map NFA.Capture Capture.SlotGroup slot NFA.Capture.toSlots.f captures).mpr
                        ⟨capture, And.intro hCapture rfl⟩
    rw [hf] at hMemMap
    have hMemSorted := (Array.mem_mergeSort filtered NFA.Capture.toSlots.le).mpr hMemMap
    rw [hs] at hMemSorted
    have hMemUnique := (Array.mem_unique sorted).mpr hMemSorted
    rw [← h] at hMemUnique
    simp_all⟩

private theorem slotsAreValid_of_slot_mod_eq_0
  (captures : Array NFA.Capture) (slots : Array Capture.SlotGroup)
  (hmem : ∀ (slot : Capture.SlotGroup), slot ∈ slots
          → ∃ capture, capture ∈ captures ∧ NFA.Capture.toSlots.f capture = slot)
    : ∀ (slot : { slot // slot ∈ slots ∧ slot.fst % 2 = 0 }), slot.val.fst = slot.val.snd * 2 := by
  intro ⟨s, hs⟩
  have ⟨capture, hi⟩ := hmem s hs.left
  unfold NFA.Capture.toSlots.f at hi
  have hIsValid := capture.isValid
  simp at hIsValid
  split at hIsValid
  · grind
  · have : s.fst % 2 = 1 := by grind
    have : s.fst % 2 = 0 := by grind
    simp_all

private theorem slotsAreValid_of_slot_mod_eq_1
  (captures : Array NFA.Capture) (slots : Array Capture.SlotGroup)
  (hmem : ∀ (slot : Capture.SlotGroup), slot ∈ slots
          → ∃ capture, capture ∈ captures ∧ NFA.Capture.toSlots.f capture = slot)
    : ∀ (slot : { slot // slot ∈ slots ∧ slot.fst % 2 = 1 }), slot.val.fst = slot.val.snd * 2 + 1 := by
  intro ⟨s, hs⟩
  have ⟨capture, hi⟩ := hmem s hs.left
  unfold NFA.Capture.toSlots.f at hi
  have hIsValid := capture.isValid
  simp at hIsValid
  split at hIsValid <;> grind

private theorem slotsAreValid_if_exists
  (captures : Array NFA.Capture) (h : NFA.Capture.valid captures)
  (slots : Array Capture.SlotGroup) (heq : NFA.Capture.toSlots captures = slots)
  (hmem : ∀ (slot : Capture.SlotGroup), slot ∈ slots
          → ∃ capture, capture ∈ captures ∧ NFA.Capture.toSlots.f capture = slot)
    : ∀ (slot : { slot // slot ∈ slots ∧ slot.fst = slot.snd * 2 + 1 }),
      ∃ slot', slot' ∈ slots ∧ slot.val.snd = slot'.snd ∧ slot'.fst = slot'.snd * 2 := by
  intro ⟨s, hs⟩
  have ⟨capture, hCapture⟩ := hmem s hs.left
  unfold NFA.Capture.valid at h
  unfold NFA.Capture.toSlots.f at hCapture
  have hIsValid := capture.isValid
  simp at hIsValid
  split at hIsValid; · grind
  have ⟨capture', hCapture'⟩ := h.right.right ⟨capture, by simp_all⟩
  have ⟨s', hs'⟩ := mem_toSlots_slot_exists captures slots heq.symm capture' hCapture'.left
  exact ⟨s', by
    and_intros
    simp_all
    all_goals simp [Capture.toSlots.f] at hs' <;> simp_all <;> grind⟩

theorem toSlots_valid (captures : Array NFA.Capture)
  (h : NFA.Capture.valid captures)
    : Slots.Valid (NFA.Capture.toSlots captures) := by
  generalize hs : NFA.Capture.toSlots captures = slots
  unfold Slots.Valid
  have hmem := mem_toSlots_capture_exists captures slots hs.symm
  and_intros
  · exact slotsAreValid_of_slot_mod_eq_0 captures slots hmem
  · exact slotsAreValid_of_slot_mod_eq_1 captures slots hmem
  · exact slotsAreValid_if_exists captures h slots hs hmem
