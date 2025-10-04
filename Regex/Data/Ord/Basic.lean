namespace Ord

theorem toLE_opposite_eq [ord : Ord α] : ∀ (a b : α),
    (Ord.toLE ord.opposite).le a b ↔ (Ord.toLE ord).le b a  := by
  unfold Ord.toLE leOfOrd
  intro a b
  rw [iff_def]
  and_intros <;> intro h <;> assumption

theorem toLT_opposite_eq [ord : Ord α] : ∀ (a b : α),
    (Ord.toLT ord.opposite).lt a b ↔ (Ord.toLT ord).lt b a  := by
  unfold Ord.toLT ltOfOrd
  intro a b
  rw [iff_def]
  and_intros <;> intro h <;> assumption

@[simp] theorem toLT_iff_opposite [ord : Ord α]
  (lt_iff : ∀ a b : α, (Ord.toLT ord).lt a b ↔ (Ord.toLE ord).le a b ∧ ¬ (Ord.toLE ord).le b a)
    : ∀ (a b : α), (Ord.toLT ord.opposite).lt a b
    ↔ (Ord.toLE ord.opposite).le a b ∧ ¬(Ord.toLE ord.opposite).le b a  := by
  intro a b
  rw [toLT_opposite_eq a b, toLE_opposite_eq b a]
  exact lt_iff b a
