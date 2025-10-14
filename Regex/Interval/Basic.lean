import Init.Data.Ord
import Batteries.Logic
import Batteries.Data.Nat.Lemmas
import Batteries.Data.Fin.Lemmas
import Init.Data.Int.Lemmas
import Batteries.Data.List.Basic
import Regex.Utils
import Regex.Data.Array.Basic
import Regex.Data.UInt.Basic
import Regex.Data.Char.Basic

/-!
## Interval Set

This file contains the definition of interval sets (`IntervalSet`),
a sorted set of non-overlapping intervals (`Interval.nonOverlapping`).
-/

/- We define intervals by the pair of endpoints `fst`, `snd`,
   see Mathlib.Order.Interval.Basic  -/
@[ext (flat := false)]
structure NonemptyInterval (α : Type) [LE α] extends Prod α α where
  /-- The starting point of an interval is smaller than the endpoint. -/
  fst_le_snd : fst ≤ snd

/-- A bounded order describes an order `(≤)` with a top and bottom element,
    see Mathlib.Order.BoundedOrder -/
class BoundedOrder (α : Type) [LE α] where
  bot : α
  bot_le : ∀ a : α, bot ≤ a
  top : α
  le_top : ∀ a : α, a ≤ top

/-- BoundedOrder is used to define negation of interval sets (`IntervalSet.negate`). -/
instance : BoundedOrder Char where
  bot := Char.min
  bot_le := Char.min_le
  top := Char.maxChar
  le_top := Char.le_max

theorem NonemptyInterval.eq_val_of_eq {α : Type} [LE α]
  {x y : NonemptyInterval α} (h : x = y) : x.fst = y.fst ∧ x.snd = y.snd := by
  simp_all

instance (α : Type) [LE α] [DecidableEq α] : DecidableEq (NonemptyInterval α) :=
  fun ⟨(a, b), _⟩ ⟨(a', b'), _⟩ =>
    match decEq a a' with
    | isTrue e₁ =>
      match decEq b b' with
      | isTrue e₂  => isTrue (e₁ ▸ e₂ ▸ rfl)
      | isFalse n₂ => isFalse fun h => absurd (NonemptyInterval.eq_val_of_eq h).right n₂
    | isFalse n₁ => isFalse fun h => absurd (NonemptyInterval.eq_val_of_eq h).left n₁

instance : ToString $ NonemptyInterval Char where
  toString s := s!"{s.fst} {s.snd}"

instance : Inhabited $ NonemptyInterval Char where
  default := ⟨default, of_decide_eq_true rfl⟩

namespace Interval

/-- Nonempty intervals `r1` and `r2` are non overlapping when they are sorted and
    they are not overlapping or adjacent, i.e. the difference of `r2.fst` and `r1.snd`
    is greater than one. Intervals with a difference of one are canonicalized
    to a new NonemptyInterval (`IntervalSet.canonicalize`). -/
def nonOverlapping {α : Type} [LE α] [HSub α α Nat] (r1 r2 : NonemptyInterval α) : Prop :=
   1 < ((r2.fst - r1.snd) : Nat)

instance {α : Type} [LE α] [HSub α α Nat]
    (r1 r2 : NonemptyInterval α) : Decidable (Interval.nonOverlapping r1 r2) :=
  inferInstanceAs (Decidable (LT.lt 1 ((r2.fst - r1.snd) : Nat)))

/-- create intersection of intervals `r1` and `r2` if it exists. -/
def intersection {α : Type} [LE α]
    [(a b : α) → Decidable (a ≤ b)] (r1 r2 : NonemptyInterval  α) : Option $ NonemptyInterval α :=
  let lower := if r1.fst ≤ r2.fst then r2.fst else r1.fst
  let upper := if r1.snd ≤ r2.snd then r1.snd else r2.snd
  if h : lower ≤ upper then some ⟨⟨lower, upper⟩, h⟩
  else none

def Char.sub (c₁ c₂ : Char) := c₁.toNat - c₂.toNat

instance : HSub Char Char Nat where
  hSub := Char.sub

theorem Char.sub_def {a b : Char} : Char.sub a b = a - b := rfl

/-- create interval between intervals `r1` and `r2`. -/
def between (r1 r2 : NonemptyInterval Char) (h : nonOverlapping r1 r2) : NonemptyInterval Char :=
  ⟨⟨Char.increment r1.snd, Char.decrement r2.fst⟩, by
    unfold nonOverlapping at h
    have h : 1 + r1.snd.toNat < r2.fst.toNat := by simp [Nat.add_lt_of_lt_sub h]
    simp [Char.incr_le_decr h]⟩

end Interval

namespace Intervals

/-- remove duplicate -/
def unique (intervals: Array (NonemptyInterval Char)) : Array (NonemptyInterval Char) :=
  match intervals.toList with
  | [] => #[]
  | [r] => #[r]
  | head :: tail  =>
    let (_, unique) := tail |> List.foldl (init := (head, #[head]))
      (fun (prev, unique) r =>
        if prev.fst = r.fst && prev.snd = r.snd then (r, unique)
        else (r, unique.push r))
    unique

/-- a list of intervals is non overlapping when intervals are sorted
    and no intervals are overlapping or adjacent -/
def dataIsNonOverlapping {α : Type} [LE α] [HSub α α Nat]
    (intervals: List (NonemptyInterval α)) : Prop :=
  match intervals with
  | [] => true
  | [_] => true
  | head :: tail => List.IsChain (Interval.nonOverlapping) (head :: tail)

/-- an array of intervals is non overlapping when `intervals.data` is non overlapping -/
def nonOverlapping {α : Type} [LE α] [HSub α α Nat]
    (intervals: Array (NonemptyInterval α)) : Prop :=
  dataIsNonOverlapping intervals.toList

end Intervals

/-- A sorted set of non-overlapping intervals. -/
structure IntervalSet (α : Type)[LT α] [LE α] [HSub α α Nat]
    [(a b : α) → Decidable (a < b)] [(a b : α) → Decidable (a = b)] where
  intervals: Array (NonemptyInterval α)
  isNonOverlapping: Intervals.nonOverlapping intervals

instance : ToString $ IntervalSet Char where
  toString s := s!"{s.intervals}"

namespace Interval

/-- last element of array `intervals` is non overlapping with NonemptyInterval `next` -/
def nonOverlappingWithLast (intervals : Array $ NonemptyInterval Char)
    (next : Option (NonemptyInterval Char)) : Prop :=
  match intervals.last?, next with
  | some last, some next => Interval.nonOverlapping last next
  | none , some _ => true
  | none, none => true
  | some _, none => false

/-- Accumulator for loop in canonicalize -/
structure Acc where
  next : Option (NonemptyInterval Char)
  set : IntervalSet Char
  nonOverlapping : nonOverlappingWithLast set.intervals next

def Acc.push (acc : Acc) (next : NonemptyInterval Char)
  (h : Intervals.nonOverlapping (Array.push acc.set.intervals next)) : IntervalSet Char :=
  ⟨acc.set.intervals.push next, h⟩

/-- is `next.fst` equal to `n.fst` -/
def is_start_eq (next : Option (NonemptyInterval Char)) (n : NonemptyInterval Char) : Prop :=
  match next with
  | some next  => next.fst = n.fst
  | _ => true

end Interval
