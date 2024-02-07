import Init.Data.Ord
import Std.Logic
import Std.Data.Nat.Lemmas
import Std.Data.Fin.Lemmas
import Std.Data.Int.Lemmas
import Std.Data.List.Basic
import Regex.Utils
import Regex.Data.Array.Basic
import Regex.Data.UInt.Basic
import Regex.Data.Char.Basic

/-!
## IntervalSet

This file contains the definition of interval sets (`IntervalSet`),
a sorted set of non-overlapping ranges (`Range`).
-/

/-- A `Bound` defines a bounded set of values with min_value, max_value and increment
    and decrement operators. Negation of ranges (`Range`) is defined wrt the
    corresponding bound. -/
class Bound (α : Type u) [Ord α] [LE α] where
  min_value : α
  max_value : α
  increment : α -> α
  decrement : α -> α
  min_value_le_max_value : min_value ≤ max_value
  min_value_le_decrement c : min_value ≤ decrement c
  increment_le_max_value c : increment c ≤ max_value

/-- a Bound of type Char -/
instance : Bound Char where
  min_value := Char.min
  max_value := Char.max
  increment (c : Char) := Char.increment c
  decrement (c : Char) := Char.decrement c
  min_value_le_max_value := by simp_arith
  increment_le_max_value c := by
    unfold Char.increment; simp_all; split <;> try simp_all
    · simp [Char.le_max]
    · simp [Char.le_max]
  min_value_le_decrement c := by
    unfold Char.decrement; simp_all; split <;> try simp_all
    · simp [Char.min_le]
    · simp [Char.min_le]

/-- A closed range bounded inclusively below and above (`start..end`). -/
structure Range (α : Type u) [Ord α] [LE α] [Bound α] where
  start: α
  «end»: α
  isLe: start ≤ «end»
deriving Repr, DecidableEq

instance (α : Type u) [Ord α] [LE α] [LT α] [Bound α]: LT $ Range α where
  lt r1 r2 := r1.end < r2.start

instance : ToString $ Range Char where
  toString s := s!"{s.start} {s.end}"

instance : Inhabited $ Range Char where
  default := ⟨default, default, of_decide_eq_true rfl⟩

namespace Range

/-- Ranges `r1` and `r2` are non overlapping when they are sorted and
    they are not overlapping or adjacent, i.e. the difference of `r2.start` and `r1.end`
    is greater than one. Ranges with a difference of one are canonicalized
    to a new range (`Interval.canonicalize`). -/
def nonOverlapping {α : Type u} [Ord α] [LE α] [LT α] [Bound α] [HSub α α Nat]
    (r1 r2 : Range α) : Prop :=
   1 < ((r2.start - r1.end) : Nat)

instance {α : Type u} [Ord α] [LE α] [LT α] [Bound α] [HSub α α Nat]
    (r1 r2 : Range α) : Decidable (Range.nonOverlapping r1 r2) :=
  inferInstanceAs (Decidable (LT.lt 1 ((r2.start - r1.end) : Nat)))

def intersection {α : Type u} [Ord α]
    [LT α] [LE α] [Bound α] [(a b : α) → Decidable (a ≤ b)]
    (r1 r2 : Range  α) : Option $ Range α :=
  let lower := if r1.start ≤ r2.start then r2.start else r1.start
  let upper := if r1.«end» ≤ r2.«end» then r1.«end» else r2.«end»
  if h : lower ≤ upper then some ⟨lower, upper, h⟩
  else none

def Char.sub (c₁ c₂ : Char) := c₁.toNat - c₂.toNat

instance : HSub Char Char Nat where
  hSub := Char.sub

theorem Char.sub_def {a b : Char} : Char.sub a b = a - b := rfl

def negate (r1 r2 : Range Char) (h : nonOverlapping r1 r2) : Range Char :=
  ⟨Bound.increment r1.end, Bound.decrement r2.start, by
    unfold nonOverlapping at h
    unfold Bound.increment
    unfold Bound.decrement
    unfold instBoundCharInstOrdCharInstLEChar
    simp_all
    have h : 1 + r1.end.toNat < r2.start.toNat := by simp [Nat.add_lt_of_lt_sub h]
    simp [Char.incr_le_decr h]⟩

end Range

namespace Ranges

def unique (ranges: Array (Range Char)) : Array (Range Char) :=
  match ranges.data with
  | [] => #[]
  | [r] => #[r]
  | head :: tail  =>
    let (_, unique) := tail |> List.foldl (init := (head, #[head]))
      (fun (prev, unique) r =>
        if prev = r then (r, unique)
        else (r, unique.push r))
    unique

/-- a list of ranges is non overlapping when ranges are sorted
    and no ranges are overlapping or adjacent -/
def dataIsNonOverlapping {α : Type u} [Ord α] [LT α] [LE α] [Bound α] [HSub α α Nat]
    (ranges: List (Range α)) : Prop :=
  match ranges with
  | [] => true
  | [_] => true
  | head :: tail  => List.Chain (Range.nonOverlapping) head tail

/-- an array of ranges is non overlapping when `ranges.data` is non overlapping -/
def nonOverlapping {α : Type u} [Ord α] [LT α] [LE α] [Bound α] [HSub α α Nat]
    (ranges: Array (Range α)) : Prop :=
  dataIsNonOverlapping ranges.data

end Ranges

/-- A sorted set of non-overlapping ranges. -/
structure IntervalSet (α : Type u) [Ord α] [LT α] [LE α] [Bound α] [HSub α α Nat]
    [(a b : α) → Decidable (a < b)] [(a b : α) → Decidable (a = b)] where
  ranges: Array (Range α)
  isNonOverlapping: Ranges.nonOverlapping ranges
deriving Repr

instance : ToString $ IntervalSet Char where
  toString s := s!"{s.ranges}"

namespace Interval

/-- last element of array `ranges` is non overlapping with range `next` -/
def nonOverlappingWithLast (ranges : Array $ Range Char) (next : Option (Range Char)) : Prop :=
  match ranges.last?, next with
  | some last, some next => Range.nonOverlapping last next
  | none , some _ => true
  | none, none => true
  | some _, none => false

/-- Accumulator for loop in canonicalize -/
structure Acc where
  next : Option (Range Char)
  set : IntervalSet Char
  nonOverlapping : nonOverlappingWithLast set.ranges next

def Acc.push (acc : Acc) (next : Range Char)
  (h : Ranges.nonOverlapping (Array.push acc.set.ranges next)) : IntervalSet Char :=
  ⟨acc.set.ranges.push next, h⟩

/-- is `next.start` equal to `n.start` -/
def is_start_eq (next : Option (Range Char)) (n : Range Char) : Prop :=
  match next with
  | some next  => next.start = n.start
  | _ => true

end Interval
