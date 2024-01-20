import Init.Data.Ord
import Regex.Utils

/-!
## IntervalSet

This file contains an implementation of interval sets (`IntervalSet`),
a sorted set of non-overlapping ranges (`Range`).
-/

class Bound (α : Type u) [Ord α] [LT α] where
  min_value : α
  max_value : α
  as_u32 : α -> UInt32
  increment : α -> α
  decrement : α -> α

instance : Bound Char where
  min_value := '\u0000'
  max_value := ⟨0x10FFFF, by simp_arith⟩
  as_u32 (c : Char) := c.val
  increment (c : Char) := if h : UInt32.isValidChar (c.val + 1) then ⟨c.val + 1, h⟩ else c
  decrement (c : Char) := if h : UInt32.isValidChar (c.val - 1) then ⟨c.val - 1, h⟩ else c

instance : HSub Char Char UInt32 where
  hSub c₁ c₂ := c₁.val - c₂.val

/-- A closed range bounded inclusively below and above (`start..end`). -/
structure Range (α : Type u) [Ord α] [LT α] [Bound α] where
  start: α
  «end»: α
deriving Repr, DecidableEq

instance : ToString $ Range Char where
  toString s := s!"{s.start} {s.end}"

instance (α : Type u) [Ord α] [LT α] [Bound α] [Inhabited α] : Inhabited $ Range α where
  default := ⟨default, default⟩

namespace Range

def intersection {α : Type u} [Ord α]
    [LT α] [LE α] [Bound α] [(a b : α) → Decidable (a ≤ b)]
    (r1 r2 : Range  α) : Option $ Range α :=
  let lower := if r1.start ≤ r2.start then r2.start else r1.start
  let upper := if r1.«end» ≤ r2.«end» then r1.«end» else r2.«end»
  if lower ≤ upper then some ⟨lower, upper⟩
  else none

end Range

/-- A sorted set of non-overlapping ranges. -/
structure IntervalSet (α : Type u) [Ord α] [LT α] [Bound α] where
  ranges: Array (Range α)
deriving Repr, DecidableEq

instance : ToString $ IntervalSet Char where
  toString s := s!"{s.ranges}"

namespace Interval

theorem pred_lt' {n m : Nat} (h : m < n) : Nat.pred n < n :=
  Nat.pred_lt (Nat.not_eq_zero_of_lt h)

/-- get predecessor of `i` in `Fin n`. -/
def Fin.pred (i : Fin n) (h : 0 < i.val) : Fin n :=
  ⟨i-1, by
    have h1 : i.val - 1 < i.val := pred_lt' h
    have h2 : i.val < n := i.isLt
    simp [Nat.lt_trans h1 h2]⟩

/-- Converts this set into a canonical ordering. That is, every interval set contains an
    ordered sequence of intervals where no two intervals are overlapping or adjacent. -/
def canonicalize [Ord α] [HSub α α UInt32] [LT α] [Bound α] [ToString α]
  [(a b : α) → Decidable (a < b)] [(a b : α) → Decidable (a = b)]
    (interval : IntervalSet α) : IntervalSet α :=
  let ranges := Array.qsort interval.ranges (fun a b => a.start < b.end)

  let init : Option (Range α) × Array (Range α) := (none, #[])
  let (v, ranges) := ranges |> Array.foldl (init := init) (fun (v, acc) r =>
    match v with
    | some l =>
      if (r.start - l.end).toNat = 1 then (some ⟨l.start, r.end⟩, acc) -- [a-bc-d] => [a-d]
      else if r.start < l.end && l.start < r.start then (some ⟨l.start, r.end⟩, acc) -- [a-cb-d] => [a-d]
      else if l.end < r.start then (r, acc.push l) -- [a-fg-h] => [a-fg-h]
      else if l.end = r.start then (none, acc.push ⟨l.start, r.end⟩) -- [a-bb-c] => [a-c]
      else if l.end < r.end then (none, acc.push r) -- [a-fb-c] => [a-f]
      else (some r, acc.push l)
    | none => (some r, acc))

  let ranges :=
    match v with
    | some v => ranges.push v
    | none => ranges

  IntervalSet.mk (Array.qsort ranges (fun a b => a.start < b.end))

/-- Negate a interval set with canonical ordering. -/
def negate [Ord α] [LT α] [Bound α] [ToString α] [(a b : α) → Decidable (a < b)]
    (interval : IntervalSet α) : IntervalSet α :=
  if interval.ranges.size = 0
  then ⟨#[⟨Bound.min_value, Bound.max_value⟩]⟩
  else
    let ranges : Array (Range α) :=
      Array.mapIdx interval.ranges  (fun i x => (i,x))
      |> Array.map (fun (i, y) =>
        if h : 0 < i.val
        then
          let j : Fin (Array.size interval.ranges) := Fin.pred i h
          let x := interval.ranges.get j
          ⟨Bound.increment x.end, Bound.decrement y.start⟩
        else
          if Bound.min_value < y.start
          then ⟨Bound.min_value, Bound.decrement y.start⟩
          else y
        )
    let last :=
      match interval.ranges.pop? with
      | some (x, _) =>
          if x.end < Bound.max_value
          then #[⟨Bound.increment x.end, Bound.max_value⟩]
          else #[]
      | none => #[]
    ⟨ranges ++ last⟩

/-- Intersection of interval sets with canonical ordering -/
def intersection [Ord α] [LT α] [LE α] [Bound α] [ToString α] [Inhabited α]
  [(a b : α) → Decidable (a ≤ b)] [(a b : α) → Decidable (a < b)]
    (interval1 interval2 : IntervalSet α) : IntervalSet α :=
  let ranges := intersection.loop 0 0 interval1.ranges interval2.ranges #[]
  ⟨ranges⟩
where
  loop [Ord α] [LT α] [LE α][Bound α] [ToString α] [Inhabited α]
    [(a b : α) → Decidable (a < b)] [(a b : α) → Decidable (a ≤ b)]
    (a b : Nat) (ra rb acc : Array $ Range α) : Array $ Range α :=
    if h₁ : a < ra.size then
      if h₂ : b < rb.size then
        let acc :=
          match Range.intersection (ra.get ⟨a, h₁⟩) (rb.get ⟨b, h₂⟩) with
          | some r => acc.push r
          | none => acc

        if (ra.get ⟨a, h₁⟩).end < (rb.get ⟨b, h₂⟩).end
        then loop (a+1) b ra rb acc
        else loop a (b+1) ra rb acc
      else acc
    else acc
termination_by _ a b ra rb _ => (ra.size - a, rb.size - b)

/-- Subtract the interval set `interval2` from `interval1`, asumes canonical ordering. -/
def difference [Ord α] [LT α] [LE α] [Bound α] [ToString α] [Inhabited α]
  [(a b : α) → Decidable (a ≤ b)] [(a b : α) → Decidable (a < b)]
    (interval1 interval2 : IntervalSet α) : IntervalSet α :=
  intersection interval1 (negate interval2)

/-- Union of interval sets, result set has canonical ordering. -/
def union [Ord α] [HSub α α UInt32] [LT α] [Bound α]
    [ToString α] [(a b : α) → Decidable (a < b)] [(a b : α) → Decidable (a = b)]
    (interval1 interval2 : IntervalSet α) : IntervalSet α :=
  ⟨interval1.ranges ++ interval2.ranges⟩ |> canonicalize

/-- Compute the symmetric difference (A⊖B = (A∪B)\(A∩B)) of the two sets,
    asumes canonical ordering. -/
def symmetric_difference [Ord α] [HSub α α UInt32] [LT α] [LE α] [Bound α] [ToString α] [Inhabited α]
  [(a b : α) → Decidable (a ≤ b)] [(a b : α) → Decidable (a < b)] [(a b : α) → Decidable (a = b)]
    (interval1 interval2 : IntervalSet α) : IntervalSet α :=
  let intervalI := intersection interval1 interval2
  let intervalU := union interval1 interval2
  difference intervalU intervalI
