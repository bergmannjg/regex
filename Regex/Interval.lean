import Init.Data.Ord
import Std.Data.Nat.Lemmas
import Std.Data.Fin.Lemmas
import Std.Data.Int.Lemmas
import Std.Data.List.Basic
import Regex.Utils
import Regex.Bound
import Regex.Data.Char.Basic

/-!
## IntervalSet

This file contains an implementation of interval sets (`IntervalSet`),
a sorted set of non-overlapping ranges (`Range`).
-/

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

/-- ranges `r1` and `r2` are non overlapping when they are sorted and
    they are not overlapping or adjacent -/
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

instance : HSub Char Char Nat where
  hSub c₁ c₂ := c₁.toNat - c₂.toNat

def negate (r1 r2 : Range Char) (h : nonOverlapping r1 r2) : Range Char :=
  ⟨Bound.increment r1.end, Bound.decrement r2.start, by
    unfold nonOverlapping at h
    unfold Bound.increment
    unfold Bound.decrement
    unfold instBoundCharInstOrdCharInstLEChar
    simp_all
    have h : 1 + r1.end.toNat < r2.start.toNat := by simp [Nat.add_lt_of_lt_sub h]
    simp [Bound.Char.incr_le_decr h]⟩

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

/-- an array of ranges is non overlapping when ranges are sorted
    and no ranges are overlapping or adjacent -/
def isNonOverlapping {α : Type u} [Ord α] [LT α] [LE α] [Bound α] [HSub α α Nat]
    (ranges: Array (Range α)) : Prop :=
  match ranges.data with
  | [] => true
  | [_] => true
  | head :: tail  => List.Chain (Range.nonOverlapping) head tail

theorem empty_isNonOverlapping {α : Type u} [Ord α] [LT α] [LE α] [Bound α] [HSub α α Nat]
    : isNonOverlapping (#[] : Array (Range α)) := by
  unfold isNonOverlapping
  split <;> simp_all

theorem single_isNonOverlapping (ranges : Array (Range Char)) (h : ranges.size = 1)
    : isNonOverlapping ranges  := by
  unfold isNonOverlapping
  split <;> try simp_all
  unfold Array.size at h
  unfold List.length at h
  split at h <;> try simp_all
  unfold List.length at h
  split at h <;> try simp_all

theorem push_isNonOverlapping (ranges : Array (Range Char)) (r : Range Char)
  (hp : ranges.pop? = some (last, rest))
  (hr : isNonOverlapping ranges) (hlr : Range.nonOverlapping last r)
    : isNonOverlapping (ranges.push r)  := by
  sorry

end Ranges

theorem Array.size_one (a : α) : (#[a] : Array α).size = 1 := rfl

/-- A sorted set of non-overlapping ranges. -/
structure IntervalSet (α : Type u) [Ord α] [LT α] [LE α] [Bound α] [HSub α α Nat]
    [(a b : α) → Decidable (a < b)] [(a b : α) → Decidable (a = b)] where
  ranges: Array (Range α)
  isNonOverlapping: Ranges.isNonOverlapping ranges
deriving Repr

instance : ToString $ IntervalSet Char where
  toString s := s!"{s.ranges}"

instance (α : Type u) [Ord α] [LT α] [LE α] [Bound α] [HSub α α Nat]
    [(a b : α) → Decidable (a < b)] [(a b : α) → Decidable (a = b)]
    : Inhabited $ IntervalSet α where
  default := ⟨#[], Ranges.empty_isNonOverlapping⟩

namespace Interval

def singleton (r : Range Char) : IntervalSet Char :=
  let arr := #[r]
  ⟨arr, by simp [Ranges.single_isNonOverlapping arr (Array.size_one r)]⟩

theorem pred_lt' {n m : Nat} (h : m < n) : Nat.pred n < n :=
  Nat.pred_lt (Nat.not_eq_zero_of_lt h)

/-- get predecessor of `i` in `Fin n`. -/
def Fin.pred (i : Fin n) (h : 0 < i.val) : Fin n :=
  ⟨i-1, by
    have h1 : i.val - 1 < i.val := pred_lt' h
    have h2 : i.val < n := i.isLt
    simp [Nat.lt_trans h1 h2]⟩

/-- Converts `ranges` into `IntervalSet` with canonical ordering.  -/
def canonicalize (ranges : Array (Range Char)) : IntervalSet Char :=
  let push (r : Range Char) (acc : IntervalSet Char) : IntervalSet Char :=
    match hp : acc.ranges.pop? with
    | some (last, rest) =>
      if hr : Range.nonOverlapping last r then -- todo: prove it
        let acc' := ⟨acc.ranges.push r,
              Ranges.push_isNonOverlapping acc.ranges r hp acc.isNonOverlapping hr⟩
        acc'
      else panic s!"overlapping {last} {r}"
    | none => singleton r

  let _ranges := Array.qsort ranges
                  (fun a b => a.start = b.start && a.end < b.end || a.start < b.start)
  let _ranges := Ranges.unique _ranges

  let init : Option (Range Char) × IntervalSet Char := (none, default)
  let (v, intervalSet) := _ranges |> Array.foldl (init := init) (fun (v, acc) r =>
    match v with
    | some l =>
      if h : (r.start.val.toNat - l.end.val.toNat) = 1 then  -- [a-bc-d] => [a-d]
          (some ⟨l.start, r.end, by
            have hx : l.end < r.start := by simp [Char.succ_lt h]
            have hy : l.end ≤ r.start := by simp [Char.lt_le hx]
            have hz : l.start ≤ r.start := by simp [Char.le_trans l.isLe hy]
            simp [Char.le_trans hz r.isLe]
        ⟩, acc)
      else if h: l.start = r.start then -- [a-ca-d] => [a-d]
        if l.end < r.end
        then (some ⟨l.start, r.end, by
            have hx : l.start ≤ r.start := by simp [Char.eq_le h]
            simp [Char.le_trans hx r.isLe]
          ⟩, acc)
        else (some l, acc) -- r.start = l.start ∧ r.end < l.end
      else if r.start < l.end then -- [a-cb-d] => [a-d]
        if r.end ≤ l.end -- [a-eb-d] => [a-e]
        then (some l, acc)
        else if h : l.start < r.start -- [a-cb-d] => [a-d]
        then (some ⟨l.start, r.end, by
            have hx : l.start ≤ r.start := by simp [Char.lt_le h]
            simp [Char.le_trans hx r.isLe]
          ⟩, acc)
        else (some r, acc) -- r.start <= l.start ∧  l.end < r.end
      else if l.end = r.start && r.start = r.end then (v, acc)
      else if h : l.end = r.start then -- [a-bb-c] => [a-c]
        let x : Range Char := ⟨l.start, r.end, by
          have hx : l.end ≤ r.start := by simp [Char.eq_le h]
          have hy : l.start ≤ r.start := by simp [Char.le_trans l.isLe hx]
          simp [Char.le_trans hy r.isLe]
        ⟩
        (some x, acc)
      else if r.start < l.start && l.end < r.end then (none, push r acc) -- [b-fa-g] => [a-g]
      else if l.end.val + 1 < r.start.val then (r, push l acc) -- [a-eg-h] => [a-eg-h]
      else (none, acc)
    | none => (some r, default))

  let intervalSet :=
    match v with
    | some v => push v intervalSet
    | none => intervalSet

  intervalSet

/-- Negate a interval set. -/
def negate (interval : IntervalSet Char) : IntervalSet Char :=
  if interval.ranges.size = 0
  then
    singleton ⟨(Bound.min_value : Char), Bound.max_value, Bound.min_value_le_max_value⟩
  else
    let ranges : Array (Range Char) :=
      Array.mapIdx interval.ranges  (fun i x => (i, x))
      |> Array.map (fun (i, y) =>
        if h : 0 < i.val
        then
          let j : Fin (Array.size interval.ranges) := Fin.pred i h
          let x := interval.ranges.get j
          -- todo: prove it using nonOverlapping property
          -- use Chain.chain_iff_get from mathlib
          Range.negate x y (by sorry)
        else
          if Bound.min_value < y.start
          then ⟨Bound.min_value, Bound.decrement y.start, by
              simp [Bound.min_value_le_decrement y.start]
            ⟩
          else y
        )
    let last : Array (Range Char) :=
      match interval.ranges.pop? with
      | some (x, _) =>
          if x.end < Bound.max_value
          then #[⟨Bound.increment x.end, Bound.max_value, by
              simp [Bound.increment_le_max_value x.end]
            ⟩]
          else #[]
      | none => #[]

    let ranges := ranges ++ last
    canonicalize ranges

/-- Intersection of interval sets -/
def intersection (interval1 interval2 : IntervalSet Char) : IntervalSet Char :=
  let ranges := intersection.loop 0 0 interval1.ranges interval2.ranges #[]
  canonicalize ranges
where
  loop (a b : Nat) (ra rb acc : Array $ Range Char) : Array $ Range Char :=
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

/-- Subtract the interval set `interval2` from `interval1`. -/
def difference (interval1 interval2 : IntervalSet Char) : IntervalSet Char :=
  intersection interval1 (negate interval2)

/-- Union of interval sets. -/
def union (interval1 interval2 : IntervalSet Char) : IntervalSet Char :=
  if interval1.ranges.size = 0 then interval2
  else if interval2.ranges.size = 0 then interval1
  else canonicalize (interval1.ranges ++ interval2.ranges)

/-- Compute the symmetric difference (A⊖B = (A∪B)\(A∩B)) of the two sets. -/
def symmetric_difference (interval1 interval2 : IntervalSet Char) : IntervalSet Char :=
  let intervalI := intersection interval1 interval2
  let intervalU := union interval1 interval2
  difference intervalU intervalI
