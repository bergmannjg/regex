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

instance : ToString $ Range Char where
  toString s := s!"{s.start} {s.end}"

/-- A sorted set of non-overlapping ranges. -/
structure IntervalSet (α : Type u) [Ord α] [LT α] [Bound α] where
  ranges: Array (Range α)

namespace Interval

theorem pred_lt' {n m : Nat} (h : m < n) : Nat.pred n < n :=
  Nat.pred_lt (Nat.not_eq_zero_of_lt h)

/-- get predecessor of `i` in `Fin n`. -/
def Fin.pred (i : Fin n) (h : 0 < i.val) : Fin n :=
  ⟨i-1, by
    have h1 : i.val - 1 < i.val := pred_lt' h
    have h2 : i.val < n := i.isLt
    simp [Nat.lt_trans h1 h2]⟩

/-- Negate this interval set. -/
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

/-- Converts this set into a canonical ordering. -/
def canonicalize [Ord α] [HSub α α UInt32] [LT α] [Bound α] [ToString α] [(a b : α) → Decidable (a < b)]
     [(a b : α) → Decidable (a = b)]
    (interval : IntervalSet α) : IntervalSet α :=
  let ranges := Array.qsort interval.ranges (fun a b => a.start < b.end)

  let init : Option (Range α) × Array (Range α) := (none, #[])
  let (v, ranges) := ranges |> Array.foldl (init := init) (fun (v, acc) r =>
    match v with
    | some v =>
      if (r.start - v.end).toNat = 1 then (some ⟨v.start, r.end⟩, acc) -- [a-bc-d] => [a-d]
      else if v.end < r.start then (r, acc.push v) -- [a-fg-h] => [a-fg-h]
      else if v.end = r.start then (none, acc.push ⟨v.start, r.end⟩) -- [a-bb-c] => [a-c]
      else if v.end < r.end then (none, acc.push r) -- [a-fb-c] => [a-f]
      else (some r, acc.push v)
    | none => (some r, acc))

  let ranges :=
    match v with
    | some v => ranges.push v
    | none => ranges

  IntervalSet.mk (Array.qsort ranges (fun a b => a.start < b.end))
