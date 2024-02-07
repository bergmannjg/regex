import Init.Data.Ord
import Regex.Utils
import Regex.Interval.Basic
import Regex.Interval.Lemmas

/-!
## IntervalSet

IntervalSet operations like `Interval.intersection`
-/

namespace Interval

def Acc.with_none (acc : Acc) (n : Range Char) (h : acc.next.isNone) : Acc :=
  {acc with next := n, nonOverlapping := nonOverlappingWithLast_of_none acc n h}

def Acc.with_next (acc : Acc) (n : Range Char) (h1 : is_start_eq acc.next n) : Acc :=
  {acc with next := n, nonOverlapping := nonOverlappingWithLast_of_val acc n h1}

def Acc.with_next_set (acc : Acc) (l r : Range Char) (h1 : Range.nonOverlapping l r)
  (h2 : acc.next = some l) : Acc :=
  match hm : acc.set.ranges.last? with
  | some _ =>
    have : Ranges.nonOverlapping (Array.push acc.set.ranges l) :=
              nonOverlapping_of_push acc l hm h2
    {acc with next := r,
              set := Acc.push acc l this,
              nonOverlapping := nonOverlappingWithLast_of_push acc h2 this h1}
  | none =>
    {acc with next := r, set := Interval.singleton l,
              nonOverlapping := nonOverlappingWithLast_of_singleton l r h1}

instance : Inhabited Acc :=
  ⟨⟨none, default, nonOverlappingWithLast_of_empty default none
                        (Array.default_size_zero default (by simp))⟩⟩

/-- Converts `ranges` into `IntervalSet` with canonical ordering.  -/
def canonicalize (ranges : Array (Range Char)) : IntervalSet Char :=
  let _ranges := Array.qsort ranges
                  (fun a b => a.start = b.start && a.end < b.end || a.start < b.start)
  let _ranges := Ranges.unique _ranges

  let init : Acc := default
  let acc := _ranges |> Array.foldl (init := init) (fun acc r =>
    match hm : acc.next with
    | some l =>
      if h1 : (r.start.toNat - l.end.toNat) = 1 then  -- [a-bc-d] => [a-d]
        let next : Range Char := ⟨l.start, r.end, by
            have hx : l.end < r.start := by simp [Char.succ_lt h1]
            have hy : l.end ≤ r.start := by simp [Char.lt_le hx]
            have hz : l.start ≤ r.start := by simp [Char.le_trans l.isLe hy]
            simp [Char.le_trans hz r.isLe]
        ⟩
        Acc.with_next acc next (is_start_eq_of_val acc.next next hm (by simp))
      else if h2 : l.start = r.start then -- [a-ca-d] => [a-d]
        if l.end < r.end
        then
          let next : Range Char := ⟨l.start, r.end, by
            have hx : l.start ≤ r.start := by simp [Char.eq_le h2]
            simp [Char.le_trans hx r.isLe]
          ⟩
          Acc.with_next acc next (is_start_eq_of_val acc.next next hm (by simp))
        else acc -- r.start = l.start ∧ r.end < l.end
      else if h2 : r.start < l.end then -- [a-cb-d] => [a-d]
        if r.end ≤ l.end -- [a-eb-d] => [a-e]
        then acc
        else if h : l.start < r.start -- [a-cb-d] => [a-d]
        then
          let next : Range Char := ⟨l.start, r.end, by
            have hx : l.start ≤ r.start := by simp [Char.lt_le h]
            simp [Char.le_trans hx r.isLe]
          ⟩
          Acc.with_next acc next (is_start_eq_of_val acc.next next hm (by simp))
        else -- ¬l.start = r.start ∧ ¬l.start < r.start => r.start < l.start
          panic s!"internal error: array not sorted at {l} {r}"
      else if l.end = r.start && r.start = r.end then acc
      else if h3 : l.end = r.start then -- [a-bb-c] => [a-c]
        let next : Range Char := ⟨l.start, r.end, by
          have hx : l.end ≤ r.start := by simp [Char.eq_le h3]
          have hy : l.start ≤ r.start := by simp [Char.le_trans l.isLe hx]
          simp [Char.le_trans hy r.isLe]
        ⟩
        Acc.with_next acc next (is_start_eq_of_val acc.next next hm (by simp))
      else if r.start < l.start then panic s!"internal error: array not sorted at {l} {r}"
      else -- [a-eg-h] => [a-eg-h]
        have : Range.nonOverlapping l r := isNonOverlapping l r h1 h2 h3
        Acc.with_next_set acc l r this hm
    | none => Acc.with_none acc r (by unfold Option.isNone; simp_all [hm]))

  let intervalSet :=
    match hm : acc.next with
    | some v =>
        match hn : acc.set.ranges.last? with
        | some _ => Acc.push acc v (nonOverlapping_of_push acc v hn (by simp[hm]; simp_all))
        | none => Interval.singleton v
    | none => acc.set

  intervalSet

/-- Negate a interval set wrt the corresponding `Bound` . -/
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
          let x := interval.ranges.get ⟨i - 1, Fin.pred h⟩
          let y := interval.ranges.get i
          Range.negate x y
            (Interval.nonOverlapping_of_pred interval.ranges i x y h
                        (by simp) (by simp) interval.isNonOverlapping)
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
