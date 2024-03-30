import Init.Data.Ord
import Regex.Utils
import Regex.Interval.Basic
import Regex.Interval.Lemmas

/-!
## Interval Set

IntervalSet operations like `IntervalSet.canonicalize` or `IntervalSet.intersection`
-/

namespace IntervalSet

def Acc.with_none (acc : Interval.Acc) (n : NonemptyInterval Char) (h : acc.next.isNone)
    : Interval.Acc :=
  {acc with next := n, nonOverlapping := Intervals.nonOverlappingWithLast_of_none acc n h}

def Acc.with_next (acc : Interval.Acc) (n : NonemptyInterval Char)
  (h1 : Interval.is_start_eq acc.next n) : Interval.Acc :=
  {acc with next := n, nonOverlapping := Intervals.nonOverlappingWithLast_of_val acc n h1}

def Acc.with_next_set (acc : Interval.Acc) (l r : NonemptyInterval Char)
  (h1 : Interval.nonOverlapping l r) (h2 : acc.next = some l) : Interval.Acc :=
  match hm : acc.set.intervals.last? with
  | some _ =>
    have : Intervals.nonOverlapping (Array.push acc.set.intervals l) :=
              Intervals.nonOverlapping_of_push acc l hm h2
    {acc with next := r,
              set := Interval.Acc.push acc l this,
              nonOverlapping := Intervals.nonOverlappingWithLast_of_push acc h2 this h1}
  | none =>
    {acc with next := r, set := Intervals.singleton l,
              nonOverlapping := Intervals.nonOverlappingWithLast_of_singleton l r h1}

instance : Inhabited Interval.Acc :=
  ⟨⟨none, default, Intervals.nonOverlappingWithLast_of_empty default none
                        (Array.default_size_zero default (by simp))⟩⟩

/-- Converts `ranges` into `IntervalSet` with canonical ordering.  -/
def canonicalize (ranges : Array (NonemptyInterval Char)) : IntervalSet Char :=
  let _ranges := Array.qsort ranges
                  (fun a b => a.fst = b.fst && a.snd < b.snd || a.fst < b.fst)
  let _ranges := Intervals.unique _ranges

  let init : Interval.Acc := default
  let acc := _ranges |> Array.foldl (init := init) (fun acc r =>
    match hm : acc.next with
    | some l =>
      if h1 : (r.fst.toNat - l.snd.toNat) = 1 then  -- [a-bc-d] => [a-d]
        let next : NonemptyInterval Char := ⟨⟨l.fst, r.snd⟩, by
            have hx : l.snd < r.fst := by simp [Char.succ_lt h1]
            have hy : l.snd ≤ r.fst := by simp [Char.lt_le hx]
            have hz : l.fst ≤ r.fst := by simp [Char.le_trans l.fst_le_snd hy]
            simp [Char.le_trans hz r.fst_le_snd]
        ⟩
        Acc.with_next acc next (Intervals.is_start_eq_of_val acc.next next hm (by simp))
      else if h2 : l.fst = r.fst then -- [a-ca-d] => [a-d]
        if l.snd < r.snd
        then
          let next : NonemptyInterval Char := ⟨⟨l.fst, r.snd⟩, by
            have hx : l.fst ≤ r.fst := by simp [Char.eq_le h2]
            simp [Char.le_trans hx r.fst_le_snd]
          ⟩
          Acc.with_next acc next (Intervals.is_start_eq_of_val acc.next next hm (by simp))
        else acc -- r.fst = l.fst ∧ r.snd < l.snd
      else if h2 : r.fst < l.snd then -- [a-cb-d] => [a-d]
        if r.snd ≤ l.snd -- [a-eb-d] => [a-e]
        then acc
        else if h : l.fst < r.fst -- [a-cb-d] => [a-d]
        then
          let next : NonemptyInterval Char := ⟨⟨l.fst, r.snd⟩, by
            have hx : l.fst ≤ r.fst := by simp [Char.lt_le h]
            simp [Char.le_trans hx r.fst_le_snd]
          ⟩
          Acc.with_next acc next (Intervals.is_start_eq_of_val acc.next next hm (by simp))
        else -- ¬l.fst = r.fst ∧ ¬l.fst < r.fst => r.fst < l.fst
          panic s!"internal error: array not sorted at {l} {r}"
      else if l.snd = r.fst && r.fst = r.snd then acc
      else if h3 : l.snd = r.fst then -- [a-bb-c] => [a-c]
        let next : NonemptyInterval Char := ⟨⟨l.fst, r.snd⟩, by
          have hx : l.snd ≤ r.fst := by simp [Char.eq_le h3]
          have hy : l.fst ≤ r.fst := by simp [Char.le_trans l.fst_le_snd hx]
          simp [Char.le_trans hy r.fst_le_snd]
        ⟩
        Acc.with_next acc next (Intervals.is_start_eq_of_val acc.next next hm (by simp))
      else if r.fst < l.fst then panic s!"internal error: array not sorted at {l} {r}"
      else -- [a-eg-h] => [a-eg-h]
        have : Interval.nonOverlapping l r := Intervals.isNonOverlapping l r h1 h2 h3
        Acc.with_next_set acc l r this hm
    | none => Acc.with_none acc r (by unfold Option.isNone; simp_all [hm]))

  let intervalSet :=
    match hm : acc.next with
    | some v =>
        match hn : acc.set.intervals.last? with
        | some _ => Interval.Acc.push acc v
            (Intervals.nonOverlapping_of_push acc v hn (by simp[hm]))
        | none => Intervals.singleton v
    | none => acc.set

  intervalSet

/-- Negate a interval set wrt the corresponding BoundedOrder `instBoundedOrderCharInstLEChar` . -/
def negate (interval : IntervalSet Char) : IntervalSet Char :=
  if interval.intervals.size = 0
  then
    Intervals.singleton ⟨⟨Bot.bot, Top.top⟩, OrderBot.bot_le Top.top⟩
  else
    let ranges : Array (NonemptyInterval Char) :=
      Array.mapIdx interval.intervals  (fun i x => (i, x))
      |> Array.map (fun (i, y) =>
        if h : 0 < i.val
        then
          let x := interval.intervals.get ⟨i - 1, Intervals.Fin.pred h⟩
          let y : NonemptyInterval Char := interval.intervals.get i
          Interval.between x y
            (Intervals.nonOverlapping_of_pred interval.intervals
              i
              (interval.intervals.get ⟨i - 1, Intervals.Fin.pred h⟩)
              (interval.intervals.get i) h
              (by simp_all) (by simp_all) interval.isNonOverlapping)
        else
          if Bot.bot < y.fst
          then ⟨⟨ Bot.bot, Char.decrement y.fst⟩ , by simp⟩
          else y
        )
    let last : Array (NonemptyInterval Char) :=
      match interval.intervals.pop? with
      | some (x, _) =>
          if x.snd <Top.top
          then #[⟨⟨Char.increment x.snd, Top.top⟩, by simp⟩]
          else #[]
      | none => #[]

    let ranges := ranges ++ last
    canonicalize ranges

/-- Intersection of interval sets -/
def intersection (interval1 interval2 : IntervalSet Char) : IntervalSet Char :=
  let ranges := intersection.loop 0 0 interval1.intervals interval2.intervals #[]
  canonicalize ranges
where
  loop (a b : Nat) (ra rb acc : Array $ NonemptyInterval Char) : Array $ NonemptyInterval Char :=
    if h₁ : a < ra.size then
      if h₂ : b < rb.size then
        let acc :=
          match Interval.intersection (ra.get ⟨a, h₁⟩) (rb.get ⟨b, h₂⟩) with
          | some r => acc.push r
          | none => acc

        if (ra.get ⟨a, h₁⟩).snd < (rb.get ⟨b, h₂⟩).snd
        then loop (a+1) b ra rb acc
        else loop a (b+1) ra rb acc
      else acc
    else acc
  termination_by (ra.size - a, rb.size - b)

/-- Subtract the interval set `interval2` from `interval1`. -/
def difference (interval1 interval2 : IntervalSet Char) : IntervalSet Char :=
  intersection interval1 (negate interval2)

/-- Union of interval sets. -/
def union (interval1 interval2 : IntervalSet Char) : IntervalSet Char :=
  if interval1.intervals.size = 0 then interval2
  else if interval2.intervals.size = 0 then interval1
  else canonicalize (interval1.intervals ++ interval2.intervals)

/-- Compute the symmetric difference (A⊖B = (A∪B)\(A∩B)) of the two sets. -/
def symmetric_difference (interval1 interval2 : IntervalSet Char) : IntervalSet Char :=
  let intervalI := intersection interval1 interval2
  let intervalU := union interval1 interval2
  difference intervalU intervalI
