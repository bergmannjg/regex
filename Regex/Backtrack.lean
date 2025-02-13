import Regex.Syntax.Hir
import Regex.Nfa
import Regex.Compiler
import Regex.Utils
import Regex.Data.Array.Basic
import Lean.Util
import Init.Core
import Batteries.Data.Nat.Lemmas
import Batteries.Tactic.Exact

/-!
## BoundedBacktracker

An NFA backed bounded backtracker for executing regex searches with capturing
groups (`BoundedBacktracker.slots`).

This regex engine only implements leftmost-first match semantics
and only supports leftmost searches. By design, this backtracking regex engine is bounded.
This bound is implemented by not visiting any combination of NFA state ID and position
in a haystack more than once.

All searches execute in linear time with respect to the size of the regular expression
and search text.
-/
namespace BoundedBacktracker

open NFA

namespace Array.Ref

/-- make reference of array -/
def mkRef {α β : Type} [Inhabited β] (arr : Array α) : ST.Ref β (Array α) :=
  let st : ST β (ST.Ref β (Array α)) := ST.Prim.mkRef arr
  match st default with | EStateM.Result.ok r _ => r

/-- get array of reference -/
def getRefValue {α β : Type} [Inhabited β] (ref : ST.Ref β (Array α)) : (Array α) :=
  let st := ST.Prim.Ref.get ref
  match st default with | EStateM.Result.ok r _ => r

/-- modify array, try to perform the update destructively -/
def modifyRefValue {α β : Type} [Inhabited β] [DecidableEq β]
    (ref : ST.Ref β (Array α)) (index : Nat) (value : α)
    : ST.Ref β (Array α)  :=
  let st := ST.Prim.Ref.modify ref (fun arr =>
    let arr := dbgTraceIfShared "array" arr
    if h : index < arr.size
    then arr.set index value h
    else arr)

  match st default with | EStateM.Result.ok _ n => if n = default then ref else mkRef #[]

instance {α β : Type} [Inhabited β] : Inhabited (ST.Ref β (Array α)) where
  default := mkRef #[]

end Array.Ref

@[simp] def CharPos.posInRange (s : Substring) (pos : String.Pos) :=
  s.startPos ≤ pos ∧ pos ≤ s.stopPos

/-- Char position in a substring-/
structure CharPos (s : Substring) where
  /-- current position -/
  pos : String.Pos := ⟨0⟩
  /-- char at current position -/
  curr? : Option Char := none
  /-- char at previous position -/
  prev? : Option Char := none
  /-- `pos` is in range of substring `s` -/
  isPosInRange : CharPos.posInRange s pos

abbrev CharPos.PosInRange s := { pos : String.Pos // CharPos.posInRange s pos }

instance : Inhabited (CharPos default) := ⟨default, none, none, by simp; decide⟩

instance : ToString (CharPos s) where
  toString s := s!"{s.pos} {s.curr?} {s.prev?}"

namespace CharPos

def toSlotEntry («at»: CharPos input) : CharPos.PosInRange input :=
  ⟨«at».pos, «at».isPosInRange⟩

def get? (s : Substring) («at» : String.Pos) : Option Char :=
  if «at» < s.stopPos then s.get «at» else none

/-- create a CharPos from `s` and position `«at»` -/
def create (s : Substring) («at» : String.Pos) (h : s.startPos ≤ «at» ∧ «at» ≤ s.stopPos )
    : CharPos s :=
  let prev? := if «at» = 0 then none else get? s (s.prev «at»)
  ⟨«at», get? s «at», prev?, h⟩

def prevOf (offset : Nat) (cp : CharPos s) : Option (CharPos s) :=
  if offset ≤ cp.pos.byteIdx then
    let pos := s.prevn offset cp.pos
    if h : s.startPos ≤ pos ∧ pos ≤ s.stopPos
    then some (create s pos h)
    else none
  else none

/-- to next position CharPos of `cp` -/
def next (cp : CharPos s) : CharPos s :=
  if cp.pos >= s.stopPos then cp
  else
    match cp.curr? with
    | some c =>
      let nextPos : String.Pos := ⟨cp.pos.byteIdx + c.utf8Size⟩
      if h : s.startPos ≤ nextPos ∧ nextPos ≤ s.stopPos
      then {cp with pos := nextPos, prev? := cp.curr?, curr? := get? s nextPos,
                    isPosInRange := h}
      else cp
    | none => cp

/-- is CharPos at start position -/
def atStart (cp : CharPos s) : Bool :=
  cp.pos = s.startPos

/-- is CharPos at stop position -/
def atStop (cp : CharPos s) : Bool :=
  cp.pos = s.stopPos

end CharPos

/-- Represents a stack frame on the heap while doing backtracking. -/
inductive Frame (n : Nat) (s : Substring) where
  /-- Look for a match starting at `sid` and the given position in the haystack. -/
  | Step (sid: Fin n) («at»: CharPos s) : Frame n s
  /-- Reset the given `slot` to the given `offset` (which might be `None`). -/
  | RestoreCapture (role : Capture.Role) (slot: Nat)
      (offset: Nat × Nat × Option (CharPos.PosInRange s)) : Frame n s

instance : ToString $ Frame n s where
  toString frame :=
    match frame with
    | .Step sid «at» => s!"Step({sid}, {«at».pos})"
    | .RestoreCapture role _ offset => s!"Restore({role}, slot: {offset})"

/-- A representation of "half" of a match reported by a DFA. -/
structure HalfMatch where
    /-- The pattern ID. -/
    pattern: PatternID
    /-- The offset of the match. -/
    offset: String.Pos

instance : Inhabited HalfMatch := ⟨0, 0⟩

instance : ToString HalfMatch where
  toString a := s!"pattern {a.pattern}, offset {a.offset}"

private def compare (a : Fin n × String.Pos) (b : Fin n × String.Pos) : Ordering :=
  if a.1 < b.1 then Ordering.lt
  else if a.1 = b.1 && a.2 = b.2 then Ordering.eq
  else Ordering.gt

/-- The stack of frames  -/
abbrev Stack n s := List $ Frame n s

namespace Stack

/-- Push frame to stack  -/
@[inline] def push (stack : Stack n s) (v : Frame n s) : Stack n s :=
  v :: stack

/-- pop head frame from stack  -/
@[inline] def pop? (stack : Stack n s) : Option (Frame n s × Stack n s) :=
  match stack with
  | [] => none
  | head :: tail => (head, tail)

theorem pop?_some_lt (s : Stack n s) (h : pop? s = some (a, s1)) : s1.length < s.length := by
  have : s = a :: s1 := by unfold pop? at h; split at h <;> simp_all
  rw [this]
  exact Nat.lt_add_one (List.length s1)

/-- append stacks -/
@[inline] def append (stack1 stack2 : Stack n s) : Stack n s :=
  match stack2 with
  | v1 :: v2 :: [] => v2 :: v1 :: stack1
  | _ => List.append (stack2.reverse) stack1

@[inline] def toStack (arr : Array $ Frame n s) : Stack n s :=
  arr |> Array.toList

end Stack

instance : Inhabited $ Stack default default := ⟨[]⟩

/-- The encoded set of (Fin n, HaystackOffset) pairs that have been visited
    by the backtracker within a single search. Optimization: encode as bits -/
abbrev Visited := Array UInt8

/-- State of the backtracking search -/
@[ext] structure SearchState (n : Nat) (input : Substring) where
  /-- Stack used on the heap for doing backtracking -/
  stack: Stack n input
  /-- The encoded set of (Fin n, HaystackOffset) pairs that have been visited
    by the backtracker within a single search. -/
  visited : ST.Ref Nat Visited
  /-- count of pairs that have been visited -/
  countVisited : Nat
  /-- current state -/
  sid: Fin n
  /-- position in input string -/
  «at»: CharPos input
  /-- slots, positions of captures in `input` -/
  slots: Array (Nat × Nat × (Option (CharPos.PosInRange input)))
  /-- recent captures of capture groups -/
  recentCaptures: Array (Option (String.Pos × String.Pos))
  /-- is logging enabled -/
  logEnabled : Bool
  /-- log msgs -/
  msgs: Array String
  /-- HalfMatch -/
  halfMatch: Option HalfMatch
  /-- count of backtracks -/
  backtracks : Nat

namespace SearchState

/-- create the SearchState from an NFA -/
def fromNfa (nfa : Checked.NFA) (input : Substring) («at» : String.Pos) (logEnabled : Bool)
  (h : 0 < nfa.n ∧ input.startPos ≤ «at» ∧ «at» ≤ input.stopPos )
    : SearchState nfa.n input :=
  let slotIdxs : Array (Nat × Nat) :=
    nfa.states
    |> Array.filterMap (fun s =>
        match s with
        | Checked.State.Capture _ _ _ g s => some (s, g)
        | _ => none)
  let sorted := Array.qsort slotIdxs (fun (a, _) (b, _) => a < b) |> Array.unique
  let slots : Array (Nat × Nat × (Option (CharPos.PosInRange input))) :=
    sorted |> Array.map (fun (s, g) => (s, g, none))

  let recentCaptures : Array $ Option (String.Pos × String.Pos) :=
    slots |> Array.map (fun (_, g, _) => g) |> Array.unique |> Array.map (fun _ => none)

  {
    stack := default
    visited := Array.Ref.mkRef <|
      Array.mkArray ((nfa.states.size + 1) * (input.stopPos.byteIdx - input.startPos.byteIdx +1)) 0
    countVisited := 0
    sid := ⟨0, h.left⟩
    «at» := CharPos.create input «at» h.right
    slots := slots
    recentCaptures := recentCaptures
    logEnabled := logEnabled
    msgs := #[]
    halfMatch := none
    backtracks := 0
  }

end SearchState

instance : Nonempty Visited := ⟨#[]⟩

namespace Visited

/-- get encoded index of Fin n and CharPos in visited array -/
def index (sid : Fin n) (cp : CharPos s) : Nat :=
  sid * (s.stopPos.byteIdx - s.startPos.byteIdx + 1)
  + cp.pos.byteIdx - s.startPos.byteIdx

theorem eq_of_linear_eq {a1 b1 a2 b2 x : Nat} (hb1 : b1 < x) (hb2 : b2 < x)
  (h : a1 * x + b1 = a2 * x + b2) : a1 = a2 ∧ b1 = b2 := by
  if ha : a1 < a2
  then
    have ⟨k, hk⟩ : ∃ k, 0 < k ∧ a1 + k = a2 := by
      have ⟨k', hk⟩ := Nat.exists_eq_add_of_lt ha
      exact ⟨k' + 1, by omega⟩
    rw [← hk.right] at h
    have : a1 * x + b1 = a1 * x + k * x + b2 := by
      have := Nat.mul_add x a1 k
      rw [Nat.mul_comm] at this
      rw [this] at h
      rw [@Nat.mul_comm x a1, @Nat.mul_comm x k] at h
      exact h
    have : b1 = k * x + b2 := by omega
    have : ¬ b1 < x := by
      have : k * x ≤ b1 := by omega
      have : x ≤ k * x := by exact Nat.le_mul_of_pos_left x hk.left
      omega
    contradiction
  else if ha : a2 < a1
  then
    have ⟨k, hk⟩ : ∃ k, 0 < k ∧ a2 + k = a1 := by
      have ⟨k', hk⟩ := Nat.exists_eq_add_of_lt ha
      exact ⟨k' + 1, by omega⟩
    rw [← hk.right] at h
    have : a2 * x + k * x + b1 = a2 * x + b2 := by
      have := Nat.mul_add x a2 k
      rw [Nat.mul_comm] at this
      rw [this] at h
      rw [@Nat.mul_comm x a2, @Nat.mul_comm x k] at h
      exact h
    have : k * x + b1 = b2 := by omega
    have : ¬ b2 < x := by
      have : k * x ≤ b2 := by omega
      have : x ≤ k * x := by exact Nat.le_mul_of_pos_left x hk.left
      omega
    contradiction
  else
    have : a1 = a2 := by omega
    rw [this] at h
    omega

/-- `index` is injective. -/
theorem index_injective (sid1 sid2 : Fin n) (cp1 cp2 : CharPos s)
  (heq : index sid1 cp1 = index sid2 cp2)
    : sid1.val = sid2.val ∧ cp1.pos.byteIdx = cp2.pos.byteIdx := by
  unfold index at heq

  have hp1 := cp1.isPosInRange
  have hp2 := cp2.isPosInRange
  have : s.startPos.byteIdx ≤ s.stopPos.byteIdx := Nat.le_trans hp1.left hp1.right
  have : s.startPos.byteIdx ≤ s.stopPos.byteIdx := Nat.le_trans hp2.left hp2.right
  have : s.startPos.byteIdx ≤ cp1.pos.byteIdx := hp1.left
  have : s.startPos.byteIdx ≤ cp2.pos.byteIdx := hp2.left
  generalize hx : (s.stopPos.byteIdx - s.startPos.byteIdx + 1) = x at heq
  have hlt1 : cp1.pos.byteIdx - s.startPos.byteIdx < x := by
    simp [← hx]
    suffices cp1.pos.byteIdx - s.startPos.byteIdx
             ≤ s.stopPos.byteIdx - s.startPos.byteIdx by
      simp [Nat.lt_add_one_of_le this]
    exact Nat.sub_le_sub_right hp1.right s.startPos.byteIdx
  have hlt2 : cp2.pos.byteIdx - s.startPos.byteIdx < x := by
    simp [← hx]
    suffices cp2.pos.byteIdx - s.startPos.byteIdx
             ≤ s.stopPos.byteIdx - s.startPos.byteIdx by
      simp [Nat.lt_add_one_of_le this]
    exact Nat.sub_le_sub_right hp2.right s.startPos.byteIdx
  have h : sid1.val * x + (cp1.pos.byteIdx - s.startPos.byteIdx)
           = sid2.val * x + (cp2.pos.byteIdx - s.startPos.byteIdx) := by omega
  have := @eq_of_linear_eq sid1.val (cp1.pos.byteIdx - s.startPos.byteIdx)
            sid2.val (cp2.pos.byteIdx - s.startPos.byteIdx) x
            hlt1 hlt2 h
  omega

private def getRefValue (ref : ST.Ref Nat Visited) : Visited :=
  Array.Ref.getRefValue ref

private def modifyRefValue (ref : ST.Ref Nat Visited) (index : Nat) (value : UInt8)
    : ST.Ref Nat Visited :=
  Array.Ref.modifyRefValue ref index value

/-- Check if current Fin n and CharPos in SearchState is already visited.
    If not visited mark pair as visited. -/
def checkVisited (state : SearchState n s) : Bool × SearchState n s :=
  let visited := Visited.getRefValue state.visited
  let index := Visited.index state.sid state.at
  if h : index < visited.size then
    if visited.get index h != 0 then (true, state)
    else
      (false, {state with visited := Visited.modifyRefValue state.visited index 1})
  else (true, state)

/-- Check if current Fin n and CharPos in SearchState is already visited.
    If not visited mark pair as visited. -/
def checkVisited' (state : SearchState n s) : Bool × SearchState n s :=
  let (f, s) := checkVisited state
  if f then (true, state)
  else (false, {s with countVisited := state.countVisited + 1})

theorem checkVisited'_false_lt (s : SearchState n input) (h : checkVisited' s = (false, s1))
    : s.countVisited < s1.countVisited := by
  unfold checkVisited' at h
  split at h
  split at h <;> simp_all
  have hx : s.countVisited + 1 ≤ s1.countVisited := by
    simp [SearchState.ext_iff] at h
    simp_all
  simp [Nat.lt_of_succ_le hx]

theorem checkVisited'_true_eq (s : SearchState n input) (h : checkVisited' s = (true, s1))
    : s.countVisited = s1.countVisited ∧ s.stack.length = s1.stack.length := by
  unfold checkVisited' at h
  split at h
  split at h <;> simp_all

end Visited

/-- build pairs of subsequent slots -/
private def toPairs (slots : Array (Nat × Nat × Option (CharPos.PosInRange s)))
    : Array (Option ((CharPos.PosInRange s) × (CharPos.PosInRange s))) :=
  if slots.size % 2 = 0
  then
    let arr : Array (Option ((CharPos.PosInRange s) × (CharPos.PosInRange s))) :=
        slots.foldl (init := #[])
          fun acc (i, _) =>
            if i % 2 = 0 then acc
            else
              match slots.get? (i - 1), slots.get? (i) with
              | some (_, _, some v0), some (_, _, some v1) => acc.push (some (v0,v1))
              | some (_, _, none), some (_, _, none) => acc.push none
              | _, _ => acc
    arr
  else #[]

/-- add a msg to the SearchState while doing backtracking.  -/
@[inline] private def withMsg (msg : Unit -> String) (state : SearchState n s) : SearchState n s :=
  if state.logEnabled then { state with msgs := state.msgs.push s!"{msg ()}"}
  else state

theorem withMsg_eq {nfa : Checked.NFA} {s s1 : SearchState nfa.n input} {msg : Unit -> String}
  (h : withMsg  msg s = s1) : s.countVisited = s1.countVisited ∧ s.stack = s1.stack := by
  unfold withMsg at h
  split at h <;> try simp_all
  simp [SearchState.ext_iff] at h
  simp_all

private def encodeChar? (c: Option Char) : String :=
  match c with
  | some curr => UInt32.intAsString curr.val
  | none => "none"

/-- Returns true when [`Look::WordUnicode`] is satisfied `at` the given position in `haystack`. -/
@[inline] private def is_word_unicode (state : SearchState n s) : Bool :=
  let word_before :=
    if state.at.atStart then false
    else state.at.prev?.any Unicode.is_word_char
  let word_after :=
    if state.at.atStop then false
    else state.at.curr?.any Unicode.is_word_char
  word_before != word_after

/-- Returns true when [`Look::WordUnicodeNegate`] is satisfied `at` the
    given position in `haystack`. -/
@[inline] private def is_word_unicode_negate (state : SearchState n s) : Bool :=
  let word_before :=
    if state.at.atStart then false
    else state.at.prev?.any Unicode.is_word_char
  let word_after :=
    if state.at.atStop then false
    else state.at.curr?.any Unicode.is_word_char
  word_before = word_after

/-- Returns true when [`Look::WordStartUnicode`] is satisfied `at` the given position
    in `haystack`. -/
@[inline] private def is_word_start_unicode (state : SearchState n s) : Bool :=
  let word_before :=
    if state.at.atStart then false
    else state.at.prev?.any Unicode.is_word_char
  let word_after :=
    if state.at.atStop then false
    else state.at.curr?.any Unicode.is_word_char
  !word_before && word_after

/-- Returns true when [`Look::WordEndUnicode`] is satisfied `at` the given position
    in `haystack`. -/
@[inline] private def is_word_end_unicode (state : SearchState n s) : Bool :=
  let word_before :=
    if state.at.atStart then false
    else state.at.prev?.any Unicode.is_word_char
  let word_after :=
    if state.at.atStop then false
    else state.at.curr?.any Unicode.is_word_char
  word_before && !word_after

/-- Returns true when [`Look::WordStartHalfUnicode`] is satisfied `at` the given position
    in `haystack`. -/
@[inline] private def is_word_start_half_unicode (state : SearchState n s) : Bool :=
  let word_before :=
    if state.at.atStart then false
    else state.at.prev?.any Unicode.is_word_char
  !word_before

/-- Returns true when [`Look::WordEndHalfUnicode`] is satisfied `at` the given position
    in `haystack`. -/
@[inline] private def is_word_end_half_unicode (state : SearchState n s) : Bool :=
  let word_after :=
    if state.at.atStop then false
    else state.at.curr?.any Unicode.is_word_char
  !word_after

@[inline] private def step_empty (next : Fin n) (state : SearchState n s) : SearchState n s :=
  withMsg (fun _ => s!"{state.sid}: Empty -> {next}") {state with sid := next}

@[inline] private def step_next_char (offset : Nat) (next : Fin n) (state : SearchState n s)
    : SearchState n s :=
  match state.at.prevOf offset with
  | some pos =>
    withMsg (fun _ => s!"{state.sid}: NextChar offset {offset} to charpos {pos} -> {next}")
                      {state with sid := next, «at» := pos}
  | none =>
    withMsg (fun _ => s!"{state.sid}: NextChar offset {offset} failed at charpos {state.at}") state

@[inline] private def step_fail (state : SearchState n s) : SearchState n s :=
  withMsg (fun _ => s!"{state.sid}: Fail") state

/-- eat frames until State `sid` found -/
@[inline] private def step_eat_until (sid next : Fin n) (state : SearchState n s) : SearchState n s :=
  let stack :=
    state.stack
    |> List.dropWhile (fun s => match s with | .Step f' _ => sid != f' | _ => true)

  match stack with
  |  .Step _ _ :: stack' =>
    withMsg (fun _ => s!"{state.sid}: EatUntil {sid} stack {stack'} => {next}")
                      {state with stack := stack', sid := next }
  | _ =>
    withMsg (fun _ => s!"{state.sid}: EatUntil failed ") state

/-- eat frames inclusive last occurunce of State `sid`  -/
@[inline] private def step_eat_to_last (sid next : Fin n) (state : SearchState n s) : SearchState n s :=
  let index := state.stack
    |> List.reverse
    |> List.findIdx (fun s => match s with | .Step f' _ => sid = f' | _ => false)

  if index < state.stack.length then
    let index := state.stack.length -index
    let stack := state.stack |> List.drop index

    withMsg (fun _ => s!"{state.sid}: EatToLast {sid} stack {stack} => {next}")
                      {state with stack := stack, sid := next }
  else withMsg (fun _ => s!"{state.sid}: EatToLast {sid} stack {state.stack} => {next}")
                         {state with sid := next }
    --withMsg (fun _ => s!"{state.sid}: EatToLast failed ") state

@[inline] private def step_eat (mode : Checked.EatMode n) (next : Fin n) (state : SearchState n s)
    : SearchState n s :=
  match mode with
  | .Until sid => step_eat_until sid next state
  | .ToLast sid => step_eat_to_last sid next state

@[inline] private def step_change_frame_step (f t : Fin n) (state : SearchState n s) : SearchState n s :=
  let cond := (fun (s : Frame n s) => match s with | .Step f' _ => f != f' | _ => true)
  let stackBeforeSid := state.stack |> List.takeWhile cond

  let slots : Array (Nat × Nat × (Option (CharPos.PosInRange s))) :=
    stackBeforeSid |> List.foldl (fun slots frame =>
        match frame with
        | .RestoreCapture _ slot v =>
          if h : slot < slots.size then slots.set slot v h else slots
        | _ => slots) state.slots

  let stack := state.stack |> List.dropWhile cond
  match stack with
  |  .Step _ «at» :: stack' =>
    let stack := Frame.Step t «at» :: stack'
    withMsg (fun _ => s!"{state.sid}: ChangeFrameStep stack {stack} slots {slots}")
                      {state with stack := stack, slots := slots}
  | _ =>
    withMsg (fun _ => s!"{state.sid}: ChangeFrameStep failed ") state

@[inline] private def step_remove_frame_step (sid : Fin n) (state : SearchState n s) : SearchState n s :=
  let cond := (fun (s : Frame n s) => match s with | .Step f' _ => sid != f' | _ => true)
  let stackBeforeSid := state.stack |> List.takeWhile cond

  let slots : Array (Nat × Nat × (Option { pos // CharPos.posInRange s pos })) :=
    stackBeforeSid |> List.foldl (fun slots frame =>
        match frame with
        | .RestoreCapture _ slot v =>
          if h : slot < slots.size then slots.set slot v h else slots
        | _ => slots) state.slots

  let stack := state.stack |> List.dropWhile cond

  match stack with
  |  .Step _ _ :: stack' =>
    withMsg (fun _ => s!"{state.sid}: RemoveFrameStep {sid} stack {stack'} slots {slots}")
                      {state with stack := stack', slots := slots}
  | _ =>
    withMsg (fun _ => s!"{state.sid}: RemoveFrameStep failed ") state

@[inline] private def step_look (look : Look) (next : Fin n)
     (state : SearchState n s) : SearchState n s :=
  match look with
  | .Start =>
    if state.at.atStart then
      let state := (withMsg (fun _ => s!"{state.sid}: Look.Start -> {next}") {state with sid := next})
      state
    else state
  | .End =>
    if state.at.atStop then
      let state := (withMsg (fun _ => s!"{state.sid}: Look.End -> {next}") {state with sid := next})
      state
    else state
  | .EndWithOptionalLF =>
    if state.at.atStop then
      let state := (withMsg (fun _ => s!"{state.sid}: Look.EndWithOptionalLF -> {next}")
                                      {state with sid := next})
      state
    else
      match (state.at.curr?, state.at.next.atStop) with
      | (some '\n', true) =>
          let state := (withMsg (fun _ => s!"{state.sid}: Look.EndWithOptionalLF -> {next}")
                                          {state with sid := next})
          state
      | _ => (withMsg (fun _ => s!"{state.sid}: Look.EndWithOptionalLF failed at pos {state.at} atStop {state.at.next.atStop}") state)
  | .StartLF =>
    if state.at.atStart || state.at.prev?.any (· = '\n') then
      (withMsg (fun _ => s!"{state.sid}: Look.StartLF -> {next}") {state with sid := next})
    else
        let prev := encodeChar? state.at.prev?
        (withMsg (fun _ => s!"{state.sid}: StartLF failed at pos {state.at.pos} prev '{prev}'") state)
  | .EndLF =>
    if state.at.atStop || state.at.curr?.any (· = '\n') then
      (withMsg (fun _ => s!"{state.sid}: Look.EndLF -> {next}") {state with sid := next})
    else state
  | .StartCRLF =>
    if state.at.atStart
        || state.at.prev?.any (· = '\n')
        || (state.at.prev?.any (· = '\r')
            && (state.at.atStop || state.at.curr?.any (· != '\n')))
    then
      (withMsg (fun _ => s!"{state.sid}: Look.StartCRLF -> {next}") {state with sid := next})
    else state
  | .EndCRLF =>
    if state.at.atStop
        || state.at.curr?.any (· = '\r')
        || state.at.curr?.any (· = '\n')
            && (state.at.pos.byteIdx = 0 || state.at.prev?.any (· != '\r'))
    then
      (withMsg (fun _ => s!"{state.sid}: Look.EndCRLF -> {next}") {state with sid := next})
    else state
  | .WordUnicode =>
    if is_word_unicode state then
      (withMsg (fun _ => s!"{state.sid}: Look.WordUnicode -> {next}") {state with sid := next})
    else
      let prev := encodeChar? state.at.prev?
      let curr := encodeChar? state.at.curr?
      (withMsg
        (fun _ => s!"WordUnicode failed at pos {state.at.pos} prev '{prev}' curr '{curr}'") state)
  | .WordUnicodeNegate =>
    if is_word_unicode_negate state then
      let state := (withMsg (fun _ => s!"{state.sid}: Look.WordUnicodeNegate -> {next}") {state with sid := next})
      state
    else state
  | .WordStartUnicode =>
    if is_word_start_unicode state then
      let state := (withMsg (fun _ => s!"{state.sid}: Look.WordStartUnicode -> {next}") {state with sid := next})
      state
    else state
  | .WordEndUnicode =>
    if is_word_end_unicode state then
      let state := (withMsg (fun _ => s!"{state.sid}: Look.WordEndUnicode -> {next}") {state with sid := next})
      state
    else state
  | .WordStartHalfUnicode =>
    if is_word_start_half_unicode state then
      let state := (withMsg
        (fun _ => s!"{state.sid}: Look.WordStartHalfUnicode -> {next}") {state with sid := next})
      state
    else state
  | .WordEndHalfUnicode =>
    if is_word_end_half_unicode state then
      let state := (withMsg
        (fun _ => s!"{state.sid}: Look.WordEndHalfUnicode -> {next}") {state with sid := next})
      state
    else state
  | .PreviousMatch =>
    if state.at.atStart then
      let state := (withMsg (fun _ => s!"{state.sid}: Look.PreviousMatch -> {next}") {state with sid := next})
      state
    else
      (withMsg
        (fun _ => s!"PreviousMatch failed at pos {state.at.pos}") state)
  | .ClearMatches =>
    if h : 0 < state.slots.size then
      let frame : Frame n s := Frame.RestoreCapture Capture.Role.Start 0 (state.slots.get 0 h)
      let stack := Stack.push state.stack frame
      let slots := state.slots |> Array.map (fun (s, g, _) =>
                    if s = 0 then (s, g, CharPos.toSlotEntry state.at) else (s, g, none))
      (withMsg (fun _ => s!"{state.sid}: Look.ClearMatches stack {stack} slots {slots} -> {next}")
                          {state with stack := stack, slots := slots, sid := next})
    else
      (withMsg
        (fun _ => s!"ClearMatches failed at pos {state.at.pos}, no slots") state)

@[inline] private def step_byterange (trans : Checked.Transition n) (state : SearchState n s)
    : SearchState n s :=
  if state.at.atStop then
    (withMsg (fun _ =>
      s!"{state.sid}: ByteRange failed at stop")
      state)
  else if state.at.curr?.any (Checked.Transition.matches trans)  then
    let next := state.at.next
    (withMsg (fun _ =>
            let t := s!"{Nat.intAsString trans.start}-{Nat.intAsString trans.end}"
            s!"{state.sid}: ByteRange matched '{t}' at charpos {state.at} -> {trans.next}")
         {state with sid := trans.next, «at» := next})
  else
    (withMsg (fun _ =>
            let t := s!"{Nat.intAsString trans.start}-{Nat.intAsString trans.end}"
            s!"{state.sid}: ByteRange failed match '{t}' at charpos {state.at}")
      state)

@[inline] private def step_backreference_loop (s : String) (i : Nat) (case_insensitive : Bool)
  (cp : CharPos input) : Option (CharPos input) :=
  if i < s.length
  then
    if cp.atStop then none else
    let c := s.get ⟨i⟩
    let cf := if case_insensitive
      then
        match Unicode.case_fold_char c with
        | #[⟨(cU, _), _⟩, ⟨(cL, _), _⟩] => if cU = c then cL else cU
        | _ => c
      else c
    if cp.curr?.any (fun x => x = c || x = cf)
    then step_backreference_loop s (i + 1) case_insensitive cp.next
    else none
  else some cp

@[inline] private def step_backreference (b : Nat) (case_insensitive : Bool) (next : Fin n)
  (state : SearchState n s) : SearchState n s :=
  if h : b < state.recentCaptures.size then
    match state.recentCaptures.get b h with
    | some (f, t) =>
        let s' := s.extract f t |>.toString
        match step_backreference_loop s' 0 case_insensitive state.«at» with
        | some cp =>
            (withMsg (fun _ => s!"{state.sid}: Backreference {b} '{s'}' matched from charpos {state.at} to {cp} -> {next}")
                {state with sid := next, «at» := cp })
        | none =>
          (withMsg (fun _ =>
            s!"{state.sid}: Backreference '{b}' failed at charpos {state.at}, no match with '{s}'")
            state)
    | _ =>
      (withMsg (fun _ =>
        s!"{state.sid}: Backreference '{b}' failed at charpos {state.at}, recentCapture empty")
        state)
  else
    (withMsg (fun _ =>
    s!"{state.sid}: Backreference '{b}' failed at charpos {state.at}, recentCapture not found")
    state)

@[inline] private def step_sparse_transitions (_ : Checked.NFA)
    (transitions : Array $ Checked.Transition n)  (state : SearchState n s) : SearchState n s :=
  if state.at.atStop then
      (withMsg
        (fun _ =>
            s!"{state.sid}: SparseTransitions failed at stop") state)
  else
    match transitions.find?
            (fun trans => state.at.curr?.any (Checked.Transition.matches trans)) with
    | some t =>
        let next := state.at.next
        (withMsg (fun _ => s!"{state.sid}: SparseTransitions '{encodeChar? state.at.curr?}' matched at charpos {state.at} -> {t.next}")
            {state with sid := t.next, «at» := next})
    | none =>
      (withMsg
        (fun _ =>
            s!"{state.sid}: SparseTransitions failed  at charpos {state.at}") state)

@[inline] private def step_union (alts : Array $ Fin n) (state : SearchState n s) : SearchState n s :=
  match alts with
  | #[alt1, alt2] =>
    let stack := Stack.push state.stack (Frame.Step alt2 state.at)
    (withMsg (fun _ => s!"{state.sid}: Union stack {stack} -> {alt1}")
      {state with sid := alt1, stack := stack})
  | _ =>
    match alts.head? with
    | some (alt, alts) =>
      let stack := Stack.append state.stack
                    (Stack.toStack (alts |> Array.map (fun a => Frame.Step a state.at)))
      (withMsg
        (fun _ => s!"{state.sid} Union stack {stack} -> {alt}")
        {state with sid := alt, stack := stack})
    | none => state

@[inline] private def step_union_reverse (alts : Array $ Fin n) (state : SearchState n s)
    : SearchState n s :=
  match alts with
  | #[alt1, alt2] =>
    let stack := Stack.push state.stack (Frame.Step alt1 state.at)
    (withMsg (fun _ => s!"{state.sid}: Union_Reverse stack {stack} -> {alt2}")
      {state with sid := alt2, stack := stack})
  | _ =>
    match alts.head? with
    | some (alt, alts) =>
      let stack := Stack.append state.stack
                    (Stack.toStack (alts.reverse |> Array.map (fun a => Frame.Step a state.at)))
      (withMsg
            (fun _ => s!"{state.sid}: Union_Reverse stack {stack} -> {alt}")
            {state with sid := alt, stack := stack})
    | none => state

@[inline] private def step_binary_union (alt1 alt2 : Fin n)
     (state : SearchState n s) : SearchState n s :=
  (withMsg (fun _ => s!"BinaryUnion {state.sid} -> {alt1}")
       {state with sid := alt1, stack := Stack.push state.stack (Frame.Step alt2 state.at)})

@[inline] private def step_change_capture_slot (next : Fin n) (slot : Nat)
     (state : SearchState n s) : SearchState n s :=
  if h : slot < state.slots.size
  then
    let (s, g, _) := state.slots.get slot h
    let slots := state.slots.set slot (s, g, CharPos.toSlotEntry state.at) h
    (withMsg (fun _ => s!"{state.sid}: ChangeCaptureSlot slot {slot} slots {slots} -> {next}")
                {state with sid := next, slots := slots })
  else
    (withMsg (fun _ => s!"{state.sid}: ChangeCaptureSlot slot {slot} invalid")
                state)

@[inline] private def step_capture (role : Capture.Role)(next : Fin n) (group slot : Nat)
     (state : SearchState n s) : SearchState n s :=
  let (stack, slots, recentCaptures) :=
    if h : slot < state.slots.size
    then
      let (s, g, _) := state.slots.get slot h
      let frame := Frame.RestoreCapture role slot (state.slots.get slot h)
      let slots := state.slots.set slot (s, g, CharPos.toSlotEntry state.at) h
      let recentCaptures :=
        if role == Capture.Role.End then

          let recentCapture :=
              let slotsOfGroup := slots.filter (fun (_, g', _) => g = g')
              match slotsOfGroup with
              | #[(_, _, some f), (_, _, some t)] => some (f, t)
              | _ => none

          if h : g < state.recentCaptures.size then state.recentCaptures.set g recentCapture h
          else state.recentCaptures
        else state.recentCaptures

      (Stack.push state.stack frame, slots, recentCaptures)
    else (state.stack, state.slots, state.recentCaptures)
  (withMsg (fun _ => s!"{state.sid}: Capture{role} group {group} stack {stack} slots {slots} recentCaptures {recentCaptures} -> {next}")
                {state with sid := next, slots := slots, stack := stack, recentCaptures := recentCaptures })

@[inline] private def step_match (pattern_id : PatternID)
     (state : SearchState n s) : SearchState n s :=
  (withMsg (fun _ => s!"Match {state.sid}")
          {state with halfMatch := some ⟨pattern_id, state.at.pos⟩})

/-- execute next step in NFA if state not already visited -/
@[inline] private def toNextStep (nfa : Checked.NFA) (state : Checked.State n)
    (searchState : SearchState n s) : SearchState n s :=
  match state with
  | .Empty next => step_empty next searchState
  | .NextChar offset next => step_next_char offset next searchState
  | .Fail => step_fail searchState
  | .Eat s next => step_eat s next searchState
  | .ChangeFrameStep f t => step_change_frame_step f t searchState
  | .RemoveFrameStep s => step_remove_frame_step s searchState
  | .Look look next => step_look look next searchState
  | .BackRef b f next => step_backreference b f next searchState
  | .ByteRange t => step_byterange t searchState
  | .SparseTransitions transitions => step_sparse_transitions nfa transitions searchState
  | .Union alts => step_union alts searchState
  | .UnionReverse alts => step_union_reverse alts searchState
  | .BinaryUnion alt1 alt2 => step_binary_union alt1 alt2 searchState
  | .Capture role next _ g slot => step_capture role next g slot searchState
  | .Match pattern_id => step_match pattern_id searchState

@[inline] private def toNextStep' (nfa : Checked.NFA) (state : Checked.State nfa.n)
    (searchState : SearchState nfa.n s) : SearchState nfa.n s :=
  let searchState' := toNextStep nfa  state searchState
  -- countVisited is not changed in `toNextStep`
  {searchState' with countVisited := searchState.countVisited}

theorem toNextStep'_eq {nfa : Checked.NFA} {state : Checked.State nfa.n} {s s1 : SearchState nfa.n input}
  {msg : Unit → String}
  (h : toNextStep' nfa state (withMsg msg s) = s1) : s.countVisited = s1.countVisited := by
  unfold toNextStep' at h
  simp [SearchState.ext_iff] at h
  unfold withMsg at h
  split at h <;> try simp_all

/-- execute next step in NFA if state not already visited. Returns true if steps available. -/
@[inline] private def toNextStepChecked (nfa : Checked.NFA) (state : SearchState nfa.n s)
    : Bool × SearchState nfa.n s :=
  match Visited.checkVisited' state with
  | (false, state') =>
      let state := nfa.states.get state'.sid.val (by
                                    rw [← Checked.NFA.isEq nfa]
                                    exact state'.sid.isLt)
      (true, toNextStep'
                nfa
                state
                (withMsg (fun _ => s!"{state'.sid}: visit charpos {state'.at}") state'))
                --state')
  | _ => (false, (withMsg (fun _ => s!"{state.sid}: isVisited charpos {state.at}") state))

theorem toNextStepChecked_true_lt (nfa : Checked.NFA) (s s1 : SearchState nfa.n input)
  (h : toNextStepChecked nfa s = (true, s1)) : s.countVisited < s1.countVisited := by
  unfold toNextStepChecked at h
  split at h <;> simp_all
  rename_i s2 hcv
  have heq : s1.countVisited = s2.countVisited := by
      simp [toNextStep'_eq h]
  have hlt : s.countVisited < s2.countVisited := by
    simp [Visited.checkVisited'_false_lt s hcv]
  exact Nat.lt_of_lt_of_eq hlt (id (Eq.symm heq))

theorem toNextStepChecked_false_eq (nfa : Checked.NFA) (s s1 : SearchState nfa.n input)
  (h : toNextStepChecked nfa s = (false, s1))
    : s.countVisited = s1.countVisited ∧ s.stack = s1.stack := by
  unfold toNextStepChecked at h
  split at h <;> try simp_all
  simp [withMsg_eq h]

@[inline] private def visitedSize (state : SearchState n s) : Nat :=
   (Visited.getRefValue state.visited).size

@[inline] private def unvisited (state : SearchState n s) : Nat :=
   (visitedSize state) - state.countVisited

/-- execute next steps in NFA. -/
def steps (nfa : Checked.NFA) (state : SearchState nfa.n s) : SearchState nfa.n s :=
  match toNextStepChecked nfa state with
  | (true, state) => loop nfa state
  | (false, state) => state
where
  loop (nfa : Checked.NFA) (state : SearchState nfa.n s) : SearchState nfa.n s :=
    match h : toNextStepChecked nfa state with
    | (true, state') =>
      have h2 : state.countVisited < state'.countVisited :=
        toNextStepChecked_true_lt nfa state state' h
      if h0 : state.countVisited < visitedSize state then
        if h1 : visitedSize state = visitedSize state' then
          have : unvisited state' < unvisited state := by
            unfold unvisited
            omega
          loop nfa state'
        else state
      else {state with msgs := state.msgs.push "overflow visited array"}
    | (false, state) => state
termination_by unvisited state

theorem steps_loop_le (nfa : Checked.NFA) (s s1 : SearchState nfa.n input) (h : steps.loop nfa s = s1)
    : s.countVisited ≤ s1.countVisited := by
  unfold steps.loop at h
  split at h <;> try simp_all
  split at h
  · rename_i state heq hlt
    have h2 : s.countVisited < state.countVisited := toNextStepChecked_true_lt nfa s state heq
    split at h
    rename_i heq
    have : unvisited state < unvisited s := by
      unfold unvisited
      omega
    have hx : state.countVisited ≤ s1.countVisited := steps_loop_le nfa state s1 h
    · simp [Nat.le_trans (Nat.le_of_lt h2) hx]
    · simp_all
  · simp [SearchState.ext_iff] at h
    simp_all
  · rename_i heq
    have h2 : s.countVisited = s1.countVisited ∧ s.stack = s1.stack :=
      toNextStepChecked_false_eq nfa s s1 heq
    simp [Nat.le_of_eq h2.left]
termination_by unvisited s

theorem steps_lt_or_eq_lt (nfa : Checked.NFA) (s s1 : SearchState nfa.n input) (h : steps nfa s = s1)
  : s.countVisited < s1.countVisited
    ∨ s.countVisited = s1.countVisited ∧ s.stack.length = s1.stack.length := by
  unfold steps at h
  split at h <;> try simp_all
  · rename_i state heq
    have h2 : s.countVisited < state.countVisited := toNextStepChecked_true_lt nfa s state heq
    have h3 : state.countVisited ≤ s1.countVisited := steps_loop_le nfa state s1 h
    omega
  · rename_i state heq
    have h2 : s.countVisited = s1.countVisited ∧ s.stack = s1.stack :=
      toNextStepChecked_false_eq nfa s s1 heq
    simp_all

@[inline] private def toNextFrameStep (nfa : Checked.NFA) (state : SearchState nfa.n s)
    : Bool × SearchState nfa.n s :=
  let state' := steps nfa state
  match state'.halfMatch with
  | some _ => (false, state')
  | none =>
    (true,
      {state' with
              msgs := if state'.logEnabled
                    then state'.msgs.push s!"{state'.sid}: Backtrack.Loop stack {state'.stack}"
                    else state'.msgs})

theorem toNextFrameStep_true_lt_or_eq_lt (nfa : Checked.NFA) (s s1 : SearchState nfa.n input)
  (h : toNextFrameStep nfa s = (true, s1)) :
    s.countVisited < s1.countVisited ∨ s.countVisited = s1.countVisited
        ∧ s.stack.length = s1.stack.length := by
  unfold toNextFrameStep at h
  simp_all
  split at h <;> try simp_all
  let state' := BoundedBacktracker.steps nfa s
  have heq : BoundedBacktracker.steps nfa s = state' := rfl
  have hx : s.countVisited < state'.countVisited
      ∨ s.countVisited = state'.countVisited ∧ s.stack.length = state'.stack.length :=
    steps_lt_or_eq_lt nfa s state' heq
  simp [SearchState.ext_iff] at h
  rw [heq] at h
  have : state'.countVisited = s1.countVisited := by simp_all
  have : state'.stack.length = s1.stack.length := by simp_all
  omega

@[inline] private def toNextFrameRestoreCapture (slot : Nat)
  (offset : Nat × Nat × Option (CharPos.PosInRange s))
  (stack : Stack n s) (state : SearchState n s) : Bool × SearchState n s :=
  if h : slot < state.slots.size
  then
    let state := {state with slots := state.slots.set slot offset h, stack := stack}
    let state := (withMsg (fun _ => s!"{state.sid}: Backtrack.RestoreCapture stack {stack} slots {state.slots}") state)
    (true, state)
  else (false, state)

theorem toNextFrameRestoreCapture_true_lt_or_eq_lt (slot : Nat)
  (offset : Nat × Nat × Option (CharPos.PosInRange s))
  (stack : Stack n s) (s : SearchState n s)
    (h : toNextFrameRestoreCapture slot offset stack s = (true, s1))
    : s.countVisited = s1.countVisited ∧ stack = s1.stack := by
  unfold toNextFrameRestoreCapture at h
  split at h <;> try simp_all
  unfold withMsg at h
  split at h <;> simp [SearchState.ext_iff] at h <;> simp_all

/-- execute steps in next frame. Returns false if no more frame available
    or match is found. -/
@[inline] private def toNextFrame (nfa : Checked.NFA) (state : SearchState nfa.n s)
    : Bool × SearchState nfa.n s :=
  match Stack.pop? state.stack with
  | some (frame, stack) =>
      match frame with
      | .Step sid «at» =>
        toNextFrameStep nfa
          {state with sid := sid, «at» := «at», stack := stack,
                      msgs := if state.logEnabled
                              then state.msgs.push s!"{state.sid}: Backtrack.Step stack {stack} at pos {state.at} -> {sid}"
                              else state.msgs}
      | .RestoreCapture _ slot offset => toNextFrameRestoreCapture slot offset stack state
  | none =>
    (false, (withMsg (fun _ => s!"{state.sid}: stack empty ") state))

theorem toNextFrame_true_lt (nfa : Checked.NFA) (s s1 : SearchState nfa.n input)
  (h : toNextFrame nfa s = (true, s1))
    : s.countVisited < s1.countVisited
      ∨ s.countVisited = s1.countVisited ∧ s1.stack.length < s.stack.length := by
  unfold toNextFrame at h
  split at h
  split at h <;> try simp
  · rename_i stack _ sid _at heq
    let state : SearchState nfa.n input :=
      { stack := stack, visited := s.visited, countVisited := s.countVisited, sid := sid,
        «at» := _at,
        slots := s.slots, logEnabled := s.logEnabled,
        recentCaptures := s.recentCaptures
        msgs := if s.logEnabled
                then s.msgs.push s!"{s.sid}: Backtrack.Step stack {stack} at pos {s.at} -> {sid}"
                else s.msgs, halfMatch := s.halfMatch,
        backtracks := s.backtracks }
    have h1 : state.countVisited < s1.countVisited ∨
          state.countVisited = s1.countVisited ∧ state.stack.length = s1.stack.length :=
        toNextFrameStep_true_lt_or_eq_lt nfa state s1 h
    have hy : state.countVisited = s.countVisited := rfl
    rw [hy] at h1
    cases h1
    · omega
    · rename_i heq h1
      have hs : stack.length < s.stack.length := Stack.pop?_some_lt s.stack heq
      rw [h1.right] at hs
      omega
  · rename_i stack _ _ slot offset heq
    have h1 : stack.length < s.stack.length := Stack.pop?_some_lt s.stack heq
    have h2 : s.countVisited = s1.countVisited ∧ stack = s1.stack :=
      toNextFrameRestoreCapture_true_lt_or_eq_lt slot offset stack s h
    rw [h2.right] at h1
    omega
  · have hx : false = true := by simp_all [h]
    contradiction

theorem searchState_lexLt (nfa : Checked.NFA) (s s1 : SearchState nfa.n input)
  (h1 : s.countVisited < visitedSize s) (h2 : visitedSize s = visitedSize s1)
  (h : toNextFrame nfa s = (true, s1)) : unvisited s1 < unvisited s
            ∨ unvisited s1 = unvisited s ∧ s1.stack.length < s.stack.length := by
  unfold unvisited
  rw [← h2]
  have hx : s.countVisited < s1.countVisited
      ∨ s.countVisited = s1.countVisited ∧ s1.stack.length < s.stack.length :=
    toNextFrame_true_lt nfa s s1 h
  omega

private def collect_info (state : SearchState n s) : Array String :=
  let visited := Visited.getRefValue state.visited
  let values := visited |> Array.filter (· = 1) |>.size
  #[
      s!"backtracks {state.backtracks}",
      s!"visited array size {visited.size}",
      s!"count visited values {values}"
  ]

/-- BoundedBacktrack search -/
def backtrack (nfa : Checked.NFA)  (state : SearchState nfa.n s) : SearchState nfa.n s :=
  let frame := Frame.Step state.sid state.at
  let state := (withMsg (fun _ => s!"Backtrack sid {state.sid} charpos {state.at.pos}")
       {state with stack := Stack.push state.stack frame})
  let state := loop nfa state
  -- let state := {state with msgs := state.msgs ++ (collect_info state)}
  state
where
  loop (nfa : Checked.NFA) (state : SearchState nfa.n s) : SearchState nfa.n s :=
    match h : toNextFrame nfa state with
    | (true, state') =>
      -- let state := {state with backtracks := state.backtracks + 1}
      if h1 : state.countVisited < visitedSize state then
        if h2 : visitedSize state = visitedSize state' then
          have : Prod.lexLt
            (unvisited state', state'.stack.length) (unvisited state, state.stack.length) :=
            searchState_lexLt nfa state state' h1 h2 h
          loop nfa state'
        else state
      else  {state with msgs := state.msgs.push "overflow visited array"}
    | (false, state) => state
termination_by (unvisited state, state.stack.length)
decreasing_by
    simp_wf
    exact Prod.lex_def.mpr this

private def dropLastWhile (arr : Array  α) (p :  α -> Bool) : Array α :=
  arr |> Array.foldr (init := #[]) fun a acc =>
    if acc.size = 0 && p a then acc
    else ⟨a :: acc.toList⟩

/-- Search for the first match of this regex in the haystack. -/
private def slots' (s : Substring) («at» : String.Pos) (nfa : Checked.NFA) (logEnabled : Bool)
    : (Array String) × (Array (Option (CharPos.PosInRange s × CharPos.PosInRange s))) :=
  if h : 0 < nfa.n ∧ s.startPos ≤ «at» ∧ «at» ≤ s.stopPos then
    let state := backtrack nfa (SearchState.fromNfa nfa s «at» logEnabled h)
    let pairs := toPairs state.slots
    (state.msgs, dropLastWhile pairs (·.isNone))
  else (#[], #[])

/-- Search for the first match of this regex in the haystack and
    simulate the unanchored prefix with looping. -/
private def slotsWithUnanchoredPrefix (s : Substring) («at» : String.Pos) (nfa : Checked.NFA)
  (logEnabled : Bool) (init : Array String)
    : (Array String) × (Array (Option (CharPos.PosInRange s × CharPos.PosInRange s))) :=
  if h: s.stopPos.byteIdx <= «at».byteIdx then
    let (msgs, slots) := slots' s «at» nfa logEnabled
    (init ++ msgs, slots)
  else
    let (msgs, slots) := slots' s «at» nfa logEnabled
    match (msgs, slots) with
    | (msgs, #[]) =>
      let c : Char := s.get «at»
      let size := c.utf8Size
      have : s.stopPos.byteIdx - (at.byteIdx + size) < s.stopPos.byteIdx - at.byteIdx := by
        have : 0 < c.utf8Size := Char.utf8Size_pos c
        omega
      slotsWithUnanchoredPrefix s («at» + ⟨size⟩) nfa logEnabled (init ++ msgs)
    | _ => (init ++ msgs, slots)
termination_by s.stopPos.byteIdx - «at».byteIdx

private def toMatches (s : Substring) (slots : Array (Option (
                     CharPos.PosInRange s × CharPos.PosInRange s)))
    : Array (Option { m : Substring // m.str = s.str }) :=
  slots
  |> Array.map (fun pair =>
      match pair with
      | some (p0, p1) =>
          have : s.startPos ≤ p0.val := p0.property.left
          have : p1.val ≤ s.stopPos := p1.property.right
          some ⟨⟨s.str, p0.val, p1.val⟩, by simp⟩
      | none => none)

/-- Search for the first match of this regex in the haystack given and return log msgs and
    the matches of each capture group. -/
def «matches» (s : Substring) («at» : String.Pos) (nfa : Checked.NFA) (logEnabled : Bool)
    : (Array String) × (Array (Option { m : Substring // m.str = s.str })) :=
  let (msgs, slots) :=
    if nfa.unanchored_prefix_in_backtrack
    then slotsWithUnanchoredPrefix s «at» nfa logEnabled #[]
    else slots' s «at» nfa logEnabled
(msgs, toMatches s slots)
