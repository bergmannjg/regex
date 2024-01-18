import Regex.Syntax.Hir
import Regex.Nfa
import Regex.Compiler
import Regex.Utils
import Lean.Util
import Init.Core
import Std.Data.Nat.Lemmas
import Std.Tactic.Ext

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
    then arr.set ⟨index, h⟩ value
    else arr)

  match st default with | EStateM.Result.ok _ n => if n = default then ref else mkRef #[]

instance {α β : Type} [Inhabited β] : Inhabited (ST.Ref β (Array α)) where
  default := mkRef #[]

end Array.Ref

/-- Char position in a substring-/
structure CharPos where
  /-- substring -/
  s : Substring
  /-- current position -/
  pos : String.Pos := ⟨0⟩
  /-- char at current position -/
  curr? : Option Char := none
  /-- char at previous position -/
  prev? : Option Char := none

instance : Inhabited CharPos := ⟨default, default, none, none⟩

instance : ToString CharPos where
  toString s := s!"{s.pos} {s.curr?} {s.prev?}"

namespace CharPos

def get? (s : Substring) («at» : String.Pos) : Option Char :=
  if «at» < s.stopPos then s.get «at» else none

/-- create a CharPos from `s` and position `«at»` -/
def create (s : Substring) («at» : String.Pos) : CharPos :=
  let prev? := if «at» = 0 then none else get? s (s.prev «at»)
  ⟨s, «at», get? s «at», prev?⟩

/-- to next position CharPos of `cp` -/
def next (cp : CharPos) : CharPos :=
  if cp.pos >= cp.s.stopPos then cp
  else
    match cp.curr? with
    | some c =>
      let nextPos : String.Pos := ⟨cp.pos.byteIdx + (String.csize c)⟩
      {cp with pos := nextPos, prev? := cp.curr?, curr? := get? cp.s nextPos}
    | none => cp

/-- is CharPos at start position -/
def atStart (cp : CharPos) : Bool :=
  cp.pos = cp.s.startPos

/-- is CharPos at stop position -/
def atStop (cp : CharPos) : Bool :=
  cp.pos = cp.s.stopPos

end CharPos

/-- Represents a stack frame on the heap while doing backtracking. -/
inductive Frame where
  /-- Look for a match starting at `sid` and the given position in the haystack. -/
  | Step (sid: StateID) («at»: CharPos) : Frame
  /-- Reset the given `slot` to the given `offset` (which might be `None`). -/
  | RestoreCapture (slot: Nat) (offset: Option String.Pos) : Frame

instance : ToString Frame where
  toString frame :=
    match frame with
    | .Step sid «at» => s!"Step({sid}, {«at».pos})"
    | .RestoreCapture slot _ => s!"RestoreCapture({slot})"

/-- A representation of "half" of a match reported by a DFA. -/
structure HalfMatch where
    /-- The pattern ID. -/
    pattern: PatternID
    /-- The offset of the match. -/
    offset: String.Pos

instance : Inhabited HalfMatch := ⟨0, 0⟩

instance : ToString HalfMatch where
  toString a := s!"pattern {a.pattern}, offset {a.offset}"

private def compare (a : StateID × String.Pos) (b : StateID × String.Pos) : Ordering :=
  if a.1 < b.1 then Ordering.lt
  else if a.1 = b.1 && a.2 = b.2 then Ordering.eq
  else Ordering.gt

/-- The stack of frames  -/
abbrev Stack := List Frame

namespace Stack

/-- Push frame to stack  -/
@[inline] def push (stack : Stack) (v : Frame) : Stack :=
  v :: stack

/-- pop head frame from stack  -/
@[inline] def pop? (stack : Stack) : Option (Frame × Stack) :=
  match stack with
  | [] => none
  | head :: tail => (head, tail)

theorem pop?_some_lt (s : Stack) (h : pop? s = some (a, s1)) : s1.length < s.length := by
  have : s = a :: s1 := by unfold pop? at h; split at h <;> simp_all
  rw [this]
  simp_all

/-- append stacks -/
@[inline] def append (stack1 stack2 : Stack) : Stack :=
  match stack2 with
  | v1 :: v2 :: [] => v2 :: v1 :: stack1
  | _ => List.append (stack2.reverse) stack1

@[inline] def toStack (arr : Array Frame) : Stack :=
  arr |> Array.toList

end Stack

instance : Inhabited Stack := ⟨[]⟩

/-- The encoded set of (StateID, HaystackOffset) pairs that have been visited
    by the backtracker within a single search. todo: encode as bits -/
abbrev Visited := Array UInt8

/-- State of the backtracking search -/
@[ext] structure SearchState where
  /-- Stack used on the heap for doing backtracking -/
  stack: Stack
  /-- The encoded set of (StateID, HaystackOffset) pairs that have been visited
    by the backtracker within a single search. -/
  visited : ST.Ref Nat Visited
  /-- count of pairs that have been visited -/
  countVisited : Nat
  /-- current state -/
  sid: StateID
  /-- input string -/
  input : Substring
  /-- position in input string -/
  «at» : CharPos
  /-- slots, positions of captures in haystack -/
  slots: Array (Option String.Pos)
  /-- is logging enabled -/
  logEnabled : Bool
  /-- log msgs -/
  msgs: Array String
  /-- HalfMatch -/
  halfMatch: Option HalfMatch
  /-- count of backtracks -/
  backtracks : Nat

instance : Inhabited SearchState :=
  ⟨default, default, 0, 0, "".toSubstring, default, #[], false, #[], none, 0⟩

namespace SearchState

/-- create the SearchState from an NFA -/
def fromNfa (nfa : NFA) (input : Substring) («at» : String.Pos) (logEnabled : Bool) : SearchState :=
  let slots : Array (Option String.Pos) :=
    nfa.states
    |> Array.filter (fun s => match s with | State.Capture _ _ _ _ => true | _ => false)
    |> Array.map (fun _ => none)
  {
    stack := default
    visited := Array.Ref.mkRef <|
      Array.mkArray ((nfa.states.size + 1) * (input.stopPos.byteIdx - input.startPos.byteIdx +1)) 0
    countVisited := 0
    sid := 0
    input := input
    «at» := CharPos.create input «at»
    slots := slots
    logEnabled := logEnabled
    msgs := #[]
    halfMatch := none
    backtracks := 0
  }

end SearchState

abbrev SearchStateM := StateM SearchState

instance : Nonempty Visited := ⟨#[]⟩

namespace Visited

/-- get encoded index of StateID an CharPos in visited array -/
def index (sid : StateID) (cp : CharPos) : Nat :=
  (sid + 1) * (cp.s.stopPos.byteIdx - cp.s.startPos.byteIdx + 1) + cp.pos.byteIdx

private def getRefValue (ref : ST.Ref Nat Visited) : Visited :=
  Array.Ref.getRefValue ref

private def modifyRefValue (ref : ST.Ref Nat Visited) (index : Nat) (value : UInt8)
    : ST.Ref Nat Visited :=
  Array.Ref.modifyRefValue ref index value

/-- Check if current StateID and CharPos in SearchState is already visited.
    If not visited mark pair as visited. -/
def checkVisited : SearchStateM Bool := do
  let state ← get
  let visited := Visited.getRefValue state.visited
  let index := Visited.index state.sid state.at
  if h : index < visited.size then
    if visited.get ⟨index, h⟩ != 0 then pure true
    else
      set {state with visited := Visited.modifyRefValue state.visited index 1}
      pure false
  else pure true

/-- Check if current StateID and CharPos in SearchState is already visited.
    If not visited mark pair as visited. -/
def checkVisited' (state : SearchState) : Bool × SearchState :=
  let (f, s) := checkVisited state
  if f then (true, state)
  else (false, {s with countVisited := state.countVisited + 1})

theorem checkVisited'_false_lt (s : SearchState) (h : checkVisited' s = (false, s1))
    : s.countVisited < s1.countVisited := by
  unfold checkVisited' at h
  split at h
  split at h <;> simp_all
  have hx : s.countVisited + 1 ≤ s1.countVisited := by
    simp [SearchState.ext_iff] at h
    simp_all
  simp [Nat.lt_of_succ_le hx]

theorem checkVisited'_true_eq (s : SearchState) (h : checkVisited' s = (true, s1))
    : s.countVisited = s1.countVisited ∧ s.stack.length = s1.stack.length := by
  unfold checkVisited' at h
  split at h
  split at h <;> simp_all

end Visited

/-- add a msg to the SearchState while doing backtracking.  -/
@[inline] private def withMsg (msg : Unit -> String) (state : SearchState) : SearchState :=
  if state.logEnabled then { state with msgs := state.msgs.push s!"{msg ()}"}
  else state

private def encodeChar? (c: Option Char) : String :=
  match c with
  | some curr => intAsString curr.val
  | none => "none"

/-- Returns true when [`Look::WordUnicode`] is satisfied `at` the given position in `haystack`. -/
@[inline] private def is_word_unicode (state : SearchState) : Bool :=
  let word_before :=
    if state.at.atStart then false
    else state.at.prev?.any Unicode.is_word_char
  let word_after :=
    if state.at.atStop then false
    else state.at.curr?.any Unicode.is_word_char
  word_before != word_after

/-- Returns true when [`Look::WordUnicodeNegate`] is satisfied `at` the
    given position in `haystack`. -/
@[inline] private def is_word_unicode_negate (state : SearchState) : Bool :=
  let word_before :=
    if state.at.atStart then false
    else state.at.prev?.any Unicode.is_word_char
  let word_after :=
    if state.at.atStop then false
    else state.at.curr?.any Unicode.is_word_char
  word_before = word_after

/-- Returns true when [`Look::WordStartUnicode`] is satisfied `at` the given position
    in `haystack`. -/
@[inline] private def is_word_start_unicode (state : SearchState) : Bool :=
  let word_before :=
    if state.at.atStart then false
    else state.at.prev?.any Unicode.is_word_char
  let word_after :=
    if state.at.atStop then false
    else state.at.curr?.any Unicode.is_word_char
  !word_before && word_after

/-- Returns true when [`Look::WordEndUnicode`] is satisfied `at` the given position
    in `haystack`. -/
@[inline] private def is_word_end_unicode (state : SearchState) : Bool :=
  let word_before :=
    if state.at.atStart then false
    else state.at.prev?.any Unicode.is_word_char
  let word_after :=
    if state.at.atStop then false
    else state.at.curr?.any Unicode.is_word_char
  word_before && !word_after

/-- Returns true when [`Look::WordStartHalfUnicode`] is satisfied `at` the given position
    in `haystack`. -/
@[inline] private def is_word_start_half_unicode (state : SearchState) : Bool :=
  let word_before :=
    if state.at.atStart then false
    else state.at.prev?.any Unicode.is_word_char
  !word_before

/-- Returns true when [`Look::WordEndHalfUnicode`] is satisfied `at` the given position
    in `haystack`. -/
@[inline] private def is_word_end_half_unicode (state : SearchState) : Bool :=
  let word_after :=
    if state.at.atStop then false
    else state.at.curr?.any Unicode.is_word_char
  !word_after

@[inline] private def step_empty (next : StateID) (state : SearchState) : SearchState :=
  withMsg (fun _ => s!"{state.sid}: Empty -> {next}") {state with sid := next}

@[inline] private def step_look (look : Look) (next : StateID)
     (state : SearchState) : SearchState :=
  match look with
  | .Start =>
    if state.at.atStart then
      let state := (withMsg (fun _ => s!"Look.Start -> {next}") {state with sid := next})
      state
    else state
  | .End =>
    if state.at.atStop then
      let state := (withMsg (fun _ => s!"Look.End -> {next}") {state with sid := next})
      state
    else state
  | .StartLF =>
    if state.at.atStart || state.at.prev?.any (· = '\n') then
      (withMsg (fun _ => s!"Look.StartLF -> {next}") {state with sid := next})
    else
        let prev := encodeChar? state.at.prev?
        (withMsg (fun _ => s!"StartLF failed at pos {state.at.pos} prev '{prev}'") state)
  | .EndLF =>
    if state.at.atStop || state.at.curr?.any (· = '\n') then
      (withMsg (fun _ => s!"Look.EndLF -> {next}") {state with sid := next})
    else state
  | .StartCRLF =>
    if state.at.atStart
        || state.at.prev?.any (· = '\n')
        || (state.at.prev?.any (· = '\r')
            && (state.at.atStop || state.at.curr?.any (· != '\n')))
    then
      (withMsg (fun _ => s!"Look.StartCRLF -> {next}") {state with sid := next})
    else state
  | .EndCRLF =>
    if state.at.atStop
        || state.at.curr?.any (· = '\r')
        || state.at.curr?.any (· = '\n')
            && (state.at.pos.byteIdx = 0 || state.at.prev?.any (· != '\r'))
    then
      (withMsg (fun _ => s!"Look.EndCRLF -> {next}") {state with sid := next})
    else state
  | .WordUnicode =>
    if is_word_unicode state then
      (withMsg (fun _ => s!"Look.WordUnicode -> {next}") {state with sid := next})
    else
      let prev := encodeChar? state.at.prev?
      let curr := encodeChar? state.at.curr?
      (withMsg
        (fun _ => s!"WordUnicode failed at pos {state.at.pos} prev '{prev}' curr '{curr}'") state)
  | .WordUnicodeNegate =>
    if is_word_unicode_negate state then
      let state := (withMsg (fun _ => s!"Look.WordUnicodeNegate -> {next}") {state with sid := next})
      state
    else state
  | .WordStartUnicode =>
    if is_word_start_unicode state then
      let state := (withMsg (fun _ => s!"Look.WordStartUnicode -> {next}") {state with sid := next})
      state
    else state
  | .WordEndUnicode =>
    if is_word_end_unicode state then
      let state := (withMsg (fun _ => s!"Look.WordEndUnicode -> {next}") {state with sid := next})
      state
    else state
  | .WordStartHalfUnicode =>
    if is_word_start_half_unicode state then
      let state := (withMsg (fun _ => s!"Look.WordStartHalfUnicode -> {next}") {state with sid := next})
      state
    else state
  | .WordEndHalfUnicode =>
    if is_word_end_half_unicode state then
      let state := (withMsg (fun _ => s!"Look.WordEndHalfUnicode -> {next}") {state with sid := next})
      state
    else state

@[inline] private def step_byterange (trans : Transition) (state : SearchState) : SearchState :=
  if state.at.atStop then state
  else if state.at.curr?.any (Transition.matches trans)  then
    let next := state.at.next
    (withMsg (fun _ => s!"{state.sid}: ByteRange charpos {next} -> {trans.next}")
         {state with sid := trans.next, «at» := next})
  else
    (withMsg (fun _ =>
      s!"{state.sid}: ByteRange failed with '{encodeChar? state.at.curr?}' at charpos {state.at}")
      state)

@[inline] private def step_sparse_transitions (_ : NFA)
    (transitions : Array Transition)  (state : SearchState) : SearchState :=
  if state.at.atStop then state
  else
    match Array.find? transitions
            (fun trans => state.at.curr?.any (Transition.matches trans)) with
    | some trans =>
        let next := state.at.next
        (withMsg (fun _ => s!"{state.sid}: SparseTransitions charpos {next} -> {trans.next}")
            {state with sid := trans.next, «at» := next})
    | none =>
      (withMsg
        (fun _ =>
            s!"{state.sid}: SparseTransitions failed with '{encodeChar? state.at.curr?}'") state)

@[inline] private def step_union (alts : Array StateID) (state : SearchState) : SearchState :=
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
            (fun _ => s!"{state.sid} Union stack {stack} -> {alt}") {state with sid := alt, stack := stack})
    | none => state

@[inline] private def step_union_reverse (alts : Array StateID) (state : SearchState)
    : SearchState :=
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
          (fun _ => s!"{state.sid}: Union_Reverse stack {stack} -> {alt}") {state with sid := alt, stack := stack})
    | none => state

@[inline] private def step_binary_union (alt1 alt2 : StateID)
     (state : SearchState) : SearchState :=
  (withMsg (fun _ => s!"BinaryUnion {state.sid} -> {alt1}")
       {state with sid := alt1, stack := Stack.push state.stack (Frame.Step alt2 state.at)})

@[inline] private def step_capture (next : StateID) (slot : Nat)
     (state : SearchState) : SearchState :=
  let (stack, slots) :=
    if h : slot < state.slots.size
    then
      let frame := Frame.RestoreCapture slot (state.slots.get ⟨slot, h⟩)
      (Stack.push state.stack frame, state.slots.set ⟨slot, h⟩ state.at.pos)
    else (state.stack, state.slots)
  (withMsg (fun _ => s!"{state.sid}: Capture stack {stack} -> {next}")
                {state with sid := next, slots := slots, stack := stack })

@[inline] private def step_match (pattern_id : PatternID)
     (state : SearchState) : SearchState :=
  (withMsg (fun _ => s!"Match {state.sid}")
          {state with halfMatch := some ⟨pattern_id, state.at.pos⟩})

/-- execute next step in NFA if state not already visited -/
@[inline] private def toNextStep (nfa : NFA) (state : State) (searchState : SearchState) : SearchState :=
  match state with
  | .Empty next => step_empty next searchState
  | .Look look next => step_look look next searchState
  | .ByteRange trans => step_byterange trans searchState
  | .SparseTransitions transitions => step_sparse_transitions nfa transitions searchState
  | .Union alts => step_union alts searchState
  | .UnionReverse alts => step_union_reverse alts searchState
  | .BinaryUnion alt1 alt2 => step_binary_union alt1 alt2 searchState
  | .Capture next _ _ slot => step_capture next slot searchState
  | .Match pattern_id => step_match pattern_id searchState

@[inline] private def toNextStep' (nfa : NFA) (state : State) (searchState : SearchState) : SearchState :=
  let searchState' := toNextStep nfa  state searchState
  -- countVisited is not changed in `toNextStep`
  {searchState' with countVisited := searchState.countVisited}

theorem toNextStep'_eq (nfa : NFA) (state : State) (s : SearchState)
  (h : toNextStep' nfa state s = s1) : s.countVisited = s1.countVisited := by
  unfold toNextStep' at h
  simp [SearchState.ext_iff] at h
  simp_all

/-- execute next step in NFA if state not already visited. Returns true if steps available. -/
@[inline] private def toNextStepChecked (nfa : NFA) (state : SearchState) : Bool × SearchState :=
  match Visited.checkVisited' state with
  | (false, state') =>
    if hs : state'.sid < nfa.states.size then
      let state := nfa.states.get ⟨state'.sid, hs⟩
      (true, toNextStep' nfa state state')
    else (false, state)
  | _ => (false, state)

theorem toNextStepChecked_true_lt (nfa : NFA) (s : SearchState)
  (h : toNextStepChecked nfa s = (true, s1)) : s.countVisited < s1.countVisited := by
  unfold toNextStepChecked at h
  split at h
  rename_i s2 hcv
  split at h <;> try simp_all
  · have heq : s1.countVisited = s2.countVisited := by
      simp [toNextStep'_eq _ _ s2 h]
    have hlt : s.countVisited < s2.countVisited := by
      simp [Visited.checkVisited'_false_lt s hcv]
    rw [← heq] at hlt
    simp [hlt]
  · have hx : false = true := by simp_all [h]
    contradiction

theorem toNextStepChecked_false_eq (nfa : NFA) (s : SearchState)
  (h : toNextStepChecked nfa s = (false, s1))
    : s.countVisited = s1.countVisited ∧ s.stack = s1.stack := by
  unfold toNextStepChecked at h
  split at h <;> try simp_all
  split at h <;> try simp_all

@[inline] private def visitedSize (state : SearchState) : Nat :=
   (Visited.getRefValue state.visited).size

@[inline] private def unvisited (state : SearchState) : Nat :=
   (visitedSize state) - state.countVisited

/-- execute next steps in NFA. -/
def steps (nfa : NFA) (state : SearchState) : SearchState :=
  match toNextStepChecked nfa state with
  | (true, state) => loop nfa state
  | (false, state) => state
where
  loop (nfa : NFA) (state : SearchState) : SearchState :=
    match h : toNextStepChecked nfa state with
    | (true, state') =>
      have h2 : state.countVisited < state'.countVisited :=
        toNextStepChecked_true_lt nfa state h
      if h0 : state.countVisited < visitedSize state then
        if h1 : visitedSize state = visitedSize state' then
          have : unvisited state' < unvisited state := by
            unfold unvisited
            rw [← h1]
            simp [Nat.sub_lt_sub_left h0 h2]
          loop nfa state'
        else state
      else {state with msgs := state.msgs.push "overflow visited array"}
    | (false, state) => state
termination_by _ nfa state => unvisited state

theorem steps_loop_le (nfa : NFA) (s : SearchState) (h : steps.loop nfa s = s1)
    : s.countVisited ≤ s1.countVisited := by
  unfold steps.loop at h
  split at h <;> try simp_all
  split at h
  · rename_i state heq hlt
    have h2 : s.countVisited < state.countVisited := toNextStepChecked_true_lt nfa s heq
    split at h
    rename_i heq
    have : unvisited state < unvisited s := by
      unfold unvisited
      rw [← heq]
      simp [Nat.sub_lt_sub_left hlt h2]
    have hx : state.countVisited ≤ s1.countVisited := steps_loop_le nfa state h
    · simp [Nat.le_trans (Nat.le_of_lt h2) hx]
    · simp_all
  · simp [SearchState.ext_iff] at h
    simp_all
  · rename_i heq
    have h2 : s.countVisited = s1.countVisited ∧ s.stack = s1.stack :=
      toNextStepChecked_false_eq nfa s heq
    simp [Nat.le_of_eq h2.left]
termination_by _ => unvisited s

theorem steps_lt_or_eq_lt (nfa : NFA) (s : SearchState) (h : steps nfa s = s1)
  : s.countVisited < s1.countVisited
    ∨ s.countVisited = s1.countVisited ∧ s.stack.length = s1.stack.length := by
  unfold steps at h
  split at h <;> try simp_all
  · rename_i state heq
    have h2 : s.countVisited < state.countVisited := toNextStepChecked_true_lt nfa s heq
    have h3 : state.countVisited ≤ s1.countVisited := steps_loop_le nfa state h
    apply Or.inl
    simp [Nat.lt_of_lt_of_le h2 h3]
  · rename_i state heq
    have h2 : s.countVisited = s1.countVisited ∧ s.stack = s1.stack :=
      toNextStepChecked_false_eq nfa s heq
    simp_all

@[inline] private def toNextFrameStep (nfa : NFA) (state : SearchState) : Bool × SearchState :=
  let state' := steps nfa state
  match state'.halfMatch with
  | some _ => (false, state')
  | none =>
    (true,
      {state' with
              msgs := if state'.logEnabled
                    then state'.msgs.push s!"{state'.sid}: backtrackLoop with stack {state'.stack}"
                    else state'.msgs})

theorem toNextFrameStep_true_lt_or_eq_lt (nfa : NFA) (s : SearchState)
  (h : toNextFrameStep nfa s = (true, s1)) :
    s.countVisited < s1.countVisited ∨ s.countVisited = s1.countVisited
        ∧ s.stack.length = s1.stack.length := by
  unfold toNextFrameStep at h
  simp_all
  split at h <;> try simp_all
  let state' := BoundedBacktracker.steps nfa s
  have heq : BoundedBacktracker.steps nfa s = state' := by simp_all
  have hx : s.countVisited < state'.countVisited
      ∨ s.countVisited = state'.countVisited ∧ s.stack.length = state'.stack.length :=
    steps_lt_or_eq_lt nfa s heq
  simp [SearchState.ext_iff] at h
  rw [heq] at h
  have hv : state'.countVisited = s1.countVisited := by simp_all
  have hs : state'.stack.length = s1.stack.length := by simp_all
  rw [hv] at hx
  rw [hs] at hx
  simp_all

@[inline] private def toNextFrameRestoreCapture (slot : Nat) (offset : Option String.Pos)
  (stack : Stack) (state : SearchState) : Bool × SearchState :=
  if h : slot < state.slots.size
  then
    let state := {state with slots := state.slots.set ⟨slot,h⟩ offset, stack := stack}
    let state := (withMsg (fun _ => s!"{state.sid}: RestoreCapture slots stack {stack}") state)
    (true, state)
  else (false, state)

theorem toNextFrameRestoreCapture_true_lt_or_eq_lt (slot : Nat) (offset : Option String.Pos)
  (stack : Stack) (s : SearchState) (h : toNextFrameRestoreCapture slot offset stack s = (true, s1))
    : s.countVisited = s1.countVisited ∧ stack = s1.stack := by
  unfold toNextFrameRestoreCapture at h
  split at h <;> try simp_all
  unfold withMsg at h
  split at h <;> simp [SearchState.ext_iff] at h <;> simp_all

/-- execute steps in next frame. Returns false if no more frame available
    or match is found. -/
@[inline] private def toNextFrame (nfa : NFA) (state : SearchState) : Bool × SearchState :=
  match Stack.pop? state.stack with
  | some (frame, stack) =>
      match frame with
      | .Step sid «at» =>
        toNextFrameStep nfa
          {state with sid := sid, «at» := «at», stack := stack,
                      msgs := if state.logEnabled
                              then state.msgs.push s!"{state.sid}: Step stack {stack} -> {sid}"
                              else state.msgs}
      | .RestoreCapture slot offset => toNextFrameRestoreCapture slot offset stack state
  | none =>
    (false, (withMsg (fun _ => s!"{state.sid}: stack empty ") state))

theorem toNextFrame_true_lt (nfa : NFA) (s : SearchState)
  (h : toNextFrame nfa s = (true, s1))
    : s.countVisited < s1.countVisited
      ∨ s.countVisited = s1.countVisited ∧ s1.stack.length < s.stack.length := by
  unfold toNextFrame at h
  split at h
  split at h <;> try simp
  · rename_i stack _ sid _at heq
    let state : SearchState :=
      { stack := stack, visited := s.visited, countVisited := s.countVisited, sid := sid,
        input := s.input, «at» := _at,
        slots := s.slots, logEnabled := s.logEnabled,
        msgs := if s.logEnabled
                then s.msgs.push s!"{s.sid}: Step stack {stack} -> {sid}"
                else s.msgs, halfMatch := s.halfMatch,
        backtracks := s.backtracks }
    have h1 : state.countVisited < s1.countVisited ∨
          state.countVisited = s1.countVisited ∧ state.stack.length = s1.stack.length :=
        toNextFrameStep_true_lt_or_eq_lt nfa state h
    have hy : state.countVisited = s.countVisited := by simp_all
    rw [hy] at h1
    cases h1
    · rename_i h1
      simp [Or.inl h1]
    · rename_i heq h1
      have hs : stack.length < s.stack.length := Stack.pop?_some_lt s.stack heq
      rw [h1.right] at hs
      apply Or.inr
      simp [And.intro h1.left hs]
  · rename_i stack _ slot offset heq
    have h1 : stack.length < s.stack.length := Stack.pop?_some_lt s.stack heq
    have h2 : s.countVisited = s1.countVisited ∧ stack = s1.stack :=
      toNextFrameRestoreCapture_true_lt_or_eq_lt slot offset stack s h
    rw [h2.right] at h1
    apply Or.inr
    simp [And.intro (And.left h2) h1]
  · have hx : false = true := by simp_all [h]
    contradiction

theorem searchState_lexLt (s s1 : SearchState) (nfa : NFA) (h1 : s.countVisited < visitedSize s)
  (h2 : visitedSize s = visitedSize s1)
  (h : toNextFrame nfa s = (true, s1)) : unvisited s1 < unvisited s
            ∨ unvisited s1 = unvisited s ∧ s1.stack.length < s.stack.length := by
  unfold unvisited
  rw [← h2]
  have hx : s.countVisited < s1.countVisited
      ∨ s.countVisited = s1.countVisited ∧ s1.stack.length < s.stack.length :=
    toNextFrame_true_lt nfa s h
  cases hx
  · apply Or.inl
    rename_i hx
    simp [Nat.sub_lt_sub_left h1 hx]
  · apply Or.inr
    rename_i hx
    have hx1 : BoundedBacktracker.visitedSize s - s1.countVisited
        = BoundedBacktracker.visitedSize s - s.countVisited := by
      simp [hx.left]
    simp [And.intro hx1 hx.right]

private def collect_info (state : SearchState) : Array String :=
  let visited := Visited.getRefValue state.visited
  let values := visited |> Array.filter (· = 1) |>.size
  #[
      s!"backtracks {state.backtracks}",
      s!"visited array size {visited.size}",
      s!"count visited values {values}"
  ]

/-- BoundedBacktrack search -/
def backtrack (nfa : NFA)  (state : SearchState) : SearchState :=
  let frame := Frame.Step state.sid state.at
  let state := (withMsg (fun _ => s!"Backtrack sid {state.sid} charpos {state.at.pos}")
       {state with stack := Stack.push state.stack frame})
  let state := loop nfa state
  -- let state := {state with msgs := state.msgs ++ (collect_info state)}
  state
where
  loop (nfa : NFA) (state : SearchState) : SearchState :=
    match h : toNextFrame nfa state with
    | (true, state') =>
      -- let state := {state with backtracks := state.backtracks + 1}
      if h1 : state.countVisited < visitedSize state then
        if h2 : visitedSize state = visitedSize state' then
          have : Prod.lexLt
            (unvisited state', state'.stack.length) (unvisited state, state.stack.length) :=
            searchState_lexLt state state' nfa h1 h2 h
          loop nfa state'
        else state
      else  {state with msgs := state.msgs.push "overflow visited array"}
    | (false, state) => state
termination_by _ _ state =>
    (unvisited state, state.stack.length)
decreasing_by
  simp_wf
  unfold Prod.lexLt at this
  cases this
  · rename_i h1
    simp at h1
    apply Prod.Lex.left
    simp [h1]
  · rename_i h1
    simp at h1
    apply Prod.Lex.right'
    · simp [Nat.le_of_eq h1.left]
    · simp [h1.right]

/-- build pairs of subsequent slots -/
private def toPairs (slots : Array (Option String.Pos))
    : Array (Option (String.Pos × String.Pos)) :=
  if slots.size % 2 = 0
  then
    let slotsIdx := Array.mapIdx slots (fun i v => (i, v))
    let arr : Array (Option (String.Pos × String.Pos)) := slotsIdx.foldl (init := #[])
      fun acc (i, _) =>
        if i.val % 2 = 0 then acc
        else
          match slots.get? (i.val - 1), slots.get? (i.val) with
          | some (some v0), some (some v1) => acc.push (some (v0,v1))
          | some none, some none => acc.push none
          | _, _ => acc
    arr
  else #[]

private def dropLastWhile (arr : Array  α) (p :  α -> Bool) : Array α :=
  arr |> Array.foldr (init := #[]) fun a acc =>
    if acc.size = 0 && p a then acc
    else ⟨a :: acc.data⟩

/-- Search for the first match of this regex in the haystack given and return log msgs and
    the slots of each capture group. -/
def slots (s : Substring) («at» : String.Pos) (nfa : NFA) (logEnabled : Bool)
    : (Array String) × (Array (Option (String.Pos × String.Pos))) :=
  let state := backtrack nfa (SearchState.fromNfa nfa s «at» logEnabled)
  let pairs := toPairs state.slots
  (state.msgs, dropLastWhile pairs (·.isNone))
