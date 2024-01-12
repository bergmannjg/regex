import Regex.Syntax.Hir
import Regex.Nfa
import Regex.Compiler
import Regex.Utils
import Lean.Util

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

/-- pop last frame from stack  -/
@[inline] def pop? (stack : Stack) : Option (Frame × Stack) :=
  match stack with
  | [] => none
  | head :: tail => (head, tail)

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
structure SearchState where
  /-- Stack used on the heap for doing backtracking -/
  stack: Stack
  /-- The encoded set of (StateID, HaystackOffset) pairs that have been visited
    by the backtracker within a single search. -/
  visited : ST.Ref Nat Visited
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
  ⟨default, default, 0, "".toSubstring, default, #[], false, #[], none, 0⟩

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

@[inline] private def step_empty (next : StateID) (state : SearchState) : SearchState :=
  withMsg (fun _ => s!"{state.sid}: Empty -> {next}") {state with sid := next}

@[inline] private def step_look (look : Look) (next : StateID)
     (state : SearchState) :SearchState :=
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

/-- execute next step in NFA if state not already visited. Returns true if steps available. -/
private def toNextStep (nfa : NFA) : SearchStateM Bool := do
  let state ← get
  let isVisited ← Visited.checkVisited
  if isVisited then pure false
  else
    if hs : state.sid < nfa.states.size then
      let state :=
        match nfa.states.get ⟨state.sid, hs⟩ with
        | .Empty next => step_empty next state
        | .Look look next => step_look look next state
        | .ByteRange trans => step_byterange trans state
        | .SparseTransitions transitions => step_sparse_transitions nfa transitions state
        | .Union alts => step_union alts state
        | .UnionReverse alts => step_union_reverse alts state
        | .BinaryUnion alt1 alt2 => step_binary_union alt1 alt2 state
        | .Capture next _ _ slot => step_capture next slot state
        | .Match pattern_id => step_match pattern_id state
      set state
      pure true
    else pure false

/-- execute next steps in NFA. -/
private partial def steps (nfa : NFA) : SearchStateM Unit := do
  if ← toNextStep nfa then steps nfa else pure ()

/-- execute steps in next frame. Returns false if no more frame available
    or match is found. -/
private def toNextFrame (nfa : NFA) : SearchStateM Bool := do
  let state ← get
  match Stack.pop? state.stack with
  | some (frame, stack) =>
      match frame with
      | .Step sid «at» =>
        let state := (withMsg (fun _ => s!"{state.sid}: Step stack {stack} -> {sid}")
                      {state with sid := sid, «at» := «at», stack := stack})
        set state
        steps nfa
        let state ← get
        match state.halfMatch with
        | some _ => pure false
        | none =>
          if state.logEnabled then
            let state := (withMsg
              (fun _ => s!"{state.sid}: backtrackLoop with stack {state.stack}") state)
            set state
          pure true
      | .RestoreCapture slot offset =>
        if h : slot < state.slots.size
        then
          let slots :=
            if state.slots.get ⟨slot,h⟩ != offset
            then state.slots.set ⟨slot,h⟩ offset
            else state.slots
          let state := {state with slots := slots, stack := stack}
          let state := (withMsg
            (fun _ =>
                s!"{state.sid}: RestoreCapture slots {slots} stack {stack}") state)
          set state
          pure true
        else pure false
  | none =>
    let state := (withMsg (fun _ => s!"pop? failed {state.sid}") state)
    set state
    pure false

private partial def backtrackLoop (nfa : NFA) : SearchStateM Unit := do
  if ← toNextFrame nfa
  then
    -- modify (fun state => {state with backtracks := state.backtracks + 1})
    backtrackLoop nfa
  else pure ()

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
  let (_, state) := backtrackLoop nfa state
  -- let state := {state with msgs := state.msgs ++ (collect_info state)}
  state

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
