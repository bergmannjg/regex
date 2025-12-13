import Lean.Util

import Batteries.Data.Nat.Lemmas
import Batteries.Tactic.Exact
import Batteries.Data.String

import Regex.Basic
import Regex.Syntax.Hir
import Regex.Nfa
import Regex.Compiler
import Regex.Utils
import Regex.Data.Array.Basic
import Regex.Data.Array.Lemmas
import Regex.Data.String.Lemmas
import Regex.Data.List.Lemmas
import Regex.Data.Nat.Basic
import Regex.Data.String.Basic


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
  st (Void.mk default) |>.val

instance {α β : Type} [Inhabited β] : Inhabited (ST.Ref β (Array α)) where
  default := mkRef #[]

/-- get array of reference -/
def getRefValue {α β : Type} [Inhabited β] (ref : ST.Ref β (Array α)) : Array α :=
  let st := ST.Prim.Ref.get ref
  st (Void.mk default) |>.val

/-- modify array, try to perform the update destructively -/
def modifyRefValue {α β : Type} [Inhabited β] (ref : ST.Ref β (Array α)) (index : Nat) (value : α)
  (f : ST.Out β Unit → Bool := fun _ => True)
    : ST.Ref β (Array α)  :=
  let st := ST.Prim.Ref.modify ref (fun arr =>
    let arr := dbgTraceIfShared "array" arr
    if h : index < arr.size
    then arr.set index value h
    else arr)

  if f (st (Void.mk default)) then ref else default -- force to run `st`

end Array.Ref

/-- Char position in a slice of some underlying string. -/
structure CharPos (s : String.Slice) where
  /-- current position -/
  pos : String.Slice.Pos s := s.startPos
  /-- char at current position -/
  curr? : Option Char := none
  /-- char at previous position -/
  prev? : Option Char := none

abbrev CharPos.Pair s := { p : (String.Slice.Pos s) × (String.Slice.Pos s) // p.1 ≤ p.2 }

instance : Inhabited (CharPos default) :=
  ⟨default, none, none⟩

instance : ToString (CharPos s) where
  toString cp := s!"{cp.pos.offset} {cp.curr?} {cp.prev?}"

instance : ToString (String.Slice.Pos s) where
  toString pos := s!"{pos.offset}"

namespace CharPos

/-- create a CharPos from `s` and position `«at»` -/
def create (s : String.Slice) («at» : String.Slice.Pos s)
    : CharPos s :=
  let prev? := if _ : «at» = s.startPos then none
    else some ((«at».prev (by assumption)).get (by exact String.Slice.Pos.prev_ne_endPos))
  if _ : «at» = s.endPos
  then ⟨«at», none,  prev?⟩
  else ⟨«at», «at».get (by assumption),  prev?⟩

/-- to prev position of `cp` -/
def prev (cp : CharPos s) : Option (CharPos s) :=
  if h : cp.pos ≠ s.startPos
  then some (create s (cp.pos.prev h))
  else none

def prevn (offset : Nat) (cp : CharPos s) : Option (CharPos s) :=
  if offset ≤ cp.pos.offset.byteIdx then loop offset cp else none
  where loop (offset : Nat) (cp : Option (CharPos s)) : Option (CharPos s) :=
    if 0 < offset
    then Option.bind cp (fun cp => Option.bind (prev cp) (loop (offset - 1) ·))
    else cp

/-- to next position of `cp` -/
def next (cp : CharPos s) : CharPos s :=
  if h : cp.pos = s.endPos then cp
  else
    match cp.curr? with
    | some _ =>
      let nextPos := cp.pos.next h
      {cp with pos := nextPos, prev? := cp.curr?, curr? := nextPos.get?}
    | none => cp

/-- is CharPos at start position -/
def atStart (cp : CharPos s) : Bool :=
  cp.pos = s.startPos

/-- is CharPos at stop position -/
def atStop (cp : CharPos s) : Bool :=
  cp.pos = s.endPos

end CharPos

/-- Represents a stack frame on the heap while doing backtracking. -/
inductive Frame (n : Nat) (s : String.Slice) where
  /-- Look for a match starting at `sid` and the given position in the haystack. -/
  | Step (sid: Fin n) («at»: CharPos s) : Frame n s
  /-- Reset the given `slot` to the given `pos` (which might be `None`). -/
  | RestoreCapture (role : Capture.Role) (slot: Nat) (pos: Option (s.Pos)) : Frame n s

instance : ToString $ Frame n s where
  toString frame :=
    match frame with
    | .Step sid «at» => s!"Step({sid}, {«at».pos.offset})"
    | .RestoreCapture role _ offset =>
        match offset with
        | some pos => s!"Restore({role}, slot: {pos.offset.byteIdx})"
        | none => s!"Restore({role}, slot: none)"

/-- A representation of "half" of a match reported by a DFA. -/
structure HalfMatch (s :  String.Slice) where
    /-- The pattern ID. -/
    pattern: PatternID
    /-- The offset of the match. -/
    offset: s.Pos

instance : Inhabited (HalfMatch s) := ⟨0, default⟩

instance : ToString (HalfMatch s) where
  toString a := s!"pattern {a.pattern}, offset {a.offset}"

private def compare (a : Fin n × String.Pos.Raw) (b : Fin n × String.Pos.Raw) : Ordering :=
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

/-- SlotEntry consists of slot, group and char pos in `s` -/
abbrev SlotEntry s := Nat × Nat × (Option (String.Slice.Pos s))

@[simp] def SearchState.Slots.Valid (slots : Array (SlotEntry s)) :=
  (∀ i : Fin slots.size, i.val = slots[i].1)
  ∧ (∀ slot : { slot : SlotEntry s // slot ∈ slots ∧ slot.1 % 2 = 1 }, slot.val.1 = slot.val.2.1 * 2 + 1)
  ∧ (∀ slot : { slot : SlotEntry s // slot ∈ slots ∧ slot.1 = slot.2.1 * 2 + 1 },
    ∃ slot' ∈ slots, (slot.val.2.1 = slot'.2.1 ∧ slot'.1 = slot'.2.1 * 2))

abbrev SlotsValid s := {slots : Array (SlotEntry s) // SearchState.Slots.Valid slots}

theorem valid_of_range_map (s : String.Slice) (slots : Array (SlotEntry s))
  (f : Nat → SlotEntry s) (hf : f = (fun i => (i, i.div 2, none)))
  (h : (List.range slots.size).map f = slots.toList)
    : SearchState.Slots.Valid slots := by
  simp
  rw [hf] at h
  and_intros
  · intro i
    have hMem (i : Fin slots.size) : ((List.range slots.size).map f)[i] = f i.val := by grind
    grind
  · intros
    expose_names
    have hMem (a : SlotEntry s) (h : a ∈ (List.range slots.size).map f) : a.2.1 = a.1.div 2 := by
      grind
    simp_all
    have := hMem a a_1 b (by simp_all)
    simp_all
    rw [Nat.mul_comm]
    have := @Nat.div_add_mod a 2
    rw [h_2] at this
    exact id (Eq.symm this)
  · intros
    expose_names
    exact ⟨a - 1, ⟨a_1, by
      and_intros
      · exact ⟨b, by
          have : (a, a_1, b) ∈ (List.range slots.size).map f := by grind
          have h : a_1 = (a - 1).div 2 := by
            rw [h_2]
            exact Eq.symm (@Nat.div_eq_of_eq_mul_left 2 (a_1 * 2) a_1 (by grind) rfl)
          have hMem (a :  SlotEntry s) (h1 : a.1 < slots.size ∧ a.2.1 = a.1.div 2) (h2 : a.2.2 = none)
              : a ∈ (List.range slots.size).map f := by
            grind
          have := hMem (a - 1, a_1, b) (And.intro (by grind) h)
          grind⟩
      · grind
      · grind⟩⟩

private theorem mem_le_max (xs : Array Nat) (h : xs.max? = some m)
    : ∀ a ∈ xs, (Ord.toLE instOrdNat).le a m := by
  exact Array.mem_le_max xs h Nat.toLT_iff Nat.toLT_notLt

namespace Capture

def toSlot (c : Capture) :=
  match c.role with
  | .Start => c.group * 2
  | .End => c.group * 2 + 1

end Capture

def toSlotEntry (c : Capture) : SlotEntry s :=
  (Capture.toSlot c, c.group, none)

theorem valid_map_of_valid (s : String.Slice)
  (captures : Array Capture) (h : NFA.Capture.Valid captures)
  (slots : Array (SlotEntry s)) (hs : slots = captures.map (@toSlotEntry s))
    : ∀ slot : { slot : SlotEntry s // slot ∈ slots ∧ slot.1 = slot.2.1 * 2 + 1},
    ∃ slot' ∈ slots, (slot.val.2.1 = slot'.2.1 ∧ slot'.1 = slot'.2.1 * 2) := by
  intro ⟨slot, ⟨h1, h2⟩⟩
  have : slot ∈ Array.map toSlotEntry captures := by grind
  have ⟨c, ⟨h1, h2⟩⟩ : ∃ c, c ∈ captures ∧ (@toSlotEntry s) c = slot := Array.mem_map.mp this
  unfold toSlotEntry Capture.toSlot at h2
  split at h2
  · grind
  · have h := NFA.Capture.Valid.forall h
    have ⟨c', h'⟩ := h ⟨c, by grind⟩
    let slot' := (@toSlotEntry s) c'
    have heq : c'.group = slot'.snd.fst := rfl
    exact ⟨slot', by
      and_intros
      · have : c' ∈ captures := h'.left
        have : slot' ∈ Array.map (@toSlotEntry s) captures := Array.mem_map_of_mem this
        simp_all
      · have : c.group = slot.snd.fst := by rw [← h2]
        simp_all
      · have : slot' = (@toSlotEntry s) c' := rfl
        rw [this]
        simp [toSlotEntry, Capture.toSlot]
        split <;> simp_all⟩

theorem mem_range_map_of_mem (captures : Array Capture)
  (slots : Array (SlotEntry s))
  (f : Nat → SlotEntry s) (hf : f = (fun i => (i, i.div 2, none)))
  (heq: (Array.range slots.size).map f = slots)
  (hsize : slots.size = match (captures.map Capture.toSlot).max? with | some m => m + 1 | none => 0)
    : ∀ capture ∈ captures, toSlotEntry capture ∈ slots := by
  rw [← heq]
  intro capture hMem
  have : ∃ i, i ∈ Array.range slots.size ∧ f i = toSlotEntry capture := by
    simp [toSlotEntry, Capture.toSlot]
    split
    · exact ⟨capture.group * 2, by
        split at hsize
        · and_intros
          · expose_names
            have : ∀ a ∈ (Array.map Capture.toSlot captures), a ≤ m := by
              intro a ha
              apply (Nat.toLE_iff_le a m).mp
              exact mem_le_max (Array.map Capture.toSlot captures) heq_2 a ha
            have := Array.forall_mem_map.mp this capture hMem
            simp [Capture.toSlot] at this
            grind
          · simp_all
            exact Nat.mul_div_cancel capture.group (by simp)
        · rename_i heq
          unfold Array.max? Array.min? at heq
          simp_all⟩
    · exact ⟨capture.group * 2 + 1, by
        split at hsize
        · and_intros
          · expose_names
            have : ∀ a ∈ (Array.map Capture.toSlot captures), a ≤ m := by
              intro a ha
              apply (Nat.toLE_iff_le a m).mp
              exact mem_le_max (Array.map Capture.toSlot captures) heq_2 a ha
            have := Array.forall_mem_map.mp this capture hMem
            simp [Capture.toSlot] at this
            grind
          · simp_all
            have h1 : (capture.group * 2 + 1) % 2 = 1 := by grind
            have h2 := @Nat.div_eq_sub_mod_div (capture.group * 2 + 1) 2
            rw [h1] at h2
            have h3 : (capture.group * 2 + 1) - 1 = capture.group * 2 := by grind
            rw [h3] at h2
            have h3 := @Nat.mul_div_cancel capture.group 2 (by simp)
            simp_all
            assumption
        · rename_i heq
          unfold Array.max? Array.min? at heq
          simp_all⟩
  grind

/-- State of the backtracking search -/
@[ext] structure SearchState (n : Nat) (input : String.Slice) where
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
  slots: Array (SlotEntry input)
  /-- slots are valid -/
  slotsValid: SearchState.Slots.Valid slots
  /-- recent captures of capture groups -/
  recentCaptures: Array (Option (String.Slice.Pos input × String.Slice.Pos input))
  /-- is logging enabled -/
  logEnabled : Bool
  /-- log msgs -/
  msgs: Array String
  /-- HalfMatch -/
  halfMatch: Option (HalfMatch input)
  /-- count of backtracks -/
  backtracks : Nat

namespace SearchState

/-- create the SearchState from an NFA -/
def fromNfa (nfa : Checked.NFA) (input : String.Slice)
  («at» : String.Slice.Pos input) (logEnabled : Bool) (h : 0 < nfa.n)
    : SearchState nfa.n input :=
  let max := match (nfa.captures.map Capture.toSlot).max? with | some max => max + 1 | none => 0
  let f : Nat → SlotEntry input := (fun i => (i, i.div 2, none))
  let slots := Array.range max |> Array.map f
  have hSlotsValid := valid_of_range_map input slots f (by simp +zetaDelta) (by simp +zetaDelta)
  let recentCaptures : Array $ Option (String.Slice.Pos input × String.Slice.Pos input) :=
    slots |> Array.map (fun (_, g, _) => g) |> Array.unique |> Array.map (fun _ => none)

  -- toSlotEntry of nfa.captures is a member of slots
  have := mem_range_map_of_mem nfa.captures slots f (by grind) (by grind) (by grind)
  -- toSlotEntry of nfa.captures gives valid slots
  have := valid_map_of_valid input nfa.captures nfa.capturesValid

  {
    stack := default
    visited := Array.Ref.mkRef <|
      Array.replicate ((nfa.states.size + 1)
                      * (input.endPos.offset.byteIdx - input.startPos.offset.byteIdx + 1)) 0
    countVisited := 0
    sid := ⟨0, h⟩
    «at» := CharPos.create input «at»
    slots := slots
    slotsValid := hSlotsValid,
    recentCaptures := recentCaptures
    logEnabled := logEnabled
    msgs := #[]
    halfMatch := none
    backtracks := 0
  }

theorem slots_of_modify_valid (slots : Array (SlotEntry s)) (h : Slots.Valid slots) (slot: Nat)
  (f : Option (String.Slice.Pos s) → Option (String.Slice.Pos s))
    : Slots.Valid (slots.modify slot (Prod.map id (Prod.map id f))) := by
  let mf : SlotEntry s → SlotEntry s := fun (i, g , v) => (i, g, if i = slot then f v else v)
  have : slots.map mf = slots.modify slot (Prod.map id (Prod.map id f)) := by
    simp [Array.map_eq_iff]
    intro i
    if hlt : i < (slots.modify slot (Prod.map id (Prod.map id f))).size
    then
      have hlt' : i < slots.size := by grind
      have : Option.map mf slots[i]? = some (mf slots[i]) := by simp_all
      have : (slots.modify slot (Prod.map id (Prod.map id f)))[i]?
              = some (slots.modify slot (Prod.map id (Prod.map id f)))[i] := by simp_all
      simp_all
      have := Array.getElem_modify hlt
      rw [this]
      simp [mf, Prod.map]
      split
      · have := h.left ⟨i, hlt'⟩
        grind
      · split
        · have := h.left ⟨i, hlt'⟩
          grind
        · rfl
    else
      grind
  rw [← this]
  simp at h
  simp [mf]
  grind

theorem slots_of_map_valid (slots : Array (SlotEntry s)) (h : Slots.Valid slots)
  (f : SlotEntry s → SlotEntry s)
  (hf : ∀ x : SlotEntry s, (f x).fst = x.fst ∧ (f x).snd.fst = x.snd.fst)
    : Slots.Valid (slots.map f) := by
  unfold Slots.Valid
  simp
  simp at h
  have : (fun x => (x.fst, x.2.fst)) ∘ f = (fun x => (x.fst, x.2.fst)) := by
    apply funext
    simp [hf]
  grind

end SearchState

instance : Nonempty Visited := ⟨#[]⟩

namespace Visited

/-- get encoded index of Fin n and CharPos in visited array -/
def index (sid : Fin n) (cp : CharPos s) : Nat :=
  sid * (s.endPos.offset.byteIdx - s.startPos.offset.byteIdx + 1)
  + cp.pos.offset.byteIdx - s.startPos.offset.byteIdx

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
      have : k * x ≤ b1 := Nat.le.intro (id (Eq.symm this))
      have : x ≤ k * x := Nat.le_mul_of_pos_left x hk.left
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
      have : k * x ≤ b2 := Nat.le.intro this
      have : x ≤ k * x := Nat.le_mul_of_pos_left x hk.left
      omega
    contradiction
  else
    have : a1 = a2 := by omega
    rw [this] at h
    omega

/-- `index` is injective. -/
theorem index_injective (sid1 sid2 : Fin n) (cp1 cp2 : CharPos s)
  (heq : index sid1 cp1 = index sid2 cp2)
    : sid1.val = sid2.val ∧ cp1.pos.offset.byteIdx = cp2.pos.offset.byteIdx := by
  unfold index at heq

  have hp1 : s.startPos.offset.byteIdx ≤ cp1.pos.offset.byteIdx
              ∧ cp1.pos.offset.byteIdx ≤ s.endPos.offset.byteIdx := by
    and_intros
    · simp
    · apply cp1.pos.isValidForSlice.le_utf8ByteSize
  have hp2 : s.startPos.offset.byteIdx ≤ cp2.pos.offset.byteIdx
              ∧ cp2.pos.offset.byteIdx ≤ s.endPos.offset.byteIdx := by
    and_intros
    · simp
    · apply cp2.pos.isValidForSlice.le_utf8ByteSize
  have : s.startPos.offset.byteIdx ≤ s.endPos.offset.byteIdx := Nat.le_trans hp1.left hp1.right
  have : s.startPos.offset.byteIdx ≤ s.endPos.offset.byteIdx := Nat.le_trans hp2.left hp2.right
  have : s.startPos.offset.byteIdx ≤ cp1.pos.offset.byteIdx := hp1.left
  have : s.startPos.offset.byteIdx ≤ cp2.pos.offset.byteIdx := hp2.left
  generalize hx : (s.endPos.offset.byteIdx - s.startPos.offset.byteIdx + 1) = x at heq
  have hlt1 : cp1.pos.offset.byteIdx - s.startPos.offset.byteIdx < x := by
    simp [← hx]
    suffices cp1.pos.offset.byteIdx - s.startPos.offset.byteIdx
             ≤ s.endPos.offset.byteIdx - s.startPos.offset.byteIdx by
      exact Nat.lt_add_one_of_le this
    exact Nat.sub_le_sub_right hp1.right s.startPos.offset.byteIdx
  have hlt2 : cp2.pos.offset.byteIdx - s.startPos.offset.byteIdx < x := by
    simp [← hx]
    suffices cp2.pos.offset.byteIdx - s.startPos.offset.byteIdx
             ≤ s.endPos.offset.byteIdx - s.startPos.offset.byteIdx by
      exact Nat.lt_add_one_of_le this
    exact Nat.sub_le_sub_right hp2.right s.startPos.offset.byteIdx
  have h : sid1.val * x + (cp1.pos.offset.byteIdx - s.startPos.offset.byteIdx)
           = sid2.val * x + (cp2.pos.offset.byteIdx - s.startPos.offset.byteIdx) := by omega
  have := @eq_of_linear_eq sid1.val (cp1.pos.offset.byteIdx - s.startPos.offset.byteIdx)
            sid2.val (cp2.pos.offset.byteIdx - s.startPos.offset.byteIdx) x
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
    if visited[index]'h != 0 then (true, state)
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
  exact hx

theorem checkVisited'_true_eq (s : SearchState n input) (h : checkVisited' s = (true, s1))
    : s.countVisited = s1.countVisited ∧ s.stack.length = s1.stack.length := by
  unfold checkVisited' at h
  split at h
  split at h <;> simp_all

end Visited

/-- build pairs of slots which correspond to same capture group via `slotsValid`. -/
private def toPairs (slots : Array (SlotEntry s)) (groups : Array Nat)
  (h : SearchState.Slots.Valid slots) : Array (Option (CharPos.Pair s)) :=
  slots.attach.foldl (init := #[]) (fun acc slot =>
    if _ : slot.val.1 % 2 = 1 -- has Capture.Role.End
    then
      let g1 := slot.val.2.1
      let p := fun (e : SlotEntry s) => g1 = e.2.1 ∧ e.1 = e.2.1 * 2
      let idx := slots.findIdx p
      have : idx < slots.size := by simp at h; grind
      let slot' := slots[idx]
      match _ : slot', slot.val.2.2 with
      | (_, g0, some v0), some v1 =>
          have : g0 = g1 := by
            have heq : slot.val.2.1 = g1 := rfl
            have := @Array.findIdx_getElem (SlotEntry s) p slots (by grind)
            simp at this
            grind
          let v0 := if groups.contains g0 then v1 else v0
          if hle : v0.offset ≤ v1.offset -- todo: prove it
          then acc.push (some ⟨(v0, v1), hle⟩)
          else acc.push none
      | (_, _, none), none => acc.push none
      | _, _ => acc
    else
      acc)

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
  match state.at.prevn offset with
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
@[inline] private def step_eat_to_last (sid next : Fin n) (state : SearchState n s)
    : SearchState n s :=
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

@[inline] private def restore_frame (stack : List (Frame n s)) (state : SearchState n s)
    : SlotsValid s  :=
  stack |> List.foldl (fun slots frame =>
      match frame with
      | .RestoreCapture _ slot v =>
        if slot < slots.val.size
        then
          let f := fun _ => v
          let slots' := slots.val.modify slot (Prod.map id (Prod.map id f))
          ⟨slots', SearchState.slots_of_modify_valid slots.val slots.property slot f⟩
        else slots
      | _ => slots) ⟨state.slots, state.slotsValid⟩

@[inline] private def step_change_frame_step (f t : Fin n) (state : SearchState n s)
    : SearchState n s :=
  let cond := (fun (s : Frame n s) => match s with | .Step f' _ => f != f' | _ => true)
  let stackBeforeSid := state.stack |> List.takeWhile cond

  let slots : SlotsValid s := restore_frame stackBeforeSid state
  let stack := state.stack |> List.dropWhile cond
  match stack with
  |  .Step _ «at» :: stack' =>
    let stack := Frame.Step t «at» :: stack'
    withMsg (fun _ => s!"{state.sid}: ChangeFrameStep stack {stack} slots {slots}")
                      {state with stack := stack, slots := slots.val, slotsValid := slots.property}
  | _ =>
    withMsg (fun _ => s!"{state.sid}: ChangeFrameStep failed ") state

@[inline] private def step_remove_frame_step (sid : Fin n) (state : SearchState n s)
    : SearchState n s :=
  let cond := (fun (s : Frame n s) => match s with | .Step f' _ => sid != f' | _ => true)
  let stackBeforeSid := state.stack |> List.takeWhile cond

  let slots : SlotsValid s := restore_frame stackBeforeSid state
  let stack := state.stack |> List.dropWhile cond

  match stack with
  |  .Step _ _ :: stack' =>
    withMsg (fun _ => s!"{state.sid}: RemoveFrameStep {sid} stack {stack'} slots {slots}")
                      {state with stack := stack', slots := slots.val, slotsValid := slots.property}
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
      | _ => (withMsg (fun _ => s!"{state.sid}: Look.EndWithOptionalLF failed at pos"
                                    ++ "{state.at} atStop {state.at.next.atStop}") state)
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
            && (state.at.pos.offset.byteIdx = 0 || state.at.prev?.any (· != '\r'))
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
      let state := (withMsg (fun _ =>
                    s!"{state.sid}: Look.WordUnicodeNegate -> {next}") {state with sid := next})
      state
    else state
  | .WordStartUnicode =>
    if is_word_start_unicode state then
      let state := (withMsg (fun _ => s!"{state.sid}: Look.WordStartUnicode -> {next}")
                       {state with sid := next})
      state
    else state
  | .WordEndUnicode =>
    if is_word_end_unicode state then
      let state := (withMsg (fun _ => s!"{state.sid}: Look.WordEndUnicode -> {next}")
                        {state with sid := next})
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
      let state := (withMsg (fun _ => s!"{state.sid}: Look.PreviousMatch -> {next}")
                   {state with sid := next})
      state
    else
      (withMsg
        (fun _ => s!"PreviousMatch failed at pos {state.at.pos}") state)
  | .ClearMatches =>
    if h : 0 < state.slots.size then
      let frame : Frame n s := Frame.RestoreCapture Capture.Role.Start 0 (state.slots[0]'h).2.2
      let stack := Stack.push state.stack frame

      let f := fun (s, g, _) =>
        if s = 0 then (s, g, state.at.pos) else (s, g, none)
      let slots := state.slots.map f
      (withMsg (fun _ => s!"{state.sid}: Look.ClearMatches stack {stack} slots {slots} -> {next}")
                          {state with stack := stack, slots := slots, sid := next,
                                      slotsValid := SearchState.slots_of_map_valid
                                                      state.slots state.slotsValid f
                                                      (by
                                                        intro x
                                                        unfold f
                                                        repeat split <;> try simp_all)})
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

@[inline] private def step_backreference_loop (s : String.Slice) (pos : s.Pos) (case_insensitive : Bool)
  (cp : CharPos input) : Option (CharPos input) :=
  if h : pos ≠ s.endPos
  then
    if cp.atStop then none else
    let c := pos.get h
    let cf := if case_insensitive
      then
        match Unicode.case_fold_char c with
        | #[⟨(cU, _), _⟩, ⟨(cL, _), _⟩] => if cU = c then cL else cU
        | _ => c
      else c
    if cp.curr?.any (fun x => x = c || x = cf)
    then step_backreference_loop s (pos.next h) case_insensitive cp.next
    else none
  else some cp
termination_by pos.offset.byteDistance s.endPos.offset

@[inline] private def step_backreference (b : Nat) (case_insensitive : Bool) (next : Fin n)
  (state : SearchState n s) : SearchState n s :=
  if h : b < state.recentCaptures.size then
    match state.recentCaptures[b]'h with
    | some (f, t) =>
        if h : f.offset ≤ t.offset then
          let slice := s.replaceStartEnd f t h
          match step_backreference_loop slice slice.startPos case_insensitive state.«at» with
          | some cp =>
              (withMsg (fun _ => s!"{state.sid}: Backreference {b} '{slice}' matched from charpos"
                                    ++ "{state.at} to {cp} -> {next}")
                  {state with sid := next, «at» := cp })
          | none =>
            (withMsg (fun _ =>
              s!"{state.sid}: Backreference '{b}' failed at charpos {state.at}, no match with '{s.startPos},{s.endPos}'")
              state)
        else
            (withMsg (fun _ =>
              s!"{state.sid}: Backreference '{b}' failed at charpos {state.at}, '{f} > {t}'")
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
        (withMsg (fun _ => s!"{state.sid}: SparseTransitions '{encodeChar? state.at.curr?}' "
                              ++ "matched at charpos {state.at} -> {t.next}")
            {state with sid := t.next, «at» := next})
    | none =>
      (withMsg
        (fun _ =>
            s!"{state.sid}: SparseTransitions failed  at charpos {state.at}") state)

@[inline] private def step_union (alts : Array $ Fin n) (state : SearchState n s) : SearchState n s :=
  if h : alts.size = 2
  then
    let alt1 := alts[0]
    let alt2 := alts[1]
    let stack := Stack.push state.stack (Frame.Step alt2 state.at)
    (withMsg (fun _ => s!"{state.sid}: Union stack {stack} -> {alt1}")
      {state with sid := alt1, stack := stack})
  else
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
  if h : alts.size = 2
  then
    let alt1 := alts[0]
    let alt2 := alts[1]
    let stack := Stack.push state.stack (Frame.Step alt1 state.at)
    (withMsg (fun _ => s!"{state.sid}: Union_Reverse stack {stack} -> {alt2}")
      {state with sid := alt2, stack := stack})
  else
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
  if slot < state.slots.size
  then
    let f := fun _ => some $ state.at.pos
    let slots := state.slots.modify slot ((Prod.map id (Prod.map id f)))
    (withMsg (fun _ => s!"{state.sid}: ChangeCaptureSlot slot {slot} slots {slots} -> {next}")
                {state with sid := next, slots := slots,
                            slotsValid := SearchState.slots_of_modify_valid state.slots
                                            state.slotsValid slot f})
  else
    (withMsg (fun _ => s!"{state.sid}: ChangeCaptureSlot slot {slot} invalid")
                state)

@[inline] private def step_capture (role : Capture.Role) (next : Fin n) (group slot : Nat)
     (state : SearchState n s) : SearchState n s :=
  let (stack, slots, recentCaptures) :=
    if h : slot < state.slots.size
    then
      let frame := Frame.RestoreCapture role slot (state.slots[slot]'h).2.2
      let f := fun _ => some $ state.at.pos
      let slots := state.slots.modify slot ((Prod.map id (Prod.map id f)))
      have hLength := @Array.size_modify _ _ _ (Prod.map id (Prod.map id f))
      let slots : SlotsValid s := ⟨slots, SearchState.slots_of_modify_valid state.slots
                                            state.slotsValid slot f⟩
      let recentCaptures :=
        if _ : slot % 2 = 1 then -- has Capture.Role.End
          have := Nat.lt_of_lt_of_eq h (Eq.symm hLength)
          match _ : slots.val[slot] with
          | (s1, g1, v1) =>
            let p := fun (e : SlotEntry s) => g1 = e.2.1 ∧ e.1 = e.2.1 * 2
            have : slots.val.findIdx p < slots.val.size := by
              have hp := slots.property
              simp at hp
              have := hp.left ⟨slot, by grind⟩
              grind
            match _ : slots.val[slots.val.findIdx p] with
            | (s0, g0, v0) =>
              have : g0 = g1 := by
                have := @Array.findIdx_getElem (SlotEntry s) p slots.val (by grind)
                simp [p] at this
                grind
              let recentCapture :=
                  match h0 : v0, v1  with
                  | some v0, some v1 => some (v0, v1)
                  | _, _ => none

              if h : g1 < state.recentCaptures.size then state.recentCaptures.set g1 recentCapture h
              else state.recentCaptures
        else state.recentCaptures
      (Stack.push state.stack frame, slots, recentCaptures)
    else (state.stack, ⟨state.slots, state.slotsValid⟩, state.recentCaptures)
  (withMsg (fun _ => s!"{state.sid}: Capture{role} group {group} stack {stack} slots {slots} "
                        ++ "recentCaptures {recentCaptures} -> {next}")
                {state with sid := next, slots := slots, stack := stack,
                            recentCaptures := recentCaptures, slotsValid := by
                              have := state.slotsValid
                              exact slots.property})

@[inline] private def step_match (pattern_id : PatternID)
     (state : SearchState n s) : SearchState n s :=
  (withMsg (fun _ => s!"Match {state.sid}")
          {state with halfMatch := some ⟨pattern_id, state.at.pos⟩})

/-- execute next step in NFA if state not already visited -/
@[inline] private def toNextStep (nfa : Checked.NFA) (state : Checked.State nfa.n)
    (searchState : SearchState nfa.n s) : SearchState nfa.n s :=
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
  | .Capture role next _ g => step_capture role next g (Capture.toSlot ⟨role, g⟩) searchState
  | .Match pattern_id => step_match pattern_id searchState

private theorem witMsg_countVisited_eq (msg : Unit -> String) (s1 s2 : SearchState n s)
  (h : withMsg msg s1 = s2) : s1.countVisited = s2.countVisited := by
  simp [withMsg, SearchState.ext_iff] at h
  split at h <;> simp_all

private theorem step_empty_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_empty next s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_empty, withMsg, SearchState.ext_iff] at h
  split at h <;> simp_all only [Bool.true_eq]

private theorem step_next_char_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_next_char offset next s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_next_char, withMsg, SearchState.ext_iff] at h
  repeat split at h <;> simp_all only [Bool.true_eq]

private theorem step_fail_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_fail s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_fail, withMsg, SearchState.ext_iff] at h
  split at h <;> simp_all only [Bool.true_eq]

private theorem step_eat_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_eat mode next s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_eat, step_eat_until, step_eat_to_last, withMsg, SearchState.ext_iff] at h
  repeat split at h <;> try simp_all only [Bool.true_eq]

private theorem step_change_frame_step_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_change_frame_step f t s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_change_frame_step, withMsg, SearchState.ext_iff] at h
  repeat split at h <;> simp_all only [Bool.true_eq]

private theorem step_remove_frame_step_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_remove_frame_step sid s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_remove_frame_step, withMsg, SearchState.ext_iff] at h
  repeat split at h <;> simp_all only [Bool.true_eq ]

private theorem step_look_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_look look next s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_look, withMsg, SearchState.ext_iff] at h
  repeat (split at h <;> try simp_all only [Bool.true_eq])

private theorem step_backreference_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_backreference b c next s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_backreference, withMsg, SearchState.ext_iff] at h
  repeat split at h <;> try simp_all only [Bool.true_eq]

private theorem step_byterange_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_byterange t s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_byterange, withMsg, SearchState.ext_iff] at h
  repeat split at h <;> try simp_all only [Bool.true_eq]

private theorem step_sparse_transitions_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_sparse_transitions nfa t s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_sparse_transitions, withMsg, SearchState.ext_iff] at h
  repeat split at h <;> try simp_all only [Bool.true_eq]

private theorem step_union_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_union alts s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_union, withMsg, SearchState.ext_iff] at h
  repeat split at h <;> try simp_all only [Bool.true_eq]

private theorem step_union_reverse_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_union_reverse alts s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_union_reverse, withMsg, SearchState.ext_iff] at h
  repeat split at h <;> try simp_all only [Bool.true_eq]

private theorem step_binary_union_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_binary_union alt1 alt2 s1 = s2) : s1.countVisited = s2.countVisited := by
  simp only [step_binary_union, withMsg, SearchState.ext_iff] at h
  split at h <;> try simp_all only [Bool.true_eq]

private theorem step_capture_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_capture role next g slot s1 = s2) : s1.countVisited = s2.countVisited := by
  unfold step_capture withMsg at h
  repeat split at h <;> (try simp [SearchState.ext_iff] at h; exact h.right.right.left)

theorem step_match_countVisited_eq (s1 s2 : SearchState n s)
  (h : step_match p s1 = s2) : s1.countVisited = s2.countVisited := by
  unfold step_match withMsg at h
  split at h <;> (try simp [SearchState.ext_iff] at h; exact h.right.right.left)

theorem toNextStep_countVisited_eq (nfa : Checked.NFA) (state : Checked.State nfa.n)
  (s1 s2 : SearchState nfa.n s) (h : toNextStep (nfa : Checked.NFA) state s1 = s2)
    : s1.countVisited = s2.countVisited := by
  unfold toNextStep at h
  split at h
  · exact step_empty_countVisited_eq s1 s2 h
  · exact step_next_char_countVisited_eq s1 s2 h
  · exact step_fail_countVisited_eq s1 s2 h
  · exact step_eat_countVisited_eq s1 s2 h
  · exact step_change_frame_step_countVisited_eq s1 s2 h
  · exact step_remove_frame_step_countVisited_eq s1 s2 h
  · exact step_look_countVisited_eq s1 s2 h
  · exact step_backreference_countVisited_eq s1 s2 h
  · exact step_byterange_countVisited_eq s1 s2 h
  · exact step_sparse_transitions_countVisited_eq s1 s2 h
  · exact step_union_countVisited_eq s1 s2 h
  · exact step_union_reverse_countVisited_eq s1 s2 h
  · exact step_binary_union_countVisited_eq s1 s2 h
  · exact step_capture_countVisited_eq s1 s2 h
  · exact step_match_countVisited_eq s1 s2 h

theorem toNextStep_eq {nfa : Checked.NFA} {state : Checked.State nfa.n}
  {s s1 : SearchState nfa.n input} {msg : Unit → String}
  (h : toNextStep nfa state (withMsg msg s) = s1) : s.countVisited = s1.countVisited := by
  generalize hs : (withMsg msg s) = s' at h
  have := witMsg_countVisited_eq msg s s' hs
  have := toNextStep_countVisited_eq nfa state s' s1
  simp_all

/-- execute next step in NFA if state not already visited. Returns true if steps available. -/
@[inline] private def toNextStepChecked (nfa : Checked.NFA) (state : SearchState nfa.n s)
    : Bool × SearchState nfa.n s :=
  match Visited.checkVisited' state with
  | (false, state') =>
      let state := nfa.states[state'.sid.val]'(by
                                    rw [← Checked.NFA.isEq nfa]
                                    exact state'.sid.isLt)
      (true, toNextStep
                nfa
                state
                (withMsg (fun _ => s!"{state'.sid}: visit charpos {state'.at}") state'))
  | _ => (false, (withMsg (fun _ => s!"{state.sid}: isVisited charpos {state.at}") state))

theorem toNextStepChecked_true_lt (nfa : Checked.NFA) (s s1 : SearchState nfa.n input)
  (h : toNextStepChecked nfa s = (true, s1)) : s.countVisited < s1.countVisited := by
  unfold toNextStepChecked at h
  split at h <;> simp_all
  rename_i s2 hcv
  have heq : s1.countVisited = s2.countVisited := by
      simp [toNextStep_eq h]
  have hlt := Visited.checkVisited'_false_lt s hcv
  exact Nat.lt_of_lt_of_eq hlt (id (Eq.symm heq))

theorem toNextStepChecked_false_eq (nfa : Checked.NFA) (s s1 : SearchState nfa.n input)
  (h : toNextStepChecked nfa s = (false, s1))
    : s.countVisited = s1.countVisited ∧ s.stack = s1.stack := by
  unfold toNextStepChecked at h
  split at h <;> try simp_all
  exact withMsg_eq h

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

theorem steps_loop_le (nfa : Checked.NFA) (s s1 : SearchState nfa.n input) (h : steps.loop nfa s = s1)
    : s.countVisited ≤ s1.countVisited := by
  unfold steps.loop at h
  split at h <;> try simp_all
  split at h
  · rename_i state heq hlt
    have h2 := toNextStepChecked_true_lt nfa s state heq
    split at h
    rename_i heq
    have : unvisited state < unvisited s := by
      unfold unvisited
      omega
    have hx := steps_loop_le nfa state s1 h
    · simp [Nat.le_trans (Nat.le_of_lt h2) hx]
    · exact Nat.le_of_eq (congrArg SearchState.countVisited h)
  · simp [SearchState.ext_iff] at h
    simp_all
  · rename_i heq
    have h2 := toNextStepChecked_false_eq nfa s s1 heq
    simp [Nat.le_of_eq h2.left]

theorem steps_lt_or_eq_lt (nfa : Checked.NFA) (s s1 : SearchState nfa.n input) (h : steps nfa s = s1)
  : s.countVisited < s1.countVisited
    ∨ s.countVisited = s1.countVisited ∧ s.stack.length = s1.stack.length := by
  unfold steps at h
  split at h <;> try simp_all
  · rename_i state heq
    have := toNextStepChecked_true_lt nfa s state heq
    have := steps_loop_le nfa state s1 h
    omega
  · rename_i heq
    have := toNextStepChecked_false_eq nfa s s1 heq
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
  have hx := steps_lt_or_eq_lt nfa s state' heq
  simp [SearchState.ext_iff] at h
  rw [heq] at h
  have : state'.countVisited = s1.countVisited := by simp_all
  have : state'.stack.length = s1.stack.length := by simp_all
  omega

@[inline] private def toNextFrameRestoreCapture (slot : Nat)
  (offset : Option (String.Slice.Pos s))
  (stack : Stack n s) (state : SearchState n s) : Bool × SearchState n s :=
  if slot < state.slots.size
  then
    let f := fun _ => offset
    let state := {state with slots := state.slots.modify slot ((Prod.map id (Prod.map id f))),
                             stack := stack,
                             slotsValid := SearchState.slots_of_modify_valid state.slots
                                            state.slotsValid slot f}
    let state := (withMsg (fun _ =>
          s!"{state.sid}: Backtrack.RestoreCapture stack {stack}, slot {slot}, slots {state.slots}") state)
    (true, state)
  else (false, state)

theorem toNextFrameRestoreCapture_true_lt_or_eq_lt (slot : Nat)
  (offset :Option (String.Slice.Pos s))
  (stack : Stack n s) (s : SearchState n s)
    (h : toNextFrameRestoreCapture slot offset stack s = (true, s1))
    : s.countVisited = s1.countVisited ∧ stack = s1.stack := by
  unfold toNextFrameRestoreCapture at h
  split at h <;> try simp_all
  unfold withMsg at h
  split at h <;> simp [SearchState.ext_iff] at h <;> simp_all

@[inline] private def backtrack_msg (state : SearchState n s) (stack : Stack n s) (sid : Fin n) :=
  (s!"{state.sid}: Backtrack.Step stack {stack} at pos {state.at} -> {sid}")

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
                              then state.msgs.push (backtrack_msg state stack sid)
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
        slots := s.slots, logEnabled := s.logEnabled, slotsValid := s.slotsValid,
        recentCaptures := s.recentCaptures
        msgs := if s.logEnabled
                then s.msgs.push (backtrack_msg s stack sid)
                else s.msgs, halfMatch := s.halfMatch,
        backtracks := s.backtracks }
    have h1 := toNextFrameStep_true_lt_or_eq_lt nfa state s1 h
    have hy : state.countVisited = s.countVisited := rfl
    rw [hy] at h1
    cases h1
    · omega
    · rename_i heq h1
      have hs := Stack.pop?_some_lt s.stack heq
      rw [h1.right] at hs
      omega
  · rename_i stack _ _ slot offset heq
    have h1 := Stack.pop?_some_lt s.stack heq
    have h2 := toNextFrameRestoreCapture_true_lt_or_eq_lt slot offset stack s h
    rw [h2.right] at h1
    omega
  · have : false = true := by simp_all
    contradiction

theorem searchState_lexLt (nfa : Checked.NFA) (s s1 : SearchState nfa.n input)
  (h1 : s.countVisited < visitedSize s) (h2 : visitedSize s = visitedSize s1)
  (h : toNextFrame nfa s = (true, s1)) : unvisited s1 < unvisited s
            ∨ unvisited s1 = unvisited s ∧ s1.stack.length < s.stack.length := by
  unfold unvisited
  rw [← h2]
  have := toNextFrame_true_lt nfa s s1 h
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
          have := searchState_lexLt nfa state state' h1 h2 h
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
private def toSlots (s : String.Slice) («at» : String.Slice.Pos s)
  (nfa : Checked.NFA) (logEnabled : Bool)
    : (Array String) × (Array (Option (CharPos.Pair s))) :=
  if h : 0 < nfa.n then
    let state := backtrack nfa (SearchState.fromNfa nfa s «at» logEnabled h)
    let pairs := toPairs state.slots nfa.groups state.slotsValid
    (state.msgs, dropLastWhile pairs (·.isNone))
  else (#[], #[])

/-- Search for the first match of this regex in the haystack and
    simulate the unanchored prefix with looping. -/
private def slotsWithUnanchoredPrefix (s : String.Slice)
  («at» : String.Slice.Pos s) (nfa : Checked.NFA) (logEnabled : Bool) (init : Array String)
    : (Array String) × (Array (Option (CharPos.Pair s))) :=
  if h : s.endPos.offset.byteIdx <= «at».offset.byteIdx then
    let (msgs, slots) := toSlots s «at» nfa logEnabled
    (init ++ msgs, slots)
  else
    let (msgs, slots) := toSlots s «at» nfa logEnabled
    if slots.size = 0 then
      let nextPos := «at».next (by grind)
      have hne : «at» ≠ s.endPos := by
        have : s.endPos.offset.byteIdx ≠ «at».offset.byteIdx := by
          have : s.endPos.offset.byteIdx > «at».offset.byteIdx := by grind
          exact Ne.symm (Nat.ne_of_lt this)
        simp [String.Slice.endPos]
        exact fun a =>
          this (congrArg String.Pos.Raw.byteIdx (congrArg String.Slice.Pos.offset (id (Eq.symm a))))
      have : s.utf8ByteSize - («at».offset.byteIdx + («at».get hne).utf8Size)
             < s.utf8ByteSize - «at».offset.byteIdx := by
        have : «at».offset.byteIdx < s.utf8ByteSize := Nat.lt_of_not_le h
        have : 0 < («at».get hne).utf8Size := by simp [Char.utf8Size]; grind
        grind
      slotsWithUnanchoredPrefix s nextPos nfa logEnabled (init ++ msgs)
    else (init ++ msgs, slots)
termination_by s.endPos.offset.byteIdx - «at».offset.byteIdx

private def toMatches (s : String.Slice) (slots : Array (Option (CharPos.Pair s)))
    : Array (Option { m : String.Slice // String.Slice.isSubslice m s}) :=
  slots
  |> Array.map (fun pair =>
      match pair with
      | some ⟨(p0, p1), h⟩ => some ⟨String.Slice.replaceStartEnd s p0 p1 h, by simp⟩
      | none => none)

/-- Search for the first match of this regex in the haystack given and return log msgs and
    the matches of each capture group. -/
def «matches» (s : String.Slice) («at» : String.Slice.Pos s)
  (nfa : Checked.NFA) (logEnabled : Bool)
    : (Array String) × (Array (Option { m : String.Slice // String.Slice.isSubslice m  s})) :=
  let (msgs, slots) :=
    if nfa.unanchored_prefix_in_backtrack
    then slotsWithUnanchoredPrefix s «at» nfa logEnabled #[]
    else toSlots s «at» nfa logEnabled
  (msgs.push s!"groups: {nfa.groups}", toMatches s slots)
