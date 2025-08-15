import Batteries.Data.Fin.Basic
import Regex.Utils
import Regex.Data.List.Lemmas
import Regex.Data.Array.Basic
import Regex.Data.Array.Lemmas

namespace NFA

/-!
## NFA

A byte oriented [Thompson](https://en.wikipedia.org/wiki/Thompson%27s_construction)
non-deterministic finite automaton (`Checked.NFA`),
see also [Tagged NFA](https://en.wikipedia.org/wiki/Tagged_Deterministic_Finite_Automaton).
-/

/-- The identifier of a regex pattern, represented by a Nat -/
abbrev PatternID := Nat

namespace Capture

inductive Role where
  | Start
  | End
deriving BEq

def toString : Role -> String
  | .Start => s!"Start"
  | .End => s!"End"

instance : ToString Role where
  toString := toString

end Capture

/-- The high-level intermediate representation for a look-around assertion. -/
inductive Look where
  /-- Match the beginning of text. -/
  | Start : Look
  /-- Match the end of text. -/
  | End : Look
  /-- Match the end of text (before optional newline). -/
  | EndWithOptionalLF : Look
  /-- Match the beginning of a line or the beginning of text. -/
  | StartLF : Look
  /-- Match of a line or the end of text. -/
  | EndLF : Look
  /-- Match the beginning of a line or the beginning of text. -/
  | StartCRLF : Look
  /-- Match of a line or the end of text. -/
  | EndCRLF : Look
  /-- Match a Unicode-aware word boundary. -/
  | WordUnicode : Look
  /-- Match a Unicode-aware negation of a word boundary. -/
  | WordUnicodeNegate : Look
  /-- Match the start of a Unicode word boundary. -/
  | WordStartUnicode : Look
  /-- Match the end of a Unicode word boundary. -/
  | WordEndUnicode : Look
  /-- Match the start half of a Unicode word boundary. -/
  | WordStartHalfUnicode : Look
  /-- Match the end half of a Unicode word boundary. -/
  | WordEndHalfUnicode : Look
  /-- Match the end of the previous match or start of string -/
  | PreviousMatch : Look
  /-- Clear matches -/
  | ClearMatches : Look
deriving BEq

namespace Look

def toString : Look -> String
  | .Start => s!"Start"
  | .End => s!"End"
  | .EndWithOptionalLF => s!"EndWithOptionalLF"
  | .StartLF => s!"StartLF"
  | .EndLF => s!"EndLF"
  | .StartCRLF => s!"StartCRLF"
  | .EndCRLF => s!"EndCRLF"
  | .WordUnicode => s!"WordUnicode"
  | .WordUnicodeNegate => s!"WordUnicodeNegate"
  | .WordStartUnicode => s!"WordStartUnicode"
  | .WordEndUnicode => s!"WordEndUnicode"
  | .WordStartHalfUnicode => s!"WordStartHalfUnicode"
  | .WordEndHalfUnicode => s!"WordEndHalfUnicode"
  | .PreviousMatch => s!"PreviousMatch"
  | .ClearMatches => s!"ClearMatches"

end Look

instance : ToString Look where
  toString := Look.toString

namespace Unchecked

/-- The identifier of a finite automaton state, represented by a Nat.
    The identifier may refer to a non existing state. -/
abbrev StateID := Nat

inductive EatMode where
  /-- Eat frames until State  found -/
  | Until : StateID -> EatMode
  /-- Eat frames inclusive last occurunce of State. -/
  | ToLast : StateID -> EatMode
deriving BEq

namespace EatMode

def toString : EatMode -> String
  | .Until sid => s!"Until {sid}"
  | .ToLast sid => s!"ToLast {sid}"

def nextOf (m : EatMode) : Nat :=
  match m with
  |.Until next => next
  |.ToLast next => next

end EatMode

instance : ToString EatMode where
  toString := EatMode.toString

/-- A single transition to another state.
    This transition may only be followed if the current char in the haystack
    falls in the inclusive range of chars specified. -/
structure Transition where
  /-- The inclusive start of the char range. -/
  start: UInt32
  /-- The inclusive end of the char range. -/
  «end»: UInt32
  /--  The identifier of the state to transition to. -/
  next: StateID
deriving BEq

namespace Transition

/-- check if `c` falls in the inclusive range of chars specified in Transition `trans` -/
def «matches» (trans : Transition) (c : Char) : Bool :=
  trans.start <= c.val && c.val <= trans.end

end Transition

/-- A state in an NFA. -/
inductive State where
  /-- An empty state whose only purpose is to forward the automaton to
      another state via an unconditional epsilon transition. -/
  | Empty (next: StateID) : State
  /-- use next char -/
  | NextChar (offset : Nat) (next: StateID) : State
  /-- Fail, force backtrack -/
  | Fail : State
  /-- remove Frame.Step in stack  -/
  | Eat (mode : EatMode) (next: StateID) : State
  /-- change Frame.Step in stack and force backtrack -/
  | ChangeFrameStep («from» to: StateID) : State
  /-- remove Frame.Step in stack and force backtrack -/
  | RemoveFrameStep (sid : StateID) : State
  /--  A state with a single transition may only be followed if the currunt chars match the
    backrefence to the capturung group. -/
  | BackRef (n : Nat) (case_insensitive : Bool) (sid : StateID) : State
  /-- A state with a single transition that can only be taken if the current
      input symbol is in a particular range of chars. -/
  | ByteRange (trans : Transition) : State
  /-- A sequence of transitions used to represent a sparse state. -/
  | SparseTransitions (transitions : Array Transition) : State
  /-- A conditional epsilon transition satisfied via some sort of look-around.  -/
  | Look (look : Look) (next: StateID) : State
  /--An alternation such that there exists an epsilon transition to all states in `alternates`,
     where matches found via earlier transitions are preferred over later transitions. -/
  | Union (alternates: Array StateID) : State
  /--An alternation such that there exists an epsilon transition to all states in `alternates`,
     where matches found via later transitions are preferred over earlier transitions. -/
  | UnionReverse (alternates: Array StateID) : State
  /-- An alternation such that there exists precisely two unconditional epsilon transitions -/
  | BinaryUnion (alt1: StateID) (alt2: StateID) : State
  /-- An empty state that records a capture location.
      `slot` in this context refers to the specific capture group slot
       offset that is being recorded. Each capturing group has two slots
       corresponding to the start and end of the matching portion of that
       group. -/
  | Capture (role : Capture.Role) (next: StateID) (pattern_id: PatternID) (group_index: Nat) (slot: Nat) : State
  /-- A match state. There is at least one such occurrence of this state for
      each regex that can match that is in this NFA. -/
  | Match (pattern_id : PatternID) : State
deriving BEq

namespace State

def toString : State -> String
  | .Empty next => s!"State.Empty => {next}"
  | .NextChar offset next => s!"State.NextChar offset  {offset} => {next}"
  | .Fail => s!"State.Fail"
  | .Eat s n => s!"State.Eat {s} => {n}"
  | .ChangeFrameStep «from» to => s!"State.ChangeFrameStep from {«from»} to {to}"
  | .RemoveFrameStep sid => s!"State.RemoveFrameStep {sid}"
  | .BackRef b f sid =>
      s!"State.BackRef {b} {if f then "case_insensitive" else ""} => {sid}"
  | .ByteRange trans =>
      s!"State.ByteRange {UInt32.intAsString trans.start}-{UInt32.intAsString trans.end} => {trans.next}"
  | .SparseTransitions trans =>
      let lines := String.join (trans.toList |> List.map (fun t =>
            s!" {UInt32.intAsString t.start}-{UInt32.intAsString t.end} => {t.next}"))
      s!"State.SparseTransitions [{lines} ]"
  | .Look look next =>
      s!"State.Look {look} => {next}"
  | .Union alts =>
      let lines := String.join (alts.toList |> List.map (fun t => s!" {t}"))
      s!"State.Union [{lines} ]"
  | .UnionReverse alts =>
      let lines := String.join (alts.toList |> List.map (fun t => s!" {t}"))
      s!"State.UnionReverse [{lines} ]"
  | .BinaryUnion alt1 alt2 => s!"State.BinaryUnion({alt1}, {alt2})"
  | .Capture role next pattern_id group slot =>
      s!"State.Capture {role}(pid={pattern_id}, group={group}, slot={slot}) => {next}"
  | .Match pattern_id => s!"State.Match ({pattern_id})"

def nextOf (s : State) : Nat :=
  match s with
  | .Empty next => next
  | .NextChar _ next => next
  | .Fail => 0
  | .Eat (EatMode.Until s) next => Nat.max s next
  | .Eat (EatMode.ToLast s) next => Nat.max s next
  | .ChangeFrameStep f t => Nat.max f t
  | .RemoveFrameStep next => next
  | .BackRef _ _ next => next
  | .ByteRange trans => trans.next
  | .SparseTransitions trans => (trans.map (·.next)).toList.maxD 0
  | .Look _ next => next
  | .Union alts => alts.toList.maxD 0
  | .UnionReverse alts => alts.toList.maxD 0
  | .BinaryUnion alt1 alt2 => Nat.max alt1 alt2
  | .Capture _ next _ _ _ => next
  | .Match _ => 0

end State

instance : ToString State where
  toString := State.toString

/-- Array of (slot, group) pairs of captures. -/
def toSlots (states : Array State) : Array (Nat × Nat) :=
  let slots := states.filterMap (fun s => match s with | .Capture _ _ _ _ s => some s | _ => none)
  match slots.getMax? (· < ·) with
  | some n => ((List.range (n + 1)).map (fun i => (i, i.div 2))).toArray
  | none => #[]

/-- A char oriented Thompson non-deterministic finite automaton (NFA). -/
structure NFA where
  states : Array State
  slots : Array (Nat × Nat)
  start_anchored: StateID
  start_unanchored: StateID

namespace NFA

def toString (nfa : NFA) : String :=
  let states := Array.mapFinIdx nfa.states (fun i s _ => (i, s))
  let states := String.join (states.toList |> List.map (fun (i, s) =>
      let iv := String.mk (Nat.toDigits 10 i)
      "\n  " ++ iv ++ ": " ++ s.toString))
  s!"states {states}\nslots {nfa.slots}"

end NFA

end Unchecked

instance : ToString Unchecked.NFA where
  toString := Unchecked.NFA.toString

namespace Checked

inductive EatMode n where
  /-- Eat frames until State  found -/
  | Until : Fin n -> EatMode n
  /-- Eat frames inclusive last occurunce of State. -/
  | ToLast : Fin n -> EatMode n

namespace EatMode

def toString : EatMode n -> String
  | .Until sid => s!"Until {sid}"
  | .ToLast sid => s!"ToLast {sid}"

end EatMode

instance : ToString (EatMode n) where
  toString := EatMode.toString


/-- A single transition to another state.
    This transition may only be followed if the current char in the haystack
    falls in the inclusive range of chars specified. -/
structure Transition (n : Nat) where
  /-- The inclusive start of the char range. -/
  start: Nat
  /-- The inclusive end of the char range. -/
  «end»: Nat
  /--  The identifier of the state to transition to. -/
  next: Fin n

namespace Transition

/-- check if `c` falls in the inclusive range of chars specified in Transition `trans` -/
def «matches» (trans : Transition n) (c : Char) : Bool :=
  trans.start <= c.val.toFin && c.val.toFin <= trans.end

end Transition

/-- A state in an NFA, the elements of `Fin n` refer to existing states in the NFA. -/
inductive State (n : Nat) where
  /-- An empty state whose only purpose is to forward the automaton to
      another state via an unconditional epsilon transition. -/
  | Empty (next: Fin n) : State n
  /-- use netx char -/
  | NextChar (offset : Nat) (next: Fin n) : State n
  /-- Fail, force backtracking -/
  | Fail : State n
  /-- remove Frame.Step in stack  -/
  | Eat (mode : EatMode n) (next: Fin n) : State n
  /-- change Frame.Step in stack and force backtracking -/
  | ChangeFrameStep (fr to: Fin n) : State n
  /-- remove Frame.Step in stack and force backtrack -/
  | RemoveFrameStep (sid : Fin n) : State n
  /--  A state with a single transition may only be followed if the current chars match the
      backrefence to the capturung group. -/
  | BackRef (b : Nat) (case_insensitive : Bool) (sid : Fin n) : State n
  /-- A state with a single transition that can only be taken if the current
      input symbol is in a particular range of chars. -/
  | ByteRange (trans : Transition n) : State n
  /-- A sequence of transitions used to represent a sparse state. -/
  | SparseTransitions (transitions : Array $ Transition n) : State n
  /-- A conditional epsilon transition satisfied via some sort of look-around.  -/
  | Look (look : Look) (next: Fin n) : State n
  /--An alternation such that there exists an epsilon transition to all states in `alternates`,
     where matches found via earlier transitions are preferred over later transitions. -/
  | Union (alternates: Array $ Fin n) : State n
  /--An alternation such that there exists an epsilon transition to all states in `alternates`,
     where matches found via later transitions are preferred over earlier transitions. -/
  | UnionReverse (alternates: Array $ Fin n) : State n
  /-- An alternation such that there exists precisely two unconditional epsilon transitions -/
  | BinaryUnion (alt1: Fin n) (alt2: Fin n) : State n
  /-- An empty state that records a capture location.
      `slot` in this context refers to the specific capture group slot
       offset that is being recorded. Each capturing group has two slots
       corresponding to the start and end of the matching portion of that
       group. -/
  | Capture (role: Capture.Role) (next: Fin n) (pattern_id: PatternID) (group_index: Nat) (slot: Nat) : State n
  /-- A match state. There is at least one such occurrence of this state for
      each regex that can match that is in this NFA. -/
  | Match (pattern_id : PatternID) : State n

private def beq' :  State n → State n → Bool
  | .Empty ⟨n1, _⟩ , .Empty ⟨n2, _⟩  => n1 = n2
  | .ByteRange trans1 , .ByteRange trans2  =>
      trans1.start = trans2.start && trans1.«end» = trans2.«end» && trans1.next = trans2.next
  | .SparseTransitions trans1 , .SparseTransitions trans2  => trans1.size = trans2.size
  | .Capture r1 ⟨n1, _⟩ p1 _ _,  .Capture r2 ⟨n2, _⟩ p2 _ _  => r1 == r2 && n1 = n2 && p1 = p2
  | .Match p1,  .Match p2 => p1 = p2
  | _, _ => false

instance : BEq (State n) where
  beq := beq'

namespace State

def toString : State n -> String
  | .Empty next => s!"State.Empty => {next}"
  | .NextChar offset next => s!"State.NextChar offset {offset} => {next}"
  | .Fail => s!"State.Fail"
  | .Eat s next => s!"State.Eat {s} => {next}"
  | .ChangeFrameStep f t => s!"State.ChangeFrameStep from {f} to {t}"
  | .RemoveFrameStep sid => s!"State.RemoveFrameStep {sid}"
  | .BackRef b f sid =>
      s!"State.BackRef {b} {if f then "case_insensitive" else ""} => {sid}"
  | .ByteRange trans =>
      s!"State.ByteRange {Nat.intAsString trans.start}-{Nat.intAsString trans.end} => {trans.next}"
  | .SparseTransitions trans =>
      let lines := String.join (trans.toList |> List.map (fun t =>
            s!" {Nat.intAsString t.start}-{Nat.intAsString t.end} => {t.next}"))
      s!"State.SparseTransitions [{lines} ]"
  | .Look look next =>
      s!"State.Look {look} => {next}"
  | .Union alts =>
      let lines := String.join (alts.toList |> List.map (fun t => s!" {t}"))
      s!"State.Union [{lines} ]"
  | .UnionReverse alts =>
      let lines := String.join (alts.toList |> List.map (fun t => s!" {t}"))
      s!"State.UnionReverse [{lines} ]"
  | .BinaryUnion alt1 alt2 => s!"State.BinaryUnion ({alt1}, {alt2})"
  | .Capture role next pattern_id group slot =>
      s!"State.Capture {role}(pid={pattern_id}, group={group}, slot={slot}) => {next}"
  | .Match pattern_id => s!"State.Match ({pattern_id})"

end State

instance : ToString $ State n where toString s := Checked.State.toString s

/-- Valid slot arrays have even size and consist of groups with two slots
    at consecutive positions. -/
def Slots.Valid (slots : Array (Nat × Nat)) : Bool :=
  slots.size % 2 = 0 && (List.range slots.size).map (fun i => (i, i.div 2)) = slots.toList

/-- A char oriented Thompson non-deterministic finite automaton (NFA) with n states -/
structure NFA where
  /-- number of states -/
  n : Nat
  /-- states of the NFA -/
  states : Array (State n)
  /-- capture groups which may match with a empty string -/
  groups : Array Nat
  /-- Array of (slot, group) pairs of captures -/
  slots : Array (Nat × Nat)
  /-- simulate a unanchored prefix by the backtracker -/
  unanchored_prefix_in_backtrack : Bool
  /-- assertion that n equals size of states -/
  isEq : n = states.size
  /-- slots are valid -/
  slotsValid : Slots.Valid slots

instance : Inhabited NFA where default := ⟨0, #[], #[], #[], false, by simp +arith, by simp +arith +decide⟩

instance {nfa : NFA} : Coe (Fin nfa.n) (Fin (Array.size nfa.states)) where
  coe n := Fin.castLE (by simp[nfa.isEq]) n

def toString (nfa : NFA) : String :=
  let states := Array.mapFinIdx nfa.states (fun i s _ => (i, s))
  let states := String.join (states.toList |> List.map (fun (i, s) =>
      let iv := String.mk (Nat.toDigits 10 i)
      "\n  " ++ iv ++ ": " ++ s.toString))
  s!"states {states}\nslots {nfa.slots}"

instance : ToString NFA where
  toString := Checked.toString

end Checked

private def toFin? (i n : Nat) : Option $ Fin n :=
  if h : i < n then some ⟨i, h⟩ else none

private def toCkeckedTransition? (t : Unchecked.Transition) (n : Nat)
    : Option $ Checked.Transition n :=
  if h : t.next < n
  then some $ ⟨t.start.toFin, t.end.toFin, ⟨t.next, h⟩⟩
  else none

private def toCkeckedState (s : Unchecked.State) (n : Nat) (h : Unchecked.State.nextOf s < n)
    : Checked.State n :=
  match s with
  | .Empty next => Checked.State.Empty ⟨next, by
    simp [Unchecked.State.nextOf] at h; exact h⟩
  | .NextChar offset next => Checked.State.NextChar offset ⟨next, by
    simp [Unchecked.State.nextOf] at h; exact h⟩
  | .Fail => Checked.State.Fail
  | .Eat (.Until s) next => Checked.State.Eat
      (.Until ⟨s, by simp [Unchecked.State.nextOf] at h; simp [Nat.max_lt.mp h]⟩)
      ⟨next, by simp [Unchecked.State.nextOf] at h; simp [Nat.max_lt.mp h]⟩
  | .Eat (.ToLast s) next => Checked.State.Eat
      (.ToLast ⟨s, by simp [Unchecked.State.nextOf] at h; simp [Nat.max_lt.mp h]⟩)
      ⟨next, by simp [Unchecked.State.nextOf] at h; simp [Nat.max_lt.mp h]⟩
  | .ChangeFrameStep f t => Checked.State.ChangeFrameStep
      ⟨f, by simp [Unchecked.State.nextOf] at h; simp [Nat.max_lt.mp h]⟩
      ⟨t, by simp [Unchecked.State.nextOf] at h; simp [Nat.max_lt.mp h]⟩
  | .RemoveFrameStep t => Checked.State.RemoveFrameStep
      ⟨t, by simp [Unchecked.State.nextOf] at h; exact h⟩
  | .BackRef b f sid => Checked.State.BackRef b f
      ⟨sid, by simp [Unchecked.State.nextOf] at h; exact h⟩
  | .ByteRange ⟨start, «end», next⟩ => Checked.State.ByteRange ⟨start.toNat, «end».toNat,
          ⟨next, by simp [Unchecked.State.nextOf] at h; exact h⟩⟩
  | .SparseTransitions trans => Checked.State.SparseTransitions
      (trans.attach |> Array.map (fun ⟨t, h'⟩ => ⟨t.start.toNat, t.end.toNat, ⟨t.next, by
        simp [Unchecked.State.nextOf] at h
        let f : Unchecked.Transition → Nat := fun x => x.next
        have := List.maxD_of_map_all_lt f h (by
          intro a ha
          exact List.mem_map_of_mem ha) t (Array.Mem.val h')
        simp_all +zetaDelta⟩⟩))
  | .Look look next => Checked.State.Look look ⟨next, by
      simp [Unchecked.State.nextOf] at h; exact h⟩
  | .Union alts => Checked.State.Union (alts.attach |> Array.map
      (fun ⟨alt, h'⟩ => ⟨alt, by
        simp [Unchecked.State.nextOf] at h
        exact List.maxD_all_lt_of_lt h alt (Array.Mem.val h')⟩))
  | .UnionReverse alts => Checked.State.UnionReverse (alts.attach |> Array.map
      (fun ⟨alt, h'⟩ => ⟨alt, by
        simp [Unchecked.State.nextOf] at h
        exact List.maxD_all_lt_of_lt h alt (Array.Mem.val h')⟩))
  | .Capture role next pattern_id group slot => Checked.State.Capture role
          ⟨next, by simp [Unchecked.State.nextOf] at h; exact h⟩ pattern_id group slot
  | .BinaryUnion alt1 alt2 => Checked.State.BinaryUnion
      ⟨alt1, by simp [Unchecked.State.nextOf] at h; simp [Nat.max_lt.mp h]⟩
      ⟨alt2, by simp [Unchecked.State.nextOf] at h; simp [Nat.max_lt.mp h]⟩
  | .Match pattern_id => Checked.State.Match pattern_id

/-- Array of (slot, group) pairs of captures. -/
private def slotsOfCaptures (states : Array (Checked.State n)) : Array (Nat × Nat) :=
  let captures := states.filterMap (fun s =>
    match s with | .Capture _ _ _ g s => some (s, g) | _ => none)

  Array.qsort captures (fun (s1, g1) (s2, g2) => Prod.lexLt (g1, s1) (g2, s2))
  |> Array.unique

/-- transform Unchecked.NFA to Checked.NFA -/
def toCkecked (nfa : Unchecked.NFA) (groups : Array Nat)
  (h : ∀ (i : Nat) _, nfa.states[i].nextOf < nfa.states.size) : Except String Checked.NFA :=
  let n := nfa.states.size
  let states := nfa.states.attach.map (fun ⟨s, _⟩ => toCkeckedState s n _)
  have h1 : nfa.states.size = states.size := by
    rw [Array.size_map, Array.size_attach]
    exact Array.forall_getElem.mp h
  /- (slotsOfCaptures states) is a subset of nfa.slots,
      see '(a){0}(a)' where (slotsOfCaptures states) is not equal to nfa.slots -/
  if h2 : Checked.Slots.Valid nfa.slots
          ∧ nfa.slots.all_contains (slotsOfCaptures states) -- todo: prove it
  then pure ⟨n, states, groups, nfa.slots, false, by rw [← h1], h2.left⟩
  else Except.error s!"internal error: Slots.Valid failed, nfa {nfa}"

end NFA

open NFA

/-- A compiled regular expression for searching Unicode haystacks. -/
structure Regex where
  nfa : Checked.NFA

instance : ToString Regex where
  toString m := s!"{m.nfa}"
