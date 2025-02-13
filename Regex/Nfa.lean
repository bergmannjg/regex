import Batteries.Data.Fin.Basic
import Regex.Utils

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

namespace EatMode

def toString : EatMode -> String
  | .Until sid => s!"Until {sid}"
  | .ToLast sid => s!"ToLast {sid}"

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

end State

instance : ToString State where
  toString := State.toString

/-- A char oriented Thompson non-deterministic finite automaton (NFA). -/
structure NFA where
  states : Array State
  start_anchored: StateID
  start_unanchored: StateID

namespace NFA

def toString (nfa : NFA) : String :=
  let states := Array.mapFinIdx nfa.states (fun i s => (i, s))
  let states := String.join (states.toList |> List.map (fun (i, s) =>
      let iv := String.mk (Nat.toDigits 10 i)
      "\n  " ++ iv ++ ": " ++ s.toString))
  s!"states {states}"

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
  trans.start <= c.val.val && c.val.val <= trans.end

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

private partial def beq' :  State n → State n → Bool
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
  | .Empty next => s!"Checked.State.Empty => {next}"
  | .NextChar offset next => s!"Checked.State.NextChar offset {offset} => {next}"
  | .Fail => s!"Checked.State.Fail"
  | .Eat s next => s!"Checked.State.Eat {s} => {next}"
  | .ChangeFrameStep f t => s!"Checked.State.ChangeFrameStep from {f} to {t}"
  | .RemoveFrameStep sid => s!"Checked.State.RemoveFrameStep {sid}"
  | .BackRef b f sid =>
      s!"Checked.State.BackRef {b} {if f then "case_insensitive" else ""} => {sid}"
  | .ByteRange trans =>
      s!"Checked.State.ByteRange {Nat.intAsString trans.start}-{Nat.intAsString trans.end} => {trans.next}"
  | .SparseTransitions trans =>
      let lines := String.join (trans.toList |> List.map (fun t =>
            s!" {Nat.intAsString t.start}-{Nat.intAsString t.end} => {t.next}"))
      s!"Checked.State.SparseTransitions [{lines} ]"
  | .Look look next =>
      s!"Checked.State.Look {look} => {next}"
  | .Union alts =>
      let lines := String.join (alts.toList |> List.map (fun t => s!" {t}"))
      s!"Checked.State.Union [{lines} ]"
  | .UnionReverse alts =>
      let lines := String.join (alts.toList |> List.map (fun t => s!" {t}"))
      s!"Checked.State.UnionReverse [{lines} ]"
  | .BinaryUnion alt1 alt2 => s!"Checked.State.BinaryUnion ({alt1}, {alt2})"
  | .Capture role next pattern_id group slot =>
      s!"Checked.State.Capture {role}(pid={pattern_id}, group={group}, slot={slot}) => {next}"
  | .Match pattern_id => s!"Checked.State.Match ({pattern_id})"

end State

instance : ToString $ State n where toString s := Checked.State.toString s

/-- A char oriented Thompson non-deterministic finite automaton (NFA) with n states -/
structure NFA where
  /-- number of states -/
  n : Nat
  /-- states of the NFA -/
  states : Array (State n)
  /-- simulate a unanchored prefix by the backtracker -/
  unanchored_prefix_in_backtrack : Bool
  /-- assertion that n equals size of states -/
  isEq : n = states.size

instance : Inhabited NFA where default := ⟨0, #[], false, by simp_arith⟩

instance {nfa : NFA} : Coe (Fin nfa.n) (Fin (Array.size nfa.states)) where
  coe n := Fin.castLE (by simp[nfa.isEq]) n

def toString (nfa : NFA) : String :=
  let states := Array.mapFinIdx nfa.states (fun i s => (i, s))
  let states := String.join (states.toList |> List.map (fun (i, s) =>
      let iv := String.mk (Nat.toDigits 10 i)
      "\n  " ++ iv ++ ": " ++ s.toString))
  s!"states {states}"

instance : ToString NFA where
  toString := Checked.toString

end Checked

private def toFin? (i n : Nat) : Option $ Fin n :=
  if h : i < n then some ⟨i, h⟩ else none

private def toCkeckedTransition? (t : Unchecked.Transition) (n : Nat)
    : Option $ Checked.Transition n :=
  if h : t.next < n
  then some $ ⟨t.start.val, t.end.val, ⟨t.next, h⟩⟩
  else none

private def toCkeckedState? (s : Unchecked.State) (n : Nat) : Option $ Checked.State n :=
  match s with
  | .Empty next => (toFin? next n) |> Option.map (Checked.State.Empty ·)
  | .NextChar offset next => (toFin? next n) |> Option.map (Checked.State.NextChar offset ·)
  | .Fail => some Checked.State.Fail
  | .Eat (.Until s) next =>
        match (toFin? s n), (toFin? next n) with
        | some s, some next => some (Checked.State.Eat (.Until s) next)
        |_, _ => none
  | .Eat (.ToLast s) next =>
        match (toFin? s n), (toFin? next n) with
        | some s, some next => some (Checked.State.Eat (.ToLast s) next)
        |_, _ => none
  | .ChangeFrameStep f t =>
        match (toFin? f n), (toFin? t n) with
        | some f, some t => some (Checked.State.ChangeFrameStep f t)
        |_, _ => none
  | .RemoveFrameStep sid => (toFin? sid n) |> Option.map (Checked.State.RemoveFrameStep ·)
  | .BackRef b f sid => (toFin? sid n) |> Option.map (Checked.State.BackRef b f ·)
  | .ByteRange trans => (toCkeckedTransition? trans n) |> Option.map (Checked.State.ByteRange ·)
  | .SparseTransitions trans =>
        trans
        |> Array.mapM (fun t => toCkeckedTransition? t n)
        |> Option.map (fun trans => (Checked.State.SparseTransitions trans))

  | .Look look next => (toFin? next n) |> Option.map (Checked.State.Look look ·)
  | .Union alts =>
        alts
        |> Array.mapM (fun alt => toFin? alt n)
        |> Option.map (fun alts => (Checked.State.Union alts))
  | .UnionReverse alts =>
        alts
        |> Array.mapM (fun alt => toFin? alt n)
        |> Option.map (fun alts => (Checked.State.UnionReverse alts))
  | .BinaryUnion alt1 alt2 =>
        match (toFin? alt1 n), (toFin? alt2 n) with
        | some alt1, some alt2 => (Checked.State.BinaryUnion alt1 alt2)
        | _, _ => none
  | .Capture role next pattern_id group slot =>
        (toFin? next n) |> Option.map (Checked.State.Capture role · pattern_id group slot)
  | .Match pattern_id => some (Checked.State.Match pattern_id)

/-- transform Unchecked.NFA to Checked.NFA -/
def toCkecked (nfa : Unchecked.NFA) : Except String $ Checked.NFA :=
  let n := nfa.states.size
  match nfa.states |> Array.mapM (toCkeckedState? · n) with
  | some states =>
    if h : nfa.states.size = states.size -- todo: prove it
    then Except.ok ⟨n, states, false, by
      have : n = nfa.states.size := by simp +zetaDelta
      simp_all⟩
    else Except.error "internal error: NFA.toCkecked failed"
  | none => Except.error "internal error: NFA.toCkecked failed"
