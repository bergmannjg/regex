import Std.Data.Fin.Basic
import Regex.Utils

namespace NFA

/-!
## NFA

A byte oriented [Thompson](https://en.wikipedia.org/wiki/Thompson%27s_construction)
non-deterministic finite automaton (`Checked.NFA`).
-/

/-- The identifier of a regex pattern, represented by a Nat -/
abbrev PatternID := Nat

/-- The high-level intermediate representation for a look-around assertion. -/
inductive Look where
  /-- Match the beginning of text. -/
  | Start : Look
  /-- Match the end of text. -/
  | End : Look
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
namespace Look

def toString : Look -> String
  | .Start => s!"Start"
  | .End => s!"End"
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

end Look

instance : ToString Look where
  toString := Look.toString

namespace Unchecked

/-- The identifier of a finite automaton state, represented by a Nat.
    The identifier may refer to a non existing state. -/
abbrev StateID := Nat

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
  | Capture (next: StateID) (pattern_id: PatternID) (group_index: Nat) (slot: Nat) : State
  /-- A match state. There is at least one such occurrence of this state for
      each regex that can match that is in this NFA. -/
  | Match (pattern_id : PatternID) : State

namespace State

def toString : State -> String
  | .Empty next => s!"Empty => {next}"
  | .ByteRange trans =>
      s!"byte-range {UInt32.intAsString trans.start}-{UInt32.intAsString trans.end} => {trans.next}"
  | .SparseTransitions trans =>
      let lines := String.join (trans.toList |> List.map (fun t =>
            s!" {UInt32.intAsString t.start}-{UInt32.intAsString t.end} => {t.next}"))
      s!"SparseTransitions [{lines} ]"
  | .Look look next =>
      s!"Look {look} => {next}"
  | .Union alts =>
      let lines := String.join (alts.toList |> List.map (fun t => s!" {t}"))
      s!"Union [{lines} ]"
  | .UnionReverse alts =>
      let lines := String.join (alts.toList |> List.map (fun t => s!" {t}"))
      s!"UnionReverse [{lines} ]"
  | .BinaryUnion alt1 alt2 => s!"binary-union({alt1}, {alt2})"
  | .Capture next pattern_id group slot =>
      s!"capture(pid={pattern_id}, group={group}, slot={slot}) => {next}"
  | .Match pattern_id => s!"Match({pattern_id})"

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
  let states := Array.mapIdx nfa.states (fun i s => (i, s))
  let states := String.join (states.toList |> List.map (fun (i, s) =>
      let iv := String.mk (Nat.toDigits 10 i.val)
      "\n  " ++ iv ++ ": " ++ s.toString))
  s!"states {states}"

end NFA

end Unchecked

instance : ToString Unchecked.NFA where
  toString := Unchecked.NFA.toString

namespace Checked

/-- A single transition to another state.
    This transition may only be followed if the current char in the haystack
    falls in the inclusive range of chars specified. -/
structure Transition (n : Nat) where
  /-- The inclusive start of the char range. -/
  start: UInt32
  /-- The inclusive end of the char range. -/
  «end»: UInt32
  /--  The identifier of the state to transition to. -/
  next: Fin n

namespace Transition

/-- check if `c` falls in the inclusive range of chars specified in Transition `trans` -/
def «matches» (trans : Transition n) (c : Char) : Bool :=
  trans.start <= c.val && c.val <= trans.end

end Transition

/-- A state in an NFA, the elements of `Fin n` refer to existing states in the NFA. -/
inductive State (n : Nat) where
  /-- An empty state whose only purpose is to forward the automaton to
      another state via an unconditional epsilon transition. -/
  | Empty (next: Fin n) : State n
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
  | Capture (next: Fin n) (pattern_id: PatternID) (group_index: Nat) (slot: Nat) : State n
  /-- A match state. There is at least one such occurrence of this state for
      each regex that can match that is in this NFA. -/
  | Match (pattern_id : PatternID) : State n

namespace State

def toString : State n -> String
  | .Empty next => s!"Empty => {next}"
  | .ByteRange trans =>
      s!"byte-range {UInt32.intAsString trans.start}-{UInt32.intAsString trans.end} => {trans.next}"
  | .SparseTransitions trans =>
      let lines := String.join (trans.toList |> List.map (fun t =>
            s!" {UInt32.intAsString t.start}-{UInt32.intAsString t.end} => {t.next}"))
      s!"SparseTransitions [{lines} ]"
  | .Look look next =>
      s!"Look {look} => {next}"
  | .Union alts =>
      let lines := String.join (alts.toList |> List.map (fun t => s!" {t}"))
      s!"Union [{lines} ]"
  | .UnionReverse alts =>
      let lines := String.join (alts.toList |> List.map (fun t => s!" {t}"))
      s!"UnionReverse [{lines} ]"
  | .BinaryUnion alt1 alt2 => s!"binary-union({alt1}, {alt2})"
  | .Capture next pattern_id group slot =>
      s!"capture(pid={pattern_id}, group={group}, slot={slot}) => {next}"
  | .Match pattern_id => s!"Match({pattern_id})"

end State

instance : ToString $ State n where toString s := Checked.State.toString s

/-- A char oriented Thompson non-deterministic finite automaton (NFA) with n states -/
structure NFA where
  /-- number of states -/
  n : Nat
  /-- states of the NFA -/
  states : Array (State n)
  /-- assertion that n equals size of states -/
  isEq : n = states.size

instance : Inhabited NFA where default := ⟨0, #[], by simp_arith⟩

instance {nfa : NFA} : Coe (Fin nfa.n) (Fin (Array.size nfa.states)) where
  coe n := Fin.castLE (by simp[nfa.isEq]) n

def toString (nfa : NFA) : String :=
  let states := Array.mapIdx nfa.states (fun i s => (i, s))
  let states := String.join (states.toList |> List.map (fun (i, s) =>
      let iv := String.mk (Nat.toDigits 10 i.val)
      "\n  " ++ iv ++ ": " ++ s.toString))
  s!"states {states}"

instance : ToString NFA where
  toString := Checked.toString

end Checked

private def toFin? (i n : Nat) : Option $ Fin n :=
  if h : i < n then some ⟨i, h⟩ else none

private def toCkeckedTransition? (t : Unchecked.Transition) (n : Nat) : Option $ Checked.Transition n :=
  if h : t.next < n
  then some $ ⟨t.start, t.end, ⟨t.next, h⟩⟩
  else none

private def toCkeckedState? (s : Unchecked.State) (n : Nat) : Option $ Checked.State n :=
  match s with
  | .Empty next => (toFin? next n) |> Option.map (Checked.State.Empty ·)
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
  | .Capture next pattern_id group slot =>
        (toFin? next n) |> Option.map (Checked.State.Capture · pattern_id group slot)
  | .Match pattern_id => some (Checked.State.Match pattern_id)

/-- transform Unchecked.NFA to Checked.NFA -/
def toCkecked (nfa : Unchecked.NFA) : Except String $ Checked.NFA :=
  let n := nfa.states.size
  match nfa.states |> Array.mapM (toCkeckedState? · n) with
  | some states =>
    if h : nfa.states.size = states.size -- todo: prove it
    then Except.ok ⟨n, states, by simp_all⟩
    else Except.error "internal error: NFA.toCkecked failed"
  | none => Except.error "internal error: NFA.toCkecked failed"
