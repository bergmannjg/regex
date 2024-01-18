import Regex.Utils

namespace NFA

/-!
## NFA

A byte oriented [Thompson](https://en.wikipedia.org/wiki/Thompson%27s_construction)
non-deterministic finite automaton (`NFA`).
-/

/-- The identifier of a finite automaton state, represented by a Nat -/
abbrev StateID := Nat

/-- The identifier of a regex pattern, represented by a Nat -/
abbrev PatternID := Nat

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
      s!"byte-range {intAsString trans.start}-{intAsString trans.end} => {trans.next}"
  | .SparseTransitions trans =>
      let lines := String.join (trans.toList |> List.map (fun t =>
            s!" {intAsString t.start}-{intAsString t.end} => {t.next}"))
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

instance : ToString NFA where
  toString := NFA.toString
