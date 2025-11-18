import Batteries.Data.String

import Regex.Basic
import Regex.Syntax.Flavor
import Regex.Unicode
import Regex.Nfa
import Regex.Backtrack
import Regex.Utils
import Regex.Syntax.Ast.Parser
import Regex.Syntax.Translate
import Regex.Data.Array.Basic
import Regex.Data.String.Lemmas

namespace Regex

/-!
## Regex

Main api for Regex

- `Regex.build`: build a Regex from the given pattern
- `Regex.captures`: searches for the first match of the regex
- `Regex.all_captures`: searches all successive non-overlapping matches of the regex
-/

namespace Captures

def startPosOfMatch (c : Captures s) : s.Pos :=
  String.Slice.startPosOfSubslice c.isSubsliceOf

def endPosOfMatch (c : Captures s) : s.Pos :=
  String.Slice.endPosOfSubslice c.isSubsliceOf

def «matches» (c : Captures s) : Array (Option String.Slice) :=
  #[(some c.fullMatch)] ++ c.groups

end Captures

instance : ToString (Captures s) where
  toString c := s!"fullMatch: {c.fullMatch}\ngroups: {c.groups}"

/-- Build a Regex from the given pattern. -/
def build (s : String) (flavor : Syntax.Flavor := default)
    (flags : Syntax.Flags := default) (config : Compiler.Config := default)
    (extended : Regex.Grammar.ExtendedKind := .None)
    : Except String Regex := do
  let nfa ← Syntax.AstItems.parse s flavor extended
              >>= Syntax.translate flags >>= Compiler.compile config flavor
  Except.ok ⟨nfa⟩

namespace Log

/-- This routine searches for the first match of this regex in the haystack given,
    returns an array of log msgs, the overall match and the matches of each capture group -/
def captures (s : String.Slice) (re : Regex) («at» : String.Slice.Pos s) (logEnabled : Bool)
    : Array String × Option (Captures s) :=
  let (msgs, «matches») := BoundedBacktracker.«matches» s «at» re.nfa logEnabled
  match «matches».head? with
  | some (some head, tail) =>
    (msgs, some ⟨head.val, tail.map (Option.map (·.val)), head.property, by
      intro g hg
      have ⟨_, hf⟩ := Array.mem_filterMap.mp hg
      have ⟨v, _⟩ := Array.mem_map.mp hf.left
      cases v <;> grind⟩)
  | _ => (msgs, none)

private def is_overlapping_empty_match (f t : String.Slice.Pos s) (acc : Array (Captures s)) : Bool :=
  match acc.pop? with
  | some (last, _) =>
      let previous_end := last.endPosOfMatch
      f = t && previous_end = t
  | none => false

open BoundedBacktracker CharPos in
private def all_captures_loop (s : String.Slice) («at» : String.Slice.Pos s) (re : Regex)
  (logEnabled : Bool) (acc : Array String × Array (Captures s))
    : Array String × Array (Captures s) :=
  match captures s re «at» logEnabled with
  | (msgs, some captures) =>
    let startPos : String.Slice.Pos s := captures.startPosOfMatch
    let stopPos : String.Slice.Pos s := captures.endPosOfMatch
    if h : s.startPos.offset ≤ stopPos.offset ∧ stopPos.offset ≤ s.endPos.offset
    then
      let cp := create s stopPos
      if cp.curr?.isSome then
        let overlapping_empty_match := is_overlapping_empty_match startPos stopPos acc.2
        let next := if startPos = stopPos then cp.next.pos else stopPos
        if h : «at» < next ∧ «at» < s.endPos then
          have : s.utf8ByteSize - next.offset.byteIdx < s.utf8ByteSize - «at».offset.byteIdx := by
              have : next.offset.byteIdx ≤ s.utf8ByteSize := next.isValidForSlice.le_utf8ByteSize
              have : «at».offset.byteIdx < next.offset.byteIdx := Nat.lt_of_lt_of_eq h.left
                    (congrArg String.Pos.Raw.byteIdx (congrArg String.Slice.Pos.offset rfl))
              grind
          all_captures_loop s next re logEnabled
            (acc.1.append msgs, (if overlapping_empty_match then acc.2 else acc.2.push captures))
        else (acc.1.append msgs, (if overlapping_empty_match then acc.2 else acc.2.push captures))
      else (acc.1.append msgs, acc.2.push captures)
    else (acc.1.append msgs, acc.2.push captures)
  | (msgs, none) => (acc.1.append msgs, acc.2)
termination_by s.endPos.offset.byteIdx - «at».offset.byteIdx

/-- Returns an array of log msgs and all successive non-overlapping matches in the given haystack. -/
def all_captures (s : String.Slice) (re : Regex) (logEnabled : Bool)
    : Array String × Array (Captures s) :=
  all_captures_loop s default re logEnabled (#[], #[])

end Log

/-- This routine searches for the first match of this regex in the haystack given, and if found,
    returns not only the overall match but also the matches of each capture group in the regex.
    If no match is found, then None is returned. -/
def captures (s : String.Slice) (re : Regex) («at» : String.Slice.Pos s := default)
    : Option (Captures s) :=
  Log.captures s re «at» false |> (·.2)

/-- Returns all successive non-overlapping matches in the given haystack. -/
def all_captures (s : String.Slice) (re : Regex) : Array (Captures s) :=
  Log.all_captures s re false |> (·.2)
