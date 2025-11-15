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

def end? (c : Captures s) : Option String.Pos.Raw :=
  c.fullMatch.val.stopPos

def «matches» (c : Captures s) : Array (Option Match) :=
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
def captures (s : ValidSubstring) (re : Regex) («at» : ValidPos s.val.str) (logEnabled : Bool)
    : Array String × Option (Captures s.val.str) :=
  let (msgs, «matches») := BoundedBacktracker.«matches» s «at» re.nfa logEnabled
  match «matches».head? with
  | some (some head, tail) =>
    let tail := tail.map_option_subtype
    (msgs, some ⟨head.val, tail.val, head.property, tail.property⟩)
  | _ => (msgs, none)

private def is_overlapping_empty_match (f t : String.Pos.Raw) (acc : Array (Captures s)) : Bool :=
  match acc.pop? with
  | some (last, _) =>
      match last.end? with
      | some previous_end => f = t && previous_end = t
      | none => false
  | none => false

private def all_captures_loop (s : ValidSubstring) («at» : ValidPos s.val.str) (re : Regex)
  (logEnabled : Bool) (acc : Array String × Array (Captures s.val.str))
    : Array String × Array (Captures s.val.str) :=
  match captures s re «at» logEnabled with
  | (msgs, some captures) =>
    let startPos := captures.fullMatch.val.startPos
    let stopPos := captures.fullMatch.val.stopPos
    if h : s.val.startPos ≤ stopPos ∧ stopPos ≤ s.val.stopPos
    then
      let cp := BoundedBacktracker.CharPos.create s ⟨stopPos, stop_pos_valid_of captures⟩ h
      if cp.curr?.isSome then
        let overlapping_empty_match := is_overlapping_empty_match startPos stopPos acc.2
        let next := if startPos = stopPos then cp.next.pos else stopPos
        if h : «at» < next ∧ «at» < s.val.stopPos then
          have hNextValid : String.Pos.Raw.Valid s.val.str next := by
            unfold next
            split
            · exact cp.next.isValidPos
            · exact stop_pos_valid_of captures
          have : sizeOf (s.val.stopPos.byteIdx - next.byteIdx)
                 < sizeOf (s.val.stopPos.byteIdx - «at».val.byteIdx) := by
            have := String.Pos.sizeof_lt_of_lt (String.Pos.sub_lt_sub_left h.right h.left)
            simp_all
          all_captures_loop s ⟨next, hNextValid⟩ re logEnabled
            (acc.1.append msgs, (if overlapping_empty_match then acc.2 else acc.2.push captures))
        else (acc.1.append msgs, (if overlapping_empty_match then acc.2 else acc.2.push captures))
      else (acc.1.append msgs, acc.2.push captures)
    else (acc.1.append msgs, acc.2.push captures)
  | (msgs, none) => (acc.1.append msgs, acc.2)
termination_by s.val.stopPos.byteIdx - «at».val.byteIdx

/-- Returns an array of log msgs and all successive non-overlapping matches in the given haystack. -/
def all_captures (s : ValidSubstring) (re : Regex) (logEnabled : Bool)
    : Array String × Array (Captures s.val.str) :=
  all_captures_loop s default re logEnabled (#[], #[])

end Log

/-- This routine searches for the first match of this regex in the haystack given, and if found,
    returns not only the overall match but also the matches of each capture group in the regex.
    If no match is found, then None is returned. -/
def captures (s : ValidSubstring) (re : Regex) («at» : ValidPos s.val.str := default)
    : Option (Captures s.val.str) :=
  Log.captures s re «at» false |> (·.2)

/-- Returns all successive non-overlapping matches in the given haystack. -/
def all_captures (s : ValidSubstring) (re : Regex) : Array (Captures s.val.str) :=
  Log.all_captures s re false |> (·.2)
