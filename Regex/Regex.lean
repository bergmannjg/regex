import Regex.Syntax.Flavor
import Regex.Unicode
import Regex.Nfa
import Regex.Backtrack
import Regex.Utils
import Regex.Syntax.Ast.Parser
import Regex.Syntax.Translate
import Regex.Data.Array.Basic

open NFA

/-- A compiled regular expression for searching Unicode haystacks. -/
structure Regex where
  nfa : Checked.NFA

instance : ToString Regex where
  toString m := s!"{m.nfa}"

namespace Regex

/-!
## Regex

Main api for Regex

- `Regex.build`: build a Regex from the given pattern
- `Regex.captures`: searches for the first match of the regex
- `Regex.all_captures`: searches all successive non-overlapping matches of the regex
-/

/-- Represents a single match of a regex in a haystack. -/
abbrev Match := Substring

instance : ToString Match where
  toString s :=
    s!"'{s}', {s.startPos}, {s.stopPos}"

/-- Represents the full match and capture groups for a single match in `s`. -/
structure Captures (s : String) where
  /-- the full match -/
  fullMatch : Match
  /-- the capture groups, empty groups can arise, for example, in alternatives -/
  groups: Array (Option Match)
  /-- `fullMatch` is a substring of `s`. -/
  isSubstringOf : fullMatch.str = s
  /-- all matches in `groups` are substrings of `s`. -/
  areSubstringsOf : groups.all (Option.all (·.str = s) ·)

namespace Captures

def end? (c : Captures s) : Option String.Pos :=
  c.fullMatch.stopPos

def «matches» (c : Captures s) :Array (Option Match) :=
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
              >>= Syntax.translate flags >>= Compiler.compile config
  Except.ok ⟨nfa⟩

namespace Log

/-- This routine searches for the first match of this regex in the haystack given,
    returns an array of log msgs, the overall match and the matches of each capture group -/
def captures (s : Substring) (re : Regex) («at» : String.Pos) (logEnabled : Bool)
    : Array String × Option (Captures s.str) :=
  let (msgs, «matches») := BoundedBacktracker.«matches» s «at» re.nfa logEnabled
  match «matches».head? with
  | some (some head, tail) =>
    let tail := tail.map_option_subtype
    (msgs, some ⟨head.val, tail.val, head.property, tail.property⟩)
  | _ => (msgs, none)

private def is_overlapping_empty_match (f t : String.Pos) (acc : Array (Captures s)) : Bool :=
  match acc.pop? with
  | some (last, _) =>
      match last.end? with
      | some previous_end => f = t && previous_end = t
      | none => false
  | none => false

theorem String.Pos.lt_def {a b : String.Pos} : a < b  ↔ a.byteIdx < b.byteIdx := Iff.rfl

theorem String.Pos.sub_lt_sub_left {k m n : String.Pos} (h1 : k < m) (h2 : k < n)
    : m - n < m - k := by
  have : m.byteIdx - n.byteIdx < m.byteIdx - k.byteIdx := Nat.sub_lt_sub_left h1 h2
  exact (String.Pos.lt_def.mpr this)

theorem String.Pos.sizeof_lt_of_lt {a b : String.Pos} (h : a < b) : sizeOf a < sizeOf b := by
  have sizeOf_string_pos {s : String.Pos} : sizeOf (s) = 1 + sizeOf s.byteIdx := rfl
  simp [String.Pos.lt_def.mp] at h
  rw [sizeOf_string_pos, sizeOf_string_pos, sizeOf_nat, sizeOf_nat]
  omega

private def all_captures_loop (s : Substring) («at» : String.Pos) (re : Regex)
  (logEnabled : Bool) (acc : Array String × Array (Captures s.str))
    : Array String × Array (Captures s.str) :=
  match Log.captures s re «at» logEnabled with
  | (msgs, some captures) =>
    let  ⟨_, start, «end»⟩ := captures.fullMatch
    if h : s.startPos ≤ «end» ∧ «end» ≤ s.stopPos
    then
      let cp := BoundedBacktracker.CharPos.create s «end» h
      match cp.curr? with
      | some _ =>
        let overlapping_empty_match := is_overlapping_empty_match start «end» acc.2
        let next := if start = «end» then cp.next.pos else «end»
        if h : «at» < next ∧ «at» < s.stopPos then
          have : sizeOf (s.stopPos - next) < sizeOf (s.stopPos - «at») :=
            String.Pos.sizeof_lt_of_lt (String.Pos.sub_lt_sub_left h.right h.left)
          all_captures_loop s next re logEnabled
            (acc.1.append msgs, (if overlapping_empty_match then acc.2 else acc.2.push captures))
        else (acc.1.append msgs, (if overlapping_empty_match then acc.2 else acc.2.push captures))
      | none => (acc.1.append msgs, acc.2.push captures)
    else (acc.1.append msgs, acc.2.push captures)
  | (msgs, none) => (acc.1.append msgs, acc.2)
termination_by s.stopPos - «at»

/-- Returns an array of log msgs and all successive non-overlapping matches in the given haystack. -/
def all_captures (s : Substring) (re : Regex) (logEnabled : Bool)
    : Array String × Array (Captures s.str) :=
  all_captures_loop s ⟨0⟩ re logEnabled (#[], #[])

end Log

/-- This routine searches for the first match of this regex in the haystack given, and if found,
    returns not only the overall match but also the matches of each capture group in the regex.
    If no match is found, then None is returned. -/
def captures (s : Substring) (re : Regex) («at» : String.Pos := ⟨0⟩) : Option (Captures s.str) :=
  let (_, captures) := Log.captures s re «at» false
  captures

/-- Returns all successive non-overlapping matches in the given haystack. -/
def all_captures (s : Substring) (re : Regex) : Array (Captures s.str) :=
  let (_, captures) := Log.all_captures s re false
  captures
