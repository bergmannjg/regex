import Regex.Nfa
import Regex.Backtrack
import Regex.Utils
import Regex.Syntax.Ast.Parse
import Regex.Syntax.Translate

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

/-- Represents the capture groups for a single match. -/
structure Captures where
  /-- the full match -/
  fullMatch : Match
  /-- the capture groups -/
  groups: Array (Option Match)

namespace Captures

def end? (c : Captures) : Option String.Pos :=
  c.fullMatch.stopPos

def «matches» (c : Captures) :Array (Option Match) :=
  #[(some c.fullMatch)] ++ c.groups

end Captures

instance : ToString Captures where
  toString c := s!"fullMatch: {c.fullMatch}\ngroups: {c.groups}"

/-- Build a Regex from the given pattern. -/
def build (s : String) (flavor : Syntax.Flavor := default)
    (flags : Syntax.Flags := default) (config : Compiler.Config := default)
    : Except String Regex := do
  if flags.extended.getD false
  then throw (Syntax.AstItems.toError s .FeatureNotImplementedFlagExtended) else
  let nfa ← Syntax.AstItems.parse s flavor >>= Syntax.translate flags >>= Compiler.compile config
  Except.ok ⟨nfa⟩

namespace Log

/-- This routine searches for the first match of this regex in the haystack given,
    returns an array of log msgs, the overall match and the matches of each capture group -/
def captures (s : Substring) (re : Regex) («at» : String.Pos) (logEnabled : Bool)
    : Array String × Option Captures :=
  let (msgs, slots) := BoundedBacktracker.slots s «at» re.nfa logEnabled
  let «matches» : Array (Option Match) := slots
            |> Array.map (fun pair =>
                match pair with
                | some (p0, p1) => some ⟨s.str, p0, p1⟩
                | none => none)

  match «matches».head? with
  | some (some head, tail) => (msgs, some ⟨head, tail⟩)
  | _ => (msgs, none)

private def is_overlapping_empty_match (start «end» : String.Pos) (acc : Array Captures) : Bool :=
  match acc.pop? with
  | some (last, _) =>
      match last.end? with
      | some previous_end => start = «end» && previous_end = «end»
      | none => false
  | none => false

theorem String.Pos.lt_def {a b : String.Pos} : a < b  ↔ a.byteIdx < b.byteIdx := Iff.rfl

theorem String.Pos.sub_lt_sub_left {k m n : String.Pos} (h1 : k < m) (h2 : k < n)
    : m - n < m - k := by
  have : m.byteIdx - n.byteIdx < m.byteIdx - k.byteIdx := Nat.sub_lt_sub_left h1 h2
  exact (String.Pos.lt_def.mpr this)

theorem String.Pos.sizeof_lt_of_lt {a b : String.Pos} (h : a < b) : sizeOf a < sizeOf b := by
  have sizeOf_string_pos {s : String.Pos} : sizeOf (s) = 1 + sizeOf s.byteIdx := rfl
  apply String.Pos.lt_def.mp at h
  rw [sizeOf_string_pos, sizeOf_string_pos, sizeOf_nat, sizeOf_nat]
  omega

private def all_captures_loop (s : Substring) («at» : String.Pos) (re : Regex)
    (logEnabled : Bool) (acc : Array String × Array Captures) : Array String × Array Captures :=
  match Log.captures s re «at» logEnabled with
  | (msgs, some captures) =>
    let  ⟨_, start, «end»⟩ := captures.fullMatch
    let cp := BoundedBacktracker.CharPos.create s «end»
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
  | (msgs, none) => (acc.1.append msgs, acc.2)
termination_by s.stopPos - «at»

/-- Returns an array of log msgs and all successive non-overlapping matches in the given haystack. -/
def all_captures (s : Substring) (re : Regex) (logEnabled : Bool)
    : Array String × Array Captures :=
  all_captures_loop s ⟨0⟩ re logEnabled (#[], #[])

end Log

/-- This routine searches for the first match of this regex in the haystack given, and if found,
    returns not only the overall match but also the matches of each capture group in the regex.
    If no match is found, then None is returned. -/
def captures (s : Substring) (re : Regex) («at» : String.Pos := ⟨0⟩) : Option Captures :=
  let (_, captures) := Log.captures s re «at» false
  captures

/-- Returns all successive non-overlapping matches in the given haystack. -/
def all_captures (s : Substring) (re : Regex) : Array Captures :=
  let (_, captures) := Log.all_captures s re false
  captures
