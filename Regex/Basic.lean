import Batteries.Data.String

namespace Regex

/-!
## Regex

Definitions for Regex api

-/

abbrev ValidSubstring := { s : Substring // Substring.Valid s }
abbrev ValidPos s := { pos : String.Pos.Raw // String.Pos.Raw.Valid s pos }

instance instSubstringValid (s : ValidSubstring) : Inhabited (ValidPos s.val.str) where
  default := ⟨s.val.startPos, s.property.startValid⟩

instance : Coe String ValidSubstring where
  coe s := ⟨s.toSubstring, String.valid_toSubstring s⟩

/-- Represents a single match of a regex in a haystack. -/
abbrev Match := ValidSubstring

instance : ToString Match where
  toString s :=
    s!"'{s}', {s.val.startPos}, {s.val.stopPos}"

/-- Represents the full match and capture groups for a single match in `s`. -/
structure Captures (s : String) where
  /-- the full match -/
  fullMatch : Match
  /-- the capture groups, empty groups can arise, for example, in alternatives -/
  groups: Array (Option Match)
  /-- `fullMatch` is a substring of `s`. -/
  isSubstringOf : fullMatch.val.str = s
  /-- all matches in `groups` are substrings of `s`. -/
  areSubstringsOf : groups.all (Option.all (·.val.str = s) ·)

theorem start_pos_valid_of {s : ValidSubstring} (captures : Captures s.val.str)
    : String.Pos.Raw.Valid s.val.str captures.fullMatch.val.startPos  := by
  have : captures.fullMatch.val.str = s.val.str := by simp [captures.isSubstringOf]
  have := captures.fullMatch.property.startValid
  simp_all

theorem stop_pos_valid_of {s : ValidSubstring} (captures : Captures s.val.str)
    : String.Pos.Raw.Valid s.val.str captures.fullMatch.val.stopPos  := by
  have : captures.fullMatch.val.str = s.val.str := by simp [captures.isSubstringOf]
  have := captures.fullMatch.property.stopValid
  simp_all
