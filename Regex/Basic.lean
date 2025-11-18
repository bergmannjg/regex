import Batteries.Data.String
import Regex.Data.String.Basic

namespace Regex

/-!
## Regex

Definitions for Regex api

-/

instance : Coe String String.Slice where
  coe s := s.toSlice

/-- Represents a single match of a regex in a haystack. -/
abbrev Match := String.Slice

instance : ToString Match where
  toString s :=
    s!"'{s.copy}', {s.startInclusive.offset}, {s.endExclusive.offset}"

/-- Represents the full match and capture groups for a single match in `s`. -/
structure Captures (s : String.Slice) where
  /-- the full match -/
  fullMatch : Match
  /-- the capture groups, empty groups can arise, for example, in alternatives -/
  groups: Array (Option Match)
  /-- `fullMatch` is a subslice of `s`. -/
  isSubsliceOf : String.Slice.isSubslice fullMatch s
  /-- all matches in `groups` are subslices of `s`. -/
  areSubslicesOf : ∀ g ∈ groups.filterMap id, String.Slice.isSubslice g s
