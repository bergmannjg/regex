import Regex.Syntax.Hir
import Regex.Nfa

namespace Compiler

open Syntax
open NFA

/-!
## Compiler

Compile from a regex's high-level intermediate representation (`Syntax.Hir`)
into an NFA state graph (`NFA`).
-/

/-- The configuration used for a Thompson NFA compiler. -/
structure Config where
  /-- Whether to compile an unanchored prefix into this NFA. -/
  unanchored_prefix: Bool
  /-- Whether to simulate an unanchored prefix with the backtracker. -/
  unanchored_prefix_simulation : Bool

instance : Inhabited Config := ⟨true, false⟩

/-- A value that represents the result of compiling a sub-expression of a regex's HIR.
    Specifically, this represents a sub-graph of the NFA that
    has an initial state at `start` and a final state at `end`.
-/
structure ThompsonRef where
  start: Unchecked.StateID
  «end»: Unchecked.StateID

instance : ToString ThompsonRef where
  toString s := s!"{s.start}, {s.end}"

/-- the next `StateID` of all states in array `arr` is less than size of `arr`. -/
@[simp] def nextOfLt (r : Array Unchecked.State) := ∀ (i : Nat) _, r[i].nextOf < r.size
