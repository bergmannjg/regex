import Regex.NFA.Basic
import Regex.NFA.Lemmas

namespace NFA

/-!
## NFA

A byte oriented [Thompson](https://en.wikipedia.org/wiki/Thompson%27s_construction)
non-deterministic finite automaton (`Checked.NFA`),
see also [Tagged NFA](https://en.wikipedia.org/wiki/Tagged_Deterministic_Finite_Automaton).
-/

/-- transform Unchecked.NFA to Checked.NFA -/
def toCkecked (nfa : Unchecked.NFA) (captures : Array NFA.Capture) (groups : Array Nat)
  (hs : ∀ (i : Nat) _, nfa.states[i].nextOf < nfa.states.size)
  (hv : NFA.Capture.valid captures) : Checked.NFA :=
  let states := nfa.states.attach.map (toFun nfa.states hs)
  ⟨nfa.states.size, states, groups, NFA.Capture.toSlots captures, false,
    by grind, toSlots_valid captures hv⟩

end NFA

open NFA

/-- A compiled regular expression for searching Unicode haystacks. -/
structure Regex where
  nfa : Checked.NFA

instance : ToString Regex where
  toString m := s!"{m.nfa}"
