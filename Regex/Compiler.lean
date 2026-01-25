import Regex.Compiler.Basic
import Regex.Compiler.Compile
import Regex.Compiler.Lemmas.Basic
import Regex.Compiler.Lemmas.Patch
import Regex.Compiler.Lemmas.AddState
import Regex.Compiler.Lemmas.Compile

namespace Compiler

open Syntax
open NFA

private def startsWithStart (hir : Hir) : Bool :=
  match hir.kind with
  | .Concat hirs =>
    match hirs.head? with
    | some (⟨HirKind.Look Syntax.Look.Start, _⟩  , _) => true
    | _ => false
  | _ => false

/-- Compile the HIR expression given. -/
def compile (config : Config := default) (flavor : Syntax.Flavor) (expr : Hir) : Checked.NFA :=
  let unanchored_prefix_simulation := expr.containsLookaround || config.unanchored_prefix_simulation
  let anchored := !config.unanchored_prefix || startsWithStart expr || unanchored_prefix_simulation
  let res := Code.compile anchored expr (#[], #[], #[])
  have : ∃ _, res = EStateM.Result.ok () _ := Lemmas.compile_eq_ok
  match hm : res with
  | EStateM.Result.ok () (states, captures, groups) =>
    let nfa := NFA.toCkecked ⟨states, 0, 0⟩ captures.mergeSort.unique
                (match flavor with | Syntax.Flavor.Pcre => groups | _ => #[])
                (NextOfLt.forall (Lemmas.compile_nextOf_lt hm))
                (by
                  have := Lemmas.compile_captures_valid hm
                  grind only [valid_sorted_of_valid, valid_unique_of_valid])
    {nfa with unanchored_prefix_in_backtrack :=
                    !startsWithStart expr && unanchored_prefix_simulation}
