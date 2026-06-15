module

public import Regex.Compiler.Basic
public import Regex.Compiler.Compile
public import Regex.Compiler.Lemmas.Basic
public import Regex.Compiler.Lemmas.Patch
public import Regex.Compiler.Lemmas.AddState
public import Regex.Compiler.Lemmas.Compile

namespace Compiler

open Regex.Syntax
open NFA

private def startsWithStart (hir : Hir) : Bool :=
  match hir.kind with
  | .Concat hirs =>
    match hirs.head? with
    | some (⟨HirKind.Look Regex.Syntax.Look.Start, _⟩  , _) => true
    | _ => false
  | _ => false

/-- Compile the HIR expression given. -/
public def compile (config : Config := default) (flavor : Regex.Syntax.Flavor) (expr : Hir) : Checked.NFA :=
  let unanchored_prefix_simulation := expr.containsLookaround || config.unanchored_prefix_simulation
  let anchored := !config.unanchored_prefix || startsWithStart expr || unanchored_prefix_simulation
  let res := Code.compile anchored expr (#[], #[], #[])
  have : ∃ _, res = EStateM.Result.ok () _ := Lemmas.compile_eq_ok
  match hm : res with
  | EStateM.Result.ok () (states, captures, groups) =>
    let nfa := NFA.toCkecked ⟨states, 0, 0⟩ captures.mergeSort.unique
                (match flavor with | Regex.Syntax.Flavor.Pcre => groups | _ => #[])
                (NextOfLt.forall (Lemmas.compile_nextOf_lt hm))
                (by
                  have := Lemmas.compile_captures_valid hm
                  grind only [valid_sorted_of_valid, valid_unique_of_valid])
    {nfa with unanchored_prefix_in_backtrack :=
                    !startsWithStart expr && unanchored_prefix_simulation}
