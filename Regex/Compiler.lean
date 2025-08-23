import Regex.Compiler.Basic
import Regex.Compiler.Compile
import Regex.Compiler.Lemmas

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
def compile (config : Config := default) (flavor : Syntax.Flavor) (expr : Hir)
    : Except String Checked.NFA := do
  let unanchored_prefix_simulation := expr.containsLookaround || config.unanchored_prefix_simulation
  let anchored := !config.unanchored_prefix || startsWithStart expr || unanchored_prefix_simulation
  match hm : Code.compile anchored expr (#[], #[]) with
  | EStateM.Result.ok _ (states, groups) =>
    let nfa ← NFA.toCkecked ⟨states, Unchecked.toSlots states, 0, 0⟩
                (match flavor with | Syntax.Flavor.Pcre => groups | _ => #[])
                (Lemmas.compile_nextOf_lt hm)
    Except.ok {nfa with unanchored_prefix_in_backtrack :=
                    !startsWithStart expr && unanchored_prefix_simulation}
  | EStateM.Result.error e _ => Except.error e
