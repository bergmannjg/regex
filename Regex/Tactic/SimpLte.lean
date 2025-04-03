import Lean.Elab.Tactic
import Lean.PrettyPrinter.Delaborator.Basic

import Regex.Data.Nat.Basic

namespace SimpLte

/-!
## SimpLte Tactic

Try to prove goals like `LT.lt` or `LE.le` from local declarations
    of type `LT.lt`, `LE.le`, `EQ`, `And` or `Subtype` using `Nat` theorems.
-/

open Lean.Elab.Tactic Lean.Meta Lean

private inductive FunType where | LT | LE | EQ deriving Repr, BEq

private instance : ToString FunType where
  toString | .LT => "LT" | .LE => "LE" | .EQ => "EQ"

private abbrev Entry := FunType × Lean.Expr × Lean.Expr

private abbrev Decl := Lean.LocalDecl × (Expr → Expr) × Entry

private instance : ToString Decl where
  toString d := s!"{d.1.userName}/{d.1.fvarId.name}"

private instance : BEq Decl where
  beq | (_, _, fa, a1, a2), (_, _, fb, b1, b2) => fa == fb && a1 == b1 && a2 == b2

private def isFrom (f : Lean.Expr) : Decl → MetaM Bool
  | (_, _, _, a, _) => do
    let eq ← isExprDefEq a f
    pure eq

private def isTo (t : Lean.Expr) : Decl → MetaM Bool
  | (_, _, _, _, b) => do
    let eq ← isExprDefEq b t
    pure eq

/-- depth first search for path from `f` to `t` in list `decls`. -/
private def tryFindPath (_f _t : Lean.Expr) (decls : List Decl) : MetaM $ Option (List Decl) := do
  trace[debug] s!"tryFindPath, from: {_f}, to: {_t}"
  if ← isExprDefEq _f _t then pure $ some [] else
  let (success, path) ← loop _f _t decls (false, [])
  trace[debug] s!"tryFindPath.result, success: {success}, path: {path}"
  if success then pure (List.reverse path) else pure none
  where loop f t decls _acc : MetaM $ Bool × List Decl := do
    let decls' : List (Decl × Bool) ← decls.mapM (fun (d : Decl) => do pure (d, ← isFrom f d))
    match decls'.filter (·.2) with
    | [] => pure (false, [])
    | l =>
      let res ← l.foldlM (init := _acc) (fun acc (decl, _) => do
        if acc.1 then pure $ acc
        else if (← isTo t decl) then pure (← isExprDefEq t _t, decl :: _acc.2)
        else
          let decls' := decls.filter (· != decl)
          if decls'.length < decls.length -- todo: prove it
          then loop decl.2.2.2.2 t decls' (acc.1, (decl :: _acc.2))
          else pure (true, []))
      pure res
termination_by decls.length

private def delabWithPath (d : LocalDecl) (path : Expr → Expr) : MetaM Term := do
  PrettyPrinter.delab (path d.toExpr)

private def delabProof (proof : List Decl) : MetaM $ Option $ Syntax.Term := do
  loop 0 proof
  where loop (n : Nat) : List Decl → (MetaM  (Option (Syntax.Term)))
    | [] => pure none
    | [(d, path, .LE, _, _)] => do
      pure $ (← delabWithPath d path)
    | [(d,  path,.LT, _, _)] => do
      if n = 0 then pure $ (← delabWithPath d path)
      else pure $ (Syntax.mkApp (mkCIdent ``Nat.le_of_lt) #[(← delabWithPath d path)])
    | [(d,  path,.EQ, _, _)] => do
      if n = 0 then pure $ (← delabWithPath d path)
      else pure $ Syntax.mkApp (mkCIdent ``Nat.le_of_eq) #[← delabWithPath d path]
    | (d,  path,.LE, _, _) :: tail => do
      match ← loop (n + 1) tail with
      | some tail =>
        pure (Syntax.mkApp (mkCIdent ``Nat.le_trans) #[← delabWithPath d path, tail])
      | none => pure none
    | (d,  path,.EQ, _, _) :: tail => do
      match ← loop (n + 1) tail with
      | some tail =>
        pure (Syntax.mkApp (mkCIdent ``Nat.le_trans)
          #[Syntax.mkApp (mkCIdent ``Nat.le_of_eq) #[← delabWithPath d path], tail])
      | none => pure none
    | (d, path, .LT, _, _) :: tail => do
      match ← loop (n + 1) tail with
      | some tail =>
        if n = 0 then pure (Syntax.mkApp (mkCIdent ``Nat.le_trans)
          #[← delabWithPath d path, tail])
        else pure (Syntax.mkApp (mkCIdent ``Nat.le_trans)
          #[Syntax.mkApp (mkCIdent ``Nat.le_of_lt) #[(← delabWithPath d path)], tail])
      | none => pure none

private def toEntry (e : Lean.Expr) : Option Entry :=
  let e :=  match e with | .mdata _ e => e | _ => e
  if let some (_, _, arg1, arg2) := e.app4? ``LT.lt then
    some (FunType.LT, arg1, arg2)
  else if let some (_, _, arg1, arg2) := e.app4? ``LE.le then
    some (FunType.LE, arg1, arg2)
  else if let some (_, arg1, arg2) := e.app3? ``Eq then
    some (FunType.EQ, arg1, arg2)
  else none

private def flattenAnd (e : Lean.Expr) (acc : Lean.Expr → Lean.Expr)
    : MetaM $ List (Lean.Expr × (Lean.Expr → Lean.Expr)) := do
  if let some (arg1, arg2) := e.app2? ``And
  then
    if let some (arg21, arg22) := arg2.app2? ``And
    then
      pure [
        (arg1, (fun e => Lean.mkProj ``And 0 (acc e))),
        (arg21, (fun e => Lean.mkProj ``And 0 (Lean.mkProj ``And 1 (acc e)))),
        (arg22, (fun e => Lean.mkProj ``And 1 (Lean.mkProj ``And 1 (acc e))))]
    else pure [
      (arg1, (fun e => Lean.mkProj ``And 0 (acc e))),
      (arg2, (fun e => Lean.mkProj ``And 1 (acc e)))]
  else pure [(e, acc)]

private def flattenSubtype (fvarId : FVarId) (e : Lean.Expr) (acc : Lean.Expr → Lean.Expr)
    : MetaM $ Lean.Expr × (Lean.Expr → Lean.Expr) := do
  if let some (_, p) := e.app2? ``Subtype
  then
    let p' := Expr.beta p #[(Lean.mkProj ``Subtype 0 (mkFVar fvarId))]
    pure (p', fun e => Lean.mkProj ``Subtype 1 e)
  else pure (e, acc)

/-- Flatten `And` and `Subtype`. -/
private partial def flatten (fvarId : FVarId) (e : Lean.Expr)
    : MetaM $ List (Lean.Expr × (Lean.Expr → Lean.Expr)) := do
  let (e, acc) ← flattenSubtype fvarId e id
  flattenAnd e acc

private def toDecls (decl : LocalDecl) : MetaM $ List Decl := do
  let e ← inferType decl.toExpr
  let decls := (← flatten decl.fvarId e) |> .filterMap (fun (e, path) =>
                 toEntry e |> .map (fun e => (decl, path, e)))
  trace[debug] s!"decl: {decl.userName}, fvarId {decl.fvarId.name} , decls: {decls}"
  pure decls

private def tryCloseGoal (goal : Entry) (decls : List Decl) : MetaM $ Option Syntax.Term := do
  match goal with | ⟨ft, a, b⟩ => do
    match ← tryFindPath a b decls with
    | some [] =>
      trace[debug] s!"path: []"
      if ft == FunType.EQ
      then pure $ (Syntax.mkApp (mkCIdent ``rfl) #[])
      else if ft == FunType.LE
      then pure $ (Syntax.mkApp (mkCIdent ``Nat.le_refl) #[(← PrettyPrinter.delab a)])
      else pure none
    | some path =>
      trace[debug] s!"path: {path}"
      pure (← delabProof path)
    | none => pure none

private def printTerm (t : Syntax) : String :=
  let kindApp : Lean.Name := ``Lean.Parser.Term.app
  match t with
  | .node _ ``Lean.Parser.Term.proj args =>
      match args with
      | #[Syntax.ident _ _  a _, _, Syntax.node _ _ #[Syntax.atom _ v]] => s!"{printName a}.{v} "
      | #[Syntax.node _ ``Lean.Parser.Term.proj
          #[Syntax.ident _ _  a _, _, Syntax.node _ _ #[Syntax.atom _ v1]],
             _, Syntax.node _ _ #[Syntax.atom _ v2]] => s!"{printName a}.{v1}.{v2} "
      | _ => s!"{t}"
  | .node _ kind args =>
    let strings := args.attach.map (fun ⟨t, _⟩ => printTerm t)
    let sOpen := if kindApp = kind then "(" else ""
    let sClose := if kindApp = kind then ") " else ""
    sOpen ++ String.join strings.toList ++ sClose
  | .ident _ _ v _ => s!" {printName v} "
  | _ => s!""
  where printName (t : Name) : String :=
    toString t.eraseMacroScopes

/-- rename decls with same name, see `Lean.Elab.Tactic.renameInaccessibles`. -/
def renameShadowed (mvarId : MVarId) : TacticM MVarId := do
  let mvarDecl ← mvarId.getDecl
  let mut lctx  := mvarDecl.lctx
  let mut info  := #[]
  let mut found : NameSet := {}
  let n := lctx.numIndices
  for i in [:n] do
    let j := n - i - 1
    match lctx.getAt? j with
    | none => pure ()
    | some localDecl =>
      if localDecl.isImplementationDetail then
        continue
      let shadowed := found.contains localDecl.userName
      if shadowed then
        let newName := Name.mkStr localDecl.userName (toString j)
        trace[debug] f!"renameShadowed  {localDecl.userName}/{localDecl.fvarId.name} to {newName}"
        let h : TSyntax `ident := mkIdent newName
        lctx := lctx.setUserName localDecl.fvarId newName
        info := info.push (localDecl.fvarId, h)
      found := found.insert localDecl.userName
  if info.size = 0 then return mvarId else
  let mvarNew ← mkFreshExprMVarAt lctx mvarDecl.localInstances mvarDecl.type MetavarKind.syntheticOpaque mvarDecl.userName
  Elab.withSaveInfoContext <| mvarNew.mvarId!.withContext do
    for (fvarId, stx) in info do
      Elab.Term.addLocalVarInfo stx (mkFVar fvarId)
  mvarId.assign mvarNew
  return mvarNew.mvarId!

private def evalSimpLte (stx : Syntax) (onlySuggestion : Bool) : TacticM PUnit :=
  Lean.Elab.Tactic.withMainContext do
    replaceMainGoal [← renameShadowed (← getMainGoal)]
    let mvarId ← getMainGoal
    match toEntry (← instantiateMVars (← mvarId.getDecl).type) with
    | some goal => do
      trace[debug] f!"goal: {goal}"
      let ctx := (← mvarId.getDecl).lctx
      let options := (← getOptions).set ``pp.sanitizeNames true
      let ctx := if onlySuggestion then ctx.sanitizeNames.run' { options := options } else ctx
      Meta.withLCtx ctx #[] do solve goal ctx
    | none =>  throwError "couldn't find goal"
  where solve goal ctx : TacticM PUnit := do
    let decls ← ctx.foldlM (init := []) (fun acc d => do pure (List.append acc (← toDecls d)))
    match ← tryCloseGoal goal decls with
    | some proof =>
      if onlySuggestion then
          trace[debug] f!"proof: {proof.raw}"
          Tactic.TryThis.addSuggestion stx
            ⟨Tactic.TryThis.SuggestionText.string s!"exact {printTerm proof.raw}",
            none, none, none, none, none⟩
      else
        trace[debug] f!"proof: {proof.raw}"
        Elab.Tactic.tryCatch
          (closeMainGoalUsing `exact (fun type _ => do elabTermEnsuringType proof type) true)
           (fun _ => do throwError s!"couldn't close main goal")
    | none =>  throwError "couldn't find proof in {decls.length} decls to close the goal {goal}"

/-- Show proof of goals like `LT.lt` or `LE.le` from local declarations
    of type `LT.lt`, `LE.le` or `EQ` using `Nat` theorems.  -/
syntax "simp_lte?" : tactic

elab_rules : tactic
  | `(tactic| simp_lte?%$tk) => evalSimpLte tk true

/-- try to prove goals like `LT.lt` or `LE.le` from local declarations
    of type `LT.lt`, `LE.le` or `EQ` using `Nat` theorems.  -/
syntax "simp_lte" : tactic

elab_rules : tactic
  | `(tactic| simp_lte%$tk) => evalSimpLte tk false

/--
info: Try this: exact ( Nat.le_trans  hab ( Nat.le_trans  hbc ( Nat.le_of_eq  hcd ) ) )
-/
#guard_msgs in
example{a b c d : Nat} (hab : a < b) (hbc : b ≤ c) (hcd : c = d) : a < d := by
  simp_lte?
  exact ( Nat.le_trans  hab ( Nat.le_trans  hbc ( Nat.le_of_eq  hcd ) ) )

example{a b c d : Nat} (hab : a < b) (hbc : b ≤ c) (hcd : c = d) : a < d := by
  simp_lte

/--
info: Try this: exact ( Nat.le_trans  hab ( Nat.le_trans ( Nat.le_of_lt  hbc ) ( Nat.le_of_eq  hcd ) ) )
-/
#guard_msgs in
example{a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c = d) : a < d := by
  simp_lte?
  exact ( Nat.le_trans  hab ( Nat.le_trans ( Nat.le_of_lt  hbc ) ( Nat.le_of_eq  hcd ) ) )

example{a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c = d) : a < d := by
  simp_lte

/--
info: Try this: exact ( Nat.le_trans  hab ( Nat.le_trans ( Nat.le_of_lt  hbc )  hcd ) )
-/
#guard_msgs in
example{a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c ≤ d) : a < d := by
  simp_lte?
  exact ( Nat.le_trans  hab ( Nat.le_trans ( Nat.le_of_lt  hbc )  hcd ) )

example{a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c ≤ d) : a < d := by
  simp_lte

/--
info: Try this: exact ( Nat.le_trans  hab ( Nat.le_trans  hbc  hcd ) )
-/
#guard_msgs in
example{a b c d : Nat} (hab : a < b) (hbc : b ≤ c) (hcd : c ≤ d) : a < d := by
  simp_lte?
  exact ( Nat.le_trans  hab ( Nat.le_trans  hbc  hcd ) )

example{a b c d : Nat} (hab : a < b) (hbc : b ≤ c) (hcd : c ≤ d) : a < d := by
  simp_lte

/--
error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.
-/
#guard_msgs in
example{a b c d : Nat} (hab : a < b) (hbc : b ≤ c) (hcd : c ≤ d) : a < d := by
  exact?

/--
info: Try this: exact ( Nat.le_trans  hab ( Nat.le_trans ( Nat.le_of_lt  hbc ) ( Nat.le_of_lt  hcd ) ) )
-/
#guard_msgs in
example{a b c d : Nat} (l : Array Nat) (l' : {a : Array Nat // 0 < a.size})
  (hab : (a, b).fst < (b, l').snd.val.size) (hbc : l'.val.size < (c, l).snd.size)
  (hcd : l.size < d)  : a < d := by
  simp_lte?
  exact ( Nat.le_trans  hab ( Nat.le_trans ( Nat.le_of_lt  hbc ) ( Nat.le_of_lt  hcd ) ) )

example{a b c d : Nat} (l : Array Nat) (l' : {a : Array Nat // 0 < a.size})
  (hab : (a, b).fst < (b, l').snd.val.size) (hbc : l'.val.size < (c, l).snd.size)
  (hcd : l.size < d)  : a < d := by
  simp_lte

set_option linter.unusedVariables false
example{a b c d : Nat} (hab : a < b) (hab' : a < d) (hbc : b ≤ c) (hcd : c ≤ d) : a < d := by
  simp_lte

/--
info: Try this: exact ( Nat.le_trans habc.1 ( Nat.le_trans ( Nat.le_of_lt habc.2 )  hcd ) )
-/
#guard_msgs in
example{a b c d : Nat} (habc : a < b ∧ b < c) (hcd : c ≤ d) : a < d := by
  simp_lte?
  exact ( Nat.le_trans habc.1 ( Nat.le_trans ( Nat.le_of_lt habc.2 )  hcd ) )

/--
info: Try this: exact ( Nat.le_trans h.1 ( Nat.le_trans ( Nat.le_of_lt h.2.1 ) h.2.2 ) )
-/
#guard_msgs in
example{a b c d : Nat} (h : a < b ∧ b < c ∧ c ≤ d) : a < d := by
  simp_lte?
  exact ( Nat.le_trans h.1 ( Nat.le_trans ( Nat.le_of_lt h.2.1 ) h.2.2 ) )

/--
info: Try this: exact ( Nat.le_trans  hab ( Nat.le_trans ( Nat.le_of_lt  hbc ) ( Nat.le_of_lt  hcd ) ) )
-/
#guard_msgs in
example{a b c d e : Nat} (hab : a < b) (hbc : b < c) (hce : c < e) (hcd : c < d) : a < d := by
  simp_lte?
  exact ( Nat.le_trans  hab ( Nat.le_trans ( Nat.le_of_lt  hbc ) ( Nat.le_of_lt  hcd ) ) )
