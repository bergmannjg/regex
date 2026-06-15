module

public import Regex.Regex
public meta import Regex.Syntax.Hir
public meta import Regex.Compiler.Basic
public meta import Regex.Regex

public section

namespace Regex.Notation

/-!
## Notation

Notation `regex%` to build the regular expression at compile time.
-/

open Lean

meta def toNumLit (n : Nat) : NumLit :=
  Lean.Syntax.mkNumLit (Nat.repr n)

theorem of_decide_eq_true_ext (p : Prop) (inst : Decidable p) : Eq (decide p) true → p :=
  @of_decide_eq_true p inst

/-- proof of `n` < `m`

  example : 1 < 300 := @of_decide_eq_true (1 < 300) (Nat.decLt 1 300) (Eq.refl true)
-/
protected meta def mkTermOfDecideLt (n m : Nat) : Term :=
  let eq_refl : Term := Syntax.mkApp (mkCIdent ``Eq.refl) #[Quote.quote true]
  let args := #[toNumLit n, toNumLit m]
  let lt_lt := Syntax.mkApp (mkCIdent ``LT.lt) args
  let decLt := Syntax.mkApp (mkCIdent ``Nat.decLt) args

  Syntax.mkApp (mkCIdent ``of_decide_eq_true_ext) #[lt_lt, decLt, eq_refl]

protected meta def mkTermOfFin (f: Fin n) : Term :=
  Syntax.mkApp (mkCIdent ``Fin.mk)
                #[Syntax.mkNumLit (ToString.toString f.val), Notation.mkTermOfDecideLt f.val n]

meta instance : Quote (Fin n) where
  quote := Notation.mkTermOfFin

protected meta def mkTermOfUInt32 (n : UInt32) : Term :=
  Syntax.mkApp (mkCIdent `UInt32.mk) #[Quote.quote n.toFin]

meta instance : Quote UInt32 where
  quote := Notation.mkTermOfUInt32

protected meta def mkTermOfTransition (t: NFA.Checked.Transition n) : Term :=
  Syntax.mkApp (mkCIdent `NFA.Checked.Transition.mk)
                #[Quote.quote t.start, Quote.quote t.«end», Quote.quote t.next]

meta instance : Quote (NFA.Checked.Transition n) where
  quote := Notation.mkTermOfTransition

protected meta def mkTermOfLook (l : NFA.Look) : Term :=
  match l with
  | .Start => Syntax.mkApp (mkCIdent ``NFA.Look.Start) #[]
  | .End => Syntax.mkApp (mkCIdent ``NFA.Look.End) #[]
  | .EndWithOptionalLF => Syntax.mkApp (mkCIdent ``NFA.Look.EndWithOptionalLF) #[]
  | .StartLF => Syntax.mkApp (mkCIdent ``NFA.Look.StartLF) #[]
  | .EndLF => Syntax.mkApp (mkCIdent ``NFA.Look.EndLF) #[]
  | .StartCRLF => Syntax.mkApp (mkCIdent ``NFA.Look.StartCRLF) #[]
  | .EndCRLF => Syntax.mkApp (mkCIdent ``NFA.Look.EndCRLF) #[]
  | .WordUnicode => Syntax.mkApp (mkCIdent ``NFA.Look.WordUnicode) #[]
  | .WordUnicodeNegate => Syntax.mkApp (mkCIdent ``NFA.Look.WordUnicodeNegate) #[]
  | .WordStartUnicode => Syntax.mkApp (mkCIdent ``NFA.Look.WordStartUnicode) #[]
  | .WordEndUnicode => Syntax.mkApp (mkCIdent ``NFA.Look.WordEndUnicode) #[]
  | .WordStartHalfUnicode => Syntax.mkApp (mkCIdent ``NFA.Look.WordStartHalfUnicode) #[]
  | .WordEndHalfUnicode => Syntax.mkApp (mkCIdent ``NFA.Look.WordEndHalfUnicode) #[]
  | .PreviousMatch => Syntax.mkApp (mkCIdent ``NFA.Look.PreviousMatch) #[]
  | .ClearMatches => Syntax.mkApp (mkCIdent ``NFA.Look.ClearMatches) #[]

meta instance : Quote NFA.Look where
  quote := Notation.mkTermOfLook

protected meta def mkTermOfRole (r : NFA.Capture.Role) : Term :=
  match r with
  | .Start => Syntax.mkApp (mkCIdent ``NFA.Capture.Role.Start) #[]
  | .End => Syntax.mkApp (mkCIdent ``NFA.Capture.Role.End) #[]

meta instance : Quote NFA.Capture.Role where
  quote := Notation.mkTermOfRole

protected meta def mkTermOfCapture (c : NFA.Capture) : Term :=
  Syntax.mkApp (mkCIdent ``NFA.Capture.mk)
    #[Notation.mkTermOfRole c.role, Quote.quote c.group]

meta instance : Quote NFA.Capture where
  quote := Notation.mkTermOfCapture

protected meta def mkTermOfEatMode (m : NFA.Checked.EatMode n) : Term :=
  match m with
  | .Until sid => Syntax.mkApp (mkCIdent ``NFA.Checked.EatMode.Until) #[Notation.mkTermOfFin sid]
  | .ToLast sid => Syntax.mkApp (mkCIdent ``NFA.Checked.EatMode.ToLast) #[Notation.mkTermOfFin sid]

meta instance : Quote (NFA.Checked.EatMode n) where
  quote := Notation.mkTermOfEatMode

protected meta def mkTermOfState (s : NFA.Checked.State n) : Term :=
  match s with
  | .Empty next =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Empty) #[Notation.mkTermOfFin next]
  | .NextChar offset next =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.NextChar) #[Quote.quote offset, Notation.mkTermOfFin next]
  | .Fail =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Fail) #[]
  | .Eat m next  =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Eat) #[Notation.mkTermOfEatMode m, Notation.mkTermOfFin next]
  | .ChangeFrameStep f t =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.ChangeFrameStep) #[Notation.mkTermOfFin f, Notation.mkTermOfFin t]
  | .RemoveFrameStep s =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.RemoveFrameStep) #[Notation.mkTermOfFin s]
  | .BackRef b f sid =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.BackRef) #[Quote.quote b, Quote.quote f, Notation.mkTermOfFin sid]
  | .ByteRange t =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.ByteRange) #[Notation.mkTermOfTransition t]
  | .SparseTransitions transitions =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.SparseTransitions) #[Quote.quote transitions]
  | .Look look next =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Look) #[Notation.mkTermOfLook look, Notation.mkTermOfFin next]
  | .Union alts =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Union) #[Quote.quote alts]
  | .UnionReverse alts =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.UnionReverse) #[Quote.quote alts]
  | .BinaryUnion alt1 alt2 =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.BinaryUnion) #[Notation.mkTermOfFin alt1, Notation.mkTermOfFin alt2]
  | .Capture next r id g =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Capture)
        #[Notation.mkTermOfRole next, Notation.mkTermOfFin r, toNumLit id, toNumLit g]
  | .Match id =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Match) #[toNumLit id]

meta instance : Quote (NFA.Checked.State n) where
  quote := Notation.mkTermOfState

protected meta def mkTermIsEq (n : Nat) : Term :=
  Syntax.mkApp (mkCIdent ``Eq.refl) #[toNumLit n]

protected meta def mkTermCapturesValid (captures : Term) : Term :=
  Syntax.mkApp (mkCIdent ``NFA.CapturesValidOfRangeMap) #[captures,
      Syntax.mkApp (mkCIdent ``rfl) #[]]

protected meta def mkTermOfNfa (nfa : NFA.Checked.NFA) : Term :=
  let states : Term := Quote.quote nfa.states
  let groups : Term := Quote.quote nfa.groups
  let captures : Term := Quote.quote nfa.captures
  let flag : Term := Quote.quote nfa.unanchored_prefix_in_backtrack
  Syntax.mkApp (mkCIdent `NFA.Checked.NFA.mk) #[toNumLit nfa.n, states, groups, captures, flag,
    Notation.mkTermIsEq nfa.n, Notation.mkTermCapturesValid captures]

protected meta def mkTermOfRegex (re : Regex) : Term :=
  Syntax.mkApp (mkCIdent `Regex.mk) #[Notation.mkTermOfNfa re.nfa]

meta instance : Quote Regex where
  quote := Notation.mkTermOfRegex

declare_syntax_cat regex
syntax str : regex
syntax "regex%" regex : term

/-- build regular expressions at compile time -/
macro_rules
| `(regex% $p:str) =>
    match Regex.build p.getString with
    | Except.ok re => return  @Quote.quote _ `term _ re
    | Except.error e => throw <| Lean.Macro.Exception.error p e
