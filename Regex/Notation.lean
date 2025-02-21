import Regex.Regex

namespace Regex.Notation

/-!
## Notation

Notation `regex%` to build the regular expression at compile time.
-/

open Lean

def toNumLit (n : Nat) : NumLit :=
  Lean.Syntax.mkNumLit (Nat.repr n)

theorem of_decide_eq_true_ext (p : Prop) (inst : Decidable p) : Eq (decide p) true → p :=
  @of_decide_eq_true p inst

/-- proof of `n` < `m`

  example : 1 < 300 := @of_decide_eq_true (1 < 300) (Nat.decLt 1 300) (Eq.refl true)
-/
private def mkTermOfDecideLt (n m : Nat) : Term :=
  let eq_refl : Term := Syntax.mkApp (mkCIdent ``Eq.refl) #[Quote.quote true]
  let args := #[toNumLit n, toNumLit m]
  let lt_lt := Syntax.mkApp (mkCIdent ``LT.lt) args
  let decLt := Syntax.mkApp (mkCIdent ``Nat.decLt) args

  Syntax.mkApp (mkCIdent ``of_decide_eq_true_ext) #[lt_lt, decLt, eq_refl]

private def mkTermOfFin (f: Fin n) : Term :=
  Syntax.mkApp (mkCIdent ``Fin.mk)
                #[Syntax.mkNumLit (ToString.toString f.val), mkTermOfDecideLt f.val n]

instance : Quote (Fin n) where
  quote := mkTermOfFin

private def mkTermOfUInt32 (n : UInt32) : Term :=
  Syntax.mkApp (mkCIdent `UInt32.mk) #[Quote.quote n.val]

instance : Quote UInt32 where
  quote := mkTermOfUInt32

private def mkTermOfTransition (t: NFA.Checked.Transition n) : Term :=
  Syntax.mkApp (mkCIdent `NFA.Checked.Transition.mk)
                #[Quote.quote t.start, Quote.quote t.«end», Quote.quote t.next]

instance : Quote (NFA.Checked.Transition n) where
  quote := mkTermOfTransition

private def mkTermOfLook (l : NFA.Look) : Term :=
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

instance : Quote NFA.Look where
  quote := mkTermOfLook

private def mkTermOfRole (l : NFA.Capture.Role) : Term :=
  match l with
  | .Start => Syntax.mkApp (mkCIdent ``NFA.Capture.Role.Start) #[]
  | .End => Syntax.mkApp (mkCIdent ``NFA.Capture.Role.End) #[]

instance : Quote NFA.Capture.Role where
  quote := mkTermOfRole

private def mkTermOfEatMode (m : NFA.Checked.EatMode n) : Term :=
  match m with
  | .Until sid => Syntax.mkApp (mkCIdent ``NFA.Checked.EatMode.Until) #[Quote.quote sid]
  | .ToLast sid => Syntax.mkApp (mkCIdent ``NFA.Checked.EatMode.ToLast) #[Quote.quote sid]

instance : Quote (NFA.Checked.EatMode n) where
  quote := mkTermOfEatMode

private def mkTermOfState (s : NFA.Checked.State n) : Term :=
  match s with
  | .Empty next =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Empty) #[Quote.quote next]
  | .NextChar offset next =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.NextChar) #[Quote.quote offset, Quote.quote next]
  | .Fail =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Fail) #[]
  | .Eat m next  =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Eat) #[Quote.quote m, Quote.quote next]
  | .ChangeFrameStep f t =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.ChangeFrameStep) #[Quote.quote f, Quote.quote t]
  | .RemoveFrameStep s =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.RemoveFrameStep) #[Quote.quote s]
  | .BackRef b f sid =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.BackRef) #[Quote.quote b, Quote.quote f, Quote.quote sid]
  | .ByteRange t =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.ByteRange) #[Quote.quote t]
  | .SparseTransitions transitions =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.SparseTransitions) #[Quote.quote transitions]
  | .Look look next =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Look) #[Quote.quote look, Quote.quote next]
  | .Union alts =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Union) #[Quote.quote alts]
  | .UnionReverse alts =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.UnionReverse) #[Quote.quote alts]
  | .BinaryUnion alt1 alt2 =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.BinaryUnion) #[Quote.quote alt1, Quote.quote alt2]
  | .Capture next r id g s =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Capture)
        #[Quote.quote next, Quote.quote r, toNumLit id, toNumLit g, toNumLit s]
  | .Match id =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Match) #[toNumLit id]

instance : Quote (NFA.Checked.State n) where
  quote := mkTermOfState

private def mkTermIsEq (n : Nat) : Term :=
  Syntax.mkApp (mkCIdent ``Eq.refl) #[toNumLit n]

private def mkTermSlotsValid (slots : Term) : Term :=
  let slotsValid := Syntax.mkApp (mkCIdent ``NFA.Checked.Slots.Valid) #[slots]
  Syntax.mkApp (mkCIdent ``Eq.refl) #[slotsValid]

private def mkTermOfNfa (nfa : NFA.Checked.NFA) : Term :=
  let states : Term := Quote.quote nfa.states
  let groups : Term := Quote.quote nfa.groups
  let slots : Term := Quote.quote nfa.slots
  let flag : Term := Quote.quote nfa.unanchored_prefix_in_backtrack
  Syntax.mkApp (mkCIdent `NFA.Checked.NFA.mk) #[toNumLit nfa.n, states, groups, slots, flag,
    mkTermIsEq nfa.n, mkTermSlotsValid slots]

private def mkTermOfRegex (re : Regex) : Term :=
  Syntax.mkApp (mkCIdent `Regex.mk) #[mkTermOfNfa re.nfa]

instance : Quote Regex where
  quote := mkTermOfRegex

declare_syntax_cat regex
syntax str : regex
syntax "regex%" regex : term

/-- build regular expressions at compile time -/
macro_rules
| `(regex% $p:str) =>
    match Regex.build p.getString with
    | Except.ok re => return @Quote.quote _ `term _ re
    | Except.error e => throw <| Lean.Macro.Exception.error p e
