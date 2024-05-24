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

instance : Quote NFA.Look where
  quote := mkTermOfLook

private def mkTermOfState (s : NFA.Checked.State n) : Term :=
  match s with
  | .Empty next =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Empty) #[Quote.quote next]
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
  | .Capture next id g s =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Capture)
        #[Quote.quote next, toNumLit id, toNumLit g, toNumLit s]
  | .Match id =>
      Syntax.mkApp (mkCIdent ``NFA.Checked.State.Match) #[toNumLit id]

instance : Quote (NFA.Checked.State n) where
  quote := mkTermOfState

/-- proof of `n` = `list.toArray.size`

  example : 1 = #[1].size :=
    of_eq_true (Eq.trans (congrArg (Eq 1) (Array.size_toArray [1])) (eq_self 1))
-/
private def mkTermIsEq (n : Nat) (list : Term) : Term :=
  let mkTermEq :=
        Syntax.mkApp (mkCIdent ``Eq) #[toNumLit n]

  let mkTermEqSelf :=
        Syntax.mkApp (mkCIdent ``eq_self) #[toNumLit n]

  let mkTermSizeToArray :=
      Syntax.mkApp (mkCIdent ``Array.size_toArray) #[list]

  let mkTermCongrArg (f h : Term) :=
        Syntax.mkApp (mkCIdent ``congrArg) #[f, h]

  let mkTermEqTrans (h1 h2 : Term) :=
        Syntax.mkApp (mkCIdent ``Eq.trans) #[h1, h2]

  let mkTermOfEqTrue (h : Term) :=
        Syntax.mkApp (mkCIdent ``of_eq_true) #[h]

  mkTermOfEqTrue (mkTermEqTrans (mkTermCongrArg mkTermEq mkTermSizeToArray) mkTermEqSelf)

private def mkTermOfNfa (nfa : NFA.Checked.NFA) : Term :=
  let data : Term := Quote.quote nfa.states.data
  let states : Term := Syntax.mkApp (mkCIdent `Array.mk) #[data]
  Syntax.mkApp (mkCIdent `NFA.Checked.NFA.mk)
      #[Lean.Syntax.mkNumLit (ToString.toString nfa.n), states, mkTermIsEq nfa.n data]

private def mkTermOfRegex (re : Regex.Regex) : Term :=
  Syntax.mkApp (mkCIdent `Regex.Regex.mk) #[mkTermOfNfa re.nfa]

instance : Quote Regex.Regex where
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
