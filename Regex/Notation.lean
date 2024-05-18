import Regex.Regex

namespace Regex.Notation

/-!
## Notation

Notation `regex%` to build the regular expression at compile time.
-/

open Lean

def toNumLit (n : Nat) : NumLit := Lean.Syntax.mkNumLit (ToString.toString n)

theorem eq_true_of_decide_ext (p : Prop) (inst : Decidable p) (h : decide p = true) : p = True :=
  @eq_true_of_decide p inst h

theorem of_eq_true_ext (p : Prop) (h : p = True) : p :=
  @of_eq_true p h

/-- proof of `n` < `m`

  for example

  @of_eq_true (1 < 300)
    (@eq_true_of_decide (1 < 300) (Nat.decLt 1 300) (of_decide_eq_true (Eq.refl true)))
  : 1 < 300

-/
private def mkTermOfDecideLt (n m : Nat) : Term :=
  let eq_refl : Term := Syntax.mkApp (mkCIdent `Eq.refl) #[Quote.quote true]
  let of_decide_eq_true := Syntax.mkApp (mkCIdent ``of_decide_eq_true) #[eq_refl]
  let decLt := Syntax.mkApp (mkCIdent `Nat.decLt) #[toNumLit n, toNumLit m]
  let lt_lt := Syntax.mkApp (mkCIdent `LT.lt) #[toNumLit n, toNumLit m]
  let eq_true_of_decide := Syntax.mkApp (mkCIdent ``eq_true_of_decide_ext)
                            #[lt_lt, decLt, of_decide_eq_true]
  Syntax.mkApp (mkCIdent ``of_eq_true_ext) #[lt_lt, eq_true_of_decide]

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

  for example:

  @of_eq_true (1 = #[1].size) ((congrArg (Eq 1) (Array.size_toArray [1])).trans (eq_self 1))
  : 1 = #[1].size

-/
private def mkTermIsEq (n : Nat) (list : Term) : Term :=
  let mkTermEq :=
        Syntax.mkApp (mkCIdent ``Eq) #[Lean.Syntax.mkNumLit (ToString.toString n)]

  let mkTermEqSelf :=
        Syntax.mkApp (mkCIdent ``eq_self) #[Lean.Syntax.mkNumLit (ToString.toString n)]

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

declare_syntax_cat regex
syntax str : regex
syntax "regex%" regex : term

/-- build regular expressions at compile time -/
macro_rules
| `(regex% $p:str) =>
    match Regex.build p.getString with
    | Except.ok re => return mkTermOfRegex re
    | Except.error e => throw <| Lean.Macro.Exception.error p e
