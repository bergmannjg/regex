import Regex.Syntax.Grammar.Grammar
import Regex.Data.Array.Basic
import Regex.Data.Array.Lemmas
import Batteries.Data.Array.Basic

open Lean Lean.Parser

/-!
## Translate

Rearrange alternatives and repetitions in a `Syntax` tree.
-/
namespace Regex.Grammar

private def isNegation (x : Syntax) :=
  match x with
  | Syntax.node _ `literal #[Lean.Syntax.atom _ "^"] => true
  | _ => false


private def isVerticalBar (x : Syntax) : Bool :=
  match x with
  | Syntax.node _ `verticalBar _ => true
  | _ => false

private def isHyphen (x : Syntax) : Bool :=
  match x with
  | Syntax.node _ `hyphen _ => true
  | _ => false

private def isCharacterClassSetOperation (x : Syntax) : Option Syntax :=
  match x with
  | Syntax.node _ `characterClassSetOperation #[op] => op
  | _ => none

private def getSequenceArr? (x : Syntax) : Option $ Array Syntax :=
  match x with
  | Syntax.node _ `sequence arr => some arr
  | _ => none

private def sourceInfoOf (arr : Array Syntax) : SourceInfo :=
  match arr.data.head?, arr.data.getLast? with
  | some (.node (.synthetic pos _) _ _), some (.node (.synthetic _ endPos) _ _)
      => SourceInfo.synthetic pos endPos
  | _, _ => SourceInfo.none

private def intoSequence (arr : Array Syntax) : Syntax :=
  match arr with
  | #[stx] => stx
  | _ => Syntax.node (SourceInfo.synthetic 0 0) `sequence arr

private def addAlternatives (alternatives arr : Array Syntax) : Array Syntax :=
    if alternatives.size > 0
    then
      let info := sourceInfoOf arr
      let alternatives :=
        Syntax.node info `alternatives (alternatives ++ #[intoSequence arr])
      #[alternatives]
    else arr

private def addPrev (prev : Option Syntax) (stxs : Array Syntax) : Array Syntax :=
  match prev with | some stx => stxs ++ #[stx] | none => stxs

/-- add the previous node to a repetition node -/
private def rearrangeRepetition (prev : Option Syntax) (x : Syntax)
    : Except String $ Option Syntax × Option Syntax :=
  match prev, x with
  | some prev', Syntax.node info `repetition arr =>
      let rep := Syntax.node info `repetition  (arr ++ #[prev'])
      pure (some rep, none)
  | _, _ => pure (prev, some x)

private def popNegation? (arr : List Syntax) : Option $ Syntax × List Syntax :=
  match arr with
  | head :: tail => if isNegation head then some (head, tail) else none
  | _ => none

mutual

private def parseVal (x : Syntax) : Except String Syntax := do
  match x with
  | Syntax.node info `group arr => pure $ ← parseGroup info arr
  | Syntax.node info `characterClass arr => pure $ ← parseCharacterClass info arr
  | _ => pure x
termination_by sizeOf x

private def parseGroup (info : SourceInfo) (arr : Array Syntax) : Except String Syntax := do
  match h : arr.head? with
  | some (kind, arr') =>
    have : sizeOf arr' < sizeOf arr := Array.sizeOf_head?_of_tail h
    pure $ Syntax.node info `group (#[kind] ++ (← fold arr'))
  | _ => Except.error "group array is empty"
termination_by sizeOf arr

private def parseCharacterClassItems (arr : List Syntax) (acc : List Syntax := [])
    : List Syntax :=
  match arr with
  | [] => acc
  | first :: second :: third :: tail =>
    if let some arr' := getSequenceArr? first then
      parseCharacterClassItems (second :: third :: tail) ((List.reverse arr'.data) ++ acc)
    else if let some op := isCharacterClassSetOperation first then
      let rest := parseCharacterClassItems (second :: third :: tail) []
      let intersection := Syntax.node .none `characterClassSetOperation #[
          Syntax.node .none  `op #[op],
          Syntax.node .none  `first acc.toArray,
          Syntax.node .none  `second rest.toArray]
      [intersection]
    else if isHyphen second then
      let hyphen := Syntax.node .none `range #[first, third]
      parseCharacterClassItems tail (hyphen :: acc)
    else parseCharacterClassItems (second :: third :: tail) (first :: acc)
  | head :: tail =>
    if let some arr' := getSequenceArr? head then
      parseCharacterClassItems tail ((List.reverse arr'.data) ++ acc)
    else if let some op := isCharacterClassSetOperation head then
      let rest := parseCharacterClassItems tail []
      let intersection := Syntax.node .none `characterClassSetOperation #[
          Syntax.node .none  `op #[op],
          Syntax.node .none  `first acc.toArray,
          Syntax.node .none  `second rest.toArray]
      [intersection]
    else
      parseCharacterClassItems tail (head :: acc)
termination_by sizeOf arr

private def parseCharacterClass (info : SourceInfo) (arr : Array Syntax)
    : Except String Syntax := do
  let items :=
    if let some (neg, tail) := popNegation? arr.data
    then neg :: (parseCharacterClassItems tail |> List.reverse)
    else parseCharacterClassItems arr.data |> List.reverse
  pure $ Syntax.node info `characterClass items.toArray

private def folder (acc : Option Syntax × Array Syntax × Array Syntax) (x : Syntax)
    (parseVal : (s : Syntax) → Except String Syntax)
    : Except String $ Option Syntax × Array Syntax × Array Syntax := do
  let (prev, stack, arr) := acc
  if isVerticalBar x
  then
    pure (none, stack ++ #[intoSequence (addPrev prev arr)], #[])
  else
    let stx ← parseVal x
    let (prev, stx?) ← rearrangeRepetition prev stx
    pure $ (stx?, stack, (addPrev prev arr))

private def fold (arr : Array Syntax) : Except String $ Array Syntax := do
  let (prev, stack, stxs)  ←
      arr.attach.foldlM (fun acc (h : { x // x ∈ arr}) =>
        have : sizeOf h.val < sizeOf arr := Array.sizeOf_lt_of_mem h.property
        folder acc h.val (fun _ => parseVal h.val)) (none, #[], #[])
  pure $ addAlternatives stack (addPrev prev stxs)
termination_by sizeOf arr

end

/-- Rearrange alternatives, character classes and repetitions in `x`. -/
def translate (x : TSyntax `sequence) : Except String $ TSyntax `sequence := do
  match x.raw with
  | Syntax.node info `sequence arr =>
      fold arr >>= (fun arr => pure $ TSyntax.mk (Syntax.node info `sequence arr))
  | _ => Except.error s!"ill-formed sequence syntax {x}"
