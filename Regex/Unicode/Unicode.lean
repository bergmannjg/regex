import Init.Data.Fin.Lemmas
import UnicodeBasic
import UnicodeData.Basic
import UnicodeData.PropList
import Regex.Interval
import Regex.Unicode.Properties
import Regex.Unicode.SentenceBreakProperty
import Regex.Unicode.WordBreakProperty
import Regex.Unicode.GraphemeBreakProperty
import Regex.Unicode.DerivedCoreProperties
import Regex.Unicode.Emoji
import Regex.Unicode.Scripts
import Regex.Data.Char.Basic

/-!
## Unicode

Support for [Unicode Regular Expressions Level 1](https://unicode.org/reports/tr18/#RL1.2)
-/

namespace Unicode

private def getUnassigned : Array (NonemptyInterval Char) :=
  let init : Option UInt32 × Array (UInt32 × UInt32) := (none, #[])
  let (prev, arr) := UnicodeData.data |> Array.foldl (init := init) (fun (prev, acc) d =>
    match prev with
    | some prev =>
      if d.code - prev = 1 then (d.code, acc)
      else (none, acc.push (prev + 1, d.code - 1))
    | none => (d.code, acc))

  let arr :=
    match prev with
    | some prev => arr.push (prev, Unicode.max)
    | none => arr

  arr |> Array.map (fun ((n1, n2) : UInt32 × UInt32)=> toRange (n1, (some n2)))

private def fold (data : Array UnicodeData) : Array (Char × Char) :=
  let (last, pairs) : (Char × Char) × Array (Char × Char) :=
    data
    |> Array.foldl (init := ((⟨0, by grind⟩, ⟨0, by grind⟩), #[])) (fun (last, s) a =>
        if h : UInt32.isValidChar a.code
        then
          let c : Char := ⟨a.code, h⟩
          if c.val - last.2.val = 1
          then ((last.1, c), s)
          else ((c, c), if last.1.val != 0 then (s.push last) else s)
        else (last, s))

  pairs.push last

def rangesOfGeneralCategory (category : GC) : Except String $ Array (NonemptyInterval Char) :=
  if category = GC.Cn
  then
    Except.ok getUnassigned
  else
    let arr :=
        UnicodeData.data
        |> .filter (fun u => u.gc ⊆ category)
        |> fold
        |> .filterMap (fun (c1, c2) => if h : c1 ≤ c2 then some ⟨⟨c1, c2⟩, h⟩ else none)
    Except.ok $ if category = GC.C then arr ++ getUnassigned else arr

private def rangesOfCategory (s : String) : Except String $ Array (NonemptyInterval Char) :=
  match GeneralCategory.ofValue? s with
  | some category => rangesOfGeneralCategory category
  | none => Except.error s!"category {s} not found"

private def property_map (arr : Array (UInt32 × Option UInt32)) : Array (NonemptyInterval Char) :=
  arr.map (fun (n, m) =>
    let a : Char := if h : UInt32.isValidChar n then ⟨n, h⟩ else 'x'
    let b : Char :=
      match m with
      | some m => if h : UInt32.isValidChar m then ⟨m, h⟩ else 'x'
      | none => a
    (a, b))
  |> .filterMap (fun (c1, c2) => if h : c1 ≤ c2 then some ⟨⟨c1, c2⟩, h⟩ else none)

private def rangessOfPropertyName (name : PropertyName) (prop : String)
    : Except String $ Array (NonemptyInterval Char) := do
  match name with
  | .General_Category => rangesOfCategory prop
  | .White_Space => Except.ok (property_map PropList.data.whiteSpace)
  | .Alphabetic => rangesOfDerivedCoreProperty "Alphabetic"
  | .Uppercase => rangesOfDerivedCoreProperty "Uppercase"
  | .Lowercase => rangesOfDerivedCoreProperty "Lowercase"
  | .Emoji => getEmoji "Emoji"
  | .Extended_Pictographic => getEmoji "Extended_Pictographic"
  | .Grapheme_Cluster_Break => rangesOfGraphemeBreak prop
  | .Sentence_Break => rangesOfSentenceBreak prop
  | .Word_Break => getWordBreak prop
  | .Math => rangesOfDerivedCoreProperty "Math"
  | .Regional_Indicator => getWordBreak "Regional_Indicator"
  | .Script => rangesOfScript prop
  | .ASCII_Hex_Digit =>
      Except.ok #[⟨⟨'0','9'⟩, by simp +arith⟩, ⟨⟨'A','F'⟩, by simp +arith⟩, ⟨⟨'a','f'⟩, by simp +arith⟩]
  | .Hex_Digit =>
      Except.ok #[⟨⟨'0','9'⟩, by simp +arith⟩, ⟨⟨'A','F'⟩, by simp +arith⟩, ⟨⟨'a','f'⟩, by simp +arith⟩]
  | .Numeric_Value => rangesOfGeneralCategory GC.N
  | .ASSIGNED => Except.ok (IntervalSet.negate (IntervalSet.canonicalize getUnassigned)).intervals
  | .ASCII => Except.ok #[⟨⟨'\x00', '\x7F'⟩, by simp +arith⟩]
  | .ANY => Except.ok #[⟨⟨'\u0000', ⟨0x10FFFF, by simp +arith +decide⟩⟩, by simp +arith +decide⟩]
  | .Default_Ignorable_Code_Point => Except.error s!"Property name {name} has no data"
  | .Noncharacter_Code_Point => Except.error s!"Property name {name} has no data"

def rangesOfNamedProperty (name prop : String) : Except String $ Array (NonemptyInterval Char) := do
  match ofName? name with
  | some p => rangessOfPropertyName p prop
  | _ => Except.error s!"Property name {name} not found"

def rangesOfProperty (prop : String) : Except String $ Array (NonemptyInterval Char) := do
  match ofName? prop with
  | some p => rangessOfPropertyName p ""
  | _ =>
    match ofValue? prop with
    | some p => rangessOfPropertyName p prop
    | none =>
      match ofCompatibilityPropertyName? prop with
      | some arr =>
        let init : Array (NonemptyInterval Char) := #[]
        let pairs : Array (NonemptyInterval Char) ←
          arr |> Array.foldlM (init := init) (fun acc (n, v) => do
            let elem ← rangessOfPropertyName n (v.getD "")
            pure (elem ++ acc))
        Except.ok pairs
      | none =>
        match rangesOfScript prop with
        | Except.ok ranges =>  Except.ok ranges
        | _ => Except.error s!"Property name or value '{prop}' not found"

private def inRangesOfProperty (c : Char) (prop : String) : Except String String := do
  let pairs ← rangesOfProperty prop
  match pairs.find? (fun p => p.fst <= c && c <= p.snd) with
  | some range =>
    Except.ok
      s!"{c} {UInt32.intAsString c.val} in range '{UInt32.intAsString range.fst.val} {UInt32.intAsString range.snd.val}'"
  | none => Except.error s!"{c} not found"

private def isCharInIntervals (c : Char)
    (intervals : Except String (Array (NonemptyInterval Char))) : Bool :=
  match intervals with
  | Except.ok arr =>
      match arr.find? (fun ⟨⟨c1, c2⟩, _⟩ => c1.val <= c.val && c.val <= c2.val) with
      | some _ => true
      | none => false
  | Except.error _ => false

/-- has `c` the word property -/
def is_word_char (c : Char) : Bool :=
  rangesOfProperty "Word" |> isCharInIntervals c

/-- has `c` the general category -/
def isCharOfGeneralCategory (category : GC) (c : Char) : Bool :=
  rangesOfGeneralCategory category |> isCharInIntervals c

/-- get ranges of case folds of char -/
def case_fold_char (c : Char) :  Array (NonemptyInterval Char) :=
  let data := getUnicodeData c
  match data.uppercase with
  | some cUpper =>
      #[⟨⟨cUpper, cUpper⟩, by simp [Char.eq_le _]⟩, ⟨⟨c, c⟩, by simp [Char.eq_le _]⟩]
  | none =>
    match data.lowercase with
    | some cLower =>
      #[⟨⟨c, c⟩ , by simp [Char.eq_le _]⟩, ⟨⟨cLower, cLower⟩, by simp [Char.eq_le _]⟩]
    | none => #[⟨⟨c, c⟩, by simp [Char.eq_le _]⟩]

private def loop (c : Char) (n count : Nat) (acc : Array Char)
    (h1 : n < UInt32.size) (h2 : count < UInt32.size) : Array Char :=
  let nextVal := c.val + ⟨n, h1⟩
  if h : UInt32.isValidChar nextVal
  then
    let nextChar : Char := ⟨nextVal, h⟩
    if h : n + 1 ≤ count then
      loop c (n+1) count (acc.push nextChar) (Nat.lt_of_le_of_lt h h2) h2
    else acc.push nextChar
  else
    if h : n + 1 ≤ count then
      loop c (n+1) count acc (Nat.lt_of_le_of_lt h h2) h2
    else acc
termination_by count - n

theorem Fin.sub_le_of_le {a b : Fin n} (h : a ≤ b) : b - a ≤ b := by
  apply Fin.le_def.mpr
  have : ↑(b - a) = b.val - a.val := Fin.coe_sub_iff_le.mpr h
  rw [this]
  apply Nat.sub_le

theorem Uint32.sub_le_of_le {a b : UInt32} (h : a ≤ b) : b - a ≤ b := by
  --apply UInt32.le_def.mp at h
  exact Fin.sub_le_of_le h

/-- get ranges of case folds of chars in range -/
def case_fold_range (r : NonemptyInterval Char) : Array (NonemptyInterval Char) :=
  loop r.fst 0 (r.snd.val - r.fst.val).toFin.val #[] (by simp)
    (Nat.lt_of_le_of_lt (Uint32.sub_le_of_le r.fst_le_snd) r.snd.val.toFin.isLt)
  |> Array.flatMap (fun c => case_fold_char c)
