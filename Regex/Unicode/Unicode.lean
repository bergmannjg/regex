import UnicodeBasic
import Regex.Interval
import Regex.Unicode.Properties
import Regex.Unicode.SentenceBreakProperty
import Regex.Unicode.WordBreakProperty
import Regex.Unicode.GraphemeBreakProperty
import Regex.Unicode.DerivedCoreProperties
import Regex.Unicode.Emoji
import Regex.Unicode.Scripts

/-!
## Unicode

Support for [Unicode Regular Expressions Level 1](https://unicode.org/reports/tr18/#RL1.2)
-/

namespace Unicode

private def getUnassigned : Array (Range Char) :=
  let init : Option UInt32 × Array (UInt32 × UInt32) := (none, #[])
  let (prev, arr) := UnicodeData.data |> Array.foldl (init := init) (fun (prev, acc) d =>
    match prev with
    | some prev =>
      if d.codeValue - prev = 1 then (d.codeValue, acc)
      else (none, acc.push (prev + 1, d.codeValue - 1))
    | none => (d.codeValue, acc))

  let arr :=
    match prev with
    | some prev => arr.push (prev, Unicode.max)
    | none => arr

  arr |> Array.map (fun ((n1, n2) : UInt32 × UInt32)=> toRange (n1, (some n2)))

private def fold (data : Array UnicodeData) : Array (Char × Char) :=
  let (last, pairs) : (Char × Char) × Array (Char × Char) :=
  data
  |> Array.foldl (init := ((⟨0, by simp_arith⟩, ⟨0, by simp_arith⟩), #[])) (fun (last, s) a =>
      if h : UInt32.isValidChar a.codeValue
      then
        let c : Char := ⟨a.codeValue, h⟩
        if c.val - last.2.val = 1
        then ((last.1, c), s)
        else
          ((c, c), if last.1.val != 0 then (s.push last) else s)
      else (last, s))

  pairs.push last

def rangesOfGeneralCategory (category : GeneralCategory) : Except String $ Array (Range Char) :=
  if category = GeneralCategory.Cn
  then
    Except.ok getUnassigned
  else
    let data :=
      match category with
      | ⟨_, some _⟩ =>
        UnicodeData.data |> Array.filter (fun u =>
          if category = GeneralCategory.LC
          then u.generalCategory = GeneralCategory.Ll
            || u.generalCategory = GeneralCategory.Lu
            || u.generalCategory = GeneralCategory.Lt
          else u.generalCategory = category)
      | ⟨major, none⟩ =>
        UnicodeData.data |> Array.filter (fun u => u.generalCategory.major = major)
    let arr := fold data |> .map (fun (c1, c2) => ⟨c1, c2⟩)
    let arr := if category = GeneralCategory.C then arr ++ getUnassigned else arr
    Except.ok arr

private def rangesOfCategory (s : String) : Except String $ Array (Range Char) :=
  match GeneralCategory.ofValue? s with
  | some category => rangesOfGeneralCategory category
  | none => Except.error s!"category {s} not found"

private def property_map (arr : Array (UInt32 × Option UInt32)) : Array (Range Char) :=
  arr.map (fun (n, m) =>
    let a : Char := if h : UInt32.isValidChar n then ⟨n, h⟩ else 'x'
    let b : Char :=
      match m with
      | some m => if h : UInt32.isValidChar m then ⟨m, h⟩ else 'x'
      | none => a
    (a, b))
  |> .map (fun (c1, c2) => ⟨c1, c2⟩)

private def rangessOfPropertyName (name : PropertyName) (prop : String)
    : Except String $ Array (Range Char) := do
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
  | .ASCII_Hex_Digit => Except.ok #[⟨'0','9'⟩, ⟨'A','F'⟩, ⟨'a','f'⟩]
  | .Hex_Digit => Except.ok #[⟨'0','9'⟩, ⟨'A','F'⟩, ⟨'a','f'⟩]
  | .Numeric_Value => rangesOfGeneralCategory GeneralCategory.N
  | .ASSIGNED => Except.ok (Interval.negate ⟨getUnassigned⟩).ranges
  | .ASCII => Except.ok #[⟨'\x00', '\x7F'⟩]
  | .ANY => Except.ok #[⟨'\u0000', ⟨0x10FFFF, by simp_arith⟩⟩]
  | .Default_Ignorable_Code_Point => Except.error s!"Property name {name} has no data"
  | .Noncharacter_Code_Point => Except.error s!"Property name {name} has no data"

def rangesOfNamedProperty (name prop : String) : Except String $ Array (Range Char) := do
  match ofName? name with
  | some p => rangessOfPropertyName p prop
  | _ => Except.error s!"Property name {name} not found"

def rangesOfProperty (prop : String) : Except String $ Array (Range Char) := do
  match ofName? prop with
  | some p => rangessOfPropertyName p ""
  | _ =>
    match ofValue? prop with
    | some p => rangessOfPropertyName p prop
    | none =>
      match ofCompatibilityPropertyName? prop with
      | some arr =>
        let init : Array (Range Char) := #[]
        let pairs : Array (Range Char) ←
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
  match pairs.find? (fun p => p.start <= c && c <= p.end) with
  | some range =>
    Except.ok
      s!"{c} {intAsString c.val} in range '{intAsString range.start.val} {intAsString range.end.val}'"
  | none => Except.error s!"{c} not found"

/-- has `c` the word property -/
def is_word_char (c : Char) : Bool :=
  match rangesOfProperty "Word" with
  | Except.ok arr =>
      match Array.find? arr (fun ⟨c1, c2⟩ => c1.val <= c.val && c.val <= c2.val) with
      | some _ => true
      | none => false
  | Except.error _ => false

/-- get ranges of case folds of char -/
def case_fold_char (c : Char) :  Array (Range Char) :=
  let data := getUnicodeData c
  match data.uppercaseMapping with
  | some cUpper => #[⟨cUpper, cUpper⟩, ⟨c, c⟩]
  | none =>
    match data.lowercaseMapping with
    | some cLower => #[⟨c, c⟩, ⟨cLower, cLower⟩]
    | none => #[⟨c, c⟩]

private partial def loop (c : Char) (n count : UInt32) (acc : Array Char) : Array Char :=
  if n > count then acc
  else
    let nextVal := c.val+n
    if h : UInt32.isValidChar nextVal
    then
      let nextChar : Char := ⟨nextVal, h⟩
      loop c (n+1) count (acc.push nextChar)
    else loop c (n+1) count acc

/-- get ranges of case folds of chars in range -/
def case_fold_range (r : Range Char) : Array (Range Char) :=
  loop r.start 0 (r.end.val - r.start.val) #[]
  |> Array.concatMap (fun c => case_fold_char c)
