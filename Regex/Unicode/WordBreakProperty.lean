import UnicodeBasic
import Regex.Interval
import Regex.Unicode.Utils

/-!
## WordBreakProperty

Properties of file [WordBreakProperty](https://www.unicode.org/Public/UCD/latest/ucd/auxiliary/WordBreakProperty.txt)
-/
namespace Unicode

structure WordBreakProperty where
  name : String
  properties : Array (UInt32 × Option UInt32) := #[]

instance : ToString WordBreakProperty where
  toString s := s!"{s.name} {s.properties}"

protected def WordBreakProperty.txt := include_str "./data/auxiliary/WordBreakProperty.txt"

private def transform (data : Array (Array Substring)) : Array WordBreakProperty :=
  let init : Array WordBreakProperty := #[]
  extract data |> Array.foldl (init := init) (fun acc (name, val) =>
    match acc.findIdx? (·.name = name) with
    | some i =>
      if h : i < acc.size then
        let entry := acc.get i h
        acc.set i {entry with properties := entry.properties.push val} h
      else acc
    | none => acc.push ⟨name, #[val]⟩)

private unsafe def WordBreakProperty.init : IO $ Array WordBreakProperty := do
  let stream := UCDStream.ofString WordBreakProperty.txt
  let mut records : Array (Array Substring) := #[]
  for record in stream do
    records := records.push record

  return transform records

@[init WordBreakProperty.init]
protected def WordBreakProperty.data : Array WordBreakProperty := #[]

def getWordBreak (s : String) : Except String $ Array (NonemptyInterval Char) :=
  match WordBreakProperty.data.find? (normalize ·.name = normalize s) with
  | some ⟨_, p⟩ => Except.ok (
      p |> Array.map toRange)
  | none => Except.error s!"WordBreak property {s} not found"
