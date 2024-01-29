import UnicodeBasic
import Regex.Interval
import Regex.Unicode.Utils
import Regex.Unicode.Properties

/-!
## GraphemeBreakProperty

Properties of file [GraphemeBreakProperty](https://www.unicode.org/Public/UCD/latest/ucd/auxiliary/GraphemeBreakProperty.txt)
-/
namespace Unicode

structure GraphemeBreakProperty where
  name : String
  properties : Array (UInt32 × Option UInt32) := #[]

instance : ToString GraphemeBreakProperty where
  toString s := s!"{s.name} {s.properties}"

protected def GraphemeBreakProperty.txt := include_str "./data/auxiliary/GraphemeBreakProperty.txt"

private def transform (data : Array (Array Substring)) : Array GraphemeBreakProperty :=
  let init : Array GraphemeBreakProperty := #[]
  extract data |> Array.foldl (init := init) (fun acc (name, val) =>
    match acc.findIdx? (·.name = name) with
    | some i =>
      if h : i < acc.size then
        let entry := acc.get ⟨i, h⟩
        acc.set ⟨i, h⟩ {entry with properties := entry.properties.push val}
      else acc
    | none => acc.push ⟨name, #[val]⟩)

private unsafe def GraphemeBreakProperty.init : IO $ Array GraphemeBreakProperty := do
  let stream := UCDStream.ofString GraphemeBreakProperty.txt
  let mut records : Array (Array Substring) := #[]
  for record in stream do
    records := records.push record

  return transform records

@[init GraphemeBreakProperty.init]
protected def GraphemeBreakProperty.data : Array GraphemeBreakProperty := #[]

def rangesOfGraphemeBreak (s : String) : Except String $ Array (Range Char) :=
  match GraphemeBreakProperty.data.find? (normalize ·.name = normalize s) with
  | some ⟨_, p⟩ => Except.ok (
      p |> Array.map toRange)
  | none =>
    match getPropertyValueAlias PropertyName.Grapheme_Cluster_Break s with
    | some palias =>
      match GraphemeBreakProperty.data.find? (normalize ·.name = normalize palias.long) with
      | some ⟨_, p⟩ => Except.ok (
          p |> Array.map toRange)
      | none => Except.error s!"GraphemeBreak property {s} not found"
    | none => Except.error s!"GraphemeBreak property {s} not found"
