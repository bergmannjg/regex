import UnicodeBasic
import Regex.Interval
import Regex.Unicode.Utils

/-!
## SentenceBreakProperty

Properties of file [SentenceBreakProperty](https://www.unicode.org/Public/UCD/latest/ucd/auxiliary/SentenceBreakProperty.txt)
-/

namespace Unicode

structure SentenceBreakProperty where
  name : String
  properties : Array (UInt32 × Option UInt32) := #[]

instance : ToString SentenceBreakProperty where
  toString s := s!"{s.name} {s.properties}"

protected def SentenceBreakProperty.txt := include_str "./data/auxiliary/SentenceBreakProperty.txt"

private def transform (data : Array (Array Substring)) : Array SentenceBreakProperty :=
  let init : Array SentenceBreakProperty := #[]
  extract data |> Array.foldl (init := init) (fun acc (name, val) =>
    match acc.findIdx? (·.name = name) with
    | some i =>
      if h : i < acc.size then
        let entry := acc.get ⟨i, h⟩
        acc.set ⟨i, h⟩ {entry with properties := entry.properties.push val}
      else acc
    | none => acc.push ⟨name, #[val]⟩)

private unsafe def SentenceBreakProperty.init : IO $ Array SentenceBreakProperty := do
  let stream := UCDStream.ofString SentenceBreakProperty.txt
  let mut records : Array (Array Substring) := #[]
  for record in stream do
    records := records.push record

  return transform records

@[init SentenceBreakProperty.init]
protected def SentenceBreakProperty.data : Array SentenceBreakProperty := #[]

def rangesOfSentenceBreak (s : String) : Except String $ Array (NonemptyInterval Char) :=
  match SentenceBreakProperty.data.find? (normalize ·.name = normalize s) with
  | some ⟨_, p⟩ => Except.ok (
      p |> Array.map toRange)
  | none => Except.error s!"SentenceBreak property {s} not found"
