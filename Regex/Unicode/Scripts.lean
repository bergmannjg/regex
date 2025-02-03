import UnicodeBasic
import Regex.Interval
import Regex.Unicode.Utils

/-!
## Script

Properties of file [Scripts](https://www.unicode.org/Public/UNIDATA/Scripts.txt).
-/

namespace Unicode

structure Script where
  name : String
  properties : Array (UInt32 × Option UInt32) := #[]

instance : ToString Script where
  toString s := s!"{s.name} {s.properties}"

protected def ScriptProperties.txt := include_str "./data/Scripts.txt"

private def transform (data : Array (Array Substring)) : Array Script :=
  let init : Array Script := #[]
  extract data |> Array.foldl (init := init) (fun acc (name, val) =>
    match acc.findIdx? (·.name = name) with
    | some i =>
      if h : i < acc.size then
        let entry := acc.get i h
        acc.set i {entry with properties := entry.properties.push val} h
      else acc
    | none => acc.push ⟨name, #[val]⟩)

private unsafe def Script.init : IO $ Array Script := do
  let stream := UCDStream.ofString ScriptProperties.txt
  let mut records : Array (Array Substring) := #[]
  for record in stream do
    records := records.push record

  return transform records

@[init Script.init]
protected def ScriptProperties.data : Array Script := #[]

def rangesOfScript (s : String) : Except String $ Array (NonemptyInterval Char) :=
  match ScriptProperties.data.find? (normalize ·.name = normalize s) with
  | some ⟨_, p⟩ => Except.ok (
      p |> Array.map toRange)
  | none => Except.error s!"Script property {s} not found"

namespace Script

def names : Array String :=
  ScriptProperties.data |> Array.map (·.name)

end Script
