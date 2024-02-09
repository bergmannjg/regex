import UnicodeBasic
import Regex.Interval
import Regex.Unicode.Utils

/-!
## DerivedCoreProperties

Properties of file [DerivedCoreProperties](https://www.unicode.org/Public/UCD/latest/ucd/DerivedCoreProperties.txt).
-/

namespace Unicode

structure DerivedCoreProperty where
  name : String
  properties : Array (UInt32 × Option UInt32) := #[]

instance : ToString DerivedCoreProperty where
  toString s := s!"{s.name} {s.properties}"

protected def DerivedCoreProperties.txt := include_str "./data/DerivedCoreProperties.txt"

private def transform (data : Array (Array Substring)) : Array DerivedCoreProperty :=
  let init : Array DerivedCoreProperty := #[]
  extract data |> Array.foldl (init := init) (fun acc (name, val) =>
    match acc.findIdx? (·.name = name) with
    | some i =>
      if h : i < acc.size then
        let entry := acc.get ⟨i, h⟩
        acc.set ⟨i, h⟩ {entry with properties := entry.properties.push val}
      else acc
    | none => acc.push ⟨name, #[val]⟩)

private unsafe def DerivedCoreProperty.init : IO $ Array DerivedCoreProperty := do
  let stream := UCDStream.ofString DerivedCoreProperties.txt
  let mut records : Array (Array Substring) := #[]
  for record in stream do
    records := records.push record

  return transform records

@[init DerivedCoreProperty.init]
protected def DerivedCoreProperties.data : Array DerivedCoreProperty := #[]

def rangesOfDerivedCoreProperty (s : String) : Except String $ Array (NonemptyInterval Char) :=
  match DerivedCoreProperties.data.find? (normalize ·.name = normalize s) with
  | some ⟨_, p⟩ => Except.ok (
      p |> Array.map toRange)
  | none => Except.error s!"DerivedCoreProperty property {s} not found"

namespace DerivedCoreProperty

def names : Array String :=
  DerivedCoreProperties.data |> Array.map (·.name)

end DerivedCoreProperty
