import UnicodeBasic
import Regex.Interval

namespace Unicode

/-- extract data from records -/
def extract (data : Array (Array Substring)) : Array (String × UInt32 × (Option UInt32)) :=
  let init : Array (String × UInt32 × (Option UInt32)) := #[]
  data |> Array.foldl (init := init) (fun acc record =>
    let val : UInt32 × Option UInt32 :=
      match record[0]!.splitOn ".." with
      | [c] => (ofHexString! c.toString, none)
      | [c₀,c₁] => (ofHexString! c₀.toString, some <| ofHexString! c₁.toString)
      | _ => panic! "invalid record in PropList.txt"
    let name := record[1]!.toString
    acc.push (name, val))

/-- normalize property name name, see https://www.unicode.org/reports/tr44/#Matching_Rules -/
def normalize (s : String) :=
  ((s.toLower).replace "_" "").replace " " ""

def toRange (val : UInt32 × Option UInt32) : Range Char :=
  let (u1, u2) := val
  let u2 := match u2 with | some u2 => u2 | none => u1
  if h1 : UInt32.isValidChar u1 then
    if h2 : UInt32.isValidChar u2 then ⟨⟨u1, h1⟩, ⟨u2, h2⟩⟩
    else ⟨default, default⟩
  else ⟨default, default⟩
