module

public import UnicodeBasic
public import UnicodeData.Scripts
public import Regex.Interval
public import Regex.Unicode.Utils

public section

/-!
## Script

Properties of file [Scripts](https://www.unicode.org/Public/UNIDATA/Scripts.txt).
-/

namespace Unicode

def rangesOfScript (s : String) : Except String $ Array (NonemptyInterval Char) :=
  match Scripts.getTable? s with
  | some arr => Except.ok (arr |> Array.map (fun p => toRange (p.fst, some p.snd)))
  | none => Except.error s!"Script property {s} not found"
