import UnicodeBasic
import Regex.Interval
import Regex.Unicode.Utils

namespace Unicode

structure Emoji where
  name : String
  properties : Array (UInt32 × Option UInt32) := #[]

instance : ToString Emoji where
  toString s := s!"{s.name} {s.properties}"

protected def Emojis.txt := include_str "./data/emoji/emoji-data.txt"

private def transform (data : Array (Array Substring)) : Array Emoji :=
  let init : Array Emoji := #[]
  extract data |> Array.foldl (init := init) (fun acc (name, val) =>
    match acc.findIdx? (·.name = name) with
    | some i =>
      if h : i < acc.size then
        let entry := acc.get i h
        acc.set i {entry with properties := entry.properties.push val} h
      else acc
    | none => acc.push ⟨name, #[val]⟩)

private unsafe def Emoji.init : IO $ Array Emoji := do
  let stream := UCDStream.ofString Emojis.txt
  let mut records : Array (Array Substring) := #[]
  for record in stream do
    records := records.push record

  return transform records

@[init Emoji.init]
protected def Emojis.data : Array Emoji := #[]

def getEmoji (s : String) : Except String $ Array (NonemptyInterval Char) :=
  match Emojis.data.find? (normalize ·.name = normalize s) with
  | some ⟨_, p⟩ => Except.ok (
      p |> Array.map toRange)
  | none => Except.error s!"Emoji property {s} not found"
