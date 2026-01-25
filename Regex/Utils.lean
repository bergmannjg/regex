import Batteries.Data.List.Lemmas

/-!
## Utils
-/

namespace Char

/-- make String with `n` `c` chars -/
def multiple (c : Char) ( n : Nat) (acc : String ): String :=
  if n = 0 then acc else multiple c ( n - 1) (c.toString ++ acc)

def isHexDigit (c : Char) : Bool :=
  if '0' ≤ c && c ≤ '9' then true
  else if 'a' ≤ c && c ≤ 'f' then true
  else if 'A' ≤ c && c ≤ 'F' then true
  else false

def decodeHexDigit (c : Char) : Option (UInt32) :=
  if '0' ≤ c && c ≤ '9' then some (c.val - '0'.val)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.val - 'a'.val)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.val - 'A'.val)
  else none

def decodeHexDigits (chars : List Char) : Except String UInt32 :=
  let l := chars |> List.filterMap (decodeHexDigit ·)
  if l.length > 0 then
    let (_, val) := l |> List.foldr (init := (1, 0)) (fun v (n, acc)  =>
      (n*16, acc + n*v))
    Except.ok val
  else Except.error s!"decodeHexDigits, invalid arg {chars}"

def decodeOctDigit (c : Char) : Option (UInt32) :=
  if '0' ≤ c && c ≤ '7' then some (c.val - '0'.val)
  else none

def decodeOctDigits (chars : List Char) : Except String UInt32 :=
  let l := chars |> List.filterMap (decodeOctDigit ·)
  if l.length > 0 then
    let (_, val) := l |> List.foldr (init := (1, 0)) (fun v (n, acc)  =>
      (n*8, acc + n*v))
    Except.ok val
  else Except.error s!"decodeOctDigits, invalid arg {chars}"

end Char

namespace Nat

def intAsString (val : Nat) : String :=
  if hu : val < UInt32.size
  then
    if h : Nat.isValidChar val
    then
      if '0'.val.toFin <= val && val <= 'z'.val.toFin
      then
        let c : Char := ⟨⟨val, hu⟩, h⟩
        c.toString
      else
        let n := val
        if n = 0 then "0x00"
        else
          let digits := (Nat.toDigits 16 n)
          let zeroes := List.replicate (if digits.length = 1 then 1 else 0) '0'
          "0x" ++ String.ofList (zeroes ++ digits)
    else s!"invalid char {val}"
  else s!"invalid uint32 {val}"

end Nat

namespace UInt32

def intAsString (val : UInt32) : String :=
  Nat.intAsString val.toFin

end UInt32

namespace String

instance : Coe String Substring.Raw where
  coe s := s.toRawSubstring

/-- get `i` char in `s`, tood: switch to String.Pos logic -/
def getAtCodepoint (s : String) (i : Nat) : Char :=
  if h : i < s.length then s.toList.get ⟨i, h⟩ else default

/-- starts string `m` at codepoint `i` in `s` -/
def startsAtCodepoint (s m : String) (i : Nat) : Bool :=
  if i + m.length ≤ s.length
  then
    let s := (s.toRawSubstring).drop i
    s.toString.startsWith m
  else false

/-- compute the byte position of the codepoint position `p` in `s` -/
def toBytePosition (s : String) (p : Nat) : String.Pos.Raw :=
  ⟨String.utf8ByteSize (s.take p).toString⟩

/-- make Substring of String -/
def toSpan (s : String) (startPos : Nat) (stopPos : Nat) : Substring.Raw :=
  ⟨s, toBytePosition s startPos, toBytePosition s stopPos⟩

def decodeHex (s : String) : Except String UInt32 :=
  let s := if s.startsWith "0x" then s.replace "0x" "" else s
  Char.decodeHexDigits s.toList

def asHex (s : String) : String :=
  let toHexDigit (c : Nat) : String := String.singleton c.digitChar

  let q := "";
  let q := s.foldl
    (fun q c => q ++
      if c.isAlphanum then String.singleton c
      else "\\x" ++ toHexDigit (c.toNat / 16) ++ toHexDigit (c.toNat % 16))
    q;
  q ++ ""

end String
