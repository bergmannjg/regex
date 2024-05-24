import Std.Data.List.Lemmas

/-!
## Utils
-/

namespace Char

/-- make String with `n` `c` chars -/
def multiple (c : Char) ( n : Nat) (acc : String ): String :=
  if n = 0 then acc else multiple c ( n - 1) (c.toString ++ acc)

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
  --| [some u1, some u2, some u3, some u4] => Except.ok (4096*u1 + 256*u2 + 16*u3 + u4)
  else Except.error s!"hexCharsToVal, invalid arg {chars}"

end Char

namespace Nat

def intAsString (val : Nat) : String :=
  if hu : val < UInt32.size
  then
    if h : Nat.isValidChar val
    then
      if '0'.val.val <= val && val <= 'z'.val.val
      then
        let c : Char := ⟨⟨val, hu⟩, h⟩
        c.toString
      else
        let n := val
        if n = 0 then "0x00"
        else
          let digits := (Nat.toDigits 16 n)
          let zeroes := List.replicate (if digits.length = 1 then 1 else 0) '0'
          "0x" ++ String.mk (zeroes ++ digits)
    else s!"invalid char {val}"
  else s!"invalid uint32 {val}"

end Nat

namespace UInt32

def intAsString (val : UInt32) : String :=
  Nat.intAsString val.val

end UInt32

namespace String

/-- get `i` char in `s`, tood: switch to String.Pos logic -/
def getAtCodepoint (s : String) (i : Nat) : Char :=
  if h : i < s.length then s.data.get ⟨i, h⟩ else default

/-- compute the byte position of the codepoint position `p` in `s` -/
def toBytePosition (s : String) (p : Nat) : String.Pos :=
  ⟨String.utf8ByteSize ⟨s.data |> List.take p⟩⟩

/-- make Substring of String -/
def toSpan (s : String) (startPos : Nat) (stopPos : Nat) : Substring :=
  ⟨s, toBytePosition s startPos, toBytePosition s stopPos⟩

def decodeHex (s : String) : Except String UInt32 :=
  let s := if s.startsWith "0x" then s.replace "0x" "" else s
  Char.decodeHexDigits s.data

end String
