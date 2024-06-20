import Lean

import RegexTest

open Lean System

namespace Loader.Pcre

private def cZero : Char := ⟨0, by simp_arith⟩

private def octDigitsToChar! (chars : List Char) : Char :=
  match Char.decodeOctDigits chars with
  | Except.ok n => if h : UInt32.isValidChar n then ⟨n, h⟩ else cZero
  | Except.error _ => cZero

/-- unescape strings from pcre json file generated from perltest.sh via JSON::PP. -/
private def unescapeStr (s : String) (backslashIsEmptyString : Bool := false) : String :=
  ⟨loop s.data⟩
where
  toChar (a b : Char) : Char :=
    match Char.decodeHexDigit a, Char.decodeHexDigit b with
    | some n, some m =>
      let val := 16*n+m
      if h : UInt32.isValidChar val then ⟨val, h⟩ else ⟨0, by simp_arith⟩
    | _, _ => ⟨0, by simp_arith⟩
  loop (chars : List Char) : List Char :=
    match chars with
    | [] => []
    | ['\\'] => if backslashIsEmptyString then [] else ['\\']
    | '\\' :: 'x' :: a :: b :: tail =>
      if b.isHexDigit
      then (toChar a b) :: (loop tail)
      else (toChar '0' a) :: (loop (b :: tail))
    | '\\' :: 'e' :: tail => ⟨27, by simp_arith⟩  :: (loop tail)
    | '\\' :: 'n' :: tail => '\n' :: (loop tail)
    | '\\' :: 'r' :: tail => '\r' :: (loop tail)
    | '\\' :: '"' :: tail => '"' :: (loop tail)
    | '\\' :: '$' :: tail => '$' :: (loop tail)
    | '\\' :: '@' :: tail => '@' :: (loop tail)
    | '\\' :: '\\' :: tail => '\\' :: (loop tail)
    | '\\' :: 't' :: tail => '\t' :: (loop tail)
    | '\\' :: c1 :: tail =>
      if c1.isDigit
      then
        match tail with
        | c2 :: c3 :: tail =>
          if c2.isDigit && c3.isDigit then octDigitsToChar! [c1, c2, c3] :: (loop tail)
          else if c2.isDigit then octDigitsToChar! [c1, c2] :: (loop (c3 :: tail))
          else octDigitsToChar! [c1] :: (loop (c2 :: c3 :: tail))
        | c2 :: [] =>
          if c2.isDigit then [octDigitsToChar! [c1, c2]]
          else  [octDigitsToChar! [c1], c2]
        | [] => [octDigitsToChar! [c1]]
      else '\\' :: c1 :: (loop tail)
    | head :: tail => head :: (loop tail)

example : unescapeStr r"\x20" = ⟨[' ']⟩  := by native_decide

example : unescapeStr r"\x20\x20" = ⟨[' ', ' ']⟩  := by native_decide

example : unescapeStr r"\0" = ⟨[cZero]⟩  := by native_decide

example : unescapeStr r"\0\0" = ⟨[cZero, cZero]⟩  := by native_decide

example : unescapeStr r"a\0" = ⟨['a', cZero]⟩  := by native_decide

example : unescapeStr r"\0a" = ⟨[cZero, 'a']⟩  := by native_decide

example : unescapeStr r"\12a" = ⟨['\n', 'a']⟩  := by native_decide

example : unescapeStr r"\12" = ⟨['\n']⟩  := by native_decide

example : unescapeStr r"\123" = ⟨['S']⟩  := by native_decide

/-- A pcre match describes outputs of a pcre regex match generated from perltest.sh. -/
private structure PcreMatch where
  «match» : String
  group1 : Option String
  group2 : Option String
  group3 : Option String
  group4 : Option String
  group5 : Option String
  group6 : Option String
  group7 : Option String
  group8 : Option String
  group9 : Option String
  deriving Lean.FromJson

/-- A pcre test describes the inputs and expected outputs of a pcre regex match
    generated from perltest.sh. -/
private structure PcreTest where
  matchExpected : Nat
  pattern : String
  haystack : String
  «match» : Option $ Array PcreMatch
  noMatch : Option Bool
  deriving Lean.FromJson

private def toCaptures (p : PcreTest) : Array $ RegexTest.Captures :=
  match p.match with
  | some arr =>
      let groups :=
        arr |> Array.map (fun m =>
          let _haystack := unescapeStr p.haystack true
          let _match := unescapeStr m.«match»

          if _match.length = 0 then some ⟨0, 0, some _match⟩ else
          match _haystack.splitOn _match with
          | f :: _ =>
            some ⟨f.utf8ByteSize, f.utf8ByteSize + _match.utf8ByteSize, some _match⟩
          | _ => none)
      #[⟨groups⟩]
  | none => #[]

private def setOption (c : Char) (t : RegexTest) : RegexTest :=
  match c with
  | 'i' => { t with «case-insensitive» := some true }
  | 's' => { t with single_line := some true }
  | 'm' => { t with multi_line := some true }
  | 'g' => { t with «global» := some true }
  | 'x' => { t with extended := some true }
  | _ => t

private def toPattern (p : PcreTest) (t : RegexTest) : RegexTest :=
  let pattern := p.pattern.trim
  match (pattern.data.head?, pattern.data.getLast?) with
  | (some '/', some '/') =>
      { t with regex :=  Sum.inl ⟨(pattern.data.drop 1).dropLast⟩ }
  | (some '/', some c1) =>
    let t := setOption c1 t
    let data := (pattern.data.drop 1).dropLast
    match data.getLast? with
    | some '/' => { t with regex :=  Sum.inl ⟨data.dropLast⟩ }
    | some c2 =>
      let t := setOption c2 t
      { t with regex :=  Sum.inl ⟨data.dropLast.dropLast⟩ }
    | none => t
  | (_, _) => t

private def toRegexTest (i : Nat) (p : PcreTest) : RegexTest :=
  toPattern p
    {
      name := s!"t{i}"
      regex := Sum.inl ""
      haystack := unescapeStr p.haystack true
      «matches» := toCaptures p
      «match-limit» := some 1
      unescape := some true
      «only-full-match» := some true
    }

def toRegexTestArray (arr : Array PcreTest) : Array RegexTest :=
  Array.mapIdx arr (fun i p => toRegexTest i p)

def load (path : FilePath) : IO (Array PcreTest) := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept <| Json.parse contents
  IO.ofExcept <| fromJson? (α := Array PcreTest) json
