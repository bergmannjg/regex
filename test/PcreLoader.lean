import Lean

import RegexTest

open Lean System

namespace Loader.Pcre

private def cZero : Char := ⟨0, by simp +arith +decide⟩

private def octDigitsToChar! (chars : List Char) : Char :=
  match Char.decodeOctDigits chars with
  | Except.ok n => if h : UInt32.isValidChar n then ⟨n, h⟩ else cZero
  | Except.error _ => cZero

/-- unescape strings from pcre json file generated from perltest.sh via JSON::PP. -/
private def unescapeStr (s : String) (isHaystack : Bool := false) : String :=
  String.mk (loop s.data)
where
  toChar (a b : Char) : Char :=
    match Char.decodeHexDigit a, Char.decodeHexDigit b with
    | some n, some m =>
      let val := 16*n+m
      if h : UInt32.isValidChar val then ⟨val, h⟩ else ⟨0, by simp +arith +decide⟩
    | _, _ => ⟨0, by simp +arith +decide⟩
  loop (chars : List Char) : List Char :=
    match chars with
    | [] => []
    | ['\\'] => if isHaystack then [] else ['\\']
    | '\\' :: 'x' :: '{' :: a :: b :: '}' :: tail => (toChar a b) :: (loop tail)
    | '\\' :: 'x' :: a :: b :: tail =>
      if b.isHexDigit
      then (toChar a b) :: (loop tail)
      else (toChar '0' a) :: (loop (b :: tail))
    | '\\' :: 'a' :: tail => '\x07' :: (loop tail)
    | '\\' :: 'e' :: tail => ⟨27, by simp +arith +decide⟩ :: (loop tail)
    | '\\' :: 'f' :: tail => '\x0c' :: (loop tail)
    | '\\' :: 'n' :: tail => '\n' :: (loop tail)
    | '\\' :: 'r' :: tail => '\r' :: (loop tail)
    | '\\' :: '"' :: tail => '"' :: (loop tail)
    | '\\' :: '$' :: tail => if isHaystack then '$' :: (loop tail) else '\\' :: '$' :: (loop tail)
    | '\\' :: '@' :: tail => '@' :: (loop tail)
    | '\\' :: '\\' :: tail => '\\' :: (loop tail)
    | '\\' :: 't' :: tail => '\t' :: (loop tail)
    | '0' :: 'x' :: '0' :: 'p' :: '+' :: '0' :: tail => '%' :: 'a' :: (loop tail) -- why?
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

example : unescapeStr r"\x20" = [' '].asString  := by native_decide

example : unescapeStr r"\x20\x20" = [' ', ' '].asString  := by native_decide

example : unescapeStr r"\0" = [cZero].asString  := by native_decide

example : unescapeStr r"\0\0" = [cZero, cZero].asString  := by native_decide

example : unescapeStr r"a\0" = ['a', cZero].asString  := by native_decide

example : unescapeStr r"\0a" = [cZero, 'a'].asString  := by native_decide

example : unescapeStr r"\12a" = ['\n', 'a'].asString  := by native_decide

example : unescapeStr r"\12" = ['\n'].asString  := by native_decide

example : unescapeStr r"\123" = ['S'].asString  := by native_decide

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

private def toSpan (_haystack _match : String ) : Except String $ Option RegexTest.Span := do
  if _haystack.length < _match.length then
    Except.error s!"haystack.length < match.length, haystack '{_haystack}' match '{_match}'" else
  if _match.length = 0 then pure <| some ⟨0, 0, some _match⟩ else
  match _haystack.splitOn _match with
  | f :: _ =>
    if false && f.utf8ByteSize = _haystack.length  then
      Except.error s!"match not found in haystack, haystack '{_haystack.quote}', _match '{_match.quote}'" else
    pure <| some ⟨f.utf8ByteSize, f.utf8ByteSize + _match.utf8ByteSize, some _match⟩
  | _ => pure none

private def toCaptures (p : PcreTest) : Except String $ (Array RegexTest.Captures) := do
  match p.match with
  | some arr =>
      let captures : Array $ RegexTest.Captures ←
        arr |> Array.mapM (fun m => do
          let _haystack := unescapeStr p.haystack true
          let _match := unescapeStr m.«match»
          let span ← toSpan _haystack _match
          let spans ← #[m.group1, m.group2, m.group3, m.group4, m.group5, m.group6]
                |> Array.mapM (Option.bindM (toSpan _haystack <| unescapeStr ·) ·)
          pure ⟨Array.append #[span] spans⟩)
      pure captures
  | none => pure #[]

private def setOption (c : Char) (t : RegexTest) : RegexTest :=
  match c with
  | 'i' => { t with «case-insensitive» := some true }
  | 's' => { t with single_line := some true }
  | 'm' => { t with multi_line := some true }
  | 'g' => { t with «global» := some true }
  | 'x' => { t with extended := some .Extended }
  | _ => t

private def toPattern (p : PcreTest) (t : RegexTest) : RegexTest :=
  let pattern := p.pattern.trim
  if pattern.endsWith "/xx" then
    { t with
      regex :=  Sum.inl ((pattern.data.drop 1).take (pattern.length - 4)).asString
      extended := some .ExtendedMore }
  else
    match (pattern.data.head?, pattern.data.getLast?) with
    | (some '/', some '/') =>
        { t with regex :=  Sum.inl (pattern.data.drop 1).dropLast.asString }
    | (some '/', some c1) =>
      let t := setOption c1 t
      let data := (pattern.data.drop 1).dropLast
      match data.getLast? with
      | some '/' => { t with regex :=  Sum.inl data.dropLast.asString }
      | some c2 =>
        let t := setOption c2 t
        { t with regex :=  Sum.inl data.dropLast.dropLast.asString }
      | none => t
    | (_, _) => t

private def toRegexTest (i : Nat) (p : PcreTest) : Except String $ RegexTest := do
  pure <| toPattern p
    {
      name := s!"t{i}"
      regex := Sum.inl ""
      haystack := unescapeStr p.haystack true
      «matches» := (← toCaptures p).take p.matchExpected
      «match-limit» := some p.matchExpected
      unescape := some true
      «only-full-match» := some true
    }

def toRegexTestArray (arr : Array PcreTest) : Except String $ Array RegexTest :=
  arr.mapIdxM (fun i p => toRegexTest i p)

def loadFromString (contents : String) : IO (Array PcreTest) := do
  let json ← IO.ofExcept <| Json.parse contents
  IO.ofExcept <| fromJson? (α := Array PcreTest) json

def load (path : FilePath) : IO (Array PcreTest) := do
  loadFromString (← IO.FS.readFile path)
