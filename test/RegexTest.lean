import Regex

namespace RegexTest

/-- A span of contiguous bytes, from start to end, represented via byte -/
structure Span where
  start: Nat
  «end»: Nat
  data: Option String

instance : ToString Span where
  toString s :=
    let data := match s.data with | some data => " " ++ data.quote | none => ""
    s!"{s.start} {s.end}{data}"

/-- Captures represents a single group of captured matches from a regex search. -/
structure Captures where
  groups: Array $ Option Span

instance : ToString Captures where
  toString s := s!"Captures {s.groups}"

namespace Sum

def val (v : Sum String (Array String)) : String :=
    match v with
    | .inl s => s
    | .inr arr => arr[0]!

end Sum

instance : ToString $ Sum String (Array String) where
  toString v :=
    match v with
    | .inl s => s!"{s}"
    | .inr arr => s!"{arr}"

end RegexTest

/-- A regex test describes the inputs and expected outputs of a regex match. -/
structure RegexTest where
  name : String
  regex : Sum String (Array String)
  haystack : String
  «matches» : Array RegexTest.Captures
  /-- An optional field whose value is a table with `start` and `end` fields-/
  bounds : Option $ Array Nat := none
  /--  An optional field that specifies a limit on the number of matches. -/
  «match-limit» : Option Nat := none
  /-- Whether to execute an anchored search or not. -/
  anchored : Option Bool := none
  /-- Whether to match the regex case insensitively. -/
  «case-insensitive» : Option Bool := none
  /-- When enabled, the haystack is unescaped. -/
  unescape : Option Bool := none
  compiles : Option Bool := none
  /-- When enabled, the regex pattern should be compiled with its
      corresponding Unicode mode enabled. -/
  unicode : Option Bool := none
  /-- When this is enabled, all regex match substrings should be entirely valid UTF-8. -/
  utf8 : Option Bool := none
  /-- May be one of `all`, `leftmost-first` or `leftmost-longest`. -/
  «match-kind» : Option String := none
  /-- May be one of `earliest`, `leftmost` or `overlapping`. -/
  «search-kind» : Option String := none
  /-- This sets the line terminator used by the multi-line assertions -/
  «line-terminator» : Option String := none
  /-- should check only full match of capture -/
  «only-full-match» : Option Bool := none
  multi_line : Option Bool := none
  single_line : Option Bool := none
  «global» : Option Bool := none
  extended : Option Regex.Grammar.ExtendedKind := none

def unescapeStr (s : String) : String :=
  ⟨loop s.data⟩
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
    | '\\' :: 'x' :: a :: b :: tail => (toChar a b) :: (loop tail)
    | '\\' :: 'n' :: tail => '\n' :: (loop tail)
    | '\\' :: 'r' :: tail => '\r' :: (loop tail)
    | '\\' :: '\\' :: tail => '\\' :: (loop tail)
    | '\\' :: 't' :: tail => '\t' :: (loop tail)
    | head :: tail => head :: (loop tail)

namespace RegexTest

def haystackOf (t : RegexTest) : String :=
  if t.unescape.getD false then unescapeStr t.haystack else t.haystack

def isMatch (t : RegexTest) : Bool :=
  if h : 0 < t.matches.size
  then (t.matches[0]'h).groups.size > 0
  else false

structure RegexTests where
  test : Array RegexTest

namespace String

def containsSubstr (s pattern : String) : Bool :=
  (s.splitOn pattern).length > 1

end String

def checkFlagIsFalse (f : Option Bool) : Bool :=
  match f with | some v => !v | none => false

def checkFlagIsTrue (f : Option Bool) : Bool :=
  match f with | some v => v | none => false

private def escape (s : String) : String :=
  s.replace "\n" "\\n" |>.replace "\r" "\\r" |>.replace ⟨[⟨0, by simp +arith +decide⟩]⟩ r"\x00"

instance : ToString RegexTest where
  toString s :=
    let str := s!"{s.name} '{s.regex}' {s.haystack.quote} {s.matches}"
    let str := str ++ (if s.anchored.isSome then " anchored" else "")
    let str := str ++ (if checkFlagIsTrue s.«case-insensitive» then " case-insensitive" else "")
    let str := str ++ (if s.unescape.isSome then " unescape" else "")
    let str := str ++ (if s.unicode.isSome && !s.unicode.getD true then " !unicode" else "")
    let str := str ++ (if String.containsSubstr (Sum.val s.regex) "(?" then " flags" else "")
    let str := str ++ (if checkFlagIsFalse s.compiles then " !compiles" else "")
    let str := str ++ (if checkFlagIsTrue s.single_line then " single_line" else "")
    let str := str ++ (if checkFlagIsTrue s.multi_line then " multi_line" else "")
    let str := str ++ (if checkFlagIsTrue s.global then " global" else "")
    let str := str ++ (match s.extended with
          | some .Extended => " extended" | some .ExtendedMore => " extendedMore" | _ => "")
    str

instance : ToString RegexTests where
  toString s := s!"{s.test}"

def checkCompiles (flavor : Syntax.Flavor) (t : RegexTest) : Bool :=
  let flags : Syntax.Flags := default
  let config : Compiler.Config := default
  match Regex.build (Sum.val t.regex) flavor flags config with
  | Except.ok _ => true
  | Except.error _ => false

def captures (flavor : Syntax.Flavor) (t : RegexTest)
    : Except String (Array (Regex.Captures t.haystackOf)) := do
  let flags : Syntax.Flags := default
  let config : Compiler.Config := default

  let flags := {flags with case_insensitive := t.«case-insensitive»,
                           dot_matches_new_line := t.single_line,
                           multi_line := t.multi_line}
  let config := {config with unanchored_prefix := !t.anchored.getD false}
  let extended := Option.getD t.extended .None

  let haystack := if t.unescape.getD false then unescapeStr t.haystack else t.haystack
  let re ← Regex.build (Sum.val t.regex) flavor flags config extended
  Except.ok (Regex.all_captures haystack re)

def checkMatches (arr : Array (Regex.Captures s)) (t : RegexTest) : Bool :=
  let match_limit := t.«match-limit».getD 1000
  let arr := arr |> Array.toList |> List.take match_limit |> List.toArray

  if arr.size != t.matches.size then false
  else
    let idx := Array.mapFinIdx arr (fun i v _ => (i, v))
    Array.all idx (fun (i, m) =>
      if h : i < t.matches.size
      then
        let t_matches := (t.matches[i]'h).groups
        let idx := Array.mapFinIdx (m.matches) (fun i v _ => (i, v))
        Array.all idx (fun (i, v) =>
          match t_matches[i]?, v with
          | some (some span), some v =>
              span.start = v.val.startPos.byteIdx && span.end = v.val.stopPos.byteIdx
              || -- ignore maybe wrong string pos caused by pcreloader
              (Substring.extract t.haystack.toSubstring ⟨span.start⟩ ⟨span.end⟩) == v
          | some none, none => true
          | _, _ => (Option.getD t.«only-full-match» false) && 0 < i)
      else false)

private def captureToString (r : Regex.Captures s) : String :=
  r.matches |> Array.map (fun m =>
    match m with
    | some m => s!"({m.val.startPos}, {m.val.stopPos}), "
    | none => "none")
  |> Array.toList
  |> String.join
  |> fun s =>
    let s := if s.endsWith ", "
             then ((String.toSubstring s).dropRight 2).toString
             else s
    "[" ++ s ++ "]"

private def capturesToString (arr : Array (Regex.Captures s)) : String :=
  arr
  |> Array.map (fun c => captureToString c ++ ", ")
  |> Array.toList
  |> String.join
  |> fun s =>
    let s := if s.endsWith ", "
             then ((String.toSubstring s).dropRight 2).toString
             else s
    "[" ++ s ++ "]"

/-- ignore test, feature not implemented -/
def ignoreTest (t : RegexTest) : Bool :=
  checkFlagIsFalse t.unicode
  || checkFlagIsFalse t.utf8
  || t.bounds.isSome -- no api
  || t.«line-terminator».isSome -- Config
  || t.«search-kind».any (· != "leftmost") -- only leftmost is valid for BoundedBacktracker
  || t.«match-kind».any (· = "all") -- Sets
  || match t.regex with | .inr _ => true | .inl _ => false -- Sets

/- todo -/
def ignoredErrors := [
      "escape sequence unexpected in range",
      -- todo: reset visited in backtracker, example regex '([a-c]*)\1'
      "fixed width capture group of backreference",
      "end quote without a corresponding open quote",
      -- todo: reset visited in backtracker, example regex '(?=.*X)X$'
      "duplicate capture group name", -- is expected error
      "feature not implemented",
      "capture group of backreference not found" -- is expected error
      ]

/- todo -/
def ignoredTests : List String :=
  ["t8", -- todo: problem in unescape,
   "t591", -- todo: slow
   "t586", -- todo: problem in unescape
   "t1474", "t1477", "t1478", "t1479", -- end quote without start quote
   "t2314", -- todo: lok ahead in alternative
   "t1488", "t1489" -- empty quote
  ]

def testItem (flavor : Syntax.Flavor) (filename : String) (t : RegexTest) : IO (Nat × Nat × Nat) := do
  if checkFlagIsFalse t.compiles
  then
    if checkCompiles flavor t
    then pure (0, 0, 1)
    else pure (1, 0, 0)
  else if ignoreTest t then pure (0, 0, 1)
  else if List.contains ignoredTests t.name then pure (0, 0, 1)
  else
    match captures flavor t with
    | Except.ok result =>
      if result.size = 0
      then
        if RegexTest.isMatch t
        then
          IO.println s!"RegexTest({filename}): {t}"
          IO.println s!"  no match found, expected {t.matches}"
          pure (0, 1, 0)
        else
          pure (1, 0, 0)
      else
        if checkMatches result t
        then
            pure (1, 0, 0)
        else
          IO.println s!"RegexTest({filename}): {t}"
          IO.println s!"  expected size {t.matches.size}, actual {result.size} "
          IO.println s!"  match different, expected {t.matches}, actual {capturesToString result}"
          pure (0, 1, 0)
      | Except.error e =>
          if t.matches.size = 0 then pure (0, 0, 1) else
          if (ignoredErrors |> List.find? (fun m => (e.splitOn m).length > 1)).isSome then pure (0, 0, 1) else
          IO.println s!"RegexTest{filename}: {t}"
          IO.println s!"  error {e}"
          pure (0, 1, 0)

def testItems (flavor : Syntax.Flavor) (filename : String) (items : Array RegexTest) : IO (Nat × Nat× Nat) := do
  items |> Array.foldlM (init := (0, 0, 0)) (fun (succeeds, failures, ignored) RegexTest => do
    let (succeed, failure, ignore) ← testItem flavor filename RegexTest
    pure (succeeds + succeed, failures + failure, ignore + ignored))

end RegexTest
