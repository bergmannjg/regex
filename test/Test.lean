import Regex

import Test.Interval
import Test.Grammar
import Test.Ast
import Test.Hir
import Test.Compiler

import RegexTest
import TomlLoader
import PcreLoader

open Lean System

open Regex

def testToml (path : FilePath) (filename : String) (verbose : Bool) (flavor : Syntax.Flavor) (tests : Array RegexTest)
    : IO (Nat × Nat × Nat) := do
  let (succeeds, failures, ignored) ← RegexTest.testItems verbose flavor filename tests
  IO.println s!"succeeds {succeeds} failures {failures} ignored {ignored} in file {path}"
  pure (succeeds, failures, ignored)

def testRustFile (path : FilePath) (verbose : Bool) : IO (Nat × Nat × Nat) := do
  let filename : String := path.fileName.getD ""
  if #["no-unicode.toml", "regex-lite.toml", "utf8.toml"].contains filename
  then pure (0, 0, 0) else
  let tests ← Loader.Toml.load path
  testToml path filename verbose Syntax.Flavor.Rust tests

def testPcreFile (path : FilePath) (verbose : Bool) : IO (Nat × Nat × Nat) := do
  let filename : String := path.fileName.getD ""
  let tests ← (← Loader.Pcre.load path) |> Loader.Pcre.toRegexTestArray |> IO.ofExcept
  testToml path filename verbose Syntax.Flavor.Pcre (tests)

def summary (arr : Array (Nat × Nat × Nat)) : IO UInt32 := do
  let (succeeds, failures, ignored) := arr |> Array.foldl
    (fun acc v => (acc.1+v.1, acc.2.1+v.2.1, acc.2.2+v.2.2) ) (0, 0, 0)
  IO.println s!"succeeds {succeeds} failures {failures} ignored {ignored} total"
  if failures > 0 then IO.eprintln s!"succeeds {succeeds} failures {failures} ignored {ignored} total"
  pure (if failures > 0 then 1 else 0)

def testRustFlavor (path : FilePath) (verbose : Bool) : IO UInt32 := do
  if ← System.FilePath.isDir path
  then
    (← System.FilePath.walkDir path)
    |> Array.filter (fun f => f.toString.endsWith "toml")
    |> Array.mapM (fun file => testRustFile file verbose)
    |> fun arr => do summary (← arr)
  else
    IO.println  s!"no such directory '{path}'"
    pure 1

def testAllFlavors (verbose : Bool) : IO UInt32 := do
  let retRust ← testRustFlavor "testdata/rust" verbose
  let retPcre ← summary #[← testPcreFile "testdata/pcre/testresult1.json" verbose]

  pure (if 0 < retRust + retPcre then 1 else 0)

def main (args : List String): IO UInt32 := do
  let exitcode ←
    try
      match args with
      | [] => pure <| ← testAllFlavors false
      | ["--pcre", path] => pure <| ← summary #[← testPcreFile path false]
      | ["--toml", path] => pure <| ← summary #[← testRustFile path false]
      | ["--toml", path, "-a"] => pure <| ← testRustFlavor path false
      | ["--toml", path, "-a", "-v"] => pure <| ← testRustFlavor path true
      | ["--pcre", path, "-v"] => pure <| ←  summary #[← testPcreFile path true]
      | _ =>
        IO.println  s!"usage: Test [--toml <path> |--pcre <path>] [-a] [-v]"
        pure 1
    catch e =>
      IO.println s!"Error: {e}"
      pure 1

  pure exitcode
