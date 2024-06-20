import Regex

import Test.Interval
import Test.Ast
import Test.Hir
import Test.Compiler

import RegexTest
import TomlLoader
import PcreLoader

open Lean System

open Regex

def testToml (path : FilePath) (filename : String) (flavor : Syntax.Flavor) (tests : Array RegexTest) : IO (Nat × Nat × Nat) := do
  let (succeeds, failures, ignored) ← RegexTest.testItems flavor filename tests
  IO.println s!"succeeds {succeeds} failures {failures} ignored {ignored} in file {path}"
  pure (succeeds, failures, ignored)

def testRustFile (path : FilePath) : IO (Nat × Nat × Nat) := do
  let filename : String := path.fileName.getD ""
  if #["no-unicode.toml", "regex-lite.toml", "utf8.toml"].contains filename
  then pure (0, 0, 0) else
  let tests ← Loader.Toml.load path
  testToml path filename Syntax.Flavor.Rust tests

def testPcreFile (path : FilePath) : IO (Nat × Nat × Nat) := do
  let filename : String := path.fileName.getD ""
  let tests := (← Loader.Pcre.load path) |> Loader.Pcre.toRegexTestArray
  testToml path filename Syntax.Flavor.Pcre tests

def summary (arr : Array (Nat × Nat × Nat)) : IO UInt32 := do
  let (succeeds, failures, ignored) := arr |> Array.foldl
    (fun acc v => (acc.1+v.1, acc.2.1+v.2.1, acc.2.2+v.2.2) ) (0, 0, 0)
  IO.println s!"succeeds {succeeds} failures {failures} ignored {ignored} total"
  if failures > 0 then IO.eprintln s!"succeeds {succeeds} failures {failures} ignored {ignored} total"
  pure (if failures > 0 then 1 else 0)

def testAll (path : FilePath): IO UInt32 := do
  if ← System.FilePath.isDir path
  then
    (← System.FilePath.walkDir path)
    |> Array.filter (fun f => f.toString.endsWith "toml")
    |> Array.mapM (fun file => testRustFile file)
    |> fun arr => do summary (← arr)
  else
    IO.println  s!"no such directory '{path}'"
    pure 1

def main (args : List String): IO UInt32 := do
  let exitcode ←
    try
      match args with
      | [] => pure <| ← testAll "testdata/rust"
      | ["--pcre", path] => pure <| ← summary #[← testPcreFile path]
      | ["--toml", path] => pure <| ← summary #[← testRustFile path]
      | ["--all", path] => pure <| ← testAll path
      | _ =>
        IO.println  s!"usage: Test [--toml <path> | --pcre] [--all path]"
        pure 1
    catch e =>
      IO.println s!"Error: {e}"
      pure 1

  pure exitcode
