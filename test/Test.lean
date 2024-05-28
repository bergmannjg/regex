import Regex

import Test.Interval
import Test.Ast
import Test.Hir
import Test.Compiler

import RegexTest
import TomlLoader

open Lean System

open Regex

def test (path : FilePath): IO (Nat × Nat × Nat) := do
  let filename : String := path.fileName.getD ""
  if #["no-unicode.toml", "regex-lite.toml", "utf8.toml"].contains filename
  then pure (0, 0, 0) else
  let tests ← Loader.loadToml path
  let (succeeds, failures, ignored) ← RegexTest.testItems filename tests
  IO.println s!"succeeds {succeeds} failures {failures} ignored {ignored} in file {path}"
  pure (succeeds, failures, ignored)

def summary (arr : Array (Nat × Nat × Nat)) : IO UInt32 := do
  let (succeeds, failures, ignored) := arr |> Array.foldl
    (fun acc v => (acc.1+v.1, acc.2.1+v.2.1, acc.2.2+v.2.2) ) (0, 0, 0)
  IO.println s!"succeeds {succeeds} failures {failures} ignored {ignored} total"
  pure (if failures > 0 then 1 else 0)

def testAll (path : FilePath): IO UInt32 := do
  if ← System.FilePath.isDir path
  then
    (← System.FilePath.walkDir path)
    |> Array.filter (fun f => f.toString.endsWith "toml")
    |> Array.mapM (fun file => test file)
    |> fun arr => do summary (← arr)
  else
    IO.println  s!"no such directory '{path}'"
    pure 1

def main (args : List String): IO UInt32 := do
  let exitcode ←
    try
      match args with
      | [] => pure <| ← testAll "testdata"
      | ["--toml", path] => pure <| ← summary #[← test path]
      | ["--all", path] => pure <| ← testAll path
      | _ =>
        IO.println  s!"usage: Test [--toml <path>] [--all path]"
        pure 1
    catch e =>
      IO.println s!"Error: {e}"
      pure 1

  pure exitcode
