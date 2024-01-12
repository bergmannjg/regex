import Regex
import Regex.Backtrack

open NFA
open Syntax
open Regex
open BoundedBacktracker

instance : MonadLift (Except String) IO where
  monadLift e :=
    match e with
    | Except.ok res => pure res
    | Except.error e => throw $ .userError e

private def compile (p : String): IO Unit := do
  let re ← build p default ⟨true⟩

  IO.println s!"{re.nfa}"

private def unescapeString (s : String) : String :=
  ⟨loop s.data []⟩
where
  toChar (a b : Char) : Char :=
    match decodeHexDigit a, decodeHexDigit b with
    | some n, some m =>
      let val := 16*n+m
      if h : UInt32.isValidChar val then ⟨val, h⟩ else ⟨0, by simp_arith⟩
    | _, _ => ⟨0, by simp_arith⟩
  loop (chars : List Char) (acc : List Char) : List Char :=
    match chars with
    | [] => acc
    | '\\' :: 'x' :: a :: b :: tail => (toChar a b) :: (loop tail acc)
    | '\\' :: 'n' :: tail => '\n' :: (loop tail acc)
    | '\\' :: 'r' :: tail => '\r' :: (loop tail acc)
    | head :: tail => head :: (loop tail acc)

private def captures (re haystack : String) (verbose : Bool := false) (all : Bool := false)
    (unescape : Bool := false) : IO Unit := do
  let haystack := if unescape then unescapeString haystack else haystack

  if verbose then
    IO.println s!"re '{re}' haystack chars '{haystack.data|>List.map (intAsString ·.val)}'"

  let regex ← Regex.build re
  if verbose then IO.println s!"nfa {regex.nfa}"

  let nl := "\n"

  if all
  then
    let (msgs, arr) := Regex.Log.all_captures haystack.toSubstring regex verbose
    IO.println s!"msgs {msgs |> Array.map (· ++ nl)}"
    match arr.size with
    | 0 => IO.println s!"captures: none"
    | _ =>
      IO.println s!"captures found: {arr.size}"
      arr |> Array.forM (fun captures => IO.println s!"{captures}")
  else
    match Regex.Log.captures haystack.toSubstring regex ⟨0⟩ verbose with
    | (msgs, none) =>
      if msgs.size > 0 then IO.println s!"msgs {msgs |> Array.map (· ++ nl)}"
      IO.println s!"captures: none"
    | (msgs, some captures) =>
      if msgs.size > 0 then IO.println s!"msgs {msgs |> Array.map (· ++ nl)}"
      IO.println s!"{captures}"

def main (args : List String): IO Unit := do
  try {
    match args with
    | ["ast", re] =>
        let ast ← Ast.parse re
        IO.println s!"Ast\n{ast}"
    | ["hir", re] =>
        let ast ← Ast.parse re
        let hir ← Syntax.translate default ast
        IO.println s!"Hir\n{hir}"
    | ["compile", re] =>
        compile re
    | ["captures", re, haystack] =>
        captures re haystack
    | ["captures", "-uv", re, haystack] =>
        captures re haystack (unescape := true) (verbose := true)
    | ["captures", "-a", re, haystack] =>
        captures re haystack (all := true)
    | ["captures", "-av", re, haystack] =>
        captures re haystack (verbose := true) (all := true)
    | ["captures", "-v", re, haystack] =>
        captures re haystack (verbose := true)
    | ["captures", re, "-f", path] =>
        let haystack ← IO.FS.readFile path
        captures re haystack
    | ["captures", "-a", re, "-f", path] =>
        let haystack ← IO.FS.readFile path
        captures re haystack (all := true)
    | _ => IO.println
            "usage: [ast <re>|[hir <re>|[compile <re>]|[captures [-v] [-a] [-av] <re> <s>]"
  }
  catch e => IO.println s!"error: {e}"
