import Init.System.IO
import Lake.Util.Cli
import Lake.Util.MainM
import Lake.CLI.Error
import Regex
import Regex.Backtrack

open Lean
open Lake
open NFA
open Syntax
open Regex
open BoundedBacktracker

instance : MonadLift (Except String) IO where
  monadLift e :=
    match e with
    | Except.ok res => pure res
    | Except.error e => throw $ .userError e

structure RegexOptions where
  verbosity : Lake.Verbosity := .quiet
  wantsHelp : Bool := false
  all : Bool := false
  unescape : Bool := false
  path : Option String := none

abbrev CliMainM := ExceptT CliError MainM
abbrev CliStateM := StateT RegexOptions CliMainM
abbrev CliM := ArgsT CliStateM

def CliM.run (self : CliM α) (args : List String) : BaseIO ExitCode := do
  let main := self.run' args |>.run' {}
  let main := main.run >>= fun | .ok a => pure a | .error e => MonadError.error e.toString
  main.run

def takeOptArg (opt arg : String) : CliM String := do
  match (← takeArg?) with
  | none => throw <| CliError.missingOptArg opt arg
  | some v => pure v

def regexShortOption : (opt : Char) → CliM PUnit
| 'a' => modifyThe RegexOptions ({· with all := true})
| 'f' => do let path ← takeOptArg "-f" "path"; modifyThe RegexOptions ({· with path})
| 'h' => modifyThe RegexOptions ({· with wantsHelp := true})
| 'u' => modifyThe RegexOptions ({· with unescape := true})
| 'v' => modifyThe RegexOptions ({· with verbosity := Lake.Verbosity.verbose})
| opt => throw <| CliError.unknownShortOption opt

def regexLongOption : (opt : String) → CliM PUnit
| "--help" => modifyThe RegexOptions ({· with wantsHelp := true})
| "--verbose" => modifyThe RegexOptions ({· with verbosity := Lake.Verbosity.verbose})
| opt =>  throw <| CliError.unknownLongOption opt

def regexOption :=
  option {
    short := regexShortOption
    long := regexLongOption
    longShort := shortOptionWithArg regexShortOption
  }

def getWantsHelp : CliStateM Bool :=
  (·.wantsHelp) <$> get

def usage :=
  "
usage: inspect [OPTIONS] <COMMAND>

COMMANDS:
  ast <re>                    print the abstract syntax tree
  hir <re>                    print the high level intermediate representation
  captures <re> <s>           get first or all captures of <re> in <s>

OPTIONS:
  --help, -h                  print help
  --verbose, -v               show verbose information
  --all, -a                   get all captures
  --file, -f <path>           path to file with haystack
  --unescape, -u              unescape haystack"

namespace regex

private def unescapeString (s : String) : String :=
  ⟨loop s.data []⟩
where
  toChar (a b : Char) : Char :=
    match Char.decodeHexDigit a, Char.decodeHexDigit b with
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

def ast : CliM PUnit := do
  match ← takeArg? with
  | some re =>
      let ast ← Ast.parse re
      IO.println s!"Ast\n{ast}"
  | none => throw <| CliError.missingArg "re"

def hir : CliM PUnit := do
  match ← takeArg? with
  | some re =>
      let ast ← Ast.parse re
      let hir ← Syntax.translate default ast
      IO.println s!"Hir\n{hir}"
  | none => throw <| CliError.missingArg "re"

def compile : CliM PUnit := do
  match ← takeArg? with
  | some pat =>
    let re ← build pat default ⟨true⟩
    IO.println s!"{re.nfa}"
  | none => throw <| CliError.missingArg "re"

def captures : CliM PUnit := do
  processOptions regexOption
  let opts ← getThe RegexOptions
  let (re, haystack) :=
    ← match ← takeArg?, ← takeArg? with
    | some re, some haystack => pure (re, haystack)
    | none, _ => throw <| CliError.missingArg "regex"
    | some re, none =>
      match opts.path with
      | some path => do
        let haystack ← IO.FS.readFile path
        pure (re, haystack)
      | none => throw <| CliError.missingArg "haystack"

  let haystack := if opts.unescape then unescapeString haystack else haystack
  let isVerbose := opts.verbosity == Lake.Verbosity.verbose
  if isVerbose then
    let chars := haystack.data |> List.map (fun (c : Char) => (UInt32.intAsString c.val))
    IO.println s!"re '{re}' haystack chars '{chars}'"

  let regex ← Regex.build re
  if isVerbose then IO.println s!"nfa {regex.nfa}"

  let nl := "\n"

  if opts.all
  then
    let (msgs, arr) := Regex.Log.all_captures haystack.toSubstring regex (isVerbose)
    if msgs.size > 0 then IO.println s!"msgs {msgs |> Array.map (· ++ nl)}"
    match arr.size with
    | 0 => IO.println s!"captures: none"
    | _ =>
      IO.println s!"captures found: {arr.size}"
      arr |> Array.forM (fun captures => IO.println s!"{captures}")
  else
    match Regex.Log.captures haystack.toSubstring regex ⟨0⟩ (isVerbose) with
    | (msgs, none) =>
      if msgs.size > 0 then IO.println s!"msgs {msgs |> Array.map (· ++ nl)}"
      IO.println s!"captures: none"
    | (msgs, some captures) =>
      if msgs.size > 0 then IO.println s!"msgs {msgs |> Array.map (· ++ nl)}"
      IO.println s!"{captures}"

end regex

def regexCli : (cmd : String) → CliM PUnit
| "ast" => regex.ast
| "hir" => regex.hir
| "compile" => regex.compile
| "captures" => regex.captures
| cmd => throw <| CliError.unknownCommand cmd

def regex : CliM PUnit := do
  match (← getArgs) with
  | [] => IO.println usage
  | _ =>
    processLeadingOptions regexOption
    if let some cmd ← takeArg? then
      regexCli cmd
    else
      if (← getWantsHelp) then
        IO.println usage
      else
        throw <| CliError.missingCommand

def cli (args : List String) : BaseIO ExitCode :=
  (regex).run args

def main (args : List String) : IO UInt32 := do
  cli args
