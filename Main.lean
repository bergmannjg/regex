import Init.System.IO
import Lake.Util.Cli
import Lake.Util.MainM
import Lake.CLI.Error
import Batteries.Data.String

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
  haystackPath : Option String := none
  patternPath : Option String := none
  unanchoredPrefix : Bool := true
  unanchoredPrefixSimulation : Bool := false
  flavor : Syntax.Flavor := Syntax.Flavor.Pcre
  extended : Regex.Grammar.ExtendedKind := .None

abbrev CliMainM := ExceptT CliError MainM
abbrev CliStateM := StateT RegexOptions CliMainM
abbrev CliM := ArgsT CliStateM

instance : MonadLift (Except String) CliMainM where
  monadLift e :=
    match e with
    | Except.ok res => pure res
    | Except.error e => throw $ .invalidEnv e

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
| 'f' => do let haystackPath ← takeOptArg "-f" "path"; modifyThe RegexOptions ({· with haystackPath})
| 'F' => do let patternPath ← takeOptArg "-F" "path"; modifyThe RegexOptions ({· with patternPath})
| 'h' => modifyThe RegexOptions ({· with wantsHelp := true})
| 'n' => modifyThe RegexOptions ({· with unanchoredPrefix := false})
| 's' => modifyThe RegexOptions ({· with unanchoredPrefixSimulation := true})
| 'u' => modifyThe RegexOptions ({· with unescape := true})
| 'v' => modifyThe RegexOptions ({· with verbosity := Lake.Verbosity.verbose})
| 'x' => modifyThe RegexOptions ({· with extended := .Extended})
| 'X' => modifyThe RegexOptions ({· with extended := .ExtendedMore})
| opt => throw <| CliError.unknownShortOption opt

def regexLongOption : (opt : String) → CliM PUnit
| "--help" => modifyThe RegexOptions ({· with wantsHelp := true})
| "--verbose" => modifyThe RegexOptions ({· with verbosity := Lake.Verbosity.verbose})
| "--no-unanchored-prefix" => modifyThe RegexOptions ({· with unanchoredPrefix := false})
| "--unanchored-prefix-simulation" => modifyThe RegexOptions ({· with unanchoredPrefixSimulation := true})
| "--flavor" => do
      let flavor ← takeOptArg "--flavor" "path"
      modifyThe RegexOptions ({· with flavor := if flavor = "Rust" then Syntax.Flavor.Rust else Syntax.Flavor.Pcre})
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
  ast <re>                       print the abstract syntax tree
  hir <re>                       print the high level intermediate representation
  compile <re>                   print the nfa
  captures <re> <s>              get first or all captures of <re> in <s>

OPTIONS:
  --help, -h                         print help
  --verbose, -v                      show verbose information
  --all, -a                          get all captures
  --file, -f <path>                  path to file with haystack
  --no-unanchored-prefix, -n         whether not to compile an unanchored prefix into the NFA
  --unanchored-prefix-simulation, -s whether to simulate an unanchored prefix with the backtracker
  --unescape, -u                     unescape haystack"

namespace regex

private def unescapeString (s : String) : String :=
  ⟨loop s.data []⟩
where
  toChar (a b : Char) : Char :=
    match Char.decodeHexDigit a, Char.decodeHexDigit b with
    | some n, some m =>
      let val := 16*n+m
      if h : UInt32.isValidChar val then ⟨val, h⟩ else ⟨0, by simp +arith +decide⟩
    | _, _ => ⟨0, by simp +arith +decide⟩
  loop (chars : List Char) (acc : List Char) : List Char :=
    match chars with
    | [] => acc
    | '\\' :: 'x' :: a :: b :: tail => (toChar a b) :: (loop tail acc)
    | '\\' :: 'n' :: tail => '\n' :: (loop tail acc)
    | '\\' :: 'r' :: tail => '\r' :: (loop tail acc)
    | '\\' :: 't' :: tail => '\t' :: (loop tail acc)
    | '\\' :: '\\' :: tail => '\\' :: (loop tail acc)
    | head :: tail => head :: (loop tail acc)

def grammar : CliM PUnit := do
  processOptions regexOption
  let opts ← getThe RegexOptions
  match ← takeArg? with
  | some re =>
      let re := if opts.unescape then unescapeString re else re
      let g ← Regex.Grammar.parse re opts.flavor opts.extended
      IO.println s!"Grammar {opts.flavor}\n{g}"
  | none => throw <| CliError.missingArg "re"

def grammarT : CliM PUnit := do
  processOptions regexOption
  let opts ← getThe RegexOptions
  match ← takeArg? with
  | some re =>
      let g ← Regex.Grammar.parse re opts.flavor opts.extended
      let g' ← Regex.Grammar.translate g
      IO.println s!"Grammar translated\n{g'}"
  | none => throw <| CliError.missingArg "re"

def ast : CliM PUnit := do
  processOptions regexOption
  let opts ← getThe RegexOptions
  match ← takeArg? with
  | some re =>
      let ast ← AstItems.parse re opts.flavor opts.extended
      IO.println s!"Ast {opts.flavor}\n{ast}"
  | none => throw <| CliError.missingArg "re"

def hir : CliM PUnit := do
  processOptions regexOption
  let opts ← getThe RegexOptions
  match ← takeArg? with
  | some re =>
      let ast ← AstItems.parse re opts.flavor
      let hir ← Syntax.translate default ast
      IO.println s!"Hir\n{hir}"
  | none => throw <| CliError.missingArg "re"

def compile : CliM PUnit := do
  processOptions regexOption
  let opts ← getThe RegexOptions
  match ← takeArg? with
  | some pat =>
    let re ← build pat opts.flavor default default
    IO.println s!"{re.nfa}"
  | none => throw <| CliError.missingArg "re"

def captures : CliM PUnit := do
  processOptions regexOption
  let opts ← getThe RegexOptions
  let (re, haystack) :=
    ← match ← takeArg?, ← takeArg? with
    | some re, some haystack => pure (re, haystack)
    | some x, none =>
      match opts.haystackPath with
      | some path => do
        let haystack ← IO.FS.readFile path
        pure (x, haystack)
      | none =>
          match opts.patternPath with
          | some path => do
            let re ← IO.FS.readFile path
            pure (re, x)
          | none => throw <| CliError.missingArg "regex or haystack"
    | none, _ => throw <| CliError.missingArg "regex and haystack"
  let haystack := if opts.unescape then unescapeString haystack else haystack
  let isVerbose := opts.verbosity == Lake.Verbosity.verbose
  if isVerbose then
    let chars := haystack.data |> List.map (fun (c : Char) => (UInt32.intAsString c.val))
    IO.println s!"re '{re}' haystack chars '{chars}'"

  let flags : Syntax.Flags := default
  let config := {(default : Compiler.Config) with
                    unanchored_prefix := opts.unanchoredPrefix
                    unanchored_prefix_simulation := opts.unanchoredPrefixSimulation }

  let regex ← Regex.build re opts.flavor flags config opts.extended
  if isVerbose then IO.println s!"nfa {regex.nfa}"
  if isVerbose then IO.println s!"nfa unanchored_prefix_in_backtrack {regex.nfa.unanchored_prefix_in_backtrack}"

  let nl := "\n"

  if opts.all
  then
    let (msgs, arr) := Regex.Log.all_captures haystack regex (isVerbose)
    if msgs.size > 0 then IO.println s!"msgs {msgs |> Array.map (· ++ nl)}"
    match arr.size with
    | 0 => IO.println s!"captures: none"
    | _ =>
      IO.println s!"captures found: {arr.size}"
      arr |> Array.forM (fun captures => IO.println s!"{captures}")
  else
    match Regex.Log.captures haystack regex (instSubstringValid haystack).default (isVerbose) with
    | (msgs, none) =>
      if msgs.size > 0 then IO.println s!"msgs {msgs |> Array.map (· ++ nl)}"
      IO.println s!"captures: none"
    | (msgs, some captures) =>
      if msgs.size > 0 then IO.println s!"msgs {msgs |> Array.map (· ++ nl)}"
      IO.println s!"{captures}"

      if isVerbose then
        IO.println s!"fullMatch chars {captures.fullMatch.val.toString.asHex} utf8ByteSize {captures.fullMatch.val.toString.utf8ByteSize}"

end regex

def regexCli : (cmd : String) → CliM PUnit
| "grammar" => regex.grammar
| "grammarT" => regex.grammarT
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
