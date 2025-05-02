import Lean
import Lake.Toml
import Lake.Toml.Decode

import RegexTest

open Lean System Lake Lake.Toml

namespace Loader.Toml

/-- load toml files from Rust testdata -/

protected def Span.decodeToml (v : Value) : Option (Option RegexTest.Span) :=
  match v with
  | .array _ v =>
    match v with
    | #[] => return none
    | #[a, b] =>
      match a, b with
      | .integer _ a, .integer _ b => return (RegexTest.Span.mk a.toNat b.toNat none)
      | _, _ => none
    | _ => none
  | _ => none

protected def Spans.decodeToml (v : Value) : Option (Array $ Option RegexTest.Span) := do
  match v with
  | .array _ v => v |> Array.mapM (fun v => Span.decodeToml v)
  | .table _ t =>
    match t.find? `span with
    | some v => return #[← Span.decodeToml v]
    | _ =>
      match t.find? `spans with
      | some _ => return #[]
      | _ => none
  | _ => none

/- possible values
   []
   [[a, b]]
   [[a, b], ..., [c, d]]
   [[[a, b], ..., [c, d]]]
-/
protected def Captures.decodeToml (v : Value) (s := Syntax.missing)
    : EDecodeM (Array RegexTest.Captures) := do
  match v with
  | .array _ arr =>
    match Spans.decodeToml v with
    | some groups => pure (groups |> Array.map (fun g => ⟨#[g]⟩))
    | none =>
        let arr ← arr |> Array.mapM (fun v =>
              match Spans.decodeToml v with
              | some spans => pure spans
              | none => throwDecodeErrorAt v.ref "decode error of captures")
        pure (arr |> Array.map (fun groups => {groups}))
  | _ => throwDecodeErrorAt s s!"Captures.decodeToml: array expected {v}"

instance : DecodeToml (Array RegexTest.Captures) := ⟨fun v => do Captures.decodeToml v v.ref⟩

protected def Regex.decodeToml (v : Value) (s := Syntax.missing)
    : EDecodeM (Sum String (Array String)) := do
  match v with
  | .string _ s => pure <| Sum.inl s
  | .array _ _ => pure <| Sum.inr #[]
  | _ => throwDecodeErrorAt s s!"Regex.decodeToml: string or array expected {v}"

protected def Bounds.decodeToml (v : Value) (s := Syntax.missing)
    : EDecodeM (Array Nat) := do
  match v with
  | .array _ #[a, b] =>
      match a, b with
      | .integer _ a, .integer _ b => pure #[a.toNat, b.toNat]
      | _, _ => throwDecodeErrorAt s s!"integer array expected {v}"
  | .table _ _ => pure <| #[]
  | _ => throwDecodeErrorAt s s!"Regex.decodeToml: array or table expected {v}"

instance : Inhabited (Sum String (Array String)) := ⟨Sum.inr #[]⟩

protected def RegexTest.decodeToml (t : Table)
    : EDecodeM RegexTest := ensureDecode do
  let name ← t.tryDecodeD `name "."
  let regex : Sum String (Array String) ← optDecode (t.find? `regex) Regex.decodeToml
  let haystack : String ← t.tryDecodeD `haystack "."
  let «matches» : Array RegexTest.Captures ← t.tryDecodeD `«matches» #[]
  let bounds : Option $ Array Nat ← optDecode? (t.find? `bounds) Bounds.decodeToml
  let «match-limit» : Option Nat ← t.tryDecode? `«match-limit»
  let anchored : Option Bool ← t.tryDecode? `anchored
  let «case-insensitive» : Option Bool ← t.tryDecode? `«case-insensitive»
  let unescape : Option Bool ← t.tryDecode? `unescape
  let compiles : Option Bool ← t.tryDecode? `compiles
  let unicode : Option Bool ← t.tryDecode? `unicode
  let utf8 : Option Bool ← t.tryDecode? `utf8
  let «match-kind» : Option String ← t.tryDecode? `«match-kind»
  let «search-kind» : Option String ← t.tryDecode? `«search-kind»
  let «line-terminator» : Option String ← t.tryDecode? `«line-terminator»
  let «only-full-match» : Option Bool ← t.tryDecode? `«only-full-match»
  return {name, regex, haystack, «matches», bounds, «match-limit», anchored, «case-insensitive»,
          unescape, compiles, unicode, utf8, «match-kind», «search-kind», «line-terminator»,
          «only-full-match» }

instance : DecodeToml RegexTest := ⟨fun v => do RegexTest.decodeToml (← v.decodeTable)⟩

nonrec def parseToml (table : Table) (tomlFile : FilePath) : IO $ Array RegexTest := do
  let .ok tests errs := EStateM.run (s := #[]) do return ← table.tryDecodeD `test #[]

  if errs.isEmpty then return tests
  else
    let msgs := errs |> Array.foldl (init := "") (fun s err => s ++ s!"{err.msg} at {err.ref.getPos?}\n")
    throw $ .userError s!"decode errors in {tomlFile}\n{msgs}"

/-- load testdata toml files of Rust Regex crate -/
nonrec def load (tomlFile : FilePath) : IO $ Array RegexTest := do
  let fileName := tomlFile.fileName.getD tomlFile.toString
  let input ←
    match (← IO.FS.readBinFile tomlFile |>.toBaseIO) with
    | .ok bytes =>
      if let some input := String.fromUTF8? bytes then
        pure (input.crlfToLf)
      else
        throw $ .userError s!"{fileName} file contains invalid characters"
    | .error e => throw $ .userError s!"{e}"
  let ictx := Lean.Parser.mkInputContext input fileName
  match (← loadToml ictx |>.toBaseIO) with
  | .ok table => parseToml table tomlFile
  | .error log =>
      let msgs := log.toArray |> Array.foldl (init := "")
                      (fun s msg => s ++ s!"error at {msg.fileName} {msg.pos}")
      throw $ .userError s!"{msgs}"

end Loader.Toml
