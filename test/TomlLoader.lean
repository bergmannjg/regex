import Lean
import Lake.Toml
import Lake.Toml.Decode

import RegexTest

open Lean System Lake Lake.Toml

namespace Loader.Toml

/-- load toml files from Rust testdata -/

protected def Span.decodeToml (v : Value) (s := Syntax.missing)
    : Except (Array DecodeError) (Option RegexTest.Span) :=
  match v with
  | .array _ v =>
    match v with
    | #[] => pure none
    | #[a, b] =>
      match a, b with
      | .integer _ a, .integer _ b => pure (RegexTest.Span.mk a.toNat b.toNat none)
      | _, _ =>  Except.error #[DecodeError.mk s s!"integer array expected {v}"]
    | _ =>  Except.error #[DecodeError.mk s s!"array size 0 or 2 expected {v}"]
  | _ =>
    Except.error #[DecodeError.mk s s!"Span.decodeToml: array expected {v}"]

protected def Spans.decodeToml (v : Value) (s := Syntax.missing)
    : Except (Array DecodeError) (Array $ Option RegexTest.Span) := do
  match v with
  | .array _ v =>
    let arr ← v |> Array.mapM (fun v => do return ← Span.decodeToml v v.ref)
    return arr
  | .table _ t =>
    match t.find? `span with
    | some v => pure #[← Span.decodeToml v]
    | _ =>
      match t.find? `spans with
      | some _ => pure #[]
      | _ => Except.error #[DecodeError.mk s s!"Spans.decodeToml: span|spans key expected {v}"]
  | _ =>
    Except.error #[DecodeError.mk s s!"Spans.decodeToml: array expected {v}"]

/- possible values
   []
   [[a, b]]
   [[a, b], ..., [c, d]]
   [[[a, b], ..., [c, d]]]
-/
protected def Captures.decodeToml (v : Value) (s := Syntax.missing)
    : Except (Array DecodeError) (Array RegexTest.Captures) := do
  match v with
  | .array _ arr =>
    match Spans.decodeToml v v.ref with
    | Except.ok groups => pure (groups |> Array.map (fun g => ⟨#[g]⟩))
    | Except.error _ =>
        let arr ← arr |> Array.mapM (fun v =>
              match Spans.decodeToml v v.ref with
              | Except.ok spans => pure spans
              | Except.error e => throw e)
        pure (arr |> Array.map (fun groups => {groups}))
  | _ => Except.error #[DecodeError.mk s s!"Captures.decodeToml: array expected {v}"]

instance : DecodeToml (Array RegexTest.Captures) := ⟨fun v => do Captures.decodeToml v v.ref⟩

protected def Regex.decodeToml (v : Value) (s := Syntax.missing)
    : Except (Array DecodeError) (Sum String (Array String)) := do
  match v with
  | .string _ s => pure <| Sum.inl s
  | .array _ _ => pure <| Sum.inr #[]
  | _ => Except.error #[DecodeError.mk s s!"Regex.decodeToml: string or array expected {v}"]

protected def Bounds.decodeToml (v : Value) (s := Syntax.missing)
    : Except (Array DecodeError) (Array Nat) := do
  match v with
  | .array _ #[a, b] =>
      match a, b with
      | .integer _ a, .integer _ b => pure #[a.toNat, b.toNat]
      | _, _ =>  Except.error #[DecodeError.mk s s!"integer array expected {v}"]
  | .table _ _ => pure <| #[]
  | _ => Except.error #[DecodeError.mk s s!"Regex.decodeToml: array or table expected {v}"]

protected def RegexTest.decodeToml (t : Table)
    : Except (Array DecodeError) RegexTest := ensureDecode do
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
  let (tests, errs) := Id.run <| StateT.run (s := (#[] : Array DecodeError)) do
    let tests ← table.tryDecodeD `test #[]
    return tests

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
