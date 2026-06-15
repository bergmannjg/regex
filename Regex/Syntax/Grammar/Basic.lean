module

public import Init.Meta
public import Parser
public import Std.Internal.Parsec

open Lean Lean.Syntax Parser Parser.Char

public section

/-! Parser utils for ReaderT and StateT -/
namespace Parser

abbrev SimpleCharParser := SimpleParser String.Slice Char

instance Parser.coeSimpleParser
    : Coe (SimpleCharParser α) ((ReaderT ρ $ StateT σ SimpleCharParser) α) where
  coe p := fun _ σ => do return (← p, σ)

/-- extends `Lean.Parser.attempt` -/
def attemptM (p : (ReaderT ρ $ StateT σ SimpleCharParser) α)
    : (ReaderT ρ $ StateT σ SimpleCharParser) α := fun f => do
  let (a, s) ← Parser.withBacktracking (p f (← get))
  set s
  pure a

def fail (msg : String) : SimpleCharParser α :=
  throwUnexpectedWithMessage none msg

private def mkSimpleError (it : String.Slice) (msg : String)
    : Parser.Result (Error.Simple String.Slice Char) String.Slice α :=
  .error it (Error.Simple.addMessage
    (Error.Simple.unexpected it.startInclusive.offset none) it.startInclusive.offset msg)

/-- Returns a natural number measure of remaining input.
  see https://github.com/fgdorais/lean4-parser/pull/99
-/
class Parser.Stream.Remaining (σ : Type) where
  remaining : σ -> Nat

/- see https://github.com/fgdorais/lean4-parser/pull/99 -/
instance : Parser.Stream.Remaining String.Slice where
  remaining s := s.utf8ByteSize

open Parser.Stream in
/--
  The recursive function ``loop`` calls ``p`` with a parser that acts like ``p``
  except it fails if called from the same or lower string position

  see https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Advent.20of.20Code.3F/near/405471085
-/
def loop (p : (ReaderT ρ $ StateT σ SimpleCharParser) α
  → (ReaderT ρ $ StateT σ SimpleCharParser) α)
    : (ReaderT ρ $ StateT σ SimpleCharParser) α := fun r s it =>
  let p' : (ReaderT ρ (StateT σ SimpleCharParser)) α := fun r s' it' =>
    if Remaining.remaining it' < Remaining.remaining it then
      loop p r s' it'
    else
      return mkSimpleError it' "recursive call going backwards in the string"
  p p' r s it
termination_by _ _ it => Remaining.remaining it

open Parser.Stream in
/-- accumulates the result of ``p`` until ``p`` fails -/
private def foldM (p : StateT σ SimpleCharParser α) (acc : Array α)
    : StateT σ SimpleCharParser $ Array α := fun s it =>
  match withBacktracking (p s) it with
  | .ok rem a =>
    if Remaining.remaining rem < Remaining.remaining it then foldM p (acc.push a.1) a.2 rem
    else return mkSimpleError rem "recursive call going backwards in the string"
  | .error rem _ => ((return acc) : StateT _ SimpleCharParser _) s rem
termination_by _ it => Remaining.remaining it

/-- accumulates the result of ``p`` until ``p`` fails -/
private def fold (p : SimpleCharParser α) (acc : Array α)
    : SimpleCharParser $ Array α :=
  foldM p acc () >>= (fun x => pure x.1)

def manyM (p : (ReaderT ρ $ StateT σ SimpleCharParser) α)
    : (ReaderT ρ $ StateT σ SimpleCharParser) $ Array α := do
  foldM (p (← read)) #[]

def ws : (ReaderT ρ $ StateT σ SimpleCharParser) PUnit := fun _ t => do
  let _ ← fold (Char.ASCII.whitespace) #[]
  pure ((), t)

def peekChar?  : SimpleCharParser $ Option Char :=
  option? peek

def peekChar : SimpleCharParser Char :=
  peek

def withPos (p : SimpleCharParser α)
    : SimpleCharParser (String.Pos.Raw × String.Pos.Raw × α) := do
  let (a, s) ← withCapture p
  return (s.start, s.stop, a)

def withPosM (p : (ReaderT ρ $ StateT σ SimpleCharParser) α)
    : (ReaderT ρ $ StateT σ SimpleCharParser) (String.Pos.Raw × String.Pos.Raw × α) := fun f s => do
  let (a, s) ← withCapture (p f s)
  return ((s.start, s.stop, a.1), a.2)

def skipChar (c : Char) : SimpleCharParser Unit := do
  match ← eoption peek with
  | .inl c' => if c = c' then anyToken *> pure () else throwUnexpected
  | .inr e => throw e

def skipAnyChar : SimpleCharParser Unit := do
  anyToken *> pure ()

def skipChar? (c : Char) : SimpleCharParser Unit := do
  try skipChar c
  catch _ => pure ()

def skipString (tks : String) : SimpleCharParser Unit := do
  chars tks *> pure ()

def skipString? (tks : String) : SimpleCharParser Unit := do
  try withBacktracking (skipString tks)
  catch _ => pure ()

/-- exec `check` on current char -/
def testChar (check : Char -> Bool) : SimpleCharParser Bool := do
  match ← peekChar? with
  | some c => if check c then pure true else pure false
  | none => pure false

/-- exec `check` on current char and consume char on success -/
def tryChar (check : Char -> Bool) : SimpleCharParser $ Option Char := do
  match ← peekChar? with
  | some c => if check c then pure $ some (← anyToken) else pure none
  | none => pure none

/-- exec `check` on current char and skip char on success -/
def trySkipChar (check : Char -> Bool) : SimpleCharParser Bool := do
  if let some _ ← tryChar check then pure true else pure false

/-- exec `check` on current char and then exec `p` on success -/
def tryCharThenPWithPos (check : Char -> Bool) (p : SimpleCharParser α)
    : SimpleCharParser $ Option (String.Pos.Raw × String.Pos.Raw × α) := do
  match ← peekChar? with
  | some c => if check c then pure $ some (← withPos p) else pure none
  | none => pure none

/-- exec `check` on current char and then exec `p` on success -/
def tryCharThenPWithPosM (check : Char -> Bool) (p : (ReaderT ρ $ StateT σ SimpleCharParser) α)
    : (ReaderT ρ $ StateT σ SimpleCharParser) $ Option (String.Pos.Raw × String.Pos.Raw × α) := fun f s => do
  match ← peekChar? with
  | some c => if check c then
                let x ← withPos (p f s)
                pure $ (some (x.1, x.2.1, x.2.2.1), x.2.2.2)
              else pure (none, s)
  | none => pure (none, s)

def tryCharWithPos (check : Char -> Bool)
    :  SimpleCharParser $ Option (String.Pos.Raw × String.Pos.Raw × Char) := do
  tryCharThenPWithPos check anyToken

def tryCharWithPosMap (check : Char -> Bool) (f : Char → String.Pos.Raw → String.Pos.Raw → α)
    :  SimpleCharParser $ Option α := do
  if let some (p1, p2, c) ← tryCharWithPos check then pure $ f c p1 p2
  else pure none

def manyChars (p : SimpleCharParser Char) : SimpleCharParser String := do
  let chars ← fold p #[]
  return String.ofList chars.toList

def many1Chars (p : SimpleCharParser Char) : SimpleCharParser String := do
  let chars ← fold p #[← p]
  return String.ofList chars.toList
