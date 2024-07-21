import Init.Meta
import Lean.Data.Parsec

open Lean Lean.Parsec Lean.Syntax

/-! Parsec utils for ReaderT and StateT -/
namespace Parsec

/-- extends `Lean.Parsec.attempt` -/
def attemptM (p : (ReaderT ρ $ StateT σ Parsec) α)
    : (ReaderT ρ $ StateT σ Parsec) α :=  λ f s it =>
  match p f s it with
  | .success rem res => .success rem res
  | .error _ err => .error it err

private def orElseT (p : Parsec α) (q : Unit → (ReaderT ρ $ StateT σ Parsec) α)
    : (ReaderT ρ $ StateT σ Parsec) α := do
  let flavor ← read
  let state ← get
  Parsec.orElse p (fun () => (·.1) <$> (q ()) flavor state)

instance : HOrElse (Parsec α) ((ReaderT ρ $ StateT σ Parsec) α) ((ReaderT ρ $ StateT σ Parsec) α) where
  hOrElse := orElseT

/-- extends `Lean.Parsec.tryCatch` -/
def tryCatchT (p : StateT σ Parsec α)
    (csuccess : α → StateT σ Parsec β)
    (cerror : Unit → StateT σ Parsec β)
    : StateT σ  Parsec β := fun s it =>
  match p s it with
  | .success rem a => csuccess a.1 a.2 rem
  | .error rem err =>
    -- We assume that it.s never changes as the `Parsec` monad only modifies `it.pos`.
    if it.pos = rem.pos then cerror () s rem else .error rem err

private partial def manyCoreT (p : StateT σ Parsec α) (acc : Array α) : StateT σ  Parsec $ Array α :=
  tryCatchT p (manyCoreT p <| acc.push ·) (fun _ => pure acc)

/-- extends `Lean.Parsec.many` -/
partial def manyM (p : (ReaderT ρ $ StateT σ Parsec) α)
    : (ReaderT ρ $ StateT σ Parsec) $ Array α := do
  manyCoreT (p (← read)) #[]

def failM {α : Type} (msg : String) : (ReaderT ρ $ StateT σ Parsec) α :=
  fail msg

def withPos (p : Parsec α) : Parsec (String.Pos × String.Pos × α) := fun it =>
  let pos := it.pos
  match p it with
  | .success rem a => .success rem (pos, rem.pos, a)
  | .error rem err => .error rem err

def withPosM (p : (ReaderT ρ $ StateT σ Parsec) α)
    : (ReaderT ρ $ StateT σ Parsec) (String.Pos × String.Pos × α) := fun f s it =>
  let pos := it.pos
  match p f s it with
  | .success rem a => .success rem ((pos, rem.pos, a.1), a.2)
  | .error rem err => .error rem err

def withPosSkip : Parsec String.Pos := do
  let (_, t, _) ← withPos skip
  pure t

def optSkipChar (c : Char) : Parsec Unit := do
  match ← peek? with
  | some c' => if c = c' then skip *> pure () else pure ()
  | none => pure ()

def optSkipString (s : String) : Parsec Unit := do
  match ← peek? with
  | some _ => skipString s
  | none => pure ()

/-- exec `check` on current char -/
def testChar (check : Char -> Bool) : Parsec Bool := do
  match ← peek? with
  | some c => if check c then pure true else pure false
  | none => pure false

/-- exec `check` on current char and consume char on success -/
def tryChar (check : Char -> Bool) : Parsec $ Option Char := do
  match ← peek? with
  | some c => if check c then pure $ some (← anyChar) else pure none
  | none => pure none

/-- exec `check` on current char and skip char on success -/
def trySkipChar (check : Char -> Bool) : Parsec Bool := do
  if let some _ ← tryChar check then pure true else pure false

/-- exec `check` on current char and then exec `f` on consumed char on success -/
def tryCharThen (check : Char -> Bool) (f : Char → α) (msg : String := "") : Parsec α := do
  if let some c ← tryChar check then pure $ f c
  else fail msg

/-- exec `check` on current char and map `f` on consumed char on success -/
def tryCharMap (check : Char -> Bool) (f : Char → α) : Parsec $ Option α := do
  if let some c ← tryChar check then pure $ f c
  else pure none

/-- exec `check` on current char and then exec `p` on success -/
def tryCharThenPWithPos (check : Char -> Bool) (p : Parsec α)
    : Parsec $ Option (String.Pos × String.Pos × α) := do
  match ← peek? with
  | some c => if check c then pure $ some (← withPos p) else pure none
  | none => pure none

/-- exec `check` on current char and then exec `p` on success -/
def tryCharThenPWithPosM (check : Char -> Bool) (p : (ReaderT ρ $ StateT σ Parsec) α)
    : (ReaderT ρ $ StateT σ Parsec) $ Option (String.Pos × String.Pos × α) := do
  match ← peek? with
  | some c => if check c then pure $ some (← withPosM (p (← read))) else pure none
  | none => pure none

def tryCharWithPos (check : Char -> Bool)
    : Parsec $ Option (String.Pos × String.Pos × Char) := do
  tryCharThenPWithPos check anyChar

def tryCharWithPosMap (check : Char -> Bool) (f : Char → String.Pos → String.Pos → α)
    : Parsec $ Option α := do
  if let some (p1, p2, c) ← tryCharWithPos check then pure $ f c p1 p2
  else pure none
