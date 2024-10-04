import Init.Meta
import Std.Internal.Parsec

open Lean Std.Internal Parsec Parsec.String Lean.Syntax

/-! Parser utils for ReaderT and StateT -/
namespace Parser

/-- extends `Lean.Parser.attempt` -/
def attemptM (p : (ReaderT ρ $ StateT σ Parser) α)
    : (ReaderT ρ $ StateT σ Parser) α :=  λ f s it =>
  match p f s it with
  | .success rem res => .success rem res
  | .error _ err => .error it err

private def orElseT (p : Parser α) (q : Unit → (ReaderT ρ $ StateT σ Parser) α)
    : (ReaderT ρ $ StateT σ Parser) α := do
  let flavor ← read
  let state ← get
  Parsec.orElse p (fun () => (·.1) <$> (q ()) flavor state)

instance : HOrElse (Parser α) ((ReaderT ρ $ StateT σ Parser) α) ((ReaderT ρ $ StateT σ Parser) α) where
  hOrElse := orElseT

/-- extends `Lean.Parser.tryCatch` -/
def tryCatchT (p : StateT σ Parser α)
    (csuccess : α → StateT σ Parser β)
    (cerror : Unit → StateT σ Parser β)
    : StateT σ  Parser β := fun s it =>
  match p s it with
  | .success rem a => csuccess a.1 a.2 rem
  | .error rem err =>
    -- We assume that it.s never changes as the `Parser` monad only modifies `it.pos`.
    if it.pos = rem.pos then cerror () s rem else .error rem err

private partial def manyCoreT (p : StateT σ Parser α) (acc : Array α) : StateT σ  Parser $ Array α :=
  tryCatchT p (manyCoreT p <| acc.push ·) (fun _ => pure acc)

/-- extends `Lean.Parser.many` -/
partial def manyM (p : (ReaderT ρ $ StateT σ Parser) α)
    : (ReaderT ρ $ StateT σ Parser) $ Array α := do
  manyCoreT (p (← read)) #[]

def failM {α : Type} (msg : String) : (ReaderT ρ $ StateT σ Parser) α :=
  ((fail msg) : Parser α)

def peekChar? : Parser $ Option Char :=
  peek?

def peekChar! : Parser Char :=
  peek!

def withPos (p : Parser α) : Parser (String.Pos × String.Pos × α) := fun it =>
  let pos := it.pos
  match p it with
  | .success rem a => .success rem (pos, rem.pos, a)
  | .error rem err => .error rem err

def withPosM (p : (ReaderT ρ $ StateT σ Parser) α)
    : (ReaderT ρ $ StateT σ Parser) (String.Pos × String.Pos × α) := fun f s it =>
  let pos := it.pos
  match p f s it with
  | .success rem a => .success rem ((pos, rem.pos, a.1), a.2)
  | .error rem err => .error rem err

def withPosSkip : Parser String.Pos := do
  let (_, t, _) ← withPos skip
  pure t

def optSkipChar (c : Char) : Parser Unit := do
  match ← peek? with
  | some c' => if c = c' then skip *> pure () else pure ()
  | none => pure ()

def optSkipString (s : String) : Parser Unit := do
  match ← peek? with
  | some _ => skipString s
  | none => pure ()

/-- exec `check` on current char -/
def testChar (check : Char -> Bool) : Parser Bool := do
  match ← peek? with
  | some c => if check c then pure true else pure false
  | none => pure false

/-- exec `check` on current char and consume char on success -/
def tryChar (check : Char -> Bool) : Parser $ Option Char := do
  match ← peek? with
  | some c => if check c then pure $ some (← any) else pure none
  | none => pure none

/-- exec `check` on current char and skip char on success -/
def trySkipChar (check : Char -> Bool) : Parser Bool := do
  if let some _ ← tryChar check then pure true else pure false

/-- exec `check` on current char and then exec `f` on consumed char on success -/
def tryCharThen (check : Char -> Bool) (f : Char → α) (msg : String := "") : Parser α := do
  if let some c ← tryChar check then pure $ f c
  else fail msg

/-- exec `check` on current char and map `f` on consumed char on success -/
def tryCharMap (check : Char -> Bool) (f : Char → α) : Parser $ Option α := do
  if let some c ← tryChar check then pure $ f c
  else pure none

/-- exec `check` on current char and then exec `p` on success -/
def tryCharThenPWithPos (check : Char -> Bool) (p : Parser α)
    : Parser $ Option (String.Pos × String.Pos × α) := do
  match ← peek? with
  | some c => if check c then pure $ some (← withPos p) else pure none
  | none => pure none

/-- exec `check` on current char and then exec `p` on success -/
def tryCharThenPWithPosM (check : Char -> Bool) (p : (ReaderT ρ $ StateT σ Parser) α)
    : (ReaderT ρ $ StateT σ Parser) $ Option (String.Pos × String.Pos × α) := do
  match ← peekChar? with
  | some c => if check c then pure $ some (← withPosM (p (← read))) else pure none
  | none => pure none

def tryCharWithPos (check : Char -> Bool)
    : Parser $ Option (String.Pos × String.Pos × Char) := do
  tryCharThenPWithPos check any

def tryCharWithPosMap (check : Char -> Bool) (f : Char → String.Pos → String.Pos → α)
    : Parser $ Option α := do
  if let some (p1, p2, c) ← tryCharWithPos check then pure $ f c p1 p2
  else pure none
