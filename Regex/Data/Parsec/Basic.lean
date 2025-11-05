import Init.Meta
import Parser

open Lean Lean.Syntax Parser Parser.Char

/-! Parser utils for ReaderT and StateT -/
namespace Parser

instance Parser.coeSimpleParser
    : Coe ((SimpleParser Substring Char) α) ((ReaderT ρ $ StateT σ (SimpleParser Substring Char)) α) where
  coe p := fun _ σ => do return (← p, σ)

/-- extends `Lean.Parser.attempt` -/
def attemptM (p : (ReaderT ρ $ StateT σ (SimpleParser Substring Char)) α)
    : (ReaderT ρ $ StateT σ (SimpleParser Substring Char)) α := fun f => do
  let (a, s) ← Parser.withBacktracking (p f (← get))
  set s
  pure a

def fail (msg : String) : (SimpleParser Substring Char) α :=
  throwUnexpectedWithMessage none msg

private def orElseT (p : (SimpleParser Substring Char) α)
  (q : Unit → (ReaderT ρ $ StateT σ (SimpleParser Substring Char)) α)
    : (ReaderT ρ $ StateT σ (SimpleParser Substring Char)) α := λ f s => do
  match ← eoption p with
  | .inl x => return (x, s)
  | .inr _ => (q ()) f s

instance : HOrElse
    ((SimpleParser Substring Char) α) ((ReaderT ρ $ StateT σ (SimpleParser Substring Char)) α)
    ((ReaderT ρ $ StateT σ (SimpleParser Substring Char)) α) where
  hOrElse := orElseT

partial def manyCore (p : (SimpleParser Substring Char) α)
  (acc : Array α) : (SimpleParser Substring Char) $ Array α := do
  let r ← Parser.efoldl (fun arr x => arr.push x) acc (Parser.withBacktracking p)
  return r.1

private def tryCatchT (p : StateT σ (SimpleParser Substring Char) α)
    (csuccess : α → StateT σ (SimpleParser Substring Char) α')
    (cerror : Unit → StateT σ (SimpleParser Substring Char) α')
    : StateT σ  (SimpleParser Substring Char) α' := fun s it =>
  match withBacktracking (p s) it with
  | .ok rem a => csuccess a.1 a.2 rem
  | .error rem _ => cerror () s rem

private partial def manyCoreT (p : StateT σ (SimpleParser Substring Char) α)
  (acc : Array α)
    : StateT σ (SimpleParser Substring Char) $ Array α :=
  tryCatchT p (manyCoreT p <| acc.push ·) (fun _ => pure acc)

/-- extends `Lean.Parser.many` -/
partial def manyM (p : (ReaderT ρ $ StateT σ (SimpleParser Substring Char)) α)
    : (ReaderT ρ $ StateT σ (SimpleParser Substring Char)) $ Array α := do
  manyCoreT (p (← read)) #[]

def ws : (ReaderT ρ $ StateT σ (SimpleParser Substring Char)) PUnit := fun _ t => do
  let _ ← manyCore (Char.ASCII.whitespace) #[]
  pure ((), t)

def peekChar?  : (SimpleParser Substring Char) $ Option Char := do
  match ← eoption peek with
  | .inl x => return some x
  | .inr _ => return none

def peekChar : (SimpleParser Substring Char) Char :=
  peek

def withPos (p : (SimpleParser Substring Char) α)
    : (SimpleParser Substring Char) (String.Pos × String.Pos × α) := do
  let cap ← Char.captureStr p
  return (cap.2.startPos, cap.2.stopPos, cap.1)

def withPosM (p : (ReaderT ρ $ StateT σ (SimpleParser Substring Char)) α)
    : (ReaderT ρ $ StateT σ (SimpleParser Substring Char)) (String.Pos × String.Pos × α) := fun f s => do
  let cap ← Char.captureStr (p f s)
  return ((cap.2.startPos, cap.2.stopPos, cap.1.1), cap.1.2)

def withPosSkip : (SimpleParser Substring Char) String.Pos := do
  let (_, t, _) ← withPos anyToken
  pure t


def skipChar (c : Char) : (SimpleParser Substring Char) Unit := do
  match ← eoption peek with
  | .inl c' => if c = c' then anyToken *> pure () else throwUnexpected
  | .inr e => throw e

def skipAnyChar : (SimpleParser Substring Char) Unit := do
  anyToken *> pure ()

def skipChar? (c : Char) : (SimpleParser Substring Char) Unit := do
  try skipChar c
  catch _ => pure ()

def skipString (tks : String) : (SimpleParser Substring Char) Unit := do
  string tks *> pure ()

def skipString? (tks : String) : (SimpleParser Substring Char) Unit := do
  try withBacktracking (skipString tks)
  catch _ => pure ()

/-- exec `check` on current char -/
def testChar (check : Char -> Bool) : (SimpleParser Substring Char) Bool := do
  match ← peekChar? with
  | some c => if check c then pure true else pure false
  | none => pure false

/-- exec `check` on current char and consume char on success -/
def tryChar (check : Char -> Bool) : (SimpleParser Substring Char) $ Option Char := do
  match ← peekChar? with
  | some c => if check c then pure $ some (← anyToken) else pure none
  | none => pure none

/-- exec `check` on current char and skip char on success -/
def trySkipChar (check : Char -> Bool) : (SimpleParser Substring Char) Bool := do
  if let some _ ← tryChar check then pure true else pure false

/-- exec `check` on current char and then exec `p` on success -/
def tryCharThenPWithPos (check : Char -> Bool) (p : (SimpleParser Substring Char) α)
    : (SimpleParser Substring Char) $ Option (String.Pos × String.Pos × α) := do
  match ← peekChar? with
  | some c => if check c then pure $ some (← withPos p) else pure none
  | none => pure none

/-- exec `check` on current char and then exec `p` on success -/
def tryCharThenPWithPosM (check : Char -> Bool) (p : (ReaderT ρ $ StateT σ (SimpleParser Substring Char)) α)
    : (ReaderT ρ $ StateT σ (SimpleParser Substring Char)) $ Option (String.Pos × String.Pos × α) := fun f s => do
  match ← peekChar? with
  | some c => if check c then
                let x ← withPos (p f s)
                pure $ (some (x.1, x.2.1, x.2.2.1), x.2.2.2)
              else pure (none, s)
  | none => pure (none, s)

def tryCharWithPos (check : Char -> Bool)
    :  (SimpleParser Substring Char) $ Option (String.Pos × String.Pos × Char) := do
  tryCharThenPWithPos check anyToken

def tryCharWithPosMap (check : Char -> Bool) (f : Char → String.Pos → String.Pos → α)
    :  (SimpleParser Substring Char) $ Option α := do
  if let some (p1, p2, c) ← tryCharWithPos check then pure $ f c p1 p2
  else pure none

def manyChars (p : (SimpleParser Substring Char) Char) : (SimpleParser Substring Char) String := do
  let chars ← manyCore p #[]
  return chars.toList.asString

def many1Chars (p : (SimpleParser Substring Char) Char) : (SimpleParser Substring Char) String := do
  let chars ← manyCore p #[← p]
  return chars.toList.asString
