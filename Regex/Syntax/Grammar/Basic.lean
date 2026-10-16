module

public import Init.Meta
public import ParseIt
public import Std.Internal.Parsec

open Std Lean Lean.Syntax ParseIt ParseIt.Char

public section

/-! Parser utils for ReaderT and StateT -/
namespace Parser

def remaining (it : Std.Iter (α := CharIterator) Char) :=
  it.internalState.slice.utf8ByteSize - it.internalState.pos.offset.byteIdx

abbrev SimpleCharParser := Parser (Error.Simple CharIterator) CharIterator Char

instance Parser.coeSimpleParser
    : Coe (SimpleCharParser α) ((ReaderT ρ $ StateT σ SimpleCharParser) α) where
  coe p := fun _ σ => do return (← p, σ)

def fail (msg : String) : SimpleCharParser α :=
  throwUnexpectedWithMessage none msg

def mkSimpleError (it : Std.Iter (α := CharIterator) Char) (msg : String)
    : ParseIt.Result (Error.Simple CharIterator) (it : Std.Iter (α := CharIterator) Char) α :=
  .error (Error.Simple.addMessage
    (Error.Simple.unexpected (HasPos.pos it) none) (HasPos.pos it) msg)

/--
  The recursive function ``loop`` calls ``p`` with a parser that acts like ``p``
  except it fails if called from the same or lower string position

  see https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Advent.20of.20Code.3F/near/405471085
-/
def loop (f : (ReaderT ρ $ StateT σ SimpleCharParser) α
  → (ReaderT ρ $ StateT σ SimpleCharParser) α)
    : (ReaderT ρ $ StateT σ SimpleCharParser) α := fun r s it =>
  let p : (ReaderT ρ (StateT σ SimpleCharParser)) α := fun r s' it' => do
    if remaining it' < remaining it then loop f r s' it'
    else return mkSimpleError it' "iterator does not move strictly forward"
  f p r s it
termination_by _ _ it => remaining it

section Folding

variable {ε ι τ : Type u} {m : Type u → Type v} [Iterator ι Id τ]

/- ParseIt.efoldlP with StateT σ -/
@[expose] def StateT.efoldlP [Iterators.Finite ι Id] [Monad m]
  (f : β → α → StateT σ (ParserT ε ι τ m) β) (init : β)
  (p : StateT σ (ParserT ε ι τ m) α) : StateT σ (ParserT ε ι τ m) (β × Option ε) := fun s it => do
  loop s it init it (.refl it)
where
  /-- Fold from iterator `cur`, which `it` progressed to, with accumulator `y`. -/
  loop [Iterators.Finite ι Id] (s : σ) (it : Iter (α := ι) τ) (y : β) (cur : Iter (α := ι) τ)
    (hcur : Progress cur it) : m (Result ε it ((β × Option ε) × σ)) := do
    match ← p s cur with
    | .error _ => return .ok cur hcur ((y, none), s)
    | .ok rest₁ h₁ x =>
      match ← f y x.1 x.2 rest₁ with
      | .error e => return .ok cur hcur ((y, some e), x.2)
      | .ok rest₂ h₂ y =>
        match h₂.trans h₁ with
        | .stay h => return .ok rest₂ (h ▸ hcur) ((y.1, none), y.2)
        | .moved h => loop y.2 it y.1 rest₂ ((Progress.moved h).trans hcur)
  termination_by cur.finitelyManySteps
  decreasing_by exact h

/- ParseIt.foldlP with StateT σ -/
def StateT.foldlP [Iterators.Finite ι Id] [Monad m]
  (f : β → α → StateT σ (ParserT ε ι τ m) β) (init : β)
  (p : StateT σ (ParserT ε ι τ m) α) : StateT σ (ParserT ε ι τ m) β :=
  Prod.fst <$> efoldlP f init p

/- ParseIt.foldl with StateT σ -/
public def StateT.foldl [Iterators.Finite ι Id] [Monad m] (f : β → α → β) (init : β)
    (p : StateT σ (ParserT ε ι τ m) α) : StateT σ (ParserT ε ι τ m) β :=
  StateT.foldlP (fun y x => pure (f y x)) init p

end Folding

def manyM (p : (ReaderT ρ $ StateT σ SimpleCharParser) α)
    : (ReaderT ρ $ StateT σ SimpleCharParser) $ Array α := fun r => do
  StateT.foldl (fun acc a => acc.push a) (#[] : Array α) (p r)

def ws : (ReaderT ρ $ StateT σ SimpleCharParser) PUnit := fun _ s => do
  let _ ← foldl (fun acc _ => acc) (#[] : Array Char) (Char.ASCII.whitespace)
  pure ((), s)

def peekChar?  : SimpleCharParser $ Option Char :=
  option? (lookAhead anyToken)

def peekChar : SimpleCharParser Char :=
  lookAhead anyToken

def withPos (p : SimpleCharParser α)
    : SimpleCharParser (String.Pos.Raw × String.Pos.Raw × α) := do
  let (a, s1, s2) ← withSpan p
  return (s1, s2, a)

def withPosM (p : (ReaderT ρ $ StateT σ SimpleCharParser) α)
    : (ReaderT ρ $ StateT σ SimpleCharParser) (String.Pos.Raw × String.Pos.Raw × α) := fun f s => do
  let (a, s1, s2) ← withSpan (p f s)
  return ((s1, s2, a.1), a.2)

def skipChar (c : Char) : SimpleCharParser Unit := do
  match ← tryCatch (Sum.inl <$> (lookAhead anyToken)) (fun e => pure (.inr e)) with
  | .inl c' => if c = c' then anyToken *> pure () else throwUnexpected
  | .inr e => throw e

def skipAnyChar : SimpleCharParser Unit := do
  anyToken *> pure ()

def skipChar? (c : Char) : SimpleCharParser Unit := do
  try skipChar c
  catch _ => pure ()

def skipString (tks : String) : SimpleCharParser Unit := do
  string tks *> pure ()

def skipString? (tks : String) : SimpleCharParser Unit := do
  try (skipString tks)
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
  let chars ← foldl (fun acc a => acc.push a)  (#[] : Array Char) p
  return String.ofList chars.toList

def many1Chars (p : SimpleCharParser Char) : SimpleCharParser String := do
  let chars ← foldl (fun acc a => acc.push a)  (#[← p] : Array Char) p
  return String.ofList chars.toList
