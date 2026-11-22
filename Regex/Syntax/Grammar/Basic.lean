module

public import Init.Meta
import all ParseIt.Error
import all ParseIt.Basic
public import ParseIt
public import Std.Internal.Parsec

public import Std.Tactic.Do
public import Std.Tactic.Do.Syntax
public import Std.WP

public import Lemmas

open Std Lean Lean.Syntax Std.WP ParseIt ParseIt.Char

@[expose] public section

set_option experimental.vcgen true

/-! Parser utils for SimpleCharParser -/
namespace Parser

section Instances

variable {ε ι τ σ ρ α : Type u} [Iterator ι Id τ]

def pushResultStateT (it : Iter (α := ι) τ)
  (post : α → (pair' : (σ × Iter (α := ι) τ)) → Progress pair'.2 it → Prop) (epost : ε → Prop)
    : (ParseIt.Result ε it (α × σ)) → Prop
  | .ok s h a => post a.1 (a.2, s) h
  | .error el => epost el

instance StateTParser.instWP
    : WP ((StateT σ (Parser ε ι τ) α)) α ((σ × IterWithProgress ι τ) → Prop) (ε → Prop)  where
  wpTrans x := ⟨fun post epost (st, it) => pushResultStateT it.rest
                (fun a it' h' => post a (it'.1, IterWithProgress.mk it.it it'.2 (h'.trans it.p)))
                epost ((x st) it.rest)⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    grind only [= pushResultStateT.eq_def]

instance ReaderTStateTParser.instWP
    : WP (ReaderT ρ (StateT σ (Parser ε ι τ)) α) α ((ρ × σ × IterWithProgress ι τ) → Prop) (ε → Prop)  where
  wpTrans x := ⟨fun post epost (r, st, it) => pushResultStateT it.rest
                (fun a it' h' => post a (r, it'.1, IterWithProgress.mk it.it it'.2 (h'.trans it.p)))
                epost ((x r st) it.rest)⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    grind only [= pushResultStateT.eq_def]

instance ReaderTStateTParser.instWPMonad
    : WPMonad (ReaderT ρ (StateT σ (Parser ε ι τ))) ((ρ × σ × IterWithProgress ι τ) → Prop) (ε → Prop) where
  toWP α := @ReaderTStateTParser.instWP ε ι τ σ ρ _ _
  pure_le_wp_pure x := fun post epost _ => by
    simp [pure, wp, WP.trans, pushResultStateT, ReaderT.pure, StateT.pure]
  bind_le_wp_bind x f := fun post epost it => by
    simp only [wp, WP.trans, bind, pushResultStateT, Order.PartialOrder.rel,
                ReaderT.bind, StateT.bind, pure]
    grind

theorem ReaderTStateTParser.of_wp_eq
  (x : ReaderT ρ (StateT σ (Parser ε ι τ)) α) (h : Triple x pre post epost) (r : ρ) (st : σ)
  (it : Iter (α := ι) τ) (hp : pre (r, st, IterWithProgress.refl it))
    : match x r st it with | .ok s h a => post a.1 (r, a.2, IterWithProgress.mk it s h) | .error e => epost e := by
  have := Triple.iff.mp h
  simp only [Order.PartialOrder.rel, wp, WP.trans, pushResultStateT] at this
  have := this (r, st, IterWithProgress.mk it it (.refl it)) (by grind [IterWithProgress.refl])
  split at this <;> simp_all

@[spec] theorem Spec.ReaderTStateTParser.monadLift (x : Parser ε ι τ α)
  (h : Triple x pre post epost) (r : ρ) (st : σ) (it : Iter (α := ι) τ)
    : Triple (MonadLift.monadLift
        (monadLift x : (StateT σ (Parser ε ι τ)) α) : ReaderT ρ (StateT σ (Parser ε ι τ)) α)
      (fun (_r, _st, s) => s.it = it ∧ s.rest = it ∧ _r = r ∧ _st = st ∧ pre s)
      (fun a (_r, _st, s) => s.it = it ∧ post a s)
      epost :=
  Triple.intro (by
    simp [Order.PartialOrder.rel, wp, WP.trans, pushResultStateT,
          MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift, bind, pure]
    have h := Triple.iff.mp h
    simp [Order.PartialOrder.rel, wp, WP.trans, pushResult, Parser.run] at h
    grind)

theorem Progress.trans_self {ι τ : Type u} [Iterator ι Id τ] [Iterators.Finite ι Id]
  (s s' : Iter  (α := ι) τ) (h1 : Progress s s') (h2 : Progress s' s')
    :  h1.trans h2 = h1 := by
  simp [ParseIt.Progress.trans]
  grind [ParseIt.Advanced.irrefl s']

theorem Spec.ReaderTStateTParser.default_parser  [Iterators.Finite ι Id]
  (x :  ReaderT ρ (StateT σ (Parser ε ι τ)) α) r st (it : Iter (α := ι) τ)
    : Triple x
      (fun (_r, _st, s) => s.it = it ∧ s.rest = it ∧ r = _r ∧ st = _st)
      (fun a (_r, _st, s) => s.it = it ∧ x _r st s.it = .ok s.rest s.p (a, _st))
      (fun e => x r st it = .error e) :=
  Triple.intro (by
    rintro ⟨r', st', s⟩ ⟨h1, h2, rfl, rfl⟩
    rcases s with ⟨sit, srest, sp⟩
    simp only at h1 h2; subst h1; subst h2
    simp only [wp, WP.trans, pushResultStateT]
    split <;> simp_all [Progress.trans_self])

@[spec] theorem Spec.ReaderTStateTParser.read (r : ρ) (st : σ) (it : Iter (α := ι) τ)
    : Triple (MonadReaderOf.read : ReaderT ρ (StateT σ (Parser ε ι τ)) ρ)
      (fun (_r, _st, s) => s.it = it ∧ s.rest = it ∧ _r = r ∧ _st = st)
      (fun a (_r, _st, s) => a = r ∧ s.it = it ∧ s.rest = it ∧ _r = r  ∧ _st = st)
      (fun _ => False) :=
  Triple.intro (by
    simp [MonadReaderOf.read, ReaderT.read, wp, WP.trans, pushResultStateT, pure, StateT.pure]
    grind)

@[spec] theorem Spec.ReaderTStateTParser.get (r : ρ) (st : σ) (it : Iter (α := ι) τ)
    : Triple (MonadLift.monadLift
        (MonadLiftT.monadLift (MonadStateOf.get : StateT σ (Parser ε ι τ) σ) : StateT σ (Parser ε ι τ) σ)
          : ReaderT ρ (StateT σ (Parser ε ι τ)) σ)
      (fun (_r, _st, s) => s.it = it ∧ s.rest = it ∧ _r = r ∧ _st = st)
      (fun a (_r, _st, s) => a = st ∧ s.it = it ∧ s.rest = it ∧ _r = r ∧ _st = st)
      (fun _ => False) :=
  Triple.intro (by
    simp [MonadLift.monadLift, MonadStateOf.get, StateT.get, wp, WP.trans, pushResultStateT, pure]
    grind)

/-- Any `x` started at `it` (with parse start `it₀`) never moves backwards from `it`. -/
theorem Spec.ReaderTStateTParser.progress
  (x : ReaderT ρ (StateT σ (Parser ε ι τ)) α) (it₀ it : Iter (α := ι) τ)
    : Triple x
      (fun (_, _, s) => s.it = it₀ ∧ s.rest = it)
      (fun _ (_, _, s) => s.it = it₀ ∧ (s.rest = it ∨ Advanced s.rest it))
      (fun _ => True) :=
  Triple.intro (by
    rintro ⟨r, st, s⟩ h
    have h := Triple.iff.mp (Spec.progress (x r st) it₀ it) s h
    simp only [wp, WP.trans, Parser.run, pushResult, pushResultStateT] at h ⊢
    split at h <;> simp_all)

end Instances

abbrev SimpleCharParser := Parser (Error.Simple CharIterator) CharIterator Char

def fail (msg : String) : SimpleCharParser α :=
  throwUnexpectedWithMessage none msg

@[spec] theorem Spec.fail (msg : String) (it : Iter (α := CharIterator) Char)
    : Triple (Parser.fail msg : SimpleCharParser α)
      (fun s => s.rest = it) (fun _ _ => False)
      (fun e => e = Error.addMessage (Error.unexpected it none) it msg) := by
  vcgen [Parser.fail] with finish

def mkSimpleError (it : Std.Iter (α := CharIterator) Char) (msg : String)
    : ParseIt.Result (Error.Simple CharIterator) (it : Std.Iter (α := CharIterator) Char) α :=
  .error (Error.Simple.addMessage
    (Error.Simple.unexpected (HasPos.pos it) none) (HasPos.pos it) msg)

section Folding

variable {ε ι τ : Type u} {m : Type u → Type v} [Iterator ι Id τ] [Iterators.Finite ι Id]

/- ParseIt.efoldlP with StateT σ -/
def StateT.efoldlP (f : β → α → StateT σ (Parser ε ι τ) β) (init : β)
  (p : StateT σ (Parser ε ι τ) α) : StateT σ (Parser ε ι τ) (β × Option ε) := fun s it =>
  loop f p s it init it (.refl it)
where loop [Iterators.Finite ι Id] (f : β → α → StateT σ (Parser ε ι τ) β)
  (p : StateT σ (Parser ε ι τ) α) (s : σ) (it : Iter (α := ι) τ) (y : β) (cur : Iter (α := ι) τ)
  (hcur : Progress cur it) : Id (Result ε it ((β × Option ε) × σ)) := do
  match ← p s cur with
  | .error _ => return .ok cur hcur ((y, none), s)
  | .ok rest₁ h₁ x =>
    match ← f y x.1 x.2 rest₁ with
    | .error e => return .ok cur hcur ((y, some e), x.2)
    | .ok rest₂ h₂ y =>
      match h₂.trans h₁ with
      | .stay h => return .ok rest₂ (h ▸ hcur) ((y.1, none), y.2)
      | .moved h => StateT.efoldlP.loop f p y.2 it y.1 rest₂ ((Progress.moved h).trans hcur)
termination_by cur.finitelyManySteps
decreasing_by exact h

/-- StateT.efoldlP.loop always returns .ok -/
theorem efoldlP.loop_eq_ok (st) (it cur) (hcur : Progress cur it)
  (f : (Array α) → α → StateT σ (Parser ε ι τ) (Array α)) (y : Array α)
  (p : StateT σ (Parser ε ι τ) α)
    : ∃ rest h x, StateT.efoldlP.loop f p st it y cur hcur = .ok rest h x := by
  fun_induction StateT.efoldlP.loop f p st it y cur hcur
  simp [bind, pure]
  repeat split <;> try grind
  simp_all

/-- every element collected by the fold loop satisfies `P` if every successful `p` result does -/
theorem efoldlP.loop_all (P : α → Prop) (st) (it cur)
  (hcur : Progress cur it) (y : Array α)
  (p : StateT σ (Parser ε ι τ) α)
  (hp : ∀ st' s rest h x, Progress s it → p st' s = .ok rest h x → P x.1)
  (hy : ∀ a ∈ y, P a) {rest h' z}
  (heq : StateT.efoldlP.loop (fun y x => StateT.pure (y.push x)) p st it y cur hcur = .ok rest h' z)
    : ∀ a ∈ z.1.1, P a := by
  fun_induction StateT.efoldlP.loop (fun y x => StateT.pure (y.push x)) p st it y cur hcur
  rename_i s y cur hcur ih
  simp only [bind, pure, StateT.pure] at heq
  split at heq
  · cases heq; exact hy
  · rename_i hpx
    split at heq
    · cases heq
      simp only [Array.mem_push]
      rintro a (ha | rfl)
      · exact hy a ha
      · exact hp _ _ _ _ _ hcur hpx
    · rename_i x _ _ _
      refine ih _ (y.push x.1, x.2) _ ?_ heq
      simp only [Array.mem_push]
      rintro a (ha | rfl)
      · exact hy a ha
      · exact hp _ _ _ _ _ hcur hpx

/- ParseIt.foldlP with StateT σ -/
def StateT.foldlP (f : β → α → StateT σ (Parser ε ι τ) β) (init : β)
  (p : StateT σ (Parser ε ι τ) α) : StateT σ (Parser ε ι τ) β :=
  Prod.fst <$> efoldlP f init p

/- ParseIt.foldl with StateT σ -/
public def StateT.foldl (f : β → α → β) (init : β) (p : StateT σ (Parser ε ι τ) α)
    : StateT σ (Parser ε ι τ) β :=
  StateT.foldlP (fun y x => pure (f y x)) init p

end Folding

def StateT.takeMany (p : (ReaderT ρ $ StateT σ SimpleCharParser) α)
    : (ReaderT ρ $ StateT σ SimpleCharParser) $ Array α := fun r => do
  StateT.foldl (fun acc a => acc.push a) #[] (p r)

/-- StateT.takeMany always returns .ok -/
theorem takeMany_eq_ok  (p : (ReaderT ρ $ StateT σ SimpleCharParser) α) (r) (st) (it)
    : ∃ rest h x, StateT.takeMany p r st it = .ok rest h x := by
  simp [StateT.takeMany, StateT.foldl, StateT.foldlP, Functor.map, StateT.map, bind, pure, StateT.efoldlP]
  split
  · rename_i rest h _ _
    have := efoldlP.loop_eq_ok st it rest h (fun y x => StateT.pure (y.push x)) #[] (p r)
    grind
  · have := efoldlP.loop_eq_ok st it it (.refl it) (fun y x => StateT.pure (y.push x)) #[] (p r)
    simp_all

/-- StateT.takeMany never returns .error -/
theorem takeMany_ne_error (h : StateT.takeMany p r st it = .error e) : false := by
  grind [takeMany_eq_ok p r st it]

/-- every element collected by `takeMany p` satisfies `P` if every successful `p` result does -/
theorem takeMany_all (P : α → Prop) (p : (ReaderT ρ $ StateT σ SimpleCharParser) α) (r st it)
  (hp : ∀ st' s rest h x, Progress s it → p r st' s = .ok rest h x → P x.1) {rest h y}
  (heq : StateT.takeMany p r st it = .ok rest h y)
    : ∀ a ∈ y.1, P a := by
  simp [StateT.takeMany, StateT.foldl, StateT.foldlP, Functor.map, StateT.map, bind, pure, StateT.efoldlP] at heq
  split at heq
  · rename_i hl
    cases heq
    exact efoldlP.loop_all P st it it _ #[] (p r) hp (by simp) hl
  · cases heq

def ws : (ReaderT ρ $ StateT σ SimpleCharParser) PUnit := fun _ s =>
  dropMany Char.ASCII.whitespace >>= (fun _ => pure ((), s))

def peekChar?  : SimpleCharParser $ Option Char :=
  option? (lookAhead anyToken)

def peekChar : SimpleCharParser Char :=
  lookAhead anyToken

def withPos (p : SimpleCharParser α)
    : SimpleCharParser (String.Pos.Raw × String.Pos.Raw × α) := do
  let (a, s1, s2) ← withSpan p
  return (s1, s2, a)

@[spec] theorem Spec.withPos
  (x : SimpleCharParser α) (h : Triple x pre post epost) (it : Iter (α := CharIterator) Char)
    : Triple (withPos x : SimpleCharParser (String.Pos.Raw × String.Pos.Raw × α))
      (fun s => s.it = it ∧ s.rest = it ∧ pre s)
      (fun (a : (String.Pos.Raw × String.Pos.Raw × α)) s => s.it = it ∧
        post a.2.2 s ∧ a.1 = HasPos.pos it ∧ a.2.1 = HasPos.pos s.rest) epost :=
   Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro s ⟨hit, rfl, hpre⟩
    have := Triple.iff.mp h s hpre
    simp only [WP.wp, WP.trans, Parser.run] at this
    simp only [Parser.withPos, ParseIt.withSpan, bind, pure]
    revert this
    generalize x s.rest = r
    cases r <;> simp [hit])

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
  match ← (option? (lookAhead anyToken)) with
  | some c => if check c then pure $ some (← withPos p) else pure none
  | none => pure none

/-- exec `check` on current char and then exec `p` on success -/
def tryCharThenPWithPosM (check : Char -> Bool) (p : (ReaderT ρ $ StateT σ SimpleCharParser) α)
    : (ReaderT ρ $ StateT σ SimpleCharParser) $ Option (String.Pos.Raw × String.Pos.Raw × α) := fun f s => do
  match ← (option? (lookAhead anyToken)) with
  | some c => if check c then
                let x ← withPos (p f s)
                pure $ (some (x.1, x.2.1, x.2.2.1), x.2.2.2)
              else pure (none, s)
  | none => pure (none, s)

def tryCharWithPos (check : Char -> Bool)
    :  SimpleCharParser $ Option (String.Pos.Raw × String.Pos.Raw × Char) := do
  tryCharThenPWithPos check anyToken

/-- `Spec.tryCharWithPos` for the special case where the parse start is the current iterator. -/
theorem Spec.tryCharWithPos.from_it (check : Char -> Bool) (it : Iter (α := CharIterator) Char)
    : Triple (tryCharWithPos check : SimpleCharParser (Option (String.Pos.Raw × String.Pos.Raw × Char)))
      (fun s => s.it = it ∧ s.rest = it)
      (fun r s => s.it = it
          ∧ match r with | some _ => Advanced s.rest it | none => s.rest = it)
      (fun _ => False) := by
  vcgen [Parser.tryCharWithPos, Parser.tryCharThenPWithPos, Parser.peekChar?,
         Spec.option? (lookAhead _) it,
         Spec.withPos _ (Spec.default_parser _ it) it]
    with try finish
  case vc9 =>
    rename_i s hs
    obtain ⟨it', rest, p⟩ := s
    obtain ⟨h₁, ⟨-, heq⟩, -⟩ := hs
    dsimp only at h₁ heq ⊢
    subst h₁
    have := Triple.iff.mp (Spec.anyToken (ε := Error.Simple CharIterator) it')
      (IterWithProgress.refl it') ⟨rfl, rfl⟩
    simp only [wp, WP.trans, Parser.run, pushResult, IterWithProgress.refl, heq] at this
    exact this.2.2
  all_goals
    simp only [ParseIt.lookAhead, bind, pure] at *
    cases h : (anyToken : SimpleCharParser Char) it <;> simp_all

@[spec] theorem Spec.tryCharWithPos (check : Char -> Bool) (it₀ it : Iter (α := CharIterator) Char)
    : Triple (tryCharWithPos check : SimpleCharParser (Option (String.Pos.Raw × String.Pos.Raw × Char)))
      (fun s => s.it = it₀ ∧ s.rest = it)
      (fun r s => s.it = it₀
          ∧ match r with | some _ => Advanced s.rest it | none => s.rest = it)
      (fun _ => False) :=
  Spec.from_start
    (Q := fun (r : Option (String.Pos.Raw × String.Pos.Raw × Char)) rest =>
      match r with | some _ => Advanced rest it | none => rest = it)
    it₀ it (Spec.tryCharWithPos.from_it check it)

def manyChars (p : SimpleCharParser Char) : SimpleCharParser String := do
  takeMany p >>= (fun chars => return String.ofList chars.toList)

def many1Chars (p : SimpleCharParser Char) : SimpleCharParser String := do
  takeMany1 p >>= (fun chars => return String.ofList chars.toList)
