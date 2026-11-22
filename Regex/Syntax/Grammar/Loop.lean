module

public import Init.Meta
public import ParseIt
public import Std.Internal.Parsec
public import Regex.Syntax.Grammar.Basic

open Std Lean Lean.Syntax ParseIt ParseIt.Char

public section

/-! Parser utils for ReaderT and StateT -/
namespace Parser

def remaining (it : Std.Iter (α := CharIterator) Char) :=
  it.internalState.slice.utf8ByteSize - it.internalState.pos.offset.byteIdx

@[simp, grind .] theorem remaining_of_advanced (it rest : Std.Iter (α := CharIterator) Char)
  (h : Advanced rest it)
    :  rest.internalState.slice = it.internalState.slice ∧ remaining rest < remaining it := by
  let f : IterM.TerminationMeasures.Finite CharIterator Id → Nat := fun x =>
    x.it.internalState.slice.utf8ByteSize - x.it.internalState.pos.offset.byteIdx
  let g : IterM.TerminationMeasures.Finite CharIterator Id → String.Slice := fun x =>
    x.it.internalState.slice
  suffices ∀ a b, IterM.TerminationMeasures.Finite.Rel a b → g a = g b ∧ f a < f b from this _ _ h
  intro a b hab
  have step : ∀ a b, InvImage IterM.IsPlausibleSuccessorOf
      IterM.TerminationMeasures.Finite.it a b → g a = g b ∧ f a < f b := by
    intro a b ⟨step, hs, hp⟩
    cases step with
    | yield it' c =>
      simp only [IterStep.successor, Option.some.injEq] at hs
      subst hs
      obtain ⟨h1, h2, _⟩ := hp
      obtain ⟨⟨⟨s, p⟩⟩⟩ := a
      simp only [CharIterator.mk.injEq] at h2
      obtain ⟨rfl, h2⟩ := h2
      cases h2
      simp only [f]
      have h3 := Char.utf8Size_pos (b.it.internalState.pos.get h1)
      have h4 := (b.it.internalState.pos.next h1).isValidForSlice.le_utf8ByteSize
      simp [String.Slice.Pos.ext_iff, String.Pos.Raw.ext_iff] at h1 h4 ⊢
      grind
    | skip _ => exact hp.elim
    | done => cases hs
  induction hab with grind

theorem advanced_of_lt (s : String.Slice) (p q : s.Pos) (h : p < q) :
    Advanced (ι := CharIterator) (τ := Char) ⟨⟨s, q⟩⟩ ⟨⟨s, p⟩⟩ := by
  have hne : p ≠ s.endPos := by
    intro he; subst he; exact absurd h (Std.not_lt.2 q.le_endPos)
  have h1 : Advanced (ι := CharIterator) (τ := Char) ⟨⟨s, p.next hne⟩⟩ ⟨⟨s, p⟩⟩ :=
    Advanced.of_yield (out := p.get hne) (by exact ⟨hne, rfl, rfl⟩)
  have hle : p.next hne ≤ q := String.Slice.Pos.next_le_of_lt h
  rcases Std.le_iff_lt_or_eq.1 hle with hlt | heq
  · exact (advanced_of_lt s (p.next hne) q hlt).trans h1
  · exact heq ▸ h1
termination_by s.utf8ByteSize - p.offset.byteIdx
decreasing_by
  have := (p.next hne).isValidForSlice.le_utf8ByteSize
  have := @String.Slice.Pos.lt_next s p hne
  simp [String.Slice.Pos.lt_iff, String.Pos.Raw.lt_iff] at *
  grind

@[simp, grind .] theorem advanced_of_remaining (it rest : Std.Iter (α := CharIterator) Char)
  (heq : rest.internalState.slice = it.internalState.slice)
  (hlt : remaining rest < remaining it) : Advanced rest it := by
  obtain ⟨⟨s, p⟩⟩ := it
  obtain ⟨⟨s', q⟩⟩ := rest
  simp only at heq
  subst heq
  apply advanced_of_lt
  have := q.isValidForSlice.le_utf8ByteSize
  simp [remaining, String.Slice.Pos.lt_iff, String.Pos.Raw.lt_iff] at hlt this ⊢
  grind

/-- loopTakeMany corresponds to the following parser:
```
  loop := (pre >>= fun x => StateT.takeMany loop >>= fun y => post x y) <|> alternative
```
  It return a value iff there is no termination failure.
-/
def loopTakeMany?
  (pre : (ReaderT ρ $ StateT σ SimpleCharParser) β)
  (post : β → (Array α) → (ReaderT ρ $ StateT σ SimpleCharParser) α)
  (alternative : (ReaderT ρ $ StateT σ SimpleCharParser) α)
  (hpre : ∀ r st it rest₁ h₁ x, pre r st it = .ok rest₁ h₁ x → Advanced rest₁ it)
    : (ReaderT ρ $ StateT σ SimpleCharParser) (Option α) := fun r st it =>
  let f r : Result (Error.Simple CharIterator) it ((Option α) × σ) :=
    match r with
    | .ok rest h a => .ok rest h (some a.1, a.2)
    | .error e => .error e
  match h : pre r st it with
  | .error _ => alternative r st it >>= f
  | .ok rest₁ h₁ x =>
    have : remaining rest₁ < remaining it := by grind only [advanced_of_remaining,
      remaining_of_advanced]
    match hm : StateT.takeMany (fun r st s =>
      if _ : s.internalState.slice == rest₁.internalState.slice ∧ remaining s ≤ remaining rest₁
      then loopTakeMany? pre post alternative hpre r st s
      else .ok s (.refl s) (none, x.2)) r x.2 rest₁
    with
    | .error _ => by have := takeMany_ne_error hm; simp_all
    | .ok rest₂ h₂ y => do
      if (Array.any y.1 (·.isNone))
      then .ok it (.refl it) (none, st)
      else
        match ← post x.1 (y.1 |> Array.filterMap id) r y.2 rest₂ with
        | .error _ => alternative r st it >>= f
        | .ok rest₃ h₃ z => .ok rest₃ (h₃.trans (h₂.trans h₁)) (some z.1, z.2)
termination_by _ _ it => remaining it

/-- A successful ``loopManyM?`` always returns ``some``. -/
theorem loopTakeMany?_eq_some
  (pre : (ReaderT ρ $ StateT σ SimpleCharParser) β)
  (post : β → (Array α) → (ReaderT ρ $ StateT σ SimpleCharParser) α)
  (alternative : (ReaderT ρ $ StateT σ SimpleCharParser) α)
  (hpre : ∀ r st it rest₁ h₁ x, pre r st it = .ok rest₁ h₁ x → Advanced rest₁ it)
  {r} {st st'} {it rest} {h : Progress rest it} {a : Option α}
  (heq : loopTakeMany? pre post alternative hpre r st it = .ok rest h (a, st'))
    : a.isSome := by
  induction hn : remaining it using Nat.strongRecOn generalizing r st st' it rest a with
  | _ n ih =>
  rw [loopTakeMany?] at heq
  split at heq
  · simp only [bind] at heq
    split at heq
    · cases heq; rfl
    · cases heq
  · rename_i rest₁ h₁ x hx
    have hlt : remaining rest₁ < remaining it := (remaining_of_advanced _ _ (hpre _ _ _ _ _ _ hx)).2
    split at heq
    · rename_i hm
      have := takeMany_ne_error hm
      simp at this
    · rename_i rest₂ h₂ y hm
      have hall := takeMany_all (fun o => o.isSome = true) _ r x.2 rest₁ (by
        intro st₂ s rest' h' ⟨a', st₃⟩ hs hcall
        split at hcall
        · rename_i hc
          exact ih (remaining s) (by omega) hcall rfl
        · rename_i hc
          exfalso
          apply hc
          cases hs with
          | stay h => subst h; simp
          | moved h =>
            have := remaining_of_advanced _ _ h
            simp [this.1]
            omega) hm
      split at heq
      · rename_i hany
        exfalso
        simp only [Array.any_eq_true] at hany
        obtain ⟨i, hi, hn⟩ := hany
        have := hall _ (Array.getElem_mem hi)
        simp_all
      · simp only [bind] at heq
        split at heq
        · split at heq
          · cases heq; rfl
          · cases heq
        · cases heq; rfl

/-- loopTakeMany corresponds to the following mutual recursive parser:
```
  loop := (pre >>= fun x => StateT.takeMany loop >>= fun y => post x y) <|> alternative
```
  with the property ```ParseIt.Advanced``` for parser ```pre``` which excludes termination failures
-/
def loopTakeMany
  (pre : (ReaderT ρ $ StateT σ SimpleCharParser) β)
  (post : β → (Array α) → (ReaderT ρ $ StateT σ SimpleCharParser) α)
  (alternative : (ReaderT ρ $ StateT σ SimpleCharParser) α)
  (hpre : ∀ r st it rest₁ h₁ x, pre r st it = .ok rest₁ h₁ x → Advanced rest₁ it)
    : (ReaderT ρ $ StateT σ SimpleCharParser) α := fun r st it =>
  match hm : loopTakeMany? pre post alternative hpre r st it with
  | .ok rest h (some a, st) => .ok rest h (a, st)
  | .ok _ _ (none, _) => by have := loopTakeMany?_eq_some pre post alternative hpre hm; simp_all
  | .error e => .error e
