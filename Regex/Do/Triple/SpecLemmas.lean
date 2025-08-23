import Std.Tactic.Do
import Std.Tactic.Do.Syntax

namespace Std.Do

@[spec]
theorem except_ok_spec {α ε : Type} {x : α} {pre : Prop}
  {post : α → Prop} {error : ε → Prop}
  (h : ∀ r, r = x ∧ pre → post r) : ⦃⌜pre⌝⦄ Except.ok x ⦃post⟨fun a => ⌜post a⌝ , fun e => ⌜ error e⌝ ⟩⦄ := by
  mintro _
  simp [wp]
  split
  · rename_i a heq
    have : x = a := by simp [Id.run] at heq; assumption
    simp_all
  · rename_i heq
    simp [Id.run] at heq

theorem Except.by_wp {α} {x : α} {prog : Except ε α} (h : prog = Except.ok x)
  {P : α → Prop} {Q : ε → Prop}
    : (⊢ₛ wp⟦prog⟧ (fun r => ⌜P r⌝, fun e => ⌜Q e⌝, ())) → P x := by
    intro hspec
    simp only [wp, PredTrans.pushExcept_apply, PredTrans.pure_apply] at hspec
    split at hspec
    all_goals rename_i heq <;> rw [h, Id.run] at heq <;> simp_all

theorem StateT.by_wp {α σ} {x : α × σ} {s : σ} {prog : StateT σ Id α}
  (h : StateT.run prog s = x) {P : α → σ → Prop}
    : (⊢ₛ wp⟦prog⟧ (fun r s => ⌜P r s⌝, ()) s) → P x.1 x.2 := by
  intro hspec
  simp only [wp, PredTrans.pure, PredTrans.pushArg_apply, Id.run] at hspec
  split at hspec
  simp [StateT.run] at h
  simp at hspec
  grind

theorem StateT.Except.by_wp {α σ ε} {x : α × σ} {s : σ} {prog : StateT σ (Except ε) α}
  (h : prog s = Except.ok x) {P : α → Prop} {Q : ε → Prop}
    : (⊢ₛ wp⟦prog⟧ (fun r _ => ⌜P r⌝, fun e => ⌜Q e⌝, ()) s) → P x.1 := by
  intro hspec
  simp [wp, PredTrans.pure, PredTrans.pushArg_apply, PredTrans.pushExcept, Id.run] at hspec
  split at hspec <;> simp_all <;> grind
