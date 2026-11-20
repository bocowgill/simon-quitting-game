module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic

/-! # Propagation along the active runs in Simon's four-block calendar

At every nonterminal active phase, the same player is active one phase later.
Each player is inactive in one entire block. A nonzero propagated discrepancy
would therefore reach a terminal phase, where the discrepancy is zero.
-/

@[expose] public section
namespace SimonActiveRuns

/-- A player's role advances once every 464 phases. -/
def role (t : Fin 1856) (i : Fin 4) : ℕ := (i.val + t.val / 464) % 4

/-- Role two quits mixing immediately after each triple phase. -/
def drop (t : Fin 1856) (i : Fin 4) : Prop :=
  role t i = 2 ∧ (t.val % 464 = 0 ∨ t.val % 464 = 451)

/-- Roles zero and one mix throughout their block. -/
def active (t : Fin 1856) (i : Fin 4) : Prop := role t i < 2 ∨ drop t i

theorem active_next_of_not_drop {t : Fin 1856} {i : Fin 4}
    (ha : active t i) (hd : ¬ drop t i) : active (t + 1) i := by
  have ht := t.isLt
  have hi := i.isLt
  unfold active drop role at *
  change (i.val + ((t.val + 1) % 1856) / 464) % 4 < 2 ∨
    (i.val + ((t.val + 1) % 1856) / 464) % 4 = 2 ∧
    (((t.val + 1) % 1856) % 464 = 0 ∨ ((t.val + 1) % 1856) % 464 = 451)
  omega

private theorem exists_inactive (i : Fin 4) : ∃ t : Fin 1856, ¬ active t i := by
  have hi := i.isLt
  refine ⟨⟨(3 - i.val) * 464, by omega⟩, ?_⟩
  unfold active drop role
  dsimp only
  omega

/-- Terminal discrepancies vanish, hence so does every active discrepancy that
propagates multiplicatively to the next phase. -/
theorem vanish (e k : Fin 1856 → Fin 4 → ℝ)
    (hdrop : ∀ t i, drop t i → e t i = 0)
    (hprop : ∀ t i, active t i → ¬ drop t i → e t i = k t i * e (t + 1) i) :
    ∀ t i, active t i → e t i = 0 := by
  intro t i ha
  by_contra hn
  let phase (n : ℕ) : Fin 1856 := ⟨(t.val + n) % 1856, Nat.mod_lt _ (by decide)⟩
  have first : phase 0 = t := Fin.ext (by simp [phase])
  have step (n : ℕ) : phase (n + 1) = phase n + 1 := by
    apply Fin.ext
    change (t.val + (n + 1)) % 1856 = ((t.val + n) % 1856 + 1) % 1856
    omega
  have hf : ∀ n : ℕ, active (phase n) i ∧ e (phase n) i ≠ 0 := by
    intro n
    induction n with
    | zero => simpa only [first] using And.intro ha hn
    | succ n ih =>
      have hd : ¬ drop (phase n) i := fun h => ih.2 (hdrop _ _ h)
      have hn' : e (phase n + 1) i ≠ 0 := by
        intro hz
        exact ih.2 (by rw [hprop _ _ ih.1 hd, hz, mul_zero])
      rw [step]
      exact ⟨active_next_of_not_drop ih.1 hd, hn'⟩
  obtain ⟨bad, hbad⟩ := exists_inactive i
  have reach : phase (1856 + bad.val - t.val) = bad := by
    apply Fin.ext
    change (t.val + (1856 + bad.val - t.val)) % 1856 = bad.val
    have ht := t.isLt
    have hb := bad.isLt
    omega
  exact hbad (reach ▸ (hf _).1)

end SimonActiveRuns

#print axioms SimonActiveRuns.vanish
