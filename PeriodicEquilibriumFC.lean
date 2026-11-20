module

public import ConcreteFC
public import ConcreteInactive
public import SimonRoot

/-! # The concrete Simon equilibrium under the frozen FC trajectory law -/

public section
namespace ConcreteFC

open SimonExpr SimonAffine PalomarSimon SimonPeriodic
open SimonPeriodic.FC

/-- The same table of target values works from every initial calendar phase.
The FC uniform witness covers all initial game states, including absorbing ones. -/
theorem periodic_equilibrium :
    ∃ w : Fin 1856 → Player → ℝ, ∀ phase : ℕ,
    let v := cycle (by decide : 0 < 1856) w
    ∃ σ : game.Profile,
      (∀ i, game.longRunPayoff .pathLiminf none σ i = v phase i ∧
        ∀ τ : game.Strategy i,
          game.longRunPayoff .pathLiminf none (game.revise σ i τ) i ≤ v phase i) ∧
      ∀ ε > 0, game.UniformWitness σ (target (shift v phase)) ε := by
  obtain ⟨u, hu, hr⟩ := simon_root
  exact ⟨lift (value (SimonExpr.cash u) (stay u)), equilibrium hu hr (Inactive.inactive hu)⟩

#print axioms periodic_equilibrium
end ConcreteFC
