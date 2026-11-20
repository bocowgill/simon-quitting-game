module

public import CertifiedTable
public import ConcreteHazards
public import SimonPeriodic

/-! # The finite Simon certificate in the frozen stochastic-game trajectory model

The hypothesis on inactive roles is checked on a single 464-phase block.
Every live phase and every absorbing initial state are covered by the
uniform witness. Its threshold is simultaneous over all unilateral
behavioral deviations and all sufficiently large horizons.
-/

public section
namespace ConcreteFC
open SimonExpr SimonAffine PalomarSimon
open SimonPeriodic.FC

theorem equilibrium {u : Fin 6 → ℝ} (h : u ∈ Metric.closedBall center radius)
    (root : residual u = 0) (inactive : ∀ t : Fin 464, ∀ i : Fin 4,
      ¬ SimonHazardBounds.active t.val i →
      quit u t.val i ≤ value (cash u) (stay u) t.val i) (phase : ℕ) :
    let v := cycle (by decide : 0 < 1856) (lift (value (cash u) (stay u)))
    ∃ σ : game.Profile,
      (∀ i, game.longRunPayoff .pathLiminf none σ i = v phase i ∧
        ∀ τ : game.Strategy i, game.longRunPayoff .pathLiminf none (game.revise σ i τ) i ≤ v phase i) ∧
      ∀ ε > 0, game.UniformWitness σ (target (SimonPeriodic.shift v phase)) ε := by
  have cert := SimonTable.from_root u (shape_of_mem (mem_box h)) (fun i ↦ congrFun root i) inactive
  exact finite_certificate (by decide : 0 < 1856) _ _ cert.legal cert.proper cert.cont
    cert.quit_le cert.active phase

#print axioms equilibrium
end ConcreteFC
