module

public import CertifiedTable
public import ConcreteHazards
public import SimonHeadline

/-! # Reduction for the 1,856-phase calendar

Once the six scalar equations and the inactive incentive inequalities hold in
the specified box, the induced calendar is an exact terminal equilibrium and a
uniform equilibrium for all sufficiently long finite horizons.
-/

public section
namespace ConcreteReduction

open SimonExpr SimonAffine PalomarSimon

theorem equilibrium {u : Fin 6 → ℝ} (h : u ∈ Metric.closedBall center radius)
    (root : residual u = 0) (inactive : ∀ t : Fin 464, ∀ i : Fin 4,
      ¬ SimonHazardBounds.active t.val i →
      quit u t.val i ≤ value (cash u) (stay u) t.val i) :
    SimonHeadline.Equilibrium
      (SimonPeriodic.FC.cycle (by decide) (lift (stage u)))
      (SimonPeriodic.FC.cycle (by decide) (lift (value (cash u) (stay u)))) := by
  have cert := SimonTable.from_root u (shape_of_mem (mem_box h)) (fun i ↦ congrFun root i)
    inactive
  exact SimonHeadline.of_finite_data (by decide) _ _ cert.legal cert.proper cert.cont
    cert.quit_le cert.active

#print axioms equilibrium
end ConcreteReduction
