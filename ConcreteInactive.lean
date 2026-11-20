module
public import InactiveCheck
public import ConcreteHazards
public import CycleBounds

/-! # Every inactive role prefers to continue on the entire shooting box -/

@[expose] public section
namespace PalomarSimon.Inactive

open SimonExpr

theorem inactive {u : Fin 6 → ℝ} (hu : u ∈ Metric.closedBall center radius) :
    ∀ t : Fin 464, ∀ i : Fin 4, ¬ SimonHazardBounds.active t.val i →
      quit u t.val i ≤ value (cash u) (stay u) t.val i := by
  have h (t : ℕ) (j : Fin 4) : 0 ≤ stage u t j ∧ stage u t j < 1 :=
    ⟨(concrete_stage_support hu t j).1,(concrete_stage_support hu t j).2.1⟩
  have hfirst (t : ℕ) (j : Fin 4) (hj : j.val < 2) : 0 < stage u t j :=
    (concrete_stage_support hu t j).2.2.mpr (Or.inl hj)
  have hd := SimonCycleBounds.denom_ne_zero u (fun t _ ↦ h t) (hfirst 0)
  have hs (t : ℕ) (i : Fin 4) := SimonCycleBounds.stay_bounds u t (h t) (hfirst t) i
  intro t i
  exact inactive_of_box hu hd (fun k _ ↦ hs k) t.val t.isLt i

#print axioms inactive
end PalomarSimon.Inactive

