module
public import BaseMatching
public import CycleBounds
public import Table

/-! # Reduction of the concrete finite table to the six equations and inactive tests

A root with the displayed strict parameter bounds supplies every active
indifference. The only additional numeric inputs are weak inequalities on
the inactive roles of the 464 base rows.
-/

public section
namespace SimonTable
open SimonExpr SimonHazardBounds SimonAffine

theorem from_root (u : Fin 6 → ℝ) (sh : Shape u) (hr : ∀ i, residual u i = 0)
    (hinactive : ∀ (t : Fin 464) (i : Fin 4),
      ¬(i.val < 2 ∨ i.val = 2 ∧ (t.val=0 ∨ t.val=451)) →
        quit u t.val i ≤ value (cash u) (stay u) t.val i) :
    FiniteData (lift (stage u)) (lift (value (cash u) (stay u))) := by
  have legal (t : ℕ) (_ : t < 464) (i : Fin 4) :=
    And.intro (stage_support sh t i).1 (stage_support sh t i).2.1
  have first (i : Fin 4) (hi : i.val < 2) : 0 < stage u 0 i :=
    (stage_support sh 0 i).2.2.mpr (Or.inl hi)
  have hd := SimonCycleBounds.denom_ne_zero u legal first
  exact finite_data u hd (fun t => legal t.val t.isLt)
    (SimonCycleBounds.lifted_proper u legal first) hinactive
    (SimonTripleBoundary.drop_eq u hr hd) (SimonBase.match_step u sh hr)

end SimonTable
#print axioms SimonTable.from_root
