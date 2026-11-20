module
public import FastExpr

/-! # Equality of the compact and date-by-date residuals -/

@[expose] public section
namespace SimonFast
open SimonExpr

/-- Arbitrary real inputs whose two pair runs have the closed affine transfer. -/
theorem residual_eq_of_transfers (u : Fin 6 → ℝ)
    (hl : ∀ i, transfer (cash u) (stay u) 1 450 i =
      pair 450 (first 450 0 (u 2)) (secondHaz 0 (u 4)) i)
    (hs : ∀ i, transfer (cash u) (stay u) 452 12 i =
      pair 12 (first 12 0 (u 3)) (secondHaz 0 (u 5)) i) :
    SimonFast.residual u = SimonExpr.residual u := by
  have hL (i : Fin 4) : half u false i = transfer (cash u) (stay u) 0 451 i := by
    change (_,_) = (_ + _ * (transfer (cash u) (stay u) 1 450 i).1,
      _ * (transfer (cash u) (stay u) 1 450 i).2)
    rw [hl]
    rfl
  have hS (i : Fin 4) : half u true i = transfer (cash u) (stay u) 451 13 i := by
    change (_,_) = (_ + _ * (transfer (cash u) (stay u) 452 12 i).1,
      _ * (transfer (cash u) (stay u) 452 12 i).2)
    rw [hs]
    rfl
  have hF (i : Fin 4) : full u i = block (cash u) (stay u) i := by
    simp only [full,SimonExpr.block,hL,hS]
  have hD : denominator u = denom (cash u) (stay u) := by
    simp only [denominator,SimonExpr.denom,hF]
  have hA (i : Fin 4) : start u i = initial (cash u) (stay u) i := by
    simp only [start,SimonExpr.initial,hF,hD]
  have hB (i : Fin 4) : middle u i = second (cash u) (stay u) i := by
    simp only [middle,SimonExpr.second,hA,hS]
  simp only [SimonFast.residual,SimonExpr.residual,hA,hB]

#print axioms residual_eq_of_transfers

end SimonFast
