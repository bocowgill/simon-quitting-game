module
public import FastCalendar
public import FastIdentity

/-! # Equality of the two real shooting maps on the admissible domain -/

public section
namespace SimonFast

theorem residual_eq (u : Fin 6 → ℝ) (hu : SimonHazardBounds.Shape u) :
    SimonFast.residual u = SimonExpr.residual u :=
  residual_eq_of_transfers u (transfer_long u hu) (transfer_short u hu)

#print axioms residual_eq
end SimonFast
