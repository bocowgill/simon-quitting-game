module
public import RootEnvelopeData
public import RootBounds
public import RootDomain

/-! # Concrete preconditioning and displacement checks for Simon's box

The remaining hypotheses are exactly the enclosures of the six residuals at the
center and their six-coordinate divided differences on the entire box.
-/

@[expose] public section
namespace PalomarSimon

def Encloses (outer inner : Interval) : Prop :=
  outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi

instance (outer inner : Interval) : Decidable (Encloses outer inner) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Encloses.mem {outer inner : Interval} {x : ℝ}
    (h : Encloses outer inner) (hx : Interval.Mem x inner) : Interval.Mem x outer := by
  exact ⟨le_trans (by exact_mod_cast h.1) hx.1, le_trans hx.2 (by exact_mod_cast h.2)⟩

theorem simon_row_check : ∀ i, 2 * rowDeviation preconditionerBox secantEnvelope i ≤
    Interval.scale := by decide +kernel

theorem simon_center_check : ∀ i, 2 * centerDeviation preconditionerBox residualEnvelope i ≤
    radiusScaled := by decide +kernel

theorem exists_root_of_simon_envelopes (F : (Fin 6 → ℝ) → Fin 6 → ℝ)
    (hcenter : ∀ i, Interval.Mem (F center i) (residualEnvelope i))
    (hsec : ∀ x ∈ Metric.closedBall center radius, ∀ y ∈ Metric.closedBall center radius,
      ∃ J : Matrix (Fin 6) (Fin 6) ℝ, F x-F y = J.mulVec (x-y) ∧
        ∀ i j, Interval.Mem (J i j) (secantEnvelope i j)) :
    ∃ w ∈ Metric.closedBall center radius, F w = 0 :=
  exists_root_of_intervals center radiusScaled preconditioner preconditionerBox
    secantEnvelope residualEnvelope F radiusScaled_nonneg preconditioner_mem hcenter
    simon_center_check simon_row_check hsec

#print axioms simon_center_check
#print axioms simon_row_check
#print axioms exists_root_of_simon_envelopes
end PalomarSimon
