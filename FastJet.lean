module

public import GuardedJet
public import FastRelation

/-! # Divided differences for the closed-form six shooting equations -/

@[expose] public section
namespace PalomarSimon

open JetEndpoints in
open scoped JetEndpoints in
theorem fast_residual_jet_at (B : Fin 6 → Interval) {x y : Fin 6 → ℝ}
    (hx : ∀ i, Interval.Mem (x i) (B i)) (hy : ∀ i, Interval.Mem (y i) (B i))
    (i : Fin 6) (v : Jet 6) (hv : (SimonFast.residual (checkedVariables B) i).result = some v) :
    v.At x y (SimonFast.residual x i) (SimonFast.residual y i) := by
  let u : Fin 6 → Ends := fun j b ↦ if b then x j else y j
  have hu : ∀ j, Checked.Lift (ERel x y) (u j) (checkedVariables B j) :=
    fun j ↦ Checked.lift_some (Jet.at_var j (hx j) (hy j))
  have h := (jetOps x y).fast_residual hu i v hv
  change v.At x y (SimonFast.residual u i true) (SimonFast.residual u i false) at h
  have h₁ := (evalOps true).fast_residual (u := u) (v := x) (fun _ ↦ rfl) i
  have h₂ := (evalOps false).fast_residual (u := u) (v := y) (fun _ ↦ rfl) i
  rw [h₁, h₂] at h
  exact h

theorem fast_residual_secants (B : Fin 6 → Interval) {x y : Fin 6 → ℝ}
    (hx : ∀ i, Interval.Mem (x i) (B i)) (hy : ∀ i, Interval.Mem (y i) (B i))
    (jets : Fin 6 → Jet 6)
    (hj : ∀ i, (SimonFast.residual (checkedVariables B) i).result = some (jets i)) :
    ∃ J : Matrix (Fin 6) (Fin 6) ℝ,
      SimonFast.residual x-SimonFast.residual y = J.mulVec (x-y) ∧
      ∀ i j, Interval.Mem (J i j) ((jets i).d j) := by
  classical
  have hs i := (fast_residual_jet_at B hx hy i (jets i) (hj i)).slope
  choose g hg eg using hs
  exact ⟨g, funext eg, hg⟩

#print axioms fast_residual_secants

end PalomarSimon
