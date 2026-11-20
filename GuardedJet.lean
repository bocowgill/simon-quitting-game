module
public import Guarded
public import Secant
public import ExprRelation
public import Mathlib.Data.Matrix.Mul

/-! # Exact secants for the six residuals

Each operation acts on both real endpoints and the interval jet in the same
order. A successful residual evaluation yields a matrix of divided differences.
-/

@[expose] public section
namespace PalomarSimon

instance {n : ℕ} : Enclosure (Jet n) := ⟨Jet.v⟩
instance {n : ℕ} : RatCast (Jet n) := ⟨fun q ↦ Jet.const (q : Interval)⟩

def checkedVariables (B : Fin 6 → Interval) (i : Fin 6) : Checked (Jet 6) :=
  Checked.some (Jet.var (B i) i)

namespace JetEndpoints

abbrev Ends := Bool → ℝ
noncomputable scoped instance : RatCast Ends := ⟨fun q _ ↦ (q : ℝ)⟩

def ERel {n : ℕ} (x y : Fin n → ℝ) (t : Ends) (a : Jet n) :=
  a.At x y (t true) (t false)

theorem jetOps {n : ℕ} (x y : Fin n → ℝ) :
    SimonExpr.RelOps (Checked.Lift (ERel x y)) where
  lit q := Checked.lift_some (Jet.at_const (mem_ratCast q))
  add := Checked.lift_binary (R := ERel x y) (· + ·) (· + ·) (fun ha hb ↦ Jet.At.add ha hb)
  sub := Checked.lift_binary (R := ERel x y) (· - ·) (· - ·) (fun ha hb ↦ Jet.At.sub ha hb)
  mul := Checked.lift_binary (R := ERel x y) (· * ·) (· * ·) (fun ha hb ↦ Jet.At.mul ha hb)
  div := Checked.lift_div (R := ERel x y) (fun ha hb hs ↦ Jet.At.div ha hb hs)

theorem evalOps (i : Bool) : SimonExpr.RelOps (fun (t : Ends) (z : ℝ) ↦ t i = z) where
  lit _ := rfl
  add h k := congrArg₂ (· + ·) h k
  sub h k := congrArg₂ (· - ·) h k
  mul h k := congrArg₂ (· * ·) h k
  div h k := congrArg₂ (· / ·) h k

end JetEndpoints

open JetEndpoints in
open scoped JetEndpoints in
theorem residual_jet_at (B : Fin 6 → Interval) {x y : Fin 6 → ℝ}
    (hx : ∀ i, Interval.Mem (x i) (B i)) (hy : ∀ i, Interval.Mem (y i) (B i))
    (i : Fin 6) (v : Jet 6) (hv : (SimonExpr.residual (checkedVariables B) i).result = some v) :
    v.At x y (SimonExpr.residual x i) (SimonExpr.residual y i) := by
  let u : Fin 6 → Ends := fun j b ↦ if b then x j else y j
  have hu : ∀ j, Checked.Lift (ERel x y) (u j) (checkedVariables B j) :=
    fun j ↦ Checked.lift_some (Jet.at_var j (hx j) (hy j))
  have h := (jetOps x y).residual hu i v hv
  change v.At x y (SimonExpr.residual u i true) (SimonExpr.residual u i false) at h
  have h₁ := (evalOps true).residual (u := u) (v := x) (fun _ ↦ rfl) i
  have h₂ := (evalOps false).residual (u := u) (v := y) (fun _ ↦ rfl) i
  rw [h₁, h₂] at h
  exact h

theorem residual_secants (B : Fin 6 → Interval) {x y : Fin 6 → ℝ}
    (hx : ∀ i, Interval.Mem (x i) (B i)) (hy : ∀ i, Interval.Mem (y i) (B i))
    (jets : Fin 6 → Jet 6)
    (hj : ∀ i, (SimonExpr.residual (checkedVariables B) i).result = some (jets i)) :
    ∃ J : Matrix (Fin 6) (Fin 6) ℝ,
      SimonExpr.residual x-SimonExpr.residual y = J.mulVec (x-y) ∧
      ∀ i j, Interval.Mem (J i j) ((jets i).d j) := by
  classical
  have hs i := (residual_jet_at B hx hy i (jets i) (hj i)).slope
  choose g hg eg using hs
  exact ⟨g, funext eg, hg⟩

#print axioms residual_secants

end PalomarSimon
