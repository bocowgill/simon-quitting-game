module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

/-! # A root from bounds on divided differences

For each pair in a closed box, choose a matrix that represents the difference
of the residual values on this pair. It may depend on both points. A uniform
row-sum bound after preconditioning gives a contraction on the box.
-/

@[expose] public section
namespace PalomarSimon

private theorem dist_bound_of_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {x y u v : Fin n → ℝ} (h : u-v = A.mulVec (x-y))
    (hrow : ∀ i, ∑ j, |A i j| ≤ 1/2) :
    dist u v ≤ (1/2) * dist x y := by
  apply (dist_pi_le_iff (by positivity)).2
  intro i
  have hi := congrFun h i
  change u i - v i = ∑ j, A i j * (x j - y j) at hi
  rw [Real.dist_eq, hi]
  calc
    _ ≤ ∑ j, |A i j * (x j - y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A i j| * dist x y := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.dist_eq] using dist_le_pi_dist x y j)
        (abs_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hrow i) dist_nonneg

/-- A divided-difference certificate places a zero of the residual inside a box.
The preconditioner need not separately be certified invertible. -/
theorem exists_root_of_secant {n : ℕ} (c : Fin n → ℝ) (r : ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (F : (Fin n → ℝ) → Fin n → ℝ)
    (hr : 0 ≤ r) (hc : dist (c - C.mulVec (F c)) c ≤ r/2)
    (hsec : ∀ x ∈ Metric.closedBall c r, ∀ y ∈ Metric.closedBall c r,
      ∃ J : Matrix (Fin n) (Fin n) ℝ,
        F x - F y = J.mulVec (x-y) ∧ ∀ i, ∑ j, |(1-C*J) i j| ≤ 1/2) :
    ∃ w ∈ Metric.closedBall c r, F w = 0 := by
  let G := fun x => x - C.mulVec (F x)
  have hcc := Metric.mem_closedBall_self hr (x := c)
  have hlip : ∀ x ∈ Metric.closedBall c r, ∀ y ∈ Metric.closedBall c r,
      dist (G x) (G y) ≤ (1/2) * dist x y := by
    intro x hx y hy
    obtain ⟨J, hJ, hrow⟩ := hsec x hx y hy
    apply dist_bound_of_matrix (1-C*J) _ hrow
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← hJ, Matrix.mulVec_sub]
    dsimp [G]
    abel
  have maps : Set.MapsTo G (Metric.closedBall c r) (Metric.closedBall c r) := by
    intro x hx
    have ha := hlip x hx c hcc
    change dist x c ≤ r at hx
    change dist (G x) c ≤ r
    change dist (G c) c ≤ r/2 at hc
    linarith [dist_triangle (G x) (G c) c]
  have cont : ContractingWith (1/2 : NNReal) (maps.restrict G _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    exact_mod_cast hlip x x.2 y y.2
  obtain ⟨w, hw, hfix, _⟩ := cont.exists_fixedPoint' Metric.isClosed_closedBall.isComplete
    maps hcc (edist_ne_top _ _)
  obtain ⟨J, _, hrow⟩ := hsec c hcc c hcc
  have hi : Function.Injective (C*J).mulVec := by
    intro x y he
    have hz : x-y = (1-C*J).mulVec (x-y) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, he, sub_self, sub_zero]
    have hb := dist_bound_of_matrix (1-C*J) hz hrow
    apply dist_eq_zero.mp
    linarith [dist_nonneg (x := x) (y := y)]
  have hu := ((C*J).isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero
  rw [Matrix.det_mul] at hu
  have hC := Matrix.mulVec_injective_of_isUnit (C.isUnit_iff_isUnit_det.mpr
    (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hu)))
  refine ⟨w, hw, hC ?_⟩
  rw [Matrix.mulVec_zero]
  change w - C.mulVec (F w) = w at hfix
  exact sub_eq_self.mp hfix

#print axioms exists_root_of_secant
end PalomarSimon
