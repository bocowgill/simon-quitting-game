module

public import HazardBounds
public import RootDomain

/-! # Hazard bounds throughout the concrete dyadic root box -/

@[expose] public section
namespace PalomarSimon

private theorem shape_numerators :
    (∀ i, 0 < (box i).lo) ∧ (∀ i, 2*(box i).hi < Interval.scale) ∧
    4*(box 1).hi < Interval.scale ∧ (box 0).hi < (box 3).lo := by decide +kernel

theorem shape_of_mem {u : Fin 6 → ℝ} (h : ∀ i, Interval.Mem (u i) (box i)) :
    SimonHazardBounds.Shape u := by
  obtain ⟨hp,hu,hs,ho⟩ := shape_numerators
  have S := Interval.scale_real_pos
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    exact pos_of_mul_pos_left (lt_of_lt_of_le (by exact_mod_cast hp i) (h i).1) S.le
  · intro i
    have hn : 2 * ((box i).hi : ℝ) < (Interval.scale : ℝ) := by exact_mod_cast hu i
    have hh : u i * (Interval.scale : ℝ) < (1/2) * (Interval.scale : ℝ) := by
      linarith [(h i).2]
    exact lt_of_mul_lt_mul_right hh S.le
  · have hn : 4 * ((box 1).hi : ℝ) < (Interval.scale : ℝ) := by exact_mod_cast hs
    have hh : u 1 * (Interval.scale : ℝ) < (1/4) * (Interval.scale : ℝ) := by
      linarith [(h 1).2]
    exact lt_of_mul_lt_mul_right hh S.le
  · exact lt_of_mul_lt_mul_right ((h 0).2.trans_lt ((show ((box 0).hi : ℝ) < (box 3).lo by
      exact_mod_cast ho).trans_le (h 3).1)) S.le

theorem concrete_stage_support {u : Fin 6 → ℝ} (h : u ∈ Metric.closedBall center radius)
    (t : ℕ) (i : Fin 4) :
    0 ≤ SimonExpr.stage u t i ∧ SimonExpr.stage u t i < 1 ∧
    (0 < SimonExpr.stage u t i ↔ SimonHazardBounds.active t i) :=
  SimonHazardBounds.stage_support (shape_of_mem (mem_box h)) t i

#print axioms concrete_stage_support
end PalomarSimon
