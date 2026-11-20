module
public import RootConstants
public import Interval
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Tactic

/-! # The six-dimensional dyadic box and preconditioner -/

@[expose] public section
namespace PalomarSimon
open PalomarSimon.Interval

def centerScaled (i : Fin 6) : ℤ := centerNumerator i * (scale / centerDenominator)
def radiusScaled : ℤ := scale / radiusDenominator
def preconditionerScaled (i j : Fin 6) : ℤ :=
  preconditionerNumerator i j * (scale / preconditionerDenominator)

noncomputable def center (i : Fin 6) : ℝ := (centerScaled i : ℝ) / scale
noncomputable def radius : ℝ := (radiusScaled : ℝ) / scale
noncomputable def preconditioner (i j : Fin 6) : ℝ := (preconditionerScaled i j : ℝ) / scale

def box (i : Fin 6) : Interval := ⟨centerScaled i - radiusScaled, centerScaled i + radiusScaled⟩
def pointBox (i : Fin 6) : Interval := ⟨centerScaled i, centerScaled i⟩
def preconditionerBox (i j : Fin 6) : Interval :=
  ⟨preconditionerScaled i j, preconditionerScaled i j⟩

theorem radiusScaled_nonneg : 0 ≤ radiusScaled := by decide +kernel

theorem center_mem (i : Fin 6) : Mem (center i) (pointBox i) := by
  simp [center, pointBox, Mem, div_mul_cancel₀ _ scale_real_pos.ne']

theorem preconditioner_mem (i j : Fin 6) : Mem (preconditioner i j) (preconditionerBox i j) := by
  simp [preconditioner, preconditionerBox, Mem, div_mul_cancel₀ _ scale_real_pos.ne']

theorem mem_box {x : Fin 6 → ℝ} (hx : x ∈ Metric.closedBall center radius) (i : Fin 6) :
    Mem (x i) (box i) := by
  have hd := (dist_le_pi_dist x center i).trans (Metric.mem_closedBall.mp hx)
  rw [Real.dist_eq, abs_le] at hd
  have h₁ := mul_le_mul_of_nonneg_right hd.1 scale_real_pos.le
  have h₂ := mul_le_mul_of_nonneg_right hd.2 scale_real_pos.le
  simp only [radius, center, neg_mul, sub_mul, div_mul_cancel₀ _ scale_real_pos.ne'] at h₁ h₂
  simp only [Mem, box, Int.cast_sub, Int.cast_add]
  constructor <;> linarith

end PalomarSimon
