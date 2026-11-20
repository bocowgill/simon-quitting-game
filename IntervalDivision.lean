module

public import Interval
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Ring

/-! # Reciprocal of a fixed-point interval

The scale is shared by the endpoints.  For a nonzero endpoint numerator
`d`, the target reciprocal numerator is `scale²/d`. Both signs of
`d` are supported by taking integer floor division with a positive divisor.
-/

@[expose] public section
namespace PalomarSimon.Interval

/-- Integer floor of a quotient (for either sign of the nonzero divisor). -/
def floorDiv (n d : ℤ) : ℤ := if d < 0 then (-n) / (-d) else n / d

/-- Integer ceiling of a quotient (for either sign of the nonzero divisor). -/
def ceilDiv (n d : ℤ) : ℤ := -(floorDiv (-n) d)

theorem floorDiv_le {n d : ℤ} (hd : d ≠ 0) :
    (floorDiv n d : ℝ) ≤ (n : ℝ) / d := by
  rcases lt_or_gt_of_ne hd with h | h
  · simpa [floorDiv, h] using (roundDown_le (n := -n) (d := -d) (neg_pos.mpr h))
  · simpa [floorDiv, not_lt_of_ge h.le] using (roundDown_le (n := n) h)

theorem le_ceilDiv {n d : ℤ} (hd : d ≠ 0) :
    (n : ℝ) / d ≤ (ceilDiv n d : ℝ) := by
  simpa only [ceilDiv, Int.cast_neg, neg_div, neg_neg] using
    neg_le_neg (floorDiv_le (n := -n) hd)

def inverse (a : Interval) : Interval :=
  ⟨floorDiv (scale * scale) a.hi, ceilDiv (scale * scale) a.lo⟩

instance : Inv Interval := ⟨inverse⟩
instance : Div Interval := ⟨fun a b ↦ a * b⁻¹⟩

theorem mem_inv {x : ℝ} {a : Interval} (hx : Mem x a)
    (hs : a.hi < 0 ∨ 0 < a.lo) : Mem x⁻¹ a⁻¹ := by
  have hlo : (a.lo : ℝ) ≤ x * (scale : ℝ) := hx.1
  have hhi : x * (scale : ℝ) ≤ (a.hi : ℝ) := hx.2
  have he : a.hi ≠ 0 ∧ a.lo ≠ 0 := by
    rcases hs with h | h
    · have hr : (a.hi : ℝ) < 0 := by exact_mod_cast h
      exact ⟨h.ne, by exact_mod_cast ((hlo.trans hhi).trans_lt hr).ne⟩
    · have hr : (0 : ℝ) < a.lo := by exact_mod_cast h
      exact ⟨by exact_mod_cast (hr.trans_le (hlo.trans hhi)).ne', h.ne'⟩
  have hanti : (a.hi : ℝ)⁻¹ ≤ (x * (scale : ℝ))⁻¹ ∧
      (x * (scale : ℝ))⁻¹ ≤ (a.lo : ℝ)⁻¹ := by
    rcases hs with h | h
    · have hr : (a.hi : ℝ) < 0 := by exact_mod_cast h
      have hm := hhi.trans_lt hr
      exact ⟨(inv_le_inv_of_neg hr hm).mpr hhi, (inv_le_inv_of_neg hm (hlo.trans_lt hm)).mpr hlo⟩
    · have hr : (0 : ℝ) < a.lo := by exact_mod_cast h
      exact ⟨inv_anti₀ (hr.trans_le hlo) hhi, inv_anti₀ hr hlo⟩
  have hpos := scale_real_pos.le
  have hscale : (scale : ℝ) * scale * (x * (scale : ℝ))⁻¹ = x⁻¹ * scale := by
    rw [mul_inv_rev]
    calc
      _ = x⁻¹ * (scale : ℝ) * ((scale : ℝ) * (scale : ℝ)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ scale_real_pos.ne', mul_one]
  constructor
  · calc
      (floorDiv (scale*scale) a.hi : ℝ) ≤ (scale : ℝ)*scale*(a.hi : ℝ)⁻¹ := by
        simpa only [Int.cast_mul, div_eq_mul_inv] using
          (floorDiv_le (n := scale*scale) he.1)
      _ ≤ (scale : ℝ)*scale*(x*(scale : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hanti.1 (mul_nonneg hpos hpos)
      _ = _ := hscale
  · calc
      x⁻¹ * (scale : ℝ) = (scale : ℝ)*scale*(x*(scale : ℝ))⁻¹ := hscale.symm
      _ ≤ (scale : ℝ)*scale*(a.lo : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hanti.2 (mul_nonneg hpos hpos)
      _ ≤ (ceilDiv (scale*scale) a.lo : ℝ) := by
        simpa only [Int.cast_mul, div_eq_mul_inv] using
          (le_ceilDiv (n := scale*scale) he.2)

theorem mem_div {x y : ℝ} {a b : Interval} (hx : Mem x a) (hy : Mem y b)
    (hs : b.hi < 0 ∨ 0 < b.lo) : Mem (x / y) (a / b) := by
  change Mem (x / y) (a * b⁻¹)
  simpa only [div_eq_mul_inv] using mem_mul hx (mem_inv hy hs)

#print axioms mem_inv
#print axioms mem_div

end PalomarSimon.Interval
