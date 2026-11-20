module

public import Expressions
public import Mathlib.Tactic

/-! # Probability bounds for every date of Simon's calendar

The pair formulas preserve interior hazards even 450 dates into the long run.
Only coarse bounds on the six shooting parameters enter this proof.
-/

@[expose] public section
namespace SimonHazardBounds

structure Shape (u : Fin 6 → ℝ) : Prop where
  pos : ∀ i, 0 < u i
  upper : ∀ i, u i < 1/2
  small : u 1 < 1/4
  ordered : u 0 < u 3

open SimonExpr

theorem first_bounds (m j : ℕ) {x : ℝ} (hx : 0 < x) (hu : x < 1) :
    0 < first m j x ∧ first m j x < 1 := by
  let p := (((99/98 : ℚ)^(m-j) : ℚ) : ℝ)
  have hp : (1 : ℝ) ≤ p := by
    dsimp [p]
    exact_mod_cast one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 99/98)
  have ht : 0 ≤ 98*(p-1)*x := by positivity
  have hd : 0 < p + 98*(p-1)*x := by linarith
  simp only [first, lit, Rat.cast_ofNat, Rat.cast_one] at *
  change 0 < x / (p + 98*(p-1)*x) ∧ x / (p + 98*(p-1)*x) < 1
  exact ⟨div_pos hx hd, (div_lt_one hd).2 (by linarith)⟩

theorem second_bounds (j : ℕ) {y : ℝ} (hy : 0 < y) (hu : y < 1/2) :
    0 < secondHaz j y ∧ secondHaz j y < 1 := by
  let p := (((1/2 : ℚ)^j : ℚ) : ℝ)
  have hp : 0 < p := by dsimp [p]; positivity
  have hyP : 0 < y*p := mul_pos hy hp
  have ht : 0 < 1 - 2*y := by linarith
  have hd : 0 < 1 - 2*y + 2*y*p := by nlinarith only [ht, hyP]
  simp only [secondHaz, lit, Rat.cast_ofNat, Rat.cast_one] at *
  change 0 < y*p / (1 - 2*y + 2*y*p) ∧ y*p / (1 - 2*y + 2*y*p) < 1
  exact ⟨div_pos hyP hd, (div_lt_one hd).2 (by nlinarith only [ht, hyP])⟩

private theorem blend {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hu : b < 1) :
    0 < (a+b)/(1+a) ∧ (a+b)/(1+a) < 1 := by
  exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩

def active (t : ℕ) (i : Fin 4) : Prop :=
  i.val < 2 ∨ i.val = 2 ∧ (t = 0 ∨ t = 451)

private theorem cases_row (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1)
    (hz : 0 ≤ z ∧ z < 1) (i : Fin 4) :
    0 ≤ (![x,y,z,0] : Fin 4 → ℝ) i ∧ (![x,y,z,0] : Fin 4 → ℝ) i < 1 ∧
    (0 < (![x,y,z,0] : Fin 4 → ℝ) i ↔ i.val < 2 ∨ i.val = 2 ∧ 0 < z) := by
  fin_cases i <;> simp [hx.1,hx.1.le,hx.2,hy.1,hy.1.le,hy.2,hz.1,hz.2]

/-- Bounds and exact support, including the two transitions into triple phases. -/
theorem stage_support {u : Fin 6 → ℝ} (h : Shape u) (t : ℕ) (i : Fin 4) :
    0 ≤ stage u t i ∧ stage u t i < 1 ∧ (0 < stage u t i ↔ active t i) := by
  have U (a : Fin 6) : u a < 1 := lt_trans (h.upper a) (by norm_num)
  have sA := second_bounds 450 (h.pos 4) (h.upper 4)
  have sB := second_bounds 12 (h.pos 5) (h.upper 5)
  have tAy : 0 < (u 3-u 0)/(1-u 0) ∧ (u 3-u 0)/(1-u 0) < 1 := by
    exact ⟨div_pos (sub_pos.mpr h.ordered) (sub_pos.mpr (U 0)),
      (div_lt_one (sub_pos.mpr (U 0))).2 (sub_lt_sub_right (U 3) _)⟩
  have tAz := blend (mul_pos (by norm_num : (0:ℝ) < 49) (h.pos 0)) sB.1 sB.2
  have tBx : 0 < (u 2+u 1/49)/(1-u 1) ∧ (u 2+u 1/49)/(1-u 1) < 1 := by
    refine ⟨div_pos (add_pos (h.pos 2) (div_pos (h.pos 1) (by norm_num))) (sub_pos.mpr (U 1)),
      (div_lt_one (sub_pos.mpr (U 1))).2 ?_⟩
    linarith [h.small, h.upper 2]
  have tBy := blend (mul_pos (by norm_num : (0:ℝ) < 49) (h.pos 1)) sA.1 sA.2
  by_cases h0 : t = 0
  · simpa [stage, lit, active, h0, tAz.1] using
      cases_row _ _ _ ⟨h.pos 0,U 0⟩ tAy ⟨tAz.1.le,tAz.2⟩ i
  by_cases h1 : t < 451
  · have ht : t ≠ 451 := Nat.ne_of_lt h1
    simpa [stage, lit, active, h0, h1, ht] using
      cases_row _ _ _ (first_bounds 450 (t-1) (h.pos 2) (U 2))
        (second_bounds (t-1) (h.pos 4) (h.upper 4)) ⟨le_rfl,by norm_num⟩ i
  by_cases h2 : t = 451
  · simpa [stage, lit, active, h2, h.pos 1, add_comm] using
      cases_row _ _ _ tBx tBy ⟨(h.pos 1).le,U 1⟩ i
  · simpa [stage, lit, active, h0, h1, h2] using
      cases_row _ _ _ (first_bounds 12 (t-452) (h.pos 3) (U 3))
        (second_bounds (t-452) (h.pos 5) (h.upper 5)) ⟨le_rfl,by norm_num⟩ i

#print axioms stage_support
end SimonHazardBounds
