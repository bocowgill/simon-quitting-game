module
public import Expressions
public import SimonPairMatching
import Mathlib.Tactic

/-! # Waiting recursion on the two active roles of a pair phase

The next phase in each identity may be the formal endpoint of a run.
-/

public section
namespace SimonPairStep
open SimonExpr SimonPairMatching

private theorem first_eq (m j : ℕ) (x : ℝ) :
    first m j x = firstHazard ((99/98 : ℝ)^(m-j)) x := by
  norm_num [first, firstHazard, lit, Rat.cast_pow]

private theorem second_eq (j : ℕ) (y : ℝ) :
    secondHaz j y = secondHazard ((1/2 : ℝ)^j) y := by
  norm_num [secondHaz, secondHazard, lit, Rat.cast_pow]

theorem first_end (m : ℕ) (x : ℝ) : first m m x = x := by
  simp [first_eq, firstHazard]

theorem rec0 (j : ℕ) (y : ℝ) (hy : 0 < y) (hhalf : y < 1/2) :
    1-2*secondHaz j y = (1-secondHaz j y)*(1-2*secondHaz (j+1) y) := by
  let p : ℝ := (1/2)^j
  have hp : 0 < p := pow_pos (by norm_num) _
  have hy2 : 0 < 1-2*y := by linarith
  have hd : 0 < 1-2*y+2*y*p := by positivity
  have hn : secondHazard p y < 1 := by
    unfold secondHazard
    rw [div_lt_one hd]
    nlinarith [mul_pos hy hp]
  have step : (1/2 : ℝ)^(j+1) = p/2 := by rw [pow_succ]; dsimp [p]; ring
  rw [second_eq, second_eq, step, ← matchFirst p y hd.ne']
  change 1-2*secondHazard p y = _
  field_simp [sub_ne_zero.mpr hn.ne']
  ring

theorem rec1 (m j : ℕ) (x : ℝ) (hj : j < m) (hx : 0 < x) :
    1+98*first m j x = (1-first m j x)*(1+98*first m (j+1) x) := by
  let p : ℝ := (99/98)^(m-j)
  let pn : ℝ := (99/98)^(m-(j+1))
  have hpnext : 1 ≤ pn := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 99/98)
  have hcount : m-j = m-(j+1)+1 := by omega
  have hp : p = pn*(99/98) := by dsimp [p, pn]; rw [hcount, pow_succ]
  have hcoef : 1 ≤ 98*(p-1) := by rw [hp]; linarith
  have hppos : 0 < p := pow_pos (by norm_num) _
  have hbound := mul_le_mul_of_nonneg_right hcoef hx.le
  have hd : 0 < p+98*(p-1)*x := by linarith
  have hdn : 0 < p+98*(p-1)*x-x := by linarith
  have hn : firstHazard p x < 1 := by
    unfold firstHazard
    rw [div_lt_one hd]
    linarith
  have hpn : pn = p*98/99 := by rw [hp]; ring
  rw [first_eq, first_eq]
  change 1+98*firstHazard p x = (1-firstHazard p x)*(1+98*firstHazard pn x)
  rw [hpn, ← matchSecond p x hd.ne' hdn.ne']
  field_simp [sub_ne_zero.mpr hn.ne']
  ring

end SimonPairStep
#print axioms SimonPairStep.rec0
#print axioms SimonPairStep.rec1
