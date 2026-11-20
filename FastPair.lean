module
public import Expressions
public import Mathlib.Tactic

/-! # A closed expression for the affine transfer through a pair phase

The first and second hazards at the *start* of the phase are `x` and `y`.
The three geometric sums depend only on the length.
-/

@[expose] public section
namespace SimonFast
open SimonExpr

def a : ℚ := 99/98
def b : ℚ := 1/2
def geom (q : ℚ) (n : ℕ) : ℚ := (q^n-1)/(q-1)

def pair {K : Type*} [RatCast K] [Add K] [Sub K] [Mul K]
    (n : ℕ) (x y : K) (i : Fin 4) : K × K :=
  let X := lit 1 + lit 98*x - lit 98*x*lit (a^n)
  let Y := lit 1 - lit 2*y + lit 2*y*lit (b^n)
  let wx := lit 100*x*((lit 1-lit 2*y)*lit (geom a n)+lit 2*y*lit (geom (a*b) n))
  let wy := lit 100*y*((lit 1+lit 98*x)*lit (geom b n)-lit 98*x*lit (geom (a*b) n))
  (![lit 0, lit 0, wx, wy] i, ![Y, X, X*Y, X*Y] i)

theorem pair_zero (x y : ℝ) (i : Fin 4) : pair 0 x y i = (0,1) := by
  fin_cases i <;> norm_num [pair, geom, lit]

private theorem geom_succ {q : ℚ} (n : ℕ) (h : q ≠ 1) :
    geom q (n+1) = 1 + q * geom q n := by
  unfold geom
  rw [pow_succ]
  field_simp [sub_ne_zero.mpr h]
  ring

/-- One period of waiting, followed by the remaining pair transfer. -/
theorem pair_succ (n : ℕ) (x y x' y' : ℝ)
    (hx : x < 1) (hy : y < 1)
    (hx' : (1-x)*x' = (99/98)*x) (hy' : (1-y)*y' = (1/2)*y) (i : Fin 4) :
    pair (n+1) x y i =
      (![0,0,100*x,100*y] i + ![1-y,1-x,(1-x)*(1-y),(1-x)*(1-y)] i * (pair n x' y' i).1,
       ![1-y,1-x,(1-x)*(1-y),(1-x)*(1-y)] i * (pair n x' y' i).2) := by
  have xeq : x' = (99/98)*x/(1-x) := (eq_div_iff (by linarith)).2 (by nlinarith only [hx'])
  have yeq : y' = (1/2)*y/(1-y) := (eq_div_iff (by linarith)).2 (by nlinarith only [hy'])
  have ha : a ≠ 1 := by norm_num [a]
  have hb : b ≠ 1 := by norm_num [b]
  have hc : a*b ≠ 1 := by norm_num [a,b]
  rw [xeq,yeq]
  fin_cases i <;>
    simp [pair, lit, pow_succ, geom_succ n ha, geom_succ n hb, geom_succ n hc,
      Rat.cast_add, Rat.cast_mul] <;>
    norm_num [a,b, Rat.cast_pow] <;>
    try constructor
  all_goals
    field_simp [sub_ne_zero.mpr (ne_of_gt (show 1 > x from hx)),
                sub_ne_zero.mpr (ne_of_gt (show 1 > y from hy))]
    ring

end SimonFast
#print axioms SimonFast.pair_succ
