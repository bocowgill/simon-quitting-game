module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Scalar identities at Simon's triple dates

The arguments of `stay` and `quit` are the hazards of the successor,
opposite player, and predecessor, in that order. The three post-value
identities are equation (7) of the periodic-equilibrium proof. The two
outgoing matches use its residuals (8). The last four identities verify the
two incoming transitions from the choice of parameters in equation (4).
-/

@[expose] public section
namespace SimonTriple

noncomputable def stay (s o p : ℝ) : ℝ := (1-s)*(1-o)*(1-p)
noncomputable def quit (s o p : ℝ) : ℝ := 100*(1-s)-1-98*stay s o p
noncomputable def odds (x : ℝ) : ℝ := x / (1-x)

theorem triplePostFirst (y z : ℝ) (hy : 1-y ≠ 0) (hz : 1-z ≠ 0) :
    quit y z 0 = 100*z + stay y z 0*(1-odds y-odds z-101*odds y*odds z) := by
  unfold quit stay odds
  field_simp [hy, hz]
  ring

theorem triplePostSecond (x z : ℝ) (hx : 1-x ≠ 0) (hz : 1-z ≠ 0) :
    quit z 0 x = stay z 0 x*(1+(99-odds z)*odds x-odds z) := by
  unfold quit stay odds
  field_simp [hx, hz]
  ring

theorem triplePostThird (x y : ℝ) (hx : 1-x ≠ 0) (hy : 1-y ≠ 0) :
    quit 0 x y = 100*x + stay 0 x y*(1+99*odds y-(1+odds y)*odds x) := by
  unfold quit stay odds
  field_simp [hx, hy]
  ring

theorem tripleFirst (y z yp : ℝ) (hy : 1-y ≠ 0) (hz : 1-z ≠ 0)
    (h0 : 2*yp-odds y-odds z-101*odds y*odds z = 0) :
    quit y z 0 = 100*z + stay y z 0*(1-2*yp) := by
  rw [triplePostFirst _ _ hy hz]
  congr 2
  linarith only [h0]

theorem tripleSecond (x z xp : ℝ) (hx : 1-x ≠ 0) (hz : 1-z ≠ 0)
    (h1 : (99-odds z)*odds x-odds z-98*xp = 0) :
    quit z 0 x = stay z 0 x*(1+98*xp) := by
  rw [triplePostSecond _ _ hx hz]
  congr 1
  linarith only [h1]

theorem tripleThird (x y : ℝ) : quit 0 x y = 1+98*(x+y-x*y) := by
  unfold quit stay
  ring

theorem beforeBFirst (z Y : ℝ) (h : 1+49*z ≠ 0) :
    quit ((Y+49*z)/(1+49*z)) z 0 = 1-2*Y := by
  unfold quit stay
  field_simp [h]
  ring

theorem beforeBSecond (z X : ℝ) (h : 1-z ≠ 0) :
    quit z 0 ((X+z/49)/(1-z)) = 1+98*X := by
  unfold quit stay
  field_simp [h]
  ring

theorem beforeRotatedAFirst (x Y : ℝ) (h : 1+49*x ≠ 0) :
    quit ((49*x+Y)/(1+49*x)) 0 x = 1-2*Y := by
  unfold quit stay
  field_simp [h]
  ring

theorem beforeRotatedASecond (x X : ℝ) (h : 1-x ≠ 0) :
    quit 0 x ((X-x)/(1-x)) = 1+98*X := by
  unfold quit stay
  field_simp [h]
  ring

end SimonTriple

#print axioms SimonTriple.tripleFirst
#print axioms SimonTriple.tripleSecond
#print axioms SimonTriple.tripleThird
#print axioms SimonTriple.triplePostThird
#print axioms SimonTriple.beforeBFirst
#print axioms SimonTriple.beforeBSecond
#print axioms SimonTriple.beforeRotatedAFirst
#print axioms SimonTriple.beforeRotatedASecond
