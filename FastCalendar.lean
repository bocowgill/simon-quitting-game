module
public import FastPair
public import HazardBounds
public import PairInterior
import Mathlib.Tactic

/-! # Closed transfers for both pair runs in Simon's calendar

The adjacent-pair transfer agrees with every individual waiting step in the
450-stage and 12-stage runs. The first date of each run follows its triple.
-/

public section
namespace SimonFast
open SimonExpr SimonHazardBounds SimonPairStep

private theorem pair_coefficients {u : Fin 6 → ℝ} {t : ℕ} {x y : ℝ}
    (hs : stage u t = ![x,y,0,0]) (i : Fin 4) :
    cash u t i = ![0,0,100*x,100*y] i ∧
    stay u t i = ![1-y,1-x,(1-x)*(1-y),(1-x)*(1-y)] i := by
  simp only [cash, stay, hs, lit, Rat.cast_ofNat, Rat.cast_one]
  fin_cases i
  · change 100*(0:ℝ) = 0 ∧ (1-y)*(1-0)*(1-0) = 1-y
    constructor <;> ring
  · change 100*(0:ℝ) = 0 ∧ (1-0)*(1-0)*(1-x) = 1-x
    constructor <;> ring
  · change 100*x = 100*x ∧ (1-0)*(1-x)*(1-y) = (1-x)*(1-y)
    constructor <;> ring
  · change 100*y = 100*y ∧ (1-x)*(1-y)*(1-0) = (1-x)*(1-y)
    constructor <;> ring

private theorem slice (u : Fin 6 → ℝ) (start m : ℕ) (x y : ℝ)
    (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1/2)
    (hs : ∀ j < m, stage u (start+j) = ![first m j x,secondHaz j y,0,0])
    (j n : ℕ) (hn : j+n ≤ m) (i : Fin 4) :
    transfer (cash u) (stay u) (start+j) n i =
      pair n (first m j x) (secondHaz j y) i := by
  induction n generalizing j with
  | zero => simp [transfer, pair_zero, lit]
  | succ n ih =>
    have hj : j < m := by omega
    have hn' : j+1+n ≤ m := by omega
    have hx' := rec1 m j x hj hx.1
    have hy' := rec0 j y hy.1 hy.2
    have hrec := pair_succ n (first m j x) (secondHaz j y)
      (first m (j+1) x) (secondHaz (j+1) y)
      (first_bounds m j hx.1 hx.2).2 (second_bounds j hy.1 hy.2).2
      (by nlinarith only [hx']) (by nlinarith only [hy']) i
    have hcoeff := pair_coefficients (hs j hj) i
    rw [transfer, hrec, hcoeff.1, hcoeff.2]
    change _ = _
    rw [show start+j+1 = start+(j+1) by omega, ih _ hn']

/-- The first pair run starts at date one and has length 450. -/
theorem transfer_long (u : Fin 6 → ℝ) (hu : Shape u) (i : Fin 4) :
    transfer (cash u) (stay u) 1 450 i =
      pair 450 (first 450 0 (u 2)) (secondHaz 0 (u 4)) i := by
  apply slice u 1 450 (u 2) (u 4) ⟨hu.pos 2, lt_trans (hu.upper 2) (by norm_num)⟩
    ⟨hu.pos 4, hu.upper 4⟩ _ 0 450 (by decide) i
  intro j hj
  simpa only [show 1+j-1 = j by omega] using SimonPairInterior.stageA u (1+j) (by omega) (by omega)

/-- The second pair run starts at date 452 and has length 12. -/
theorem transfer_short (u : Fin 6 → ℝ) (hu : Shape u) (i : Fin 4) :
    transfer (cash u) (stay u) 452 12 i =
      pair 12 (first 12 0 (u 3)) (secondHaz 0 (u 5)) i := by
  apply slice u 452 12 (u 3) (u 5) ⟨hu.pos 3, lt_trans (hu.upper 3) (by norm_num)⟩
    ⟨hu.pos 5, hu.upper 5⟩ _ 0 12 (by decide) i
  intro j _
  simpa only [show 452+j-452 = j by omega] using SimonPairInterior.stageB u (452+j) (by omega)

end SimonFast

#print axioms SimonFast.transfer_long
#print axioms SimonFast.transfer_short
