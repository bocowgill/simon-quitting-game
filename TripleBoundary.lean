module

public import Affine
public import Triple
import Mathlib.Tactic

/-! # From the shooting residuals to the Bellman equalities at both triples -/

public section
namespace SimonTripleBoundary
open SimonExpr

private noncomputable def reservation (u : Fin 6 → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then initial (cash u) (stay u) 2 else second (cash u) (stay u) 2

private theorem local_residuals (u : Fin 6 → ℝ) (hr : ∀ i, residual u i = 0)
    (t : ℕ) (ht : t = 0 ∨ t = 451) (j : Fin 3) :
    residualTriple u t (reservation u t) j = 0 := by
  rcases ht with rfl | rfl
  · fin_cases j
    · exact hr 0
    · exact hr 1
    · exact hr 2
  · fin_cases j
    · exact hr 3
    · exact hr 4
    · exact hr 5

private theorem sparse (u : Fin 6 → ℝ) (t : ℕ) (ht : t = 0 ∨ t = 451) :
    stage u t 3 = 0 ∧ stage u (t+1) 2 = 0 ∧ stage u (t+1) 3 = 0 := by
  have hz : lit (K := ℝ) 0 = 0 := by simp only [lit, Rat.cast_zero]
  rcases ht with rfl | rfl <;> exact ⟨hz, hz, hz⟩

private theorem scalar_quit (u : Fin 6 → ℝ) (t : ℕ) (i : Fin 4) :
    quit u t i =
      SimonTriple.quit (stage u t (i+1)) (stage u t (i+2)) (stage u t (i+3)) := by
  simp only [quit, stay, SimonTriple.quit, SimonTriple.stay, lit, Rat.cast_ofNat, Rat.cast_one]

private theorem scalar_stay (u : Fin 6 → ℝ) (t : ℕ) (i : Fin 4) :
    stay u t i =
      SimonTriple.stay (stage u t (i+1)) (stage u t (i+2)) (stage u t (i+3)) := by
  simp only [stay, SimonTriple.stay, lit, Rat.cast_one]

private theorem pair_quit₀ (y : ℝ) : SimonTriple.quit y 0 0 = 1-2*y := by
  unfold SimonTriple.quit SimonTriple.stay
  ring

private theorem pair_quit₁ (x : ℝ) : SimonTriple.quit 0 0 x = 1+98*x := by
  unfold SimonTriple.quit SimonTriple.stay
  ring

/-- The first two residuals at a triple match its active roles to their quit
values on the first pair date after the triple. -/
theorem outgoing (u : Fin 6 → ℝ) (hr : ∀ i, residual u i = 0)
    (hl : ∀ t : Fin 464, ∀ i, 0 ≤ stage u t.val i ∧ stage u t.val i < 1)
    (t : Fin 464) (ht : t.val = 0 ∨ t.val = 451) (i : Fin 4) (hi : i.val < 2) :
    quit u t.val i = cash u t.val i + stay u t.val i * quit u (t.val+1) i := by
  obtain ⟨h3, h2', h3'⟩ := sparse u t.val ht
  have h (a : Fin 4) : 1-stage u t.val a ≠ 0 := (sub_pos.mpr (hl t a).2).ne'
  have cases : i = 0 ∨ i = 1 := by apply Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h); omega
  rcases cases with rfl | rfl
  · have h0 := local_residuals u hr _ ht 0
    change lit (K := ℝ) 2 * stage u (t.val+1) 1 - odds (stage u t.val 1) -
      odds (stage u t.val 2) - lit 101 * odds (stage u t.val 1) * odds (stage u t.val 2) = 0 at h0
    simp only [odds, lit, Rat.cast_one, Rat.cast_ofNat] at h0
    rw [scalar_quit, scalar_quit, scalar_stay]
    change SimonTriple.quit (stage u t.val 1) (stage u t.val 2) (stage u t.val 3) =
      lit 100 * stage u t.val 2 +
      SimonTriple.stay (stage u t.val 1) (stage u t.val 2) (stage u t.val 3) *
      SimonTriple.quit (stage u (t.val+1) 1) (stage u (t.val+1) 2) (stage u (t.val+1) 3)
    rw [h3, h2', h3', pair_quit₀]
    simpa only [lit, Rat.cast_ofNat] using SimonTriple.tripleFirst _ _ _ (h 1) (h 2) h0
  · have h1 := local_residuals u hr _ ht 1
    change (lit (K := ℝ) 99 - odds (stage u t.val 2))*odds (stage u t.val 0) -
      odds (stage u t.val 2) - lit 98 * stage u (t.val+1) 0 = 0 at h1
    simp only [odds, lit, Rat.cast_one, Rat.cast_ofNat] at h1
    rw [scalar_quit, scalar_quit, scalar_stay]
    change SimonTriple.quit (stage u t.val 2) (stage u t.val 3) (stage u t.val 0) =
      lit 100 * stage u t.val 3 +
      SimonTriple.stay (stage u t.val 2) (stage u t.val 3) (stage u t.val 0) *
      SimonTriple.quit (stage u (t.val+1) 2) (stage u (t.val+1) 3) (stage u (t.val+1) 0)
    rw [h3, h2', h3', pair_quit₁, mul_zero, zero_add]
    exact SimonTriple.tripleSecond _ _ _ (h 0) (h 2) h1

/-- The third residual directly pins the departing player's quit payoff to her
periodic waiting value. -/
theorem drop_eq (u : Fin 6 → ℝ) (hr : ∀ i, residual u i = 0)
    (hd : denom (cash u) (stay u) ≠ 0) (t : Fin 464) (ht : t.val = 0 ∨ t.val = 451) :
    quit u t.val 2 = value (cash u) (stay u) t.val 2 := by
  have h2 := local_residuals u hr _ ht 2
  change lit (K := ℝ) 1 + lit 98 * (stage u t.val 0 + stage u t.val 1 -
    stage u t.val 0 * stage u t.val 1) - reservation u t.val = 0 at h2
  simp only [lit, Rat.cast_one, Rat.cast_ofNat, sub_eq_zero] at h2
  rw [scalar_quit]
  change SimonTriple.quit (stage u t.val 3) (stage u t.val 0) (stage u t.val 1) = _
  rw [(sparse u _ ht).1, SimonTriple.tripleThird, h2]
  rcases ht with ht | ht
  · rw [ht, SimonAffine.value_zero _ _ hd]
    rfl
  · rw [ht, SimonAffine.value_second]
    rfl

end SimonTripleBoundary

#print axioms SimonTripleBoundary.outgoing
#print axioms SimonTripleBoundary.drop_eq
