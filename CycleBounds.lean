module

public import Affine
public import SimonCalendar
public import Mathlib.Tactic

/-! # Strict rival survival in the four-block Simon calendar

The first two players mix at phase zero. Thus every player has a rival with
positive quit probability there. Every other rival survival factor is at most one.
-/

@[expose] public section
namespace SimonCycleBounds

open Finset
open SimonExpr

private def surv (p : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  (1-p (i+1))*(1-p (i+2))*(1-p (i+3))

private theorem mul_bound {a b : ℝ} (ha : a ≤ 1) (hb : 0 ≤ b) (hb' : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_of_le_one_left hb ha).trans hb'

private theorem surv_bounds (p : Fin 4 → ℝ) (h : ∀ j, 0 ≤ p j ∧ p j < 1) (i : Fin 4) :
    0 < surv p i ∧ surv p i ≤ 1 := by
  have lo (j : Fin 4) : 0 < 1-p j := sub_pos.mpr (h j).2
  have hi (j : Fin 4) : 1-p j ≤ 1 := sub_le_self _ (h j).1
  refine ⟨mul_pos (mul_pos (lo _) (lo _)) (lo _), ?_⟩
  exact mul_bound (mul_bound (hi _) (lo _).le (hi _)) (lo _).le (hi _)

private theorem surv_lt (p : Fin 4 → ℝ) (h : ∀ j, 0 ≤ p j ∧ p j < 1)
    (hfirst : ∀ j : Fin 4, j.val < 2 → 0 < p j) (i : Fin 4) : surv p i < 1 := by
  have lo (j : Fin 4) : 0 ≤ 1-p j := (sub_pos.mpr (h j).2).le
  have hi (j : Fin 4) : 1-p j ≤ 1 := sub_le_self _ (h j).1
  have h12 := mul_bound (hi (i+1)) (lo (i+2)) (hi (i+2))
  have h23 := mul_bound (hi (i+2)) (lo (i+3)) (hi (i+3))
  have a : surv p i ≤ 1-p (i+1) := by
    unfold surv
    rw [mul_assoc]
    exact mul_le_of_le_one_right (lo _) h23
  have b : surv p i ≤ 1-p (i+3) := mul_le_of_le_one_left (lo _) h12
  have odd : (i+1 : Fin 4).val < 2 ∨ (i+3 : Fin 4).val < 2 := by
    fin_cases i <;> decide
  rcases odd with h1 | h3
  · exact a.trans_lt (sub_lt_self _ (hfirst _ h1))
  · exact b.trans_lt (sub_lt_self _ (hfirst _ h3))

/-- Positive hazards for two roles force strict rival escape for every role. -/
theorem stay_bounds (u : Fin 6 → ℝ) (t : ℕ)
    (h : ∀ j, 0 ≤ stage u t j ∧ stage u t j < 1)
    (hfirst : ∀ j : Fin 4, j.val < 2 → 0 < stage u t j) (i : Fin 4) :
    0 ≤ stay u t i ∧ stay u t i < 1 := by
  simpa only [stay, lit, Rat.cast_one, surv] using
    And.intro (surv_bounds _ h i).1.le (surv_lt _ h hfirst i)

private theorem transfer_bounds (c s : Row ℝ)
    (hs : ∀ t, t < 464 → ∀ i, 0 ≤ s t i ∧ s t i ≤ 1)
    (t n : ℕ) (h : t+n ≤ 464) (i : Fin 4) :
    0 ≤ (transfer c s t n i).2 ∧ (transfer c s t n i).2 ≤ 1 := by
  induction n generalizing t with
  | zero => norm_num [transfer, lit]
  | succ n ih =>
    obtain ⟨x,y⟩ := ih (t+1) (by omega)
    obtain ⟨a,b⟩ := hs t (by omega) i
    exact ⟨mul_nonneg a x, mul_bound b x y⟩

/-- Strict escape at date zero makes the cycle denominator positive. -/
theorem denom_ne_zero (u : Fin 6 → ℝ)
    (h : ∀ t, t < 464 → ∀ i, 0 ≤ stage u t i ∧ stage u t i < 1)
    (hfirst : ∀ i : Fin 4, i.val < 2 → 0 < stage u 0 i) :
    denom (cash u) (stay u) ≠ 0 := by
  have hs (t : ℕ) (ht : t < 464) (i : Fin 4) : 0 ≤ stay u t i ∧ stay u t i ≤ 1 := by
    simpa only [stay, lit, Rat.cast_one, surv] using
      (show 0 ≤ surv (stage u t) i ∧ surv (stage u t) i ≤ 1 from
        ⟨(surv_bounds _ (h t ht) i).1.le,(surv_bounds _ (h t ht) i).2⟩)
  have hstrict (i : Fin 4) : stay u 0 i < 1 := by
    simpa only [stay, lit, Rat.cast_one, surv] using surv_lt _ (h 0 (by decide)) hfirst i
  let d (i : Fin 4) := (block (cash u) (stay u) i).2
  have bound (i : Fin 4) : 0 ≤ d i ∧ d i < 1 := by
    have ht := transfer_bounds (cash u) (stay u) hs
    obtain ⟨x0,x1⟩ := ht 1 450 (by decide) i
    obtain ⟨y0,y1⟩ := ht 451 13 (by decide) i
    change 0 ≤ (stay u 0 i * (transfer (cash u) (stay u) 1 450 i).2) *
      (transfer (cash u) (stay u) 451 13 i).2 ∧ _ < 1
    have nz := mul_nonneg (hs 0 (by decide) i).1 x0
    have zz := mul_le_of_le_one_right (hs 0 (by decide) i).1 x1
    exact ⟨mul_nonneg nz y0, ((mul_le_of_le_one_right nz y1).trans zz).trans_lt (hstrict i)⟩
  simp only [denom, lit, Rat.cast_one]
  change 1 - d 0 * d 1 * d 2 * d 3 ≠ 0
  have nz := mul_nonneg (bound 0).1 (bound 1).1
  have z := mul_nonneg nz (bound 2).1
  exact (sub_pos.mpr <| ((mul_le_of_le_one_right z (bound 3).2.le).trans
    ((mul_le_of_le_one_right nz (bound 2).2.le).trans
      (mul_le_of_le_one_right (bound 0).1 (bound 1).2.le))).trans_lt (bound 0).2).ne'

/-- Two positive hazards in the first row suffice for strict rival escape in a period. -/
theorem proper (p : Fin 1856 → Fin 4 → ℝ)
    (h : ∀ t i, 0 ≤ p t i ∧ p t i < 1)
    (hfirst : ∀ i : Fin 4, i.val < 2 → 0 < p 0 i) (i : Fin 4) :
    (∏ k ∈ range 1856, SimonPeriodic.rivals
      (SimonPeriodic.FC.cycle (by decide : 0 < 1856) p) k i) < 1 := by
  let per := SimonPeriodic.FC.cycle (by decide : 0 < 1856) p
  have heq (k : ℕ) : SimonPeriodic.rivals per k i = surv (per k) i := by
    unfold SimonPeriodic.rivals surv
    ring
  have H (k : ℕ) : 0 < SimonPeriodic.rivals per k i ∧ SimonPeriodic.rivals per k i ≤ 1 := by
    rw [heq]
    exact surv_bounds _ (h _) i
  have first : SimonPeriodic.rivals per 0 i < 1 := by
    rw [heq]
    exact surv_lt _ (h 0) hfirst i
  have rest (n : ℕ) : (∏ k ∈ range n, SimonPeriodic.rivals per (k+1) i) ≤ 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ]
      exact mul_bound ih (H _).1.le (H _).2
  rw [Finset.prod_range_succ' (fun k => SimonPeriodic.rivals per k i) 1855]
  exact (mul_le_of_le_one_left (H 0).1.le (rest 1855)).trans_lt first

/-- The lifted two-run calendar satisfies the properness hypothesis of the
finite-table theorem. -/
theorem lifted_proper (u : Fin 6 → ℝ)
    (h : ∀ t, t < 464 → ∀ i, 0 ≤ stage u t i ∧ stage u t i < 1)
    (hfirst : ∀ i : Fin 4, i.val < 2 → 0 < stage u 0 i) (i : Fin 4) :
    (∏ k ∈ range 1856, SimonPeriodic.rivals
      (SimonPeriodic.FC.cycle (by decide : 0 < 1856) (SimonAffine.lift (stage u))) k i) < 1 := by
  apply proper
  · intro t j
    exact h (t.val % 464) (Nat.mod_lt _ (by decide)) _
  · intro j hj
    simpa [SimonAffine.lift] using hfirst j hj

end SimonCycleBounds

#print axioms SimonCycleBounds.stay_bounds
#print axioms SimonCycleBounds.denom_ne_zero
#print axioms SimonCycleBounds.proper

#print axioms SimonCycleBounds.lifted_proper
