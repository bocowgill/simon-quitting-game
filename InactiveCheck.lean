module
public import InactiveChecks
public import InactivePropagation
public import GuardedInterval

/-! # Inactive quitting comparisons throughout the Simon parameter box

A cyclic table of lower bounds satisfies the waiting Bellman inequalities on
the entire box. At each inactive date the quitting payoff is below the table.
-/

@[expose] public section
namespace PalomarSimon.Inactive

theorem rows {u : Fin 6 → ℝ} (hu : u ∈ Metric.closedBall center radius)
    (t : ℕ) (ht : t < 464) (i : Fin 4) :
    lower t i ≤ SimonExpr.cash u t i + SimonExpr.stay u t i * lower (t+1) i ∧
    (¬ SimonHazardBounds.active t i → SimonExpr.quit u t i ≤ lower t i) := by
  have h := verified ⟨t,ht⟩ i
  change rowOK t i = true at h
  have hv (j : Fin 6) : Checked.Lift Interval.Mem (u j) (inputs j) :=
    Checked.lift_some (mem_box hu j)
  let H := checkedIntervalOps
  have hl (k : ℕ) : Checked.Lift Interval.Mem (lower k i)
      (SimonExpr.lit (lowerRat k i) : CI) := H.lit _
  obtain ⟨hstep,hquit⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨certLE_sound (hl t) (H.add (H.cash hv t i) (H.mul (H.stay hv t i) (hl (t+1)))) hstep, ?_⟩
  intro hInactive
  have hn : ¬ active t i := hInactive
  exact certLE_sound (H.quit hv t i) (hl t) (by simpa [hn] using hquit)

theorem lower_wrap (i : Fin 4) : lower 464 i = lower 0 (i+1) := by
  have hn : ∀ j : Fin 4, numerator 464 j = numerator 0 (j+1) := by decide +kernel
  unfold lower lowerRat
  rw [hn]

theorem inactive_of_box {u : Fin 6 → ℝ} (hu : u ∈ Metric.closedBall center radius)
    (hd : SimonExpr.denom (SimonExpr.cash u) (SimonExpr.stay u) ≠ 0)
    (hs : ∀ t, t < 464 → ∀ i, 0 ≤ SimonExpr.stay u t i ∧ SimonExpr.stay u t i < 1) :
    ∀ t, t < 464 → ∀ i, ¬ SimonHazardBounds.active t i →
      SimonExpr.quit u t i ≤ SimonExpr.value (SimonExpr.cash u) (SimonExpr.stay u) t i :=
  SimonBound.inactive_of_cycle u lower hd hs (rows hu) (fun i ↦ (lower_wrap i).le)

#print axioms inactive_of_box
end PalomarSimon.Inactive

