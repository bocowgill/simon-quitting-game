module

public import Affine
public import HazardBounds
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith

/-! # Lower bounds for waiting values in Simon's rotated calendar

A table of lower bounds can be checked one date at a time. The endpoint can
either be bounded separately or compared with the lower bound for the next
role at date zero. In the latter case the minimum principle closes the cycle.
-/

@[expose] public section
namespace SimonBound

open SimonExpr (Row)

/-- Check one row of the Bellman inequality using lower bounds on the current
cash payment and on survival and a nonnegative next-date certificate. -/
theorem one_step {c s l cn sn next : ℝ} (hc : cn ≤ c) (hs : sn ≤ s)
    (hn : 0 ≤ next) (hb : l ≤ cn + sn * next) : l ≤ c + s * next :=
  hb.trans (add_le_add hc (mul_le_mul_of_nonneg_right hs hn))

/-- Backward propagation when a separate terminal lower bound is available. -/
theorem of_terminal (v c s l : Row ℝ)
    (hv : ∀ t i, t < 464 → v t i = c t i + s t i * v (t+1) i)
    (hs : ∀ t i, t < 464 → 0 ≤ s t i)
    (hl : ∀ t i, t < 464 → l t i ≤ c t i + s t i * l (t+1) i)
    (hend : ∀ i, l 464 i ≤ v 464 i) : ∀ t i, t ≤ 464 → l t i ≤ v t i := by
  have h : ∀ n t i, t+n=464 → l t i ≤ v t i := by
    intro n
    induction n with
    | zero =>
      intro t i heq
      rw [Nat.add_zero] at heq
      simpa only [heq] using hend i
    | succ n ih =>
      intro t i heq
      have ht : t < 464 := by omega
      rw [hv t i ht]
      exact (hl t i ht).trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (ih (t+1) i (by omega)) (hs t i ht)))
  intro t i ht
  exact h (464-t) t i (by omega)

private theorem exists_argmin {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ x, ∀ y, f x ≤ f y := by
  obtain ⟨x, _, h⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  exact ⟨x, fun y => h y (Finset.mem_univ y)⟩

/-- A cyclic Bellman subsolution is a lower bound if the rival survival
probability is strictly below one in each role at each date. -/
theorem of_cycle (v c s l : Row ℝ)
    (hv : ∀ t i, t < 464 → v t i = c t i + s t i * v (t+1) i)
    (hwrap : ∀ i, v 464 i = v 0 (i+1))
    (hs : ∀ t i, t < 464 → 0 ≤ s t i ∧ s t i < 1)
    (hl : ∀ t i, t < 464 → l t i ≤ c t i + s t i * l (t+1) i)
    (hend : ∀ i, l 464 i ≤ l 0 (i+1)) : ∀ t i, t ≤ 464 → l t i ≤ v t i := by
  let gap (p : Fin 464 × Fin 4) := v p.1.val p.2 - l p.1.val p.2
  obtain ⟨⟨t,i⟩, hmin⟩ := exists_argmin gap
  have hleast (j : Fin 464) (k : Fin 4) : gap (t,i) ≤ v j.val k - l j.val k :=
    hmin (j,k)
  have hnext : gap (t,i) ≤ v (t.val+1) i - l (t.val+1) i := by
    by_cases h : t.val + 1 < 464
    · exact hleast ⟨t.val + 1, h⟩ i
    · have he : t.val + 1 = 464 := by have := t.isLt; omega
      rw [he, hwrap]
      exact (hleast 0 (i+1)).trans (sub_le_sub_left (hend i) _)
  have hzero : 0 ≤ gap (t,i) := by
    by_contra! hneg
    have hstrict : gap (t,i) < s t.val i * gap (t,i) := by
      simpa only [one_mul] using mul_lt_mul_of_neg_right (hs t.val i t.isLt).2 hneg
    have hstep := mul_le_mul_of_nonneg_left hnext (hs t.val i t.isLt).1
    have hdiff := hstrict.trans_le hstep
    change v t.val i - l t.val i < _ at hdiff
    linarith only [hv t.val i t.isLt, hl t.val i t.isLt, hdiff,
      mul_sub (s t.val i) (v (t.val+1) i) (l (t.val+1) i)]
  intro j k hj
  by_cases h : j < 464
  · exact sub_nonneg.mp (hzero.trans (hleast ⟨j,h⟩ k))
  · have he : j = 464 := by omega
    rw [he, hwrap]
    exact (hend k).trans (sub_nonneg.mp (hzero.trans (hleast 0 (k+1))))

open SimonExpr

/-- Certified one-step inequalities imply every inactive player's inequality
on the 464-date calendar, including its rotation into the next role. -/
theorem inactive_of_cycle (u : Fin 6 → ℝ) (l : Row ℝ)
    (hd : denom (cash u) (stay u) ≠ 0)
    (hs : ∀ t, t < 464 → ∀ i, 0 ≤ stay u t i ∧ stay u t i < 1)
    (hrows : ∀ t, t < 464 → ∀ i,
      l t i ≤ cash u t i + stay u t i * l (t+1) i ∧
      (¬ SimonHazardBounds.active t i → quit u t i ≤ l t i))
    (hend : ∀ i, l 464 i ≤ l 0 (i+1)) : ∀ t, t < 464 → ∀ i,
      ¬ SimonHazardBounds.active t i → quit u t i ≤ value (cash u) (stay u) t i := by
  have hbound := of_cycle _ _ _ l (SimonAffine.value_step _ _) (SimonAffine.value_wrap _ _ hd)
    (fun t i ht => hs t ht i) (fun t i ht => (hrows t ht i).1) hend
  intro t ht i hi
  exact ((hrows t ht i).2 hi).trans (hbound t i ht.le)

end SimonBound

#print axioms SimonBound.of_terminal
#print axioms SimonBound.of_cycle
#print axioms SimonBound.inactive_of_cycle
