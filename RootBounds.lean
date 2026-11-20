module

public import RootExistence
public import Interval

/-! # From integer enclosure checks to the divided-difference criterion

The two checks use the fixed-point denominator of the interval representation.
The radius numerator uses the same denominator.
-/

@[expose] public section
namespace PalomarSimon

def isum : {n : ℕ} → (Fin n → Interval) → Interval
  | 0, _ => Interval.exact 0
  | n+1, a => a 0 + isum (n := n) (fun j => a j.succ)

theorem mem_isum {n : ℕ} (f : Fin n → ℝ) (a : Fin n → Interval)
    (h : ∀ i, Interval.Mem (f i) (a i)) : Interval.Mem (∑ i, f i) (isum a) := by
  induction n with
  | zero => simpa [isum] using Interval.mem_exact 0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact Interval.mem_add (h 0) (ih (fun j => f j.succ) (fun j => a j.succ) (fun j => h j.succ))

def magnitude (a : Interval) : ℤ := max |a.lo| |a.hi|

theorem abs_mul_scale_le {x : ℝ} {a : Interval} (h : Interval.Mem x a) :
    |x| * (Interval.scale : ℝ) ≤ (magnitude a : ℝ) := by
  rw [← abs_of_nonneg Interval.scale_real_pos.le, ← abs_mul]
  apply abs_le.mpr
  unfold magnitude
  constructor
  · refine le_trans ?_ h.1
    exact_mod_cast (neg_le.mpr ((neg_le_abs a.lo).trans (le_max_left _ _)))
  · refine le_trans h.2 ?_
    exact_mod_cast ((le_abs_self a.hi).trans (le_max_right _ _))

def productEntry {n : ℕ} (A B : Matrix (Fin n) (Fin n) Interval) (i j : Fin n) : Interval :=
  isum (fun k => A i k * B k j)

def remainderEntry {n : ℕ} (A B : Matrix (Fin n) (Fin n) Interval) (i j : Fin n) : Interval :=
  Interval.exact (if i = j then 1 else 0) - productEntry A B i j

def rowDeviation {n : ℕ} (A B : Matrix (Fin n) (Fin n) Interval) (i : Fin n) : ℤ :=
  ∑ j, magnitude (remainderEntry A B i j)

def centerDeviation {n : ℕ} (A : Matrix (Fin n) (Fin n) Interval) (E : Fin n → Interval)
    (i : Fin n) : ℤ := magnitude (isum (fun k => A i k * E k))

theorem mem_remainderEntry {n : ℕ} {C J : Matrix (Fin n) (Fin n) ℝ}
    {A B : Matrix (Fin n) (Fin n) Interval}
    (hc : ∀ i j, Interval.Mem (C i j) (A i j)) (hj : ∀ i j, Interval.Mem (J i j) (B i j))
    (i j : Fin n) :
    Interval.Mem ((1-C*J) i j) (remainderEntry A B i j) := by
  apply Interval.mem_sub
  · rw [Matrix.one_apply]
    split
    · simpa using Interval.mem_exact 1
    · simpa using Interval.mem_exact 0
  · exact mem_isum _ _ (fun k => Interval.mem_mul (hc i k) (hj k j))

/-- The integer certificate bounds the radius and the sup-norm contraction factor. -/
theorem exists_root_of_intervals {n : ℕ} (c : Fin n → ℝ) (R : ℤ)
    (C : Matrix (Fin n) (Fin n) ℝ) (A B : Matrix (Fin n) (Fin n) Interval)
    (E : Fin n → Interval) (F : (Fin n → ℝ) → Fin n → ℝ) (hR : 0 ≤ R)
    (hC : ∀ i j, Interval.Mem (C i j) (A i j))
    (hE : ∀ i, Interval.Mem (F c i) (E i))
    (hcenter : ∀ i, 2 * centerDeviation A E i ≤ R)
    (hrow : ∀ i, 2 * rowDeviation A B i ≤ Interval.scale)
    (hsec : ∀ x ∈ Metric.closedBall c ((R : ℝ)/Interval.scale),
      ∀ y ∈ Metric.closedBall c ((R : ℝ)/Interval.scale),
      ∃ J : Matrix (Fin n) (Fin n) ℝ, F x-F y = J.mulVec (x-y) ∧
        ∀ i j, Interval.Mem (J i j) (B i j)) :
    ∃ w ∈ Metric.closedBall c ((R : ℝ)/Interval.scale), F w = 0 := by
  have hs := Interval.scale_real_pos
  have hr : 0 ≤ (R : ℝ) / Interval.scale := div_nonneg (by exact_mod_cast hR) hs.le
  apply exists_root_of_secant c _ C F hr
  · apply (dist_pi_le_iff (by positivity)).2
    intro i
    have he : Interval.Mem (C.mulVec (F c) i) (isum (fun k => A i k * E k)) :=
      mem_isum _ _ (fun k => Interval.mem_mul (hC i k) (hE k))
    have he' := abs_mul_scale_le he
    have htwo : 2 * (centerDeviation A E i : ℝ) ≤ R := by exact_mod_cast hcenter i
    change |C.mulVec (F c) i| * (Interval.scale : ℝ) ≤ (centerDeviation A E i : ℝ) at he'
    rw [Real.dist_eq]
    change |c i - C.mulVec (F c) i - c i| ≤ _
    rw [show c i - C.mulVec (F c) i - c i = -(C.mulVec (F c) i) by abel, abs_neg]
    rw [div_right_comm]
    apply (le_div_iff₀ hs).2
    linarith
  · intro x hx y hy
    obtain ⟨J, he, hj⟩ := hsec x hx y hy
    refine ⟨J, he, fun i => ?_⟩
    have hb : (∑ j, |(1-C*J) i j|) * (Interval.scale : ℝ) ≤ (rowDeviation A B i : ℝ) := by
      rw [Finset.sum_mul]
      unfold rowDeviation
      push_cast
      exact Finset.sum_le_sum (fun j _ => abs_mul_scale_le (mem_remainderEntry hC hj i j))
    have htwo : 2 * (rowDeviation A B i : ℝ) ≤ (Interval.scale : ℝ) := by exact_mod_cast hrow i
    apply (le_of_mul_le_mul_right (a := (Interval.scale : ℝ)) (b := _) (c := _) ?_ hs)
    linarith

#print axioms exists_root_of_intervals
end PalomarSimon
