module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Integer enclosures at 768 binary places

Bounds store integer numerators and an implicit positive denominator. Product
and quotient operations round outward. No validity assumption on the endpoint
order is necessary in the containment theorems.
-/

@[expose] public section

namespace PalomarSimon

structure Interval where
  lo : ℤ
  hi : ℤ
deriving Repr, DecidableEq, Inhabited

namespace Interval

def scale : ℤ := 2 ^ 768

theorem scale_pos : 0 < scale := by unfold scale; positivity

theorem scale_real_pos : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast scale_pos

def Mem (x : ℝ) (a : Interval) : Prop :=
  (a.lo : ℝ) ≤ x * (scale : ℝ) ∧ x * (scale : ℝ) ≤ (a.hi : ℝ)

def exact (n : ℤ) : Interval := ⟨n * scale, n * scale⟩

def ratio (n d : ℤ) : Interval := ⟨(n * scale) / d, -(-(n * scale) / d)⟩

instance : Add Interval := ⟨fun a b ↦ ⟨a.lo + b.lo, a.hi + b.hi⟩⟩
instance : Neg Interval := ⟨fun a ↦ ⟨-a.hi, -a.lo⟩⟩
instance : Sub Interval := ⟨fun a b ↦ a + -b⟩

def lowerProduct (a b : Interval) : ℤ :=
  min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))

def upperProduct (a b : Interval) : ℤ :=
  max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))

instance : Mul Interval := ⟨fun a b ↦
  ⟨lowerProduct a b / scale, -(-upperProduct a b / scale)⟩⟩

theorem roundDown_le {n d : ℤ} (hd : 0 < d) : ((n / d : ℤ) : ℝ) ≤ (n : ℝ) / d := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).2
  exact_mod_cast Int.ediv_mul_le n (ne_of_gt hd)

theorem le_roundUp {n d : ℤ} (hd : 0 < d) : (n : ℝ) / d ≤ ((-((-n) / d) : ℤ) : ℝ) := by
  have h := roundDown_le (n := -n) hd
  push_cast at h ⊢
  simpa only [neg_div, neg_neg] using neg_le_neg h

theorem mem_exact (n : ℤ) : Mem (n : ℝ) (exact n) := by simp [Mem, exact]

theorem mem_ratio (n : ℤ) {d : ℤ} (hd : 0 < d) : Mem ((n : ℝ) / d) (ratio n d) := by
  have hl := roundDown_le (n := n*scale) hd
  have hu := le_roundUp (n := n*scale) hd
  change _ ≤ _ ∧ _ ≤ _
  dsimp [ratio]
  rw [div_mul_eq_mul_div]
  simpa only [Int.cast_mul] using And.intro hl hu

theorem ne_zero_of_mem {x : ℝ} {a : Interval} (hx : Mem x a)
    (hs : a.hi < 0 ∨ 0 < a.lo) : x ≠ 0 := by
  rintro rfl
  simp only [Mem, zero_mul] at hx
  rcases hs with h | h
  · exact (not_lt_of_ge hx.2) (by exact_mod_cast h)
  · exact (not_lt_of_ge hx.1) (by exact_mod_cast h)

theorem mem_add {x y : ℝ} {a b : Interval} (hx : Mem x a) (hy : Mem y b) :
    Mem (x+y) (a+b) := by
  change ((a.lo + b.lo : ℤ) : ℝ) ≤ _ ∧ _ ≤ ((a.hi + b.hi : ℤ) : ℝ)
  simpa only [Int.cast_add, add_mul] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem mem_neg {x : ℝ} {a : Interval} (hx : Mem x a) : Mem (-x) (-a) := by
  change ((-a.hi : ℤ) : ℝ) ≤ _ ∧ _ ≤ ((-a.lo : ℤ) : ℝ)
  simpa only [Int.cast_neg, neg_mul] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem mem_sub {x y : ℝ} {a b : Interval} (hx : Mem x a) (hy : Mem y b) :
    Mem (x-y) (a-b) := by
  change Mem (x-y) (a + -b)
  simpa only [sub_eq_add_neg] using mem_add hx (mem_neg hy)

private theorem lower_linear {k t s l h : ℝ} (hl : l ≤ t) (hh : t ≤ h)
    (kl : k ≤ l*s) (kh : k ≤ h*s) : k ≤ t*s := by
  rcases le_total 0 s with hs | hs
  · exact kl.trans (mul_le_mul_of_nonneg_right hl hs)
  · exact kh.trans (mul_le_mul_of_nonpos_right hh hs)

private theorem upper_linear {k t s l h : ℝ} (hl : l ≤ t) (hh : t ≤ h)
    (kl : l*s ≤ k) (kh : h*s ≤ k) : t*s ≤ k := by
  rcases le_total 0 s with hs | hs
  · exact (mul_le_mul_of_nonneg_right hh hs).trans kh
  · exact (mul_le_mul_of_nonpos_right hl hs).trans kl

theorem mem_mul {x y : ℝ} {a b : Interval} (hx : Mem x a) (hy : Mem y b) :
    Mem (x*y) (a*b) := by
  let X := x * (scale : ℝ)
  let Y := y * (scale : ℝ)
  have hl : (lowerProduct a b : ℝ) ≤ X * Y := by
    apply lower_linear hx.1 hx.2
    all_goals rw [mul_comm (a := (_ : ℝ)) (b := Y)]
    all_goals apply lower_linear hy.1 hy.2
    all_goals rw [mul_comm]; exact_mod_cast (by simp [lowerProduct] : _)
  have hu : X * Y ≤ (upperProduct a b : ℝ) := by
    apply upper_linear hx.1 hx.2
    all_goals rw [mul_comm (a := (_ : ℝ)) (b := Y)]
    all_goals apply upper_linear hy.1 hy.2
    all_goals rw [mul_comm]; exact_mod_cast (by simp [upperProduct] : _)
  have heq : (x*y)*(scale:ℝ) = X*Y/(scale:ℝ) := by
    apply (eq_div_iff (ne_of_gt scale_real_pos)).2
    dsimp [X,Y]
    ring
  unfold Mem
  rw [heq]
  exact ⟨(roundDown_le scale_pos).trans (div_le_div_of_nonneg_right hl scale_real_pos.le),
    (div_le_div_of_nonneg_right hu scale_real_pos.le).trans (le_roundUp scale_pos)⟩

end Interval
end PalomarSimon
