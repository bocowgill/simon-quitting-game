module

public import IntervalDivision
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Interval secants for rational expressions

A jet encloses both endpoint values and the coefficients of an exact secant.
The two endpoints may coincide. All operations below are algebraic and require
no differentiability hypotheses.
-/

@[expose] public section
namespace PalomarSimon
open PalomarSimon.Interval

structure Jet (n : ℕ) where
  v : Interval
  d : Fin n → Interval

namespace Jet
variable {n : ℕ}

def const (v : Interval) : Jet n := ⟨v, fun _ ↦ exact 0⟩
def var (v : Interval) (i : Fin n) : Jet n := ⟨v, fun j ↦ exact (if i = j then 1 else 0)⟩

instance : Add (Jet n) := ⟨fun a b ↦ ⟨a.v + b.v, fun j ↦ a.d j + b.d j⟩⟩
instance : Neg (Jet n) := ⟨fun a ↦ ⟨-a.v, fun j ↦ -(a.d j)⟩⟩
instance : Sub (Jet n) := ⟨fun a b ↦ ⟨a.v - b.v, fun j ↦ a.d j - b.d j⟩⟩
instance : Mul (Jet n) := ⟨fun a b ↦ ⟨a.v * b.v, fun j ↦ a.d j * b.v + a.v * b.d j⟩⟩
instance : Div (Jet n) := ⟨fun a b ↦
  let u := a.v / b.v
  ⟨u, fun j ↦ (a.d j - u * b.d j) / b.v⟩⟩

/-- A jet tested at two points and the corresponding values of a function. -/
structure At (a : Jet n) (x y : Fin n → ℝ) (fx fy : ℝ) : Prop where
  left : Mem fx a.v
  right : Mem fy a.v
  slope : ∃ g : Fin n → ℝ, (∀ i, Mem (g i) (a.d i)) ∧
    fx - fy = ∑ i, g i * (x i - y i)

variable {x y : Fin n → ℝ} {a b : Jet n} {ax ay bx by' : ℝ}

theorem at_const {v : Interval} {c : ℝ} (hc : Mem c v) : (const v).At x y c c := by
  exact ⟨hc, hc, fun _ ↦ 0, fun _ ↦ by simpa [const] using mem_exact 0, by simp⟩

theorem at_var {v : Interval} (i : Fin n) (hx : Mem (x i) v) (hy : Mem (y i) v) :
    (var v i).At x y (x i) (y i) := by
  refine ⟨hx, hy, fun j ↦ if i = j then 1 else 0, ?_, ?_⟩
  · intro j
    by_cases h : i = j
    · simpa [var, h] using mem_exact 1
    · simpa [var, h] using mem_exact 0
  · simp [ite_mul]

theorem At.add (ha : a.At x y ax ay) (hb : b.At x y bx by') :
    (a + b).At x y (ax + bx) (ay + by') := by
  obtain ⟨g, hg, eg⟩ := ha.slope
  obtain ⟨h, hh, eh⟩ := hb.slope
  refine ⟨mem_add ha.left hb.left, mem_add ha.right hb.right, fun i ↦ g i + h i,
    fun i ↦ mem_add (hg i) (hh i), ?_⟩
  simp_rw [add_mul, Finset.sum_add_distrib, ← eg, ← eh]
  ring

theorem At.neg (ha : a.At x y ax ay) : (-a).At x y (-ax) (-ay) := by
  obtain ⟨g, hg, eg⟩ := ha.slope
  refine ⟨mem_neg ha.left, mem_neg ha.right, fun i ↦ -(g i), fun i ↦ mem_neg (hg i), ?_⟩
  simp_rw [neg_mul, Finset.sum_neg_distrib, ← eg]
  ring

theorem At.sub (ha : a.At x y ax ay) (hb : b.At x y bx by') :
    (a - b).At x y (ax - bx) (ay - by') := by
  obtain ⟨g, hg, eg⟩ := ha.slope
  obtain ⟨h, hh, eh⟩ := hb.slope
  refine ⟨mem_sub ha.left hb.left, mem_sub ha.right hb.right, fun i ↦ g i - h i,
    fun i ↦ mem_sub (hg i) (hh i), ?_⟩
  simp_rw [sub_mul, Finset.sum_sub_distrib, ← eg, ← eh]
  ring

theorem At.mul (ha : a.At x y ax ay) (hb : b.At x y bx by') :
    (a*b).At x y (ax*bx) (ay*by') := by
  obtain ⟨g, hg, eg⟩ := ha.slope
  obtain ⟨h, hh, eh⟩ := hb.slope
  refine ⟨mem_mul ha.left hb.left, mem_mul ha.right hb.right, fun i ↦ g i * bx + ay * h i,
    fun i ↦ mem_add (mem_mul (hg i) hb.left) (mem_mul ha.right (hh i)), ?_⟩
  calc
    ax*bx - ay*by' = (ax-ay)*bx + ay*(bx-by') := by ring
    _ = _ := by
      rw [eg, eh, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem At.div (ha : a.At x y ax ay) (hb : b.At x y bx by')
    (hs : b.v.hi < 0 ∨ 0 < b.v.lo) : (a/b).At x y (ax/bx) (ay/by') := by
  obtain ⟨g, hg, eg⟩ := ha.slope
  obtain ⟨h, hh, eh⟩ := hb.slope
  have hx := ne_zero_of_mem hb.left hs
  have hy := ne_zero_of_mem hb.right hs
  refine ⟨mem_div ha.left hb.left hs, mem_div ha.right hb.right hs,
    fun i ↦ (g i - ay/by' * h i)/bx,
    fun i ↦ mem_div (mem_sub (hg i) (mem_mul (mem_div ha.right hb.right hs) (hh i))) hb.left hs,
    ?_⟩
  calc
    ax/bx - ay/by' = ((ax-ay) - ay/by' * (bx-by'))/bx := by field_simp; ring
    _ = _ := by
      rw [eg, eh, Finset.mul_sum, ← Finset.sum_sub_distrib, div_eq_mul_inv _ bx, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring

#print axioms At.div

end Jet
end PalomarSimon
