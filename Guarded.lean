module
public import IntervalDivision
public import Expressions

/-! # Arithmetic enclosures with checked denominators

A failed division invalidates its output and every dependent expression.
-/

@[expose] public section
namespace PalomarSimon

class Enclosure (K : Type*) where
  range : K → Interval

instance : Enclosure Interval := ⟨id⟩
instance : RatCast Interval := ⟨fun q ↦ Interval.ratio q.num q.den⟩

theorem mem_ratCast (q : ℚ) : Interval.Mem (q : ℝ) (q : Interval) := by
  change Interval.Mem (q : ℝ) (Interval.ratio q.num q.den)
  rw [Rat.cast_def]
  simpa only [Int.cast_natCast] using
    Interval.mem_ratio q.num (show (0 : ℤ) < (q.den : ℤ) by exact_mod_cast q.den_pos)

structure Checked (K : Type*) where
  result : Option K

namespace Checked

def some (a : K) : Checked K := ⟨Option.some a⟩

def binary (op : K → K → K) (a b : Checked K) : Checked K :=
  ⟨do return op (← a.result) (← b.result)⟩

def divide [Enclosure K] [Div K] (a b : Checked K) : Checked K :=
  ⟨do
    let x ← a.result
    let y ← b.result
    let v := Enclosure.range y
    if v.hi < 0 ∨ 0 < v.lo then return x / y else none⟩

instance [RatCast K] : RatCast (Checked K) := ⟨fun q ↦ some (q : K)⟩
instance [Add K] : Add (Checked K) := ⟨binary (· + ·)⟩
instance [Sub K] : Sub (Checked K) := ⟨binary (· - ·)⟩
instance [Mul K] : Mul (Checked K) := ⟨binary (· * ·)⟩
instance [Enclosure K] [Div K] : Div (Checked K) := ⟨divide⟩

def Lift (R : A → K → Prop) (x : A) (a : Checked K) : Prop :=
  ∀ v, a.result = Option.some v → R x v

theorem lift_some {R : A → K → Prop} {x : A} {a : K} (h : R x a) : Lift R x (some a) := by
  rintro v ⟨⟩
  exact h

theorem lift_binary {R : A → K → Prop} (op : A → A → A) (ik : K → K → K)
    (hop : ∀ {x y a b}, R x a → R y b → R (op x y) (ik a b))
    {x y : A} {a b : Checked K} (hx : Lift R x a) (hy : Lift R y b) :
    Lift R (op x y) (binary ik a b) := by
  intro v hv
  cases ha : a.result with
  | none => simp [binary, ha] at hv
  | some u =>
    cases hb : b.result with
    | none => simp [binary, ha, hb] at hv
    | some w =>
      have e : ik u w = v := by simpa [binary, ha, hb] using hv
      exact e ▸ hop (hx u ha) (hy w hb)

theorem lift_div [Div A] [Div K] [Enclosure K] {R : A → K → Prop}
    (hop : ∀ {x y a b}, R x a → R y b →
      ((Enclosure.range b).hi < 0 ∨ 0 < (Enclosure.range b).lo) → R (x/y) (a/b))
    {x y : A} {a b : Checked K} (hx : Lift R x a) (hy : Lift R y b) :
    Lift R (x/y) (a/b) := by
  intro v hv
  change (divide a b).result = Option.some v at hv
  cases ha : a.result with
  | none => simp [divide, ha] at hv
  | some u =>
    cases hb : b.result with
    | none => simp [divide, ha, hb] at hv
    | some w =>
      by_cases hs : (Enclosure.range w).hi < 0 ∨ 0 < (Enclosure.range w).lo
      · have e : u/w = v := by simpa [divide, ha, hb, hs] using hv
        exact e ▸ hop (hx u ha) (hy w hb) hs
      · simp [divide, ha, hb, hs] at hv

end Checked
end PalomarSimon
