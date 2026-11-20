module
public import RootDomain
public import Guarded
public import InactiveWitness

/-! # Finite checks for the lower Bellman witness -/

@[expose] public section
namespace PalomarSimon.Inactive

abbrev CI := Checked Interval

def inputs (j : Fin 6) : CI := Checked.some (box j)

def certLE (a b : CI) : Bool :=
  match a.result, b.result with
  | some x, some y => decide (x.hi ≤ y.lo)
  | _, _ => false

def active (t : ℕ) (i : Fin 4) : Prop :=
  i.val < 2 ∨ i.val = 2 ∧ (t = 0 ∨ t = 451)

instance (t : ℕ) (i : Fin 4) : Decidable (active t i) := by
  unfold active
  infer_instance

def rowOK (t : ℕ) (i : Fin 4) : Bool :=
  let l : CI := SimonExpr.lit (lowerRat t i)
  let next : CI := SimonExpr.lit (lowerRat (t+1) i)
  certLE l (SimonExpr.cash inputs t i + SimonExpr.stay inputs t i * next) &&
    (decide (active t i) || certLE (SimonExpr.quit inputs t i) l)

theorem certLE_sound {a b : CI} {x y : ℝ}
    (ha : Checked.Lift Interval.Mem x a) (hb : Checked.Lift Interval.Mem y b)
    (hle : certLE a b = true) : x ≤ y := by
  cases h₁ : a.result with
  | none => simp [certLE,h₁] at hle
  | some al =>
    cases h₂ : b.result with
    | none => simp [certLE,h₂] at hle
    | some bl =>
      have h : al.hi ≤ bl.lo := by simpa [certLE,h₁,h₂] using hle
      apply (mul_le_mul_iff_left₀ Interval.scale_real_pos).mp
      exact (ha _ h₁).2.trans ((by exact_mod_cast h : (al.hi : ℝ) ≤ bl.lo).trans (hb _ h₂).1)

def groupOK (k : ℕ) : Prop := ∀ j : Fin 16, ∀ i : Fin 4, rowOK (16*k+j.val) i = true

instance (k : ℕ) : Decidable (groupOK k) := by
  unfold groupOK
  infer_instance

end PalomarSimon.Inactive

