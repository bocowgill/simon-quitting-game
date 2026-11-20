module

public import Expressions
public import Mathlib.Tactic

/-! # Waiting values for four rotated blocks

The same 464-stage schedule is repeated in four orientations. The Bellman
identity at the last date of each block uses the next role's initial value.
-/

@[expose] public section

namespace SimonAffine

open SimonExpr

private theorem cycle_identity (r s : Fin 4 → ℝ) (i : Fin 4)
    (hd : 1 - s 0 * s 1 * s 2 * s 3 ≠ 0) :
    let den := 1 - s 0 * s 1 * s 2 * s 3
    let start := fun j : Fin 4 =>
      (r j + s j * r (j+1) + s j * s (j+1) * r (j+2) +
        s j * s (j+1) * s (j+2) * r (j+3)) / den
    start i = r i + s i * start (i+1) := by
  dsimp only
  field_simp [hd]
  have hp : s 0 * s 1 * s 2 * s 3 = s i * s (i+1) * s (i+2) * s (i+3) := by
    fin_cases i
    · rfl
    · change _ = s 1 * s 2 * s 3 * s 0
      ring
    · change _ = s 2 * s 3 * s 0 * s 1
      ring
    · change _ = s 3 * s 0 * s 1 * s 2
      ring
  have h2 : ∀ j : Fin 4, j+1+1 = j+2 := by decide
  have h3 : ∀ j : Fin 4, j+1+2 = j+3 := by decide
  have h4 : ∀ j : Fin 4, j+1+3 = j := by decide
  rw [hp]
  simp only [h2, h3, h4]
  ring

private theorem calendar_step (w c s : ℕ → Fin 4 → ℝ)
    (step : ∀ t i, t < 464 → w t i = c t i + s t i * w (t+1) i)
    (wrap : ∀ i, w 464 i = w 0 (i+1))
    (t : Fin 1856) (i : Fin 4) :
    let idx := fun (d : Fin 1856) => d.val % 464
    let role := fun (d : Fin 1856) => i + Fin.ofNat 4 (d.val / 464)
    w (idx t) (role t) = c (idx t) (role t) + s (idx t) (role t) *
      w (idx (t+1)) (role (t+1)) := by
  dsimp only
  have ht := t.isLt
  rw [step (t.val % 464) _ (Nat.mod_lt _ (by decide))]
  congr 2
  by_cases hlast : t.val % 464 = 463
  · have hidx : (t + 1).val % 464 = 0 := by
      change ((t.val + 1) % 1856) % 464 = 0
      omega
    have hrole : i + Fin.ofNat 4 (t.val / 464) + 1 =
        i + Fin.ofNat 4 ((t+1).val / 464) := by
      apply Fin.ext
      change (((i.val + (t.val / 464) % 4) % 4 + 1) % 4) =
        ((i.val + (((t.val + 1) % 1856) / 464) % 4) % 4)
      omega
    rw [hlast, hidx, show 463+1 = 464 by decide, wrap, hrole]
  · have hidx : (t + 1).val % 464 = t.val % 464 + 1 := by
      change ((t.val + 1) % 1856) % 464 = t.val % 464 + 1
      omega
    have hrole : (t+1).val / 464 = t.val / 464 := by
      change ((t.val + 1) % 1856) / 464 = t.val / 464
      omega
    rw [hidx, hrole]

/-- Evaluation of a local table at the current date and player role. -/
def lift {K : Type*} (row : Row K) (t : Fin 1856) (i : Fin 4) : K :=
  row (t.val % 464) (i + Fin.ofNat 4 (t.val / 464))

theorem initial_eq (c s : Row ℝ) (hd : denom c s ≠ 0) (i : Fin 4) :
    initial c s i = (block c s i).1 + (block c s i).2 * initial c s (i+1) := by
  have h := cycle_identity (fun j => (block c s j).1) (fun j => (block c s j).2) i
    (by simpa only [denom, lit, Rat.cast_one] using hd)
  simpa only [initial, denom, lit, Rat.cast_one] using h

private theorem compose (r s q d v : ℝ) :
    r+s*(q+d*v) = (r+s*q)+(s*d)*v := by ring

private theorem value_before (c s : Row ℝ) (t : ℕ) (i : Fin 4) (h : t < 451) :
    value c s t i =
      (transfer c s t (451-t) i).1 + (transfer c s t (451-t) i).2 * second c s i := by
  simp [value, h]

private theorem value_after (c s : Row ℝ) (t : ℕ) (i : Fin 4) (h : ¬t < 451) :
    value c s t i =
      (transfer c s t (464-t) i).1 + (transfer c s t (464-t) i).2 * initial c s (i+1) := by
  simp [value, h]

/-- The continuation at the first triple agrees with the closed cycle value. -/
theorem value_zero (c s : Row ℝ) (hd : denom c s ≠ 0) (i : Fin 4) :
    value c s 0 i = initial c s i := by
  calc
    _ = (block c s i).1 + (block c s i).2 * initial c s (i+1) := by
      rw [value_before _ _ _ _ (by decide)]
      exact compose _ _ _ _ _
    _ = _ := (initial_eq c s hd i).symm

/-- The continuation at the second triple uses the remaining thirteen stages. -/
theorem value_second (c s : Row ℝ) (i : Fin 4) : value c s 451 i = second c s i := by
  rw [value_after _ _ _ _ (by decide)]
  rfl

private def suffix (c s : Row ℝ) (t n : ℕ) (i : Fin 4) (v : ℝ) :=
  let a := transfer c s t n i
  a.1 + a.2 * v

private theorem suffix_zero (c s : Row ℝ) (t : ℕ) (i : Fin 4) (v : ℝ) :
    suffix c s t 0 i v = v := by
  simp [suffix, transfer, lit]

private theorem suffix_step (c s : Row ℝ) (m t : ℕ) (ht : t < m) (i : Fin 4) (v : ℝ) :
    suffix c s t (m-t) i v = c t i + s t i * suffix c s (t+1) (m-(t+1)) i v := by
  have h : m - t = (m-(t+1))+1 := by omega
  rw [h]
  unfold suffix
  rw [transfer]
  exact (compose _ _ _ _ _).symm

theorem value_step (c s : Row ℝ) (t : ℕ) (i : Fin 4) (ht : t < 464) :
    value c s t i = c t i + s t i * value c s (t+1) i := by
  by_cases ha : t < 451
  · rw [value_before _ _ _ _ ha]
    change suffix c s t (451-t) i _ = _
    rw [suffix_step _ _ _ _ ha]
    by_cases hb : t+1 < 451
    · rw [value_before _ _ _ _ hb]
      rfl
    · have hj : t+1 = 451 := by omega
      rw [hj, value_second, show 451-451 = 0 by decide, suffix_zero]
  · have hb : ¬t+1 < 451 := by omega
    rw [value_after _ _ _ _ ha]
    change suffix c s t (464-t) i _ = _
    rw [suffix_step _ _ _ _ ht, value_after _ _ _ _ hb]
    rfl

/-- The final continuation rotates into the next block. -/
theorem value_wrap (c s : Row ℝ) (hd : denom c s ≠ 0) (i : Fin 4) :
    value c s 464 i = value c s 0 (i+1) := by
  rw [value_zero _ _ hd, value_after _ _ _ _ (by decide)]
  exact suffix_zero _ _ _ _ _

/-- The waiting recursion holds at every phase, including the cyclic boundary. -/
theorem lift_value_step (c s : Row ℝ) (hd : denom c s ≠ 0) (t : Fin 1856) (i : Fin 4) :
    lift (value c s) t i = lift c t i + lift s t i * lift (value c s) (t+1) i :=
  calendar_step _ _ _ (value_step c s) (value_wrap c s hd) t i

#print axioms lift_value_step
#print axioms value_second

end SimonAffine
