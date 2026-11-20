module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Real.Basic

/-! # Active-player identities along the adjacent-pair phases of Simon's calendar

The closed forms are written in terms of the remaining power of 99/98 and the
elapsed power of 1/2. Advancing one phase divides these powers by their bases
of backward and forward scaling respectively, as stated in the two identities.
-/

@[expose] public section
namespace SimonPairMatching

noncomputable def firstHazard (power endpoint : ℝ) : ℝ :=
  endpoint / (power + 98 * (power - 1) * endpoint)

noncomputable def secondHazard (power initial : ℝ) : ℝ :=
  initial * power / (1 - 2 * initial + 2 * initial * power)

/-- The first active player's required post-value equals her next quit value. -/
theorem matchFirst (p y : ℝ) (h : 1 - 2*y + 2*y*p ≠ 0) :
    1 - secondHazard p y / (1 - secondHazard p y) =
      1 - 2 * secondHazard (p/2) y := by
  unfold secondHazard
  rw [one_sub_div h, div_div_div_cancel_right₀ h]
  have h1 : 1 - 2*y + 2*y*p - y*p = 1 - 2*y + y*p := by ring
  have h2 : 1 - 2*y + 2*y*(p/2) = 1 - 2*y + y*p := by ring
  rw [h1,h2]
  ring

/-- The second active player's required post-value equals his next quit value. -/
theorem matchSecond (p x : ℝ) (h : p + 98*(p-1)*x ≠ 0)
    (hn : p + 98*(p-1)*x - x ≠ 0) :
    1 + 99 * firstHazard p x / (1 - firstHazard p x) =
      1 + 98 * firstHazard (p*98/99) x := by
  unfold firstHazard
  rw [one_sub_div h, ← mul_div_assoc, div_div_div_cancel_right₀ h]
  have hnext : p*98/99 + 98*(p*98/99-1)*x ≠ 0 := by
    intro hz
    apply hn
    linear_combination (99/98) * hz
  congr 1
  rw [← mul_div_assoc, div_eq_div_iff hn hnext]
  ring

#print axioms matchFirst
#print axioms matchSecond

end SimonPairMatching
