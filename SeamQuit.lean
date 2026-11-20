module
public import Expressions
public import Triple
import Mathlib.Tactic

/-! # Quit values at the ends of the two pair runs

Upon crossing the end of the base block, roles zero and one become roles one
and two. These four identities include that change of role.
-/

public section
namespace SimonSeam
open SimonExpr

private theorem quit0 (u : Fin 6 → ℝ) (t : ℕ) :
    quit u t 0 = SimonTriple.quit (stage u t 1) (stage u t 2) (stage u t 3) := by
  simp only [quit,stay,SimonTriple.quit,SimonTriple.stay,lit,Rat.cast_ofNat,Rat.cast_one]
  rfl

private theorem quit1 (u : Fin 6 → ℝ) (t : ℕ) :
    quit u t 1 = SimonTriple.quit (stage u t 2) (stage u t 3) (stage u t 0) := by
  simp only [quit,stay,SimonTriple.quit,SimonTriple.stay,lit,Rat.cast_ofNat,Rat.cast_one]
  rfl

private theorem quit2 (u : Fin 6 → ℝ) (t : ℕ) :
    quit u t 2 = SimonTriple.quit (stage u t 3) (stage u t 0) (stage u t 1) := by
  simp only [quit,stay,SimonTriple.quit,SimonTriple.stay,lit,Rat.cast_ofNat,Rat.cast_one]
  rfl

theorem first_B (u : Fin 6 → ℝ) (hz : 0 < u 1) :
    quit u 451 0 = 1 - 2*secondHaz 450 (u 4) := by
  rw [quit0]
  simpa [stage,lit] using SimonTriple.beforeBFirst (u 1) (secondHaz 450 (u 4)) (by positivity)

theorem second_B (u : Fin 6 → ℝ) (hz : u 1 < 1) :
    quit u 451 1 = 1 + 98*u 2 := by
  rw [quit1]
  simpa [stage,lit] using SimonTriple.beforeBSecond (u 1) (u 2) (sub_pos.mpr hz).ne'

theorem first_rotA (u : Fin 6 → ℝ) (hx : 0 < u 0) :
    quit u 0 1 = 1 - 2*secondHaz 12 (u 5) := by
  rw [quit1]
  simpa [stage,lit] using SimonTriple.beforeRotatedAFirst (u 0) (secondHaz 12 (u 5)) (by positivity)

theorem second_rotA (u : Fin 6 → ℝ) (hx : u 0 < 1) :
    quit u 0 2 = 1 + 98*u 3 := by
  rw [quit2]
  simpa [stage,lit] using SimonTriple.beforeRotatedASecond (u 0) (u 3) (sub_pos.mpr hx).ne'

end SimonSeam
#print axioms SimonSeam.first_rotA
#print axioms SimonSeam.second_rotA
