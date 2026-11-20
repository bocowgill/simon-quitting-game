module
public import PairStep
import Mathlib.Tactic

/-! # Active Bellman matching inside an adjacent-pair run -/

public section
namespace SimonPairInterior
open SimonExpr SimonPairStep

theorem role0 (u : Fin 6 → ℝ) (t : ℕ) (x y : ℝ) (h : stage u t = ![x,y,0,0]) :
    quit u t 0 = 1-2*y ∧ cash u t 0 = 0 ∧ stay u t 0 = 1-y := by
  simp only [quit, cash, stay, h]
  rw [show (![x,y,0,0] : Fin 4 → ℝ) (0+1) = y by rfl]
  rw [show (![x,y,0,0] : Fin 4 → ℝ) (0+2) = 0 by rfl]
  rw [show (![x,y,0,0] : Fin 4 → ℝ) (0+3) = 0 by rfl]
  norm_num [lit]
  ring

theorem role1 (u : Fin 6 → ℝ) (t : ℕ) (x y : ℝ) (h : stage u t = ![x,y,0,0]) :
    quit u t 1 = 1+98*x ∧ cash u t 1 = 0 ∧ stay u t 1 = 1-x := by
  simp only [quit, cash, stay, h]
  rw [show (![x,y,0,0] : Fin 4 → ℝ) (1+1) = 0 by rfl]
  rw [show (![x,y,0,0] : Fin 4 → ℝ) (1+2) = 0 by rfl]
  rw [show (![x,y,0,0] : Fin 4 → ℝ) (1+3) = x by rfl]
  norm_num [lit]
  ring

theorem stageA (u : Fin 6 → ℝ) (t : ℕ) (h : 0 < t) (ha : t < 451) :
    stage u t = ![first 450 (t-1) (u 2),secondHaz (t-1) (u 4),0,0] := by
  simp [stage, h.ne', ha, lit]

theorem stageB (u : Fin 6 → ℝ) (t : ℕ) (h : 451 < t) :
    stage u t = ![first 12 (t-452) (u 3),secondHaz (t-452) (u 5),0,0] := by
  have ht : t ≠ 0 := by omega
  simp [stage, ht, h.ne', not_lt.mpr h.le, lit]

private theorem within (u : Fin 6 → ℝ) (t m j : ℕ) (x y : ℝ) (hx : 0 < x)
    (hy : 0 < y ∧ y < 1/2) (hj : j < m)
    (h : stage u t = ![first m j x,secondHaz j y,0,0])
    (h' : stage u (t+1) = ![first m (j+1) x,secondHaz (j+1) y,0,0])
    (i : Fin 4) (hi : i.val < 2) :
    quit u t i = cash u t i + stay u t i*quit u (t+1) i := by
  have hc : i = 0 ∨ i = 1 := by
    rcases (show i.val = 0 ∨ i.val = 1 by omega) with hi | hi
    · exact Or.inl (Fin.ext hi)
    · exact Or.inr (Fin.ext hi)
  rcases hc with rfl | rfl
  · obtain ⟨hq, hc, hs⟩ := role0 _ _ _ _ h
    rw [hq, hc, hs, (role0 _ _ _ _ h').1, zero_add]
    exact rec0 _ _ hy.1 hy.2
  · obtain ⟨hq, hc, hs⟩ := role1 _ _ _ _ h
    rw [hq, hc, hs, (role1 _ _ _ _ h').1, zero_add]
    exact rec1 _ _ _ hj hx

theorem match_step (u : Fin 6 → ℝ) (hxA : 0 < u 2) (hxB : 0 < u 3)
    (hyA : 0 < u 4 ∧ u 4 < 1/2) (hyB : 0 < u 5 ∧ u 5 < 1/2)
    (t : Fin 464) (ht : (0 < t.val ∧ t.val < 450) ∨ (451 < t.val ∧ t.val < 463))
    (i : Fin 4) (hi : i.val < 2) :
    quit u t.val i = cash u t.val i + stay u t.val i * quit u (t.val+1) i := by
  rcases ht with ha | hb
  · apply within u _ 450 (t.val-1) _ _ hxA hyA (by omega) (stageA _ _ ha.1 (by omega)) _ _ hi
    rw [← show t.val+1-1 = t.val-1+1 by omega]
    exact stageA _ _ (by omega) (by omega)
  · apply within u _ 12 (t.val-452) _ _ hxB hyB (by omega) (stageB _ _ hb.1) _ _ hi
    rw [← show t.val+1-452 = t.val-452+1 by omega]
    exact stageB _ _ (by omega)

end SimonPairInterior
#print axioms SimonPairInterior.match_step
