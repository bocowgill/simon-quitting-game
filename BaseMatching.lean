module
public import HazardBounds
public import SeamQuit
public import PairInterior
public import TripleBoundary
import Mathlib.Tactic

/-! # Exact matching of active quit values through one 464-date block

The pair recurrences cover strict interiors; the two triple residuals cover
their outgoing edges. The two last pairs have separately matched successor
rows, with a change of role at phase 463.
-/

public section
namespace SimonBase
open SimonExpr SimonHazardBounds

private theorem index_cases (i : Fin 4) (hi : i.val < 2) : i = 0 ∨ i = 1 := by
  have h : i.val = 0 ∨ i.val = 1 := by omega
  exact h.imp (fun a => Fin.ext a) (fun a => Fin.ext a)

private theorem seamA (u : Fin 6 → ℝ) (sh : Shape u) (i : Fin 4) (hi : i.val < 2) :
    quit u 450 i = cash u 450 i + stay u 450 i * quit u 451 i := by
  have hrow := SimonPairInterior.stageA u 450 (by decide) (by decide)
  rcases index_cases i hi with rfl | rfl
  · obtain ⟨hq,hc,hs⟩ := SimonPairInterior.role0 u 450 _ _ hrow
    rw [hq,hc,hs,zero_add,SimonSeam.first_B _ (sh.pos 1)]
    exact SimonPairStep.rec0 449 (u 4) (sh.pos 4) (sh.upper 4)
  · obtain ⟨hq,hc,hs⟩ := SimonPairInterior.role1 u 450 _ _ hrow
    rw [hq,hc,hs,zero_add,SimonSeam.second_B _ (lt_trans (sh.upper 1) (by norm_num))]
    simpa only [SimonPairStep.first_end] using
      SimonPairStep.rec1 450 449 (u 2) (by decide) (sh.pos 2)

private theorem seamB (u : Fin 6 → ℝ) (sh : Shape u) (i : Fin 4) (hi : i.val < 2) :
    quit u 463 i = cash u 463 i + stay u 463 i * quit u 0 (i+1) := by
  have hrow := SimonPairInterior.stageB u 463 (by decide)
  rcases index_cases i hi with rfl | rfl
  · obtain ⟨hq,hc,hs⟩ := SimonPairInterior.role0 u 463 _ _ hrow
    rw [hq,hc,hs,zero_add,show (0:Fin 4)+1=1 by decide,SimonSeam.first_rotA _ (sh.pos 0)]
    exact SimonPairStep.rec0 11 (u 5) (sh.pos 5) (sh.upper 5)
  · obtain ⟨hq,hc,hs⟩ := SimonPairInterior.role1 u 463 _ _ hrow
    rw [hq,hc,hs,zero_add,show (1:Fin 4)+1=2 by decide,
      SimonSeam.second_rotA _ (lt_trans (sh.upper 0) (by norm_num))]
    simpa only [SimonPairStep.first_end] using
      SimonPairStep.rec1 12 11 (u 3) (by decide) (sh.pos 3)

theorem match_step (u : Fin 6 → ℝ) (sh : Shape u) (hr : ∀ i, residual u i = 0)
    (t : Fin 464) (i : Fin 4) (hi : i.val < 2) :
    quit u t.val i = cash u t.val i + stay u t.val i *
      quit u ((t.val+1)%464) (if t.val = 463 then i+1 else i) := by
  have hb := t.isLt
  by_cases hl : t.val = 463
  · simpa only [hl, ↓reduceIte, show (463+1)%464 = 0 by decide] using seamB u sh i hi
  have hm : (t.val+1)%464 = t.val+1 := Nat.mod_eq_of_lt (by omega)
  simp only [hm, hl, ↓reduceIte]
  by_cases ht : t.val=0 ∨ t.val=451
  · exact SimonTripleBoundary.outgoing u hr
      (fun d j => ⟨(stage_support sh d.val j).1,(stage_support sh d.val j).2.1⟩) t ht i hi
  by_cases ha : t.val=450
  · simpa only [ha] using seamA u sh i hi
  exact SimonPairInterior.match_step u (sh.pos 2) (sh.pos 3) ⟨sh.pos 4,sh.upper 4⟩
    ⟨sh.pos 5,sh.upper 5⟩ t (by omega) i hi

end SimonBase
#print axioms SimonBase.match_step
