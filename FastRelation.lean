module

public import FastExpr
public import ExprRelation

/-! # Transport of closed pair transfers through interval arithmetic -/

@[expose] public section
namespace SimonExpr.RelOps

variable {K L : Type*} [RatCast K] [Add K] [Sub K] [Mul K] [Div K]
    [RatCast L] [Add L] [Sub L] [Mul L] [Div L] {R : K → L → Prop}
    (H : RelOps R)
include H

theorem fast_pair (n : ℕ) {x y : K} {x' y' : L} (hx : R x x') (hy : R y y')
    (i : Fin 4) :
    R (SimonFast.pair n x y i).1 (SimonFast.pair n x' y' i).1 ∧
    R (SimonFast.pair n x y i).2 (SimonFast.pair n x' y' i).2 := by
  have xc := H.mul (H.lit 98) hx
  have yc := H.mul (H.lit 2) hy
  have X := H.sub (H.add (H.lit 1) xc) (H.mul xc (H.lit (SimonFast.a^n)))
  have Y := H.add (H.sub (H.lit 1) yc) (H.mul yc (H.lit (SimonFast.b^n)))
  have W := H.mul (H.mul (H.lit 100) hx)
    (H.add (H.mul (H.sub (H.lit 1) yc) (H.lit (SimonFast.geom SimonFast.a n)))
      (H.mul yc (H.lit (SimonFast.geom (SimonFast.a*SimonFast.b) n))))
  have V := H.mul (H.mul (H.lit 100) hy)
    (H.sub (H.mul (H.add (H.lit 1) xc) (H.lit (SimonFast.geom SimonFast.b n)))
      (H.mul xc (H.lit (SimonFast.geom (SimonFast.a*SimonFast.b) n))))
  fin_cases i
  · exact ⟨H.lit 0,Y⟩
  · exact ⟨H.lit 0,X⟩
  · exact ⟨W,H.mul X Y⟩
  · exact ⟨V,H.mul X Y⟩

variable {u : Fin 6 → K} {v : Fin 6 → L} (hu : ∀ i, R (u i) (v i))
include hu

theorem fast_half (b : Bool) (i : Fin 4) :
    R (SimonFast.half u b i).1 (SimonFast.half v b i).1 ∧
    R (SimonFast.half u b i).2 (SimonFast.half v b i).2 := by
  cases b
  · obtain ⟨a,d⟩ := H.fast_pair 450 (H.first 450 0 (hu 2)) (H.secondHaz 0 (hu 4)) i
    exact ⟨H.add (H.cash hu 0 i) (H.mul (H.stay hu 0 i) a), H.mul (H.stay hu 0 i) d⟩
  · obtain ⟨a,d⟩ := H.fast_pair 12 (H.first 12 0 (hu 3)) (H.secondHaz 0 (hu 5)) i
    exact ⟨H.add (H.cash hu 451 i) (H.mul (H.stay hu 451 i) a), H.mul (H.stay hu 451 i) d⟩

theorem fast_full (i : Fin 4) :
    R (SimonFast.full u i).1 (SimonFast.full v i).1 ∧
    R (SimonFast.full u i).2 (SimonFast.full v i).2 := by
  obtain ⟨a,b⟩ := H.fast_half hu false i
  obtain ⟨c,d⟩ := H.fast_half hu true i
  exact ⟨H.add a (H.mul b c), H.mul b d⟩

theorem fast_denominator : R (SimonFast.denominator u) (SimonFast.denominator v) := by
  let d := fun i ↦ (H.fast_full hu i).2
  exact H.sub (H.lit 1) (H.mul (H.mul (H.mul (d 0) (d 1)) (d 2)) (d 3))

theorem fast_start (i : Fin 4) : R (SimonFast.start u i) (SimonFast.start v i) := by
  let f := fun j ↦ (H.fast_full hu j).1
  let g := fun j ↦ (H.fast_full hu j).2
  let g2 := H.mul (g i) (g (i+1))
  exact H.div (H.add (H.add (H.add (f i) (H.mul (g i) (f (i+1)))) (H.mul g2 (f (i+2))))
    (H.mul (H.mul g2 (g (i+2))) (f (i+3)))) (H.fast_denominator hu)

theorem fast_middle (i : Fin 4) : R (SimonFast.middle u i) (SimonFast.middle v i) := by
  obtain ⟨a,b⟩ := H.fast_half hu true i
  exact H.add a (H.mul b (H.fast_start hu _))

theorem fast_residual (i : Fin 6) : R (SimonFast.residual u i) (SimonFast.residual v i) := by
  have ha := H.residualTriple hu 0 (H.fast_start hu 2)
  have hb := H.residualTriple hu 451 (H.fast_middle hu 2)
  fin_cases i
  · exact ha 0
  · exact ha 1
  · exact ha 2
  · exact hb 0
  · exact hb 1
  · exact hb 2
  
end SimonExpr.RelOps
