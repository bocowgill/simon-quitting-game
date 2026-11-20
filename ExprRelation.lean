module
public import Expressions
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

/-! # Transport of Simon's six equations through arithmetic enclosures

A relation preserving rational constants and four binary operations holds
coordinatewise for the whole calendar, its continuation values, and its six
residuals. No algebraic identities are required of either implementation.
-/

@[expose] public section
namespace SimonExpr

variable {K L : Type*} [RatCast K] [Add K] [Sub K] [Mul K] [Div K]
  [RatCast L] [Add L] [Sub L] [Mul L] [Div L]

structure RelOps (R : K → L → Prop) : Prop where
  lit (q : ℚ) : R (SimonExpr.lit q) (SimonExpr.lit q)
  add {a b : K} {c d : L} : R a c → R b d → R (a+b) (c+d)
  sub {a b : K} {c d : L} : R a c → R b d → R (a-b) (c-d)
  mul {a b : K} {c d : L} : R a c → R b d → R (a*b) (c*d)
  div {a b : K} {c d : L} : R a c → R b d → R (a/b) (c/d)

namespace RelOps
variable {R : K → L → Prop} (H : RelOps R)
  {u : Fin 6 → K} {v : Fin 6 → L}

include H

theorem first (m j : ℕ) {x : K} {y : L} (h : R x y) :
    R (SimonExpr.first m j x) (SimonExpr.first m j y) :=
  H.div h (H.add (H.lit _) (H.mul (H.mul (H.lit _) (H.sub (H.lit _) (H.lit _))) h))

theorem secondHaz (j : ℕ) {x : K} {y : L} (h : R x y) :
    R (SimonExpr.secondHaz j x) (SimonExpr.secondHaz j y) :=
  H.div (H.mul h (H.lit _))
    (H.add (H.sub (H.lit _) (H.mul (H.lit _) h)) (H.mul (H.mul (H.lit _) h) (H.lit _)))

theorem stage (hu : ∀ i, R (u i) (v i)) (t : ℕ) (i : Fin 4) :
    R (SimonExpr.stage u t i) (SimonExpr.stage v t i) := by
  unfold SimonExpr.stage
  split_ifs <;> fin_cases i <;>
    solve_by_elim (maxDepth := 20) only
      [hu, H.lit, H.first, H.secondHaz, H.add, H.sub, H.mul, H.div]

theorem cash (hu : ∀ i, R (u i) (v i)) (t : ℕ) (i : Fin 4) :
    R (SimonExpr.cash u t i) (SimonExpr.cash v t i) :=
  H.mul (H.lit _) (H.stage hu _ _)

theorem stay (hu : ∀ i, R (u i) (v i)) (t : ℕ) (i : Fin 4) :
    R (SimonExpr.stay u t i) (SimonExpr.stay v t i) :=
  H.mul (H.mul (H.sub (H.lit _) (H.stage hu _ _)) (H.sub (H.lit _) (H.stage hu _ _)))
    (H.sub (H.lit _) (H.stage hu _ _))

theorem quit (hu : ∀ i, R (u i) (v i)) (t : ℕ) (i : Fin 4) :
    R (SimonExpr.quit u t i) (SimonExpr.quit v t i) :=
  H.sub (H.sub (H.mul (H.lit _) (H.sub (H.lit _) (H.stage hu _ _))) (H.lit _))
    (H.mul (H.lit _) (H.stay hu _ _))

variable {c s : Row K} {c' s' : Row L}
  (hc : ∀ t i, R (c t i) (c' t i)) (hs : ∀ t i, R (s t i) (s' t i))

include hc hs

theorem transfer (t n : ℕ) (i : Fin 4) :
    R (SimonExpr.transfer c s t n i).1 (SimonExpr.transfer c' s' t n i).1 ∧
    R (SimonExpr.transfer c s t n i).2 (SimonExpr.transfer c' s' t n i).2 := by
  induction n generalizing t with
  | zero => exact ⟨H.lit _, H.lit _⟩
  | succ n ih =>
    obtain ⟨a,b⟩ := ih (t+1)
    exact ⟨H.add (hc _ _) (H.mul (hs _ _) a), H.mul (hs _ _) b⟩

theorem block (i : Fin 4) :
    R (SimonExpr.block c s i).1 (SimonExpr.block c' s' i).1 ∧
    R (SimonExpr.block c s i).2 (SimonExpr.block c' s' i).2 := by
  obtain ⟨a,b⟩ := H.transfer hc hs 0 451 i
  obtain ⟨d,e⟩ := H.transfer hc hs 451 13 i
  exact ⟨H.add a (H.mul b d), H.mul b e⟩

theorem denom : R (SimonExpr.denom c s) (SimonExpr.denom c' s') := by
  let d := fun i => (H.block hc hs i).2
  exact H.sub (H.lit _) (H.mul (H.mul (H.mul (d 0) (d 1)) (d 2)) (d 3))

theorem initial (i : Fin 4) :
    R (SimonExpr.initial c s i) (SimonExpr.initial c' s' i) := by
  let f := fun j => (H.block hc hs j).1
  let g := fun j => (H.block hc hs j).2
  let g2 := H.mul (g i) (g (i+1))
  exact H.div (H.add (H.add (H.add (f i) (H.mul (g i) (f (i+1)))) (H.mul g2 (f (i+2))))
    (H.mul (H.mul g2 (g (i+2))) (f (i+3)))) (H.denom hc hs)

theorem second (i : Fin 4) :
    R (SimonExpr.second c s i) (SimonExpr.second c' s' i) := by
  obtain ⟨a,b⟩ := H.transfer hc hs 451 13 i
  exact H.add a (H.mul b (H.initial hc hs _))

theorem value (t : ℕ) (i : Fin 4) :
    R (SimonExpr.value c s t i) (SimonExpr.value c' s' t i) := by
  unfold SimonExpr.value
  split_ifs
  · obtain ⟨a,b⟩ := H.transfer hc hs t (451-t) i
    exact H.add a (H.mul b (H.second hc hs _))
  · obtain ⟨a,b⟩ := H.transfer hc hs t (464-t) i
    exact H.add a (H.mul b (H.initial hc hs _))

omit hc hs

theorem odds {x : K} {y : L} (h : R x y) : R (SimonExpr.odds x) (SimonExpr.odds y) :=
  H.div h (H.sub (H.lit _) h)

theorem residualTriple (hu : ∀ i, R (u i) (v i)) (t : ℕ) {w : K} {w' : L}
    (hw : R w w') (i : Fin 3) :
    R (SimonExpr.residualTriple u t w i) (SimonExpr.residualTriple v t w' i) := by
  let p := H.stage hu t
  let q := H.stage hu (t+1)
  let a := H.odds (p 0)
  let b := H.odds (p 1)
  let c := H.odds (p 2)
  fin_cases i
  · exact H.sub (H.sub (H.sub (H.mul (H.lit _) (q 1)) b) c) (H.mul (H.mul (H.lit _) b) c)
  · exact H.sub (H.sub (H.mul (H.sub (H.lit _) c) a) c) (H.mul (H.lit _) (q 0))
  · exact H.sub (H.add (H.lit _) (H.mul (H.lit _) (H.sub (H.add (p 0) (p 1)) (H.mul (p 0) (p 1))))) hw

theorem residual (hu : ∀ i, R (u i) (v i)) (i : Fin 6) :
    R (SimonExpr.residual u i) (SimonExpr.residual v i) := by
  have ha := H.residualTriple hu 0 (H.initial (H.cash hu) (H.stay hu) 2)
  have hb := H.residualTriple hu 451 (H.second (H.cash hu) (H.stay hu) 2)
  fin_cases i
  · exact ha 0
  · exact ha 1
  · exact ha 2
  · exact hb 0
  · exact hb 1
  · exact hb 2

#print axioms residual
#print axioms value
end RelOps
end SimonExpr
