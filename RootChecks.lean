module
public import GuardedJet
public import GuardedInterval
public import RootEnvelope

/-! # Scalar predicates whose verification places an exact zero in Simon's box -/

@[expose] public section
namespace PalomarSimon

def checkedCenter (i : Fin 6) : Checked Interval := Checked.some (pointBox i)

def centerCheckBool (i : Fin 6) : Bool :=
  match (SimonExpr.residual checkedCenter i).result with
  | none => false
  | some v => decide (Encloses (residualEnvelope i) v)

def slopeCheckBool (i : Fin 6) : Bool :=
  match (SimonExpr.residual (checkedVariables box) i).result with
  | none => false
  | some v => decide (∀ j, Encloses (secantEnvelope i j) (v.d j))

abbrev CenterCheck (i : Fin 6) : Prop := centerCheckBool i = true
abbrev SlopeCheck (i : Fin 6) : Prop := slopeCheckBool i = true

theorem exists_root_of_checks (hc : ∀ i, CenterCheck i) (hs : ∀ i, SlopeCheck i) :
    ∃ w ∈ Metric.closedBall center radius, SimonExpr.residual w = 0 := by
  apply exists_root_of_simon_envelopes SimonExpr.residual
  · intro i
    have hi := hc i
    unfold CenterCheck centerCheckBool at hi
    split at hi
    · exact Bool.noConfusion hi
    · rename_i v hv
      apply (of_decide_eq_true hi : Encloses _ v).mem
      exact checkedIntervalOps.residual (fun j ↦ Checked.lift_some (center_mem j)) i v hv
  · intro x hx y hy
    have existsJet (i : Fin 6) : ∃ v : Jet 6,
        (SimonExpr.residual (checkedVariables box) i).result = some v ∧
        ∀ j, Encloses (secantEnvelope i j) (v.d j) := by
      have hi := hs i
      unfold SlopeCheck slopeCheckBool at hi
      split at hi
      · exact Bool.noConfusion hi
      · rename_i v hv
        exact ⟨v,hv,of_decide_eq_true hi⟩
    choose v hv hmem using existsJet
    obtain ⟨J, hJ, hbounds⟩ := residual_secants box (mem_box hx) (mem_box hy) v hv
    exact ⟨J,hJ,fun i j ↦ (hmem i j).mem (hbounds i j)⟩

#print axioms exists_root_of_checks
end PalomarSimon
