module

public import FastJet
public import FastPredicates


/-! # Compact residual checks imply a zero of the compact system

The two global value equations use closed pair transfers. In the four local
equations the compact and original arithmetic expressions coincide.
-/

@[expose] public section
namespace PalomarSimon

set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

theorem fast_root_of_checks (hc : ∀ i, FastCenterCheck i) (hs : ∀ i, FastSlopeCheck i) :
    ∃ w ∈ Metric.closedBall center radius, SimonFast.residual w = 0 := by
  apply exists_root_of_simon_envelopes SimonFast.residual
  · intro i
    have hi := hc i
    unfold FastCenterCheck fastCenterCheckBool at hi
    split at hi
    · exact Bool.noConfusion hi
    · rename_i v hv
      apply (of_decide_eq_true hi : Encloses _ v).mem
      exact checkedIntervalOps.fast_residual (fun j ↦ Checked.lift_some (center_mem j)) i v hv
  · intro x hx y hy
    have existsJet (i : Fin 6) : ∃ v : Jet 6,
        (SimonFast.residual (checkedVariables box) i).result = some v ∧
        ∀ j, Encloses (secantEnvelope i j) (v.d j) := by
      have hi := hs i
      unfold FastSlopeCheck fastSlopeCheckBool at hi
      split at hi
      · exact Bool.noConfusion hi
      · rename_i v hv
        exact ⟨v,hv,of_decide_eq_true hi⟩
    choose v hv hmem using existsJet
    obtain ⟨J, hJ, hbounds⟩ := fast_residual_secants box (mem_box hx) (mem_box hy) v hv
    exact ⟨J,hJ,fun i j ↦ (hmem i j).mem (hbounds i j)⟩

theorem fast_root_of_global_checks
    (hc2 : FastCenterCheck 2) (hc5 : FastCenterCheck 5)
    (hs2 : FastSlopeCheck 2) (hs5 : FastSlopeCheck 5) :
    ∃ w ∈ Metric.closedBall center radius, SimonFast.residual w = 0 := by
  apply fast_root_of_checks
  · intro i
    fin_cases i
    · decide +kernel
    · decide +kernel
    · exact hc2
    · decide +kernel
    · decide +kernel
    · exact hc5
  · intro i
    fin_cases i
    · decide +kernel
    · decide +kernel
    · exact hs2
    · decide +kernel
    · decide +kernel
    · exact hs5

#print axioms fast_root_of_global_checks
end PalomarSimon
