module
public import FastExpr
public import RootChecks

/-! # Interval tests for the residual calculated by geometric sums -/

@[expose] public section
namespace PalomarSimon

def fastCenterCheckBool (i : Fin 6) : Bool :=
  match (SimonFast.residual checkedCenter i).result with
  | none => false
  | some v => decide (Encloses (residualEnvelope i) v)

def fastSlopeCheckBool (i : Fin 6) : Bool :=
  match (SimonFast.residual (checkedVariables box) i).result with
  | none => false
  | some v => decide (∀ j, Encloses (secantEnvelope i j) (v.d j))

abbrev FastCenterCheck (i : Fin 6) : Prop := fastCenterCheckBool i = true
abbrev FastSlopeCheck (i : Fin 6) : Prop := fastSlopeCheckBool i = true

end PalomarSimon
