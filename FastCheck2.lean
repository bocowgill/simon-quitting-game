module
public import FastPredicates

/-! # Center and secant bounds for the third shooting equation -/

@[expose] public section
namespace PalomarSimon

set_option maxRecDepth 4096
set_option exponentiation.threshold 2048

theorem fastCenter2 : FastCenterCheck 2 := by decide +kernel

theorem fastSlope2 : FastSlopeCheck 2 := by decide +kernel

#print axioms fastCenter2
#print axioms fastSlope2
end PalomarSimon
