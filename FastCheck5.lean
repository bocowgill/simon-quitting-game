module
public import FastPredicates

/-! # Direct kernel checks for the second triple's third role -/

public section
namespace PalomarSimon

theorem fastCenter5 : FastCenterCheck 5 := by decide +kernel
theorem fastSlope5 : FastSlopeCheck 5 := by decide +kernel

#print axioms fastCenter5
#print axioms fastSlope5

end PalomarSimon
