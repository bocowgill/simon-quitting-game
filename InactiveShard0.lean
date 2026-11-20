module
public import InactiveRows

/-! # Inactive Bellman certificate, phases 0 through 63 -/

@[expose] public section
namespace PalomarSimon.Inactive
set_option maxRecDepth 16000

theorem group0 : groupOK 0 := by decide +kernel

theorem group1 : groupOK 1 := by decide +kernel

theorem group2 : groupOK 2 := by decide +kernel

theorem group3 : groupOK 3 := by decide +kernel

end PalomarSimon.Inactive

