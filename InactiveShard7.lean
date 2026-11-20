module
public import InactiveRows

/-! # Inactive Bellman certificate, phases 448 through 463 -/

@[expose] public section
namespace PalomarSimon.Inactive
set_option maxRecDepth 16000

theorem group28 : groupOK 28 := by decide +kernel

end PalomarSimon.Inactive

