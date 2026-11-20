module
public import InactiveRows

/-! # Inactive Bellman certificate, phases 256 through 319 -/

@[expose] public section
namespace PalomarSimon.Inactive
set_option maxRecDepth 16000

theorem group16 : groupOK 16 := by decide +kernel

theorem group17 : groupOK 17 := by decide +kernel

theorem group18 : groupOK 18 := by decide +kernel

theorem group19 : groupOK 19 := by decide +kernel

end PalomarSimon.Inactive

