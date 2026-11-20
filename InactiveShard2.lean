module
public import InactiveRows

/-! # Inactive Bellman certificate, phases 128 through 191 -/

@[expose] public section
namespace PalomarSimon.Inactive
set_option maxRecDepth 16000

theorem group8 : groupOK 8 := by decide +kernel

theorem group9 : groupOK 9 := by decide +kernel

theorem group10 : groupOK 10 := by decide +kernel

theorem group11 : groupOK 11 := by decide +kernel

end PalomarSimon.Inactive

