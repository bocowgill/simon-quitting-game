module
public import InactiveRows

/-! # Inactive Bellman certificate, phases 192 through 255 -/

@[expose] public section
namespace PalomarSimon.Inactive
set_option maxRecDepth 16000

theorem group12 : groupOK 12 := by decide +kernel

theorem group13 : groupOK 13 := by decide +kernel

theorem group14 : groupOK 14 := by decide +kernel

theorem group15 : groupOK 15 := by decide +kernel

end PalomarSimon.Inactive

