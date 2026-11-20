module
public import InactiveRows

/-! # Inactive Bellman certificate, phases 64 through 127 -/

@[expose] public section
namespace PalomarSimon.Inactive
set_option maxRecDepth 16000

theorem group4 : groupOK 4 := by decide +kernel

theorem group5 : groupOK 5 := by decide +kernel

theorem group6 : groupOK 6 := by decide +kernel

theorem group7 : groupOK 7 := by decide +kernel

end PalomarSimon.Inactive

