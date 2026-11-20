module
public import Interval
public import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Proposed coarse enclosures for Simon's six shooting equations -/

@[expose] public section
namespace PalomarSimon

def scaledEndpoints (lo hi : ℤ) (bits : ℕ) : Interval :=
  ⟨lo * 2^(768-bits), hi * 2^(768-bits)⟩

def residualEnvelope : Fin 6 → Interval :=
  ![scaledEndpoints (3) (6) 56, scaledEndpoints (27) (30) 56, scaledEndpoints (6362) (6365) 56, scaledEndpoints (15) (18) 56, scaledEndpoints (3264) (3267) 56, scaledEndpoints (3252) (3255) 56]

def secantEnvelope : Matrix (Fin 6) (Fin 6) Interval :=
  ![![scaledEndpoints (-6737987) (-6737984) 12, scaledEndpoints (-1) (1) 12, scaledEndpoints (-1) (1) 12, scaledEndpoints (-13776) (-13773) 12, scaledEndpoints (8190) (8194) 12, scaledEndpoints (-325) (-322) 12], ![scaledEndpoints (204820) (204823) 12, scaledEndpoints (-1) (1) 12, scaledEndpoints (-110) (-107) 12, scaledEndpoints (-1) (1) 12, scaledEndpoints (-1) (1) 12, scaledEndpoints (-11) (-8) 12], ![scaledEndpoints (-381986) (-381983) 12, scaledEndpoints (171277) (171280) 12, scaledEndpoints (-211268) (-211265) 12, scaledEndpoints (534149) (534152) 12, scaledEndpoints (549194) (549197) 12, scaledEndpoints (20710) (20713) 12], ![scaledEndpoints (-1) (1) 12, scaledEndpoints (-519149) (-519146) 12, scaledEndpoints (-1) (1) 12, scaledEndpoints (-1) (1) 12, scaledEndpoints (-2) (1) 12, scaledEndpoints (8190) (8194) 12], ![scaledEndpoints (-1) (1) 12, scaledEndpoints (29644) (29647) 12, scaledEndpoints (456709) (456712) 12, scaledEndpoints (-25335) (-25332) 12, scaledEndpoints (-1) (1) 12, scaledEndpoints (-1) (1) 12], ![scaledEndpoints (610960) (610963) 12, scaledEndpoints (13644516) (13644519) 12, scaledEndpoints (8248) (8251) 12, scaledEndpoints (-50848) (-50845) 12, scaledEndpoints (-32332) (-32329) 12, scaledEndpoints (458220) (458223) 12]]

end PalomarSimon
