module
public import FastPair

/-! # Compact evaluation of the original six residuals

Each pair segment is evaluated by its affine transfer. All operations from
the start of a triple to the six residuals retain their original order.
-/

@[expose] public section
namespace SimonFast
open SimonExpr

variable {K : Type*} [RatCast K] [Add K] [Sub K] [Mul K] [Div K]

/-- The first triple starts the long half; the second starts the short half. -/
def half (u : Fin 6 → K) (short : Bool) (i : Fin 4) : K × K :=
  let t := if short then 451 else 0
  let a := if short then
      pair 12 (first 12 0 (u 3)) (secondHaz 0 (u 5)) i
    else pair 450 (first 450 0 (u 2)) (secondHaz 0 (u 4)) i
  (cash u t i + stay u t i * a.1, stay u t i * a.2)

def full (u : Fin 6 → K) (i : Fin 4) : K × K :=
  let a := half u false i
  let b := half u true i
  (a.1+a.2*b.1,a.2*b.2)

def denominator (u : Fin 6 → K) : K :=
  let d := fun i => (full u i).2
  lit 1-d 0*d 1*d 2*d 3

def start (u : Fin 6 → K) (i : Fin 4) : K :=
  let f := full u
  ((f i).1 + (f i).2*(f (i+1)).1 + ((f i).2*(f (i+1)).2)*(f (i+2)).1 +
    ((f i).2*(f (i+1)).2*(f (i+2)).2)*(f (i+3)).1)/denominator u

def middle (u : Fin 6 → K) (i : Fin 4) : K :=
  let b := half u true i
  b.1+b.2*start u (i+1)

def residual (u : Fin 6 → K) : Fin 6 → K :=
  let a := residualTriple u 0 (start u 2)
  let b := residualTriple u 451 (middle u 2)
  ![a 0,a 1,a 2,b 0,b 1,b 2]

end SimonFast
