module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Real.Basic

/-! # The six scalar equations for Simon's two-triple calendar

The same straight-line operations can be evaluated on reals and on checked
enclosures. Rational powers in the pair phases are constants.
-/

@[expose] public section
namespace SimonExpr

abbrev Row (K : Type*) := ℕ → Fin 4 → K
variable {K : Type*} [RatCast K] [Add K] [Sub K] [Mul K] [Div K]

def lit (q : ℚ) : K := (q : K)

def first (m j : ℕ) (x : K) : K :=
  let p : K := lit ((99/98 : ℚ)^(m-j))
  x / (p + lit 98 * (p-lit 1) * x)

def secondHaz (j : ℕ) (y : K) : K :=
  let p : K := lit ((1/2 : ℚ)^j)
  y * p / (lit 1 - lit 2*y + lit 2*y*p)

def stage (u : Fin 6 → K) (t : ℕ) : Fin 4 → K :=
  if t = 0 then
    ![u 0, (u 3-u 0)/(lit 1-u 0),
      (lit 49*u 0+secondHaz 12 (u 5))/(lit 1+lit 49*u 0), lit 0]
  else if t < 451 then
    ![first 450 (t-1) (u 2), secondHaz (t-1) (u 4), lit 0, lit 0]
  else if t = 451 then
    ![(u 2+u 1/lit 49)/(lit 1-u 1),
      (secondHaz 450 (u 4)+lit 49*u 1)/(lit 1+lit 49*u 1), u 1, lit 0]
  else
    ![first 12 (t-452) (u 3), secondHaz (t-452) (u 5), lit 0, lit 0]

def cash (u : Fin 6 → K) (t : ℕ) (i : Fin 4) : K :=
  lit 100 * stage u t (i+2)

def stay (u : Fin 6 → K) (t : ℕ) (i : Fin 4) : K :=
  (lit 1 - stage u t (i+1)) * (lit 1 - stage u t (i+2)) *
  (lit 1 - stage u t (i+3))

def quit (u : Fin 6 → K) (t : ℕ) (i : Fin 4) : K :=
  lit 100 * (lit 1 - stage u t (i+1)) - lit 1 - lit 98 * stay u t i

def transfer (c s : Row K) (t : ℕ) : ℕ → Fin 4 → K × K
  | 0, _ => (lit 0, lit 1)
  | n+1, i =>
    let a := transfer c s (t+1) n i
    (c t i+s t i*a.1,s t i*a.2)

def block (c s : Row K) (i : Fin 4) : K × K :=
  let a := transfer c s 0 451 i
  let b := transfer c s 451 13 i
  (a.1+a.2*b.1,a.2*b.2)

def denom (c s : Row K) : K :=
  let d := fun i => (block c s i).2
  lit 1 - d 0*d 1*d 2*d 3

def initial (c s : Row K) (i : Fin 4) : K :=
  let b := block c s
  ((b i).1 + (b i).2*(b (i+1)).1 +
    ((b i).2*(b (i+1)).2)*(b (i+2)).1 +
    ((b i).2*(b (i+1)).2*(b (i+2)).2)*(b (i+3)).1) / denom c s

def second (c s : Row K) (i : Fin 4) : K :=
  let b := transfer c s 451 13 i
  b.1+b.2*initial c s (i+1)

def value (c s : Row K) (t : ℕ) (i : Fin 4) : K :=
  if t < 451 then
    let a := transfer c s t (451-t) i
    a.1+a.2*second c s i
  else
    let b := transfer c s t (464-t) i
    b.1+b.2*initial c s (i+1)

def odds (x : K) : K := x / (lit 1-x)

def residualTriple (u : Fin 6 → K) (t : ℕ) (v : K) : Fin 3 → K :=
  let p := stage u t
  let a := odds (p 0)
  let b := odds (p 1)
  let c := odds (p 2)
  ![lit 2 * stage u (t+1) 1-b-c-lit 101*b*c,
    (lit 99-c)*a-c-lit 98*stage u (t+1) 0,
    lit 1+lit 98*(p 0+p 1-p 0*p 1)-v]

def residual (u : Fin 6 → K) : Fin 6 → K :=
  let a := residualTriple u 0 (initial (cash u) (stay u) 2)
  let b := residualTriple u 451 (second (cash u) (stay u) 2)
  ![a 0,a 1,a 2,b 0,b 1,b 2]

end SimonExpr
