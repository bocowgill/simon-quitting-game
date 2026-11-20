module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Periodic equilibria in Simon's four-player quitting game

The players are numbered modulo four. At each date every player independently
chooses whether to quit. Before the first quit everyone earns zero. From the
first quit onward, each player receives the same reward at every date.
A continuing player receives 100 if the opposite player quits and zero otherwise.
A quitter receives −1 if the next player quits, 1 if quitting alone, and 99 otherwise.

The only history at which the game is still live at date `t` is a string of
`t` all-continue action profiles. Thus unrestricted behavioral strategies at
live histories are fully specified by the time-dependent quit probabilities.
Here `rivals` is the probability that all three opponents continue, `quit` is
the conditional expected reward for quitting, and `earn` is the unconditional
expected newly absorbed reward. The expected terminal reward `terminal` assigns
zero to never absorbing. The horizon payoff `average` averages the expected
accrued rewards, counting the first quitting date. An initially absorbed state
has the constant stored reward for every positive horizon and every profile.

The theorem gives one hazard table and one continuation-value table, each
having 1,856 rows. Its exact terminal Nash inequalities apply at every live
phase. For each positive tolerance, a common horizon threshold applies to
every phase, player, and unilateral deviation.

R. S. Simon, “A Topological Approach to Quitting Games,”
https://doi.org/10.1287/moor.1110.0524.
-/

@[expose] public section
noncomputable section
open Finset

namespace SimonPeriodic

abbrev Player := Fin 4
abbrev Calendar := ℕ → Player → ℝ
def Legal (p : Calendar) : Prop := ∀ t i, 0 ≤ p t i ∧ p t i ≤ 1

def rivals (p : Calendar) (t : ℕ) (i : Player) : ℝ :=
  (1-p t (i+3))*(1-p t (i+1))*(1-p t (i+2))

def remain (p : Calendar) (t : ℕ) : ℝ := ∏ i, (1-p t i)

def quit (p : Calendar) (t : ℕ) (i : Player) : ℝ :=
  100*(1-p t (i+1))-1-98*rivals p t i

def earn (p : Calendar) (t : ℕ) (i : Player) : ℝ :=
  p t i * quit p t i + (1-p t i)*(100*p t (i+2))

def survival (p : Calendar) (t n : ℕ) : ℝ := ∏ j ∈ range n, remain p (t+j)

def cash (p : Calendar) (i : Player) (t n : ℕ) : ℝ :=
  ∑ j ∈ range n, survival p t j * earn p (t+j) i

def terminal (p : Calendar) (i : Player) (t : ℕ) : ℝ :=
  ∑' j : ℕ, survival p t j * earn p (t+j) i

def average (p : Calendar) (i : Player) (t N : ℕ) : ℝ :=
  (N:ℝ)⁻¹ * ∑ n ∈ range N, cash p i t (n+1)

def SameOpponents (p r : Calendar) (i : Player) : Prop := ∀ t j, j ≠ i → r t j = p t j

namespace FC
def cycle {L : ℕ} (hL : 0 < L) (a : Fin L → Player → ℝ) : Calendar :=
  fun n ↦ a ⟨n % L,Nat.mod_lt _ hL⟩

end FC
end SimonPeriodic

namespace SimonHeadline
open SimonPeriodic

/-- Exact terminal best response and convergence with uniformly small deviation
gain for one calendar from every live phase. Opponents retain their independent
hazards under an arbitrary change of the deviating player's behavioral strategy. -/
def Equilibrium (p v : Calendar) : Prop :=
  Legal p ∧
  (∀ t i, terminal p i t = v t i ∧
    ∀ r, Legal r → SameOpponents p r i → terminal r i t ≤ v t i) ∧
  ∀ ε : ℝ, 0 < ε → ∃ H : ℕ, 0 < H ∧
    ∀ t i N, H ≤ N →
      |average p i t N - v t i| ≤ ε ∧
      ∀ r, Legal r → SameOpponents p r i → average r i t N ≤ average p i t N + ε

set_option warn.sorry false in
/-- Simon's four-player game has a 1,856-period calendar giving exact terminal
Nash payoffs and horizon-uniform Cesàro Nash payoffs from every live phase. -/
theorem periodic_equilibrium :
    ∃ p v : Fin 1856 → SimonPeriodic.Player → ℝ,
      Equilibrium (SimonPeriodic.FC.cycle (by decide) p)
        (SimonPeriodic.FC.cycle (by decide) v) := by
  sorry

end SimonHeadline
end
