module

public import ConcreteReduction
public import ConcreteInactive
public import SimonRoot

/-! # A 1,856-period equilibrium in Simon's four-player quitting game

The witness comes from two pair runs of lengths 450 and 12, separated by
three-player mixing phases. Each of four consecutive blocks rotates the roles.
-/

public section
namespace SimonHeadline

open SimonExpr SimonAffine PalomarSimon

/-- One periodic calendar is terminal Nash from every phase and satisfies the
uniform Nash inequalities for every sufficiently large finite horizon. -/
theorem periodic_equilibrium :
    ∃ p v : Fin 1856 → SimonPeriodic.Player → ℝ,
      Equilibrium (SimonPeriodic.FC.cycle (by decide) p) (SimonPeriodic.FC.cycle (by decide) v) := by
  obtain ⟨u, hu, hr⟩ := simon_root
  exact ⟨lift (stage u), lift (value (cash u) (stay u)),
    ConcreteReduction.equilibrium hu hr (Inactive.inactive hu)⟩

#print axioms periodic_equilibrium
end SimonHeadline
