module

public import FastRootReduction
public import FastReal
public import FastCheck2
public import FastCheck5
public import ConcreteHazards

/-! # Existence of parameters satisfying Simon's six exact shooting equations -/

public section
namespace PalomarSimon

theorem simon_root : ∃ u ∈ Metric.closedBall center radius, SimonExpr.residual u = 0 := by
  obtain ⟨u, hu, hz⟩ := fast_root_of_global_checks fastCenter2 fastCenter5 fastSlope2 fastSlope5
  exact ⟨u, hu, (SimonFast.residual_eq u (shape_of_mem (mem_box hu))).symm.trans hz⟩

#print axioms simon_root
end PalomarSimon
