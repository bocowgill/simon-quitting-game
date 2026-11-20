module
public import Guarded
public import ExprRelation

/-! # Soundness of scalar interval evaluation of the calendar -/

@[expose] public section
namespace PalomarSimon

theorem checkedIntervalOps : SimonExpr.RelOps (Checked.Lift Interval.Mem) where
  lit q := Checked.lift_some (mem_ratCast q)
  add := Checked.lift_binary (· + ·) (· + ·) Interval.mem_add
  sub := Checked.lift_binary (· - ·) (· - ·) Interval.mem_sub
  mul := Checked.lift_binary (· * ·) (· * ·) Interval.mem_mul
  div := Checked.lift_div Interval.mem_div

end PalomarSimon
