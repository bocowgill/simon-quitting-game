module

public import ActiveRuns
public import Affine
public import SimonCalendar

/-! # From the base block to all incentive tests in Simon's finite calendar

The role changes at every block boundary, including the end of phase 1855.
The third active role at a triple supplies the terminal condition for the
active-run recursion.
-/

@[expose] public section
namespace SimonTable

open SimonExpr SimonAffine

noncomputable section

abbrev Table := Fin 1856 → Fin 4 → ℝ

/-- The premises for the finite-calendar equilibrium theorem. -/
structure FiniteData (p v : Table) : Prop where
  legal : ∀ t i, 0 ≤ p t i ∧ p t i ≤ 1
  proper : ∀ i, (∏ k ∈ Finset.range 1856,
    SimonPeriodic.rivals (SimonPeriodic.FC.cycle (by decide) p) k i) < 1
  cont : ∀ (t : Fin 1856) i, 100*p t (i+2) +
    SimonPeriodic.rivals (SimonPeriodic.FC.cycle (by decide) p) t.val i *
      SimonPeriodic.FC.cycle (by decide) v (t.val+1) i = v t i
  quit_le : ∀ (t : Fin 1856) i,
    SimonPeriodic.quit (SimonPeriodic.FC.cycle (by decide) p) t.val i ≤ v t i
  active : ∀ (t : Fin 1856) i, 0 < p t i →
    SimonPeriodic.quit (SimonPeriodic.FC.cycle (by decide) p) t.val i = v t i

private def phase (t : Fin 1856) : Fin 464 := ⟨t.val%464,Nat.mod_lt _ (by decide)⟩
private def role (t : Fin 1856) (i : Fin 4) : Fin 4 := i + Fin.ofNat 4 (t.val / 464)

private theorem role_val (t : Fin 1856) (i : Fin 4) :
    (role t i).val = SimonActiveRuns.role t i := by
  change (i.val+(t.val/464)%4)%4 = (i.val+t.val/464)%4
  omega

private theorem phase_next (t : Fin 1856) :
    (phase (t+1)).val = ((phase t).val+1)%464 := by
  change ((t.val+1)%1856)%464 = (t.val%464+1)%464
  omega

private theorem role_next (t : Fin 1856) (i : Fin 4) :
    role (t+1) i = if (phase t).val = 463 then role t i + 1 else role t i := by
  split <;> rename_i h <;> apply Fin.ext
  · change t.val%464 = 463 at h
    change (i.val+(((t.val+1)%1856)/464)%4)%4 = ((i.val+(t.val/464)%4)%4+1)%4
    omega
  · change t.val%464 ≠ 463 at h
    change (i.val+(((t.val+1)%1856)/464)%4)%4 = (i.val+(t.val/464)%4)%4
    omega

private theorem cycle_phase (a : Table) (t : Fin 1856) (i : Fin 4) :
    SimonPeriodic.FC.cycle (by decide) a t.val i = a t i := by
  unfold SimonPeriodic.FC.cycle
  congr 2
  exact Nat.mod_eq_of_lt t.isLt

private theorem cycle_next (a : Table) (t : Fin 1856) (i : Fin 4) :
    SimonPeriodic.FC.cycle (by decide) a (t.val+1) i = a (t+1) i := rfl

private theorem lift_rivals (u : Fin 6 → ℝ) (t : Fin 1856) (i : Fin 4) :
    SimonPeriodic.rivals (SimonPeriodic.FC.cycle (by decide) (lift (stage u))) t.val i =
      lift (stay u) t i := by
  simp only [SimonPeriodic.rivals,cycle_phase,lift,stay,lit,Rat.cast_one]
  simp only [add_right_comm i]
  ring

private theorem lift_quit (u : Fin 6 → ℝ) (t : Fin 1856) (i : Fin 4) :
    SimonPeriodic.quit (SimonPeriodic.FC.cycle (by decide) (lift (stage u))) t.val i =
      lift (quit u) t i := by
  rw [SimonPeriodic.quit,lift_rivals,cycle_phase]
  simp only [lift,quit,lit,Rat.cast_one,add_right_comm i]
  norm_num

private theorem lift_cash (u : Fin 6 → ℝ) (t : Fin 1856) (i : Fin 4) :
    100*lift (stage u) t (i+2) = lift (cash u) t i := by
  simp only [lift,cash,lit,add_right_comm i]
  norm_num

/-- Every positive hazard has a role in the stated support. -/
private theorem positive_support (u : Fin 6 → ℝ) (t : Fin 464) (i : Fin 4)
    (h : 0 < stage u t.val i) :
    i.val < 2 ∨ i.val = 2 ∧ (t.val=0 ∨ t.val=451) := by
  fin_cases i
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · right
    refine ⟨rfl,?_⟩
    by_contra! hz
    simp [stage,hz.1,hz.2,lit] at h
    split at h <;> exact (lt_irrefl (0 : ℝ)) h
  · exfalso
    by_cases h0 : t.val=0 <;> by_cases ha : t.val<451 <;> by_cases hb : t.val=451 <;>
      simp [stage,h0,ha,hb,lit] at h

theorem finite_data (u : Fin 6 → ℝ) (hd : denom (cash u) (stay u) ≠ 0)
    (hlegal : ∀ (t : Fin 464) i, 0 ≤ stage u t.val i ∧ stage u t.val i < 1)
    (hproper : ∀ i, (∏ k ∈ Finset.range 1856,
      SimonPeriodic.rivals (SimonPeriodic.FC.cycle (by decide) (lift (stage u))) k i) < 1)
    (hinactive : ∀ (t : Fin 464) (i : Fin 4),
      ¬(i.val < 2 ∨ i.val = 2 ∧ (t.val=0 ∨ t.val=451)) →
        quit u t.val i ≤ value (cash u) (stay u) t.val i)
    (hdrop : ∀ (t : Fin 464), (t.val=0 ∨ t.val=451) →
      quit u t.val 2 = value (cash u) (stay u) t.val 2)
    (hstep : ∀ (t : Fin 464) (i : Fin 4), i.val < 2 →
      quit u t.val i = cash u t.val i + stay u t.val i *
        quit u ((t.val+1)%464) (if t.val=463 then i+1 else i)) :
    FiniteData (lift (stage u)) (lift (value (cash u) (stay u))) := by
  let e := fun t i => lift (quit u) t i - lift (value (cash u) (stay u)) t i
  have hv := lift_value_step (cash u) (stay u) hd
  have hterm (t i) (h : SimonActiveRuns.drop t i) : e t i = 0 := by
    have hr : role t i = 2 := Fin.ext ((role_val t i).trans h.1)
    change quit u (phase t).val (role t i) - value _ _ (phase t).val (role t i) = 0
    rw [hr,hdrop _ h.2,sub_self]
  have hprop (t i) (h : SimonActiveRuns.active t i) (nd : ¬ SimonActiveRuns.drop t i) :
      e t i = lift (stay u) t i * e (t+1) i := by
    have hi : (role t i).val < 2 := (role_val t i) ▸ h.resolve_right nd
    have hh := hstep (phase t) (role t i) hi
    rw [← phase_next,← role_next] at hh
    change lift (quit u) t i = lift (cash u) t i + lift (stay u) t i * lift (quit u) (t+1) i at hh
    dsimp only [e]
    rw [hh,hv t i]
    ring
  have heq (t i) (h : SimonActiveRuns.active t i) :
      lift (quit u) t i = lift (value (cash u) (stay u)) t i :=
    sub_eq_zero.mp (SimonActiveRuns.vanish e _ hterm hprop t i h)
  refine ⟨?_,hproper,?_,?_,?_⟩
  · intro t i
    exact ⟨(hlegal (phase t) (role t i)).1,(hlegal (phase t) (role t i)).2.le⟩
  · intro t i
    rw [lift_cash,lift_rivals,cycle_next]
    exact (hv t i).symm
  · intro t i
    rw [lift_quit]
    by_cases h : SimonActiveRuns.active t i
    · exact (heq _ _ h).le
    · apply hinactive (phase t) (role t i)
      simpa only [SimonActiveRuns.active,SimonActiveRuns.drop,role_val,phase] using h
  · intro t i hp
    rw [lift_quit]
    apply heq
    have h := positive_support u (phase t) (role t i) hp
    simpa only [SimonActiveRuns.active,SimonActiveRuns.drop,role_val,phase] using h

#print axioms finite_data

end
end SimonTable
