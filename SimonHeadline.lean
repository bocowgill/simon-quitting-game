module

public import SimonCalendar

@[expose] public section
noncomputable section
open Finset

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

/-- Finite tests sufficient for a concrete table of hazards and continuation
values to yield a periodic equilibrium from every initial phase. -/
theorem of_finite_data {L : ℕ} (hL : 0 < L) (p v : Fin L → Player → ℝ)
    (hp : ∀ j i, 0 ≤ p j i ∧ p j i ≤ 1)
    (proper : ∀ i, (∏ k ∈ range L, rivals (FC.cycle hL p) k i) < 1)
    (cont : ∀ (j : Fin L) i, 100*p j (i+2) +
      rivals (FC.cycle hL p) j.val i*FC.cycle hL v (j.val+1) i = v j i)
    (ql : ∀ (j : Fin L) i, quit (FC.cycle hL p) j.val i ≤ v j i)
    (ac : ∀ (j : Fin L) i, 0 < p j i → quit (FC.cycle hL p) j.val i = v j i) :
    Equilibrium (FC.cycle hL p) (FC.cycle hL v) := by
  let idx := fun n : ℕ ↦ (⟨n%L,Nat.mod_lt n hL⟩ : Fin L)
  have per (a : Fin L → Player → ℝ) (n : ℕ) : FC.cycle hL a (n+L) = FC.cycle hL a n := by
    simp [FC.cycle]
  have succidx (t : ℕ) : ((t%L)+1)%L = (t+1)%L := Nat.mod_add_mod t L 1
  have legal : Legal (FC.cycle hL p) := fun t i ↦ hp (idx t) i
  obtain ⟨D,hD,B⟩ := uniform_block_from_period _ (per p) proper
  have cont' : ∀ t i, 100*FC.cycle hL p t (i+2) +
      rivals (FC.cycle hL p) t i * FC.cycle hL v (t+1) i = FC.cycle hL v t i := by
    intro t i
    simpa only [idx,rivals,FC.cycle,Nat.mod_mod,succidx] using cont (idx t) i
  have cert : Bellman (FC.cycle hL p) (FC.cycle hL v) := by
    refine ⟨legal,periodic_range legal hD B (per v) cont',cont',?_,?_⟩
    · intro t i
      simpa only [idx,quit,rivals,FC.cycle,Nat.mod_mod] using ql (idx t) i
    · intro t i hi
      simpa only [idx,quit,rivals,FC.cycle,Nat.mod_mod] using ac (idx t) i hi
  refine ⟨legal,fun t i ↦ ⟨terminal_honest cert hD B t i,
    fun _ hr hs ↦ terminal_best_reply cert hr hs hD B t⟩,?_⟩
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_gt ((100*((L:ℝ)/(1-D)))/ε)
  refine ⟨k+1,Nat.succ_pos _,?_⟩
  intro t i N hN
  have hn : 0 < N := lt_of_lt_of_le (Nat.succ_pos _) hN
  have cut : 100*((L:ℝ)/(1-D))/(N:ℝ) ≤ ε := by
    have hkn : (k:ℝ) ≤ N := Nat.cast_le.mpr ((Nat.le_succ _).trans hN)
    apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
    simpa [mul_comm] using ((div_lt_iff₀ hε).1 (hk.trans_le hkn)).le
  exact ⟨((average_bound (i := i) cert legal (fun _ _ _ ↦ rfl) hD B t N hn).1).trans cut,
    fun _ hr hs ↦ ((average_bound cert hr hs hD B t N hn).2).trans (add_le_add_right cut _)⟩

end SimonHeadline
end
