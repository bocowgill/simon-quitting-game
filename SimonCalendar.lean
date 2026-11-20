module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-!
# Periodic equilibria of Simon's four-player quitting game

A calendar of independent quitting hazards is used at the unique live history.
The terminal reward begins on the quitting date; earlier rewards are zero.
The Bellman and one-period contraction hypotheses below can be supplied by an
external parameter certificate. The statements quantify over every live phase.
-/

@[expose] public section
open Finset Filter
open scoped Topology
namespace SimonPeriodic
noncomputable section

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

structure Bellman (p v : Calendar) : Prop where
  legal : Legal p
  bounded : ∀ t i, 0 ≤ v t i ∧ v t i ≤ 100
  continuation : ∀ t i, 100*p t (i+2) + rivals p t i*v (t+1) i = v t i
  quit_le : ∀ t i, quit p t i ≤ v t i
  active : ∀ t i, 0 < p t i → quit p t i = v t i

/-- Every full block of L dates has rival survival bounded by the same D < 1. -/
def Blocks (p : Calendar) (L : ℕ) (D : ℝ) : Prop :=
  ∀ t i, (∏ j ∈ range L, rivals p (t+j) i) ≤ D

theorem rotate_product (f : ℕ → ℝ) {L : ℕ} (per : ∀ t, f (t+L) = f t) (t : ℕ) :
    ∏ j ∈ range L, f (t+j) = ∏ j ∈ range L, f j := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← ih]
    cases L with
    | zero => simp
    | succ l =>
      conv_lhs => rw [prod_range_succ]
      conv_rhs => rw [prod_range_succ']
      simp only [Nat.add_zero]
      have he : f (t+1+l) = f t := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using per t
      rw [he]
      apply congrArg (· * f t)
      apply prod_congr rfl
      intro j _
      congr 1
      omega

theorem blocks_of_period (p : Calendar) {L : ℕ} {D : ℝ} (per : ∀ t, p (t+L) = p t)
    (h : ∀ i, (∏ j ∈ range L, rivals p j i) ≤ D) : Blocks p L D := by
  intro t i
  rw [rotate_product (fun n ↦ rivals p n i) (fun n ↦ by simp only [rivals,per]) t]
  exact h i

private theorem other (i : Player) :
    i+1 ≠ i ∧ i+2 ≠ i ∧ i+3 ≠ i := by fin_cases i <;> decide

theorem rival_eq {p r : Calendar} {i : Player} (H : SameOpponents p r i) (t : ℕ) :
    rivals r t i = rivals p t i := by
  simp only [rivals,H t _ (other i).1,H t _ (other i).2.1,H t _ (other i).2.2]

theorem quit_eq {p r : Calendar} {i : Player} (H : SameOpponents p r i) (t : ℕ) :
    quit r t i = quit p t i := by simp only [quit,H t _ (other i).1,rival_eq H t]

theorem remain_factor (p : Calendar) (t : ℕ) (i : Player) :
    remain p t = (1-p t i)*rivals p t i := by
  unfold remain rivals
  rw [Fin.prod_univ_four]
  fin_cases i
  · change _ = (1-p t 0)*((1-p t 3)*(1-p t 1)*(1-p t 2)); ring
  · change _ = (1-p t 1)*((1-p t 0)*(1-p t 2)*(1-p t 3)); ring
  · change _ = (1-p t 2)*((1-p t 1)*(1-p t 3)*(1-p t 0)); ring
  · change _ = (1-p t 3)*((1-p t 2)*(1-p t 0)*(1-p t 1)); ring

private theorem mul_unit_upper {a b : ℝ} (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a*b ≤ 1 :=
  (mul_le_of_le_one_left hb₀ ha).trans hb

private theorem product_bound (a b : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hab : ∀ k, a k ≤ b k)
    (n : ℕ) : ∏ k ∈ range n, a k ≤ ∏ k ∈ range n, b k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [prod_range_succ]
    exact mul_le_mul ih (hab n) (ha n) (prod_nonneg (fun k _ ↦ (ha k).trans (hab k)))

theorem rival_unit {p : Calendar} (h : Legal p) (t : ℕ) (i : Player) :
    0 ≤ rivals p t i ∧ rivals p t i ≤ 1 := by
  have I (j : Player) : 0 ≤ 1-p t j ∧ 1-p t j ≤ 1 := ⟨sub_nonneg.mpr (h t j).2,by linarith [(h t j).1]⟩
  unfold rivals
  exact ⟨mul_nonneg (mul_nonneg (I _).1 (I _).1) (I _).1,
    mul_unit_upper (mul_unit_upper (I _).2 (I _).1 (I _).2) (I _).1 (I _).2⟩

theorem survival_unit {p : Calendar} (h : Legal p) (t n : ℕ) :
    0 ≤ survival p t n ∧ survival p t n ≤ 1 := by
  have hu k : 0 ≤ remain p k ∧ remain p k ≤ 1 := by
    rw [remain_factor p k 0]
    exact ⟨mul_nonneg (sub_nonneg.mpr (h k 0).2) (rival_unit h k 0).1,
      mul_unit_upper (by linarith [(h k 0).1]) (rival_unit h k 0).1 (rival_unit h k 0).2⟩
  exact ⟨prod_nonneg (fun j _ ↦ (hu (t+j)).1),
    by
      simpa [survival] using
        product_bound (fun j ↦ remain p (t+j)) (fun _ ↦ 1)
          (fun j ↦ (hu (t+j)).1) (fun j ↦ (hu (t+j)).2) n⟩

theorem block_survival {p r : Calendar} {i : Player} (hh : Legal r) (same : SameOpponents p r i)
    {L : ℕ} {D : ℝ} (blocks : Blocks p L D) (t n : ℕ) :
    survival r t (n+L) ≤ D*survival r t n := by
  have step j : remain r j ≤ rivals p j i := by
    rw [remain_factor r j i,←rival_eq same j]
    exact mul_le_of_le_one_left (rival_unit hh j i).1 (by linarith [(hh j i).1])
  have seg : (∏ j ∈ range L, remain r (t+(n+j))) ≤ D := by
    apply le_trans _ (blocks (t+n) i)
    simp only [Nat.add_assoc]
    apply product_bound
    · intro j; exact prod_nonneg (fun k _ ↦ sub_nonneg.mpr (hh _ k).2)
    · intro j; exact step _
  unfold survival
  rw [prod_range_add,mul_comm D]
  exact mul_le_mul_of_nonneg_left seg (survival_unit hh t n).1

theorem sum_survival {p r : Calendar} {i : Player} (hh : Legal r) (same : SameOpponents p r i)
    {L : ℕ} {D : ℝ} (hD : D < 1) (blocks : Blocks p L D) (t N : ℕ) :
    (∑ j ∈ range N, survival r t j) ≤ L/(1-D) := by
  let s := survival r t
  have he : (∑ j ∈ range N, s j) + (∑ j ∈ range L, s (N+j)) =
      (∑ j ∈ range L, s j) + (∑ j ∈ range N, s (L+j)) := by
    rw [←sum_range_add,←sum_range_add,Nat.add_comm N L]
  have hi : (∑ j ∈ range L, s j) ≤ (L:ℝ) := by
    calc
      _ ≤ ∑ _j ∈ range L, (1:ℝ) := sum_le_sum fun j _ ↦ (survival_unit hh t j).2
      _ = _ := by simp
  have htail : (∑ j ∈ range N, s (L+j)) ≤ D * ∑ j ∈ range N, s j := by
    rw [mul_sum]
    exact sum_le_sum fun j _ ↦ by simpa only [Nat.add_comm j L] using block_survival hh same blocks t j
  have hn : 0 ≤ ∑ j ∈ range L, s (N+j) := sum_nonneg fun j _ ↦ (survival_unit hh _ _).1
  apply (le_div_iff₀ (sub_pos.mpr hD)).2
  change (∑ j ∈ range N, s j)*(1-D) ≤ _
  linarith only [he,hi,htail,hn]

theorem one_step {p r v : Calendar} {i : Player} (b : Bellman p v) (hr : Legal r)
    (same : SameOpponents p r i) (t : ℕ) :
    earn r t i + remain r t*v (t+1) i ≤ v t i := by
  rw [earn,remain_factor r t i,quit_eq same,rival_eq same,same t _ (other i).2.1]
  have he := b.continuation t i
  linarith only [mul_le_mul_of_nonneg_left (b.quit_le t i) (hr t i).1,
    congrArg ((1-r t i)*·) he]

theorem honest_step {p v : Calendar} (b : Bellman p v) (t : ℕ) (i : Player) :
    earn p t i + remain p t*v (t+1) i = v t i := by
  rw [earn,remain_factor p t i]
  have he := congrArg ((1-p t i)*·) (b.continuation t i)
  by_cases ha : p t i = 0
  · rw [ha] at he ⊢; linarith only [he]
  · have hpos := lt_of_le_of_ne (b.legal t i).1 (Ne.symm ha)
    rw [b.active t i hpos]
    linarith only [he]

theorem cash_step (p : Calendar) (i : Player) (t n : ℕ) :
    cash p i t (n+1) = cash p i t n + survival p t n*earn p (t+n) i := by
  simp only [cash,sum_range_succ]

theorem survival_step (p : Calendar) (t n : ℕ) :
    survival p t (n+1) = survival p t n*remain p (t+n) := by simp only [survival,prod_range_succ]

theorem finite_bound {p r v : Calendar} {i : Player} (b : Bellman p v) (hr : Legal r)
    (same : SameOpponents p r i) (t n : ℕ) :
    cash r i t n + survival r t n*v (t+n) i ≤ v t i := by
  induction n with
  | zero => simp [cash,survival]
  | succ n ih =>
    rw [cash_step,survival_step]
    have he := mul_le_mul_of_nonneg_left (one_step b hr same (t+n)) (survival_unit hr t n).1
    simp only [Nat.add_assoc] at he
    linarith only [he,ih]

theorem finite_honest {p v : Calendar} (b : Bellman p v) (i : Player) (t n : ℕ) :
    cash p i t n + survival p t n*v (t+n) i = v t i := by
  induction n with
  | zero => simp [cash,survival]
  | succ n ih =>
    rw [cash_step,survival_step]
    have he := congrArg (survival p t n * ·) (honest_step b (t+n) i)
    simp only [Nat.add_assoc] at he
    linarith only [he,ih]


theorem cash_le {p r v : Calendar} {i : Player} (b : Bellman p v) (hr : Legal r)
    (same : SameOpponents p r i) (t n : ℕ) : cash r i t n ≤ v t i := by
  linarith only [finite_bound b hr same t n,
    mul_nonneg (survival_unit hr t n).1 (b.bounded (t+n) i).1]

theorem earn_bound {p : Calendar} (hp : Legal p) (t : ℕ) (i : Player) : |earn p t i| ≤ 100 := by
  have hi := hp t i
  have hk := rival_unit hp t i
  have hs := hp t (i+1)
  have ho := hp t (i+2)
  have hq : -100 ≤ quit p t i ∧ quit p t i ≤ 100 := by
    unfold quit
    constructor <;> linarith only [hs.1,hs.2,hk.1,hk.2]
  have hc : 0 ≤ 1-p t i := sub_nonneg.mpr hi.2
  unfold earn
  apply abs_le.mpr
  constructor
  · linarith only [mul_le_mul_of_nonneg_left hq.1 hi.1,mul_nonneg hc ho.1,hc]
  · linarith only [mul_le_mul_of_nonneg_left hq.2 hi.1,mul_le_mul_of_nonneg_left ho.2 hc]

theorem terminal_limit {p r : Calendar} {i : Player} (hr : Legal r) (same : SameOpponents p r i)
    {L : ℕ} {D : ℝ} (hD : D < 1) (B : Blocks p L D) (t : ℕ) :
    Tendsto (cash r i t) atTop (𝓝 (terminal r i t)) := by
  have hs := summable_of_sum_range_le (fun n ↦ (survival_unit hr t n).1)
    (sum_survival hr same hD B t)
  have hh : Summable (fun j ↦ survival r t j * earn r (t+j) i) := by
    apply (hs.mul_right 100).of_norm_bounded
    intro j
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (survival_unit hr t j).1]
    exact mul_le_mul_of_nonneg_left (earn_bound hr _ i) (survival_unit hr t j).1
  exact hh.hasSum.tendsto_sum_nat

/-- Every calendar deviation, including any deterministic stopping date and never
quitting, has terminal payoff no greater than the certified continuation value. -/
theorem terminal_best_reply {p r v : Calendar} {i : Player} (b : Bellman p v) (hr : Legal r)
    (same : SameOpponents p r i) {L : ℕ} {D : ℝ} (hD : D < 1) (B : Blocks p L D) (t : ℕ) :
    terminal r i t ≤ v t i :=
  le_of_tendsto_of_tendsto' (terminal_limit hr same hD B t) tendsto_const_nhds
    (cash_le b hr same t)

theorem terminal_honest {p v : Calendar} (b : Bellman p v) {L : ℕ} {D : ℝ}
    (hD : D < 1) (B : Blocks p L D) (t : ℕ) (i : Player) : terminal p i t = v t i := by
  have same : SameOpponents p p i := fun _ _ _ ↦ rfl
  have hs := summable_of_sum_range_le (fun n ↦ (survival_unit b.legal t n).1)
    (sum_survival b.legal same hD B t)
  have hgap : Tendsto (fun n ↦ survival p t n*v (t+n) i) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ mul_nonneg (survival_unit b.legal t n).1 (b.bounded (t+n) i).1)
      (fun n ↦ mul_le_mul_of_nonneg_left (b.bounded (t+n) i).2 (survival_unit b.legal t n).1)
      (by simpa using hs.tendsto_atTop_zero.mul_const 100)
  have hcash := terminal_limit b.legal same hD B t
  have hsum := hcash.add hgap
  simp only [fun n ↦ finite_honest b i t n,add_zero] at hsum
  exact tendsto_nhds_unique hsum tendsto_const_nhds

/-- Uniform error for the fixed honest calendar, at any initial phase and
against every rival-preserving behavioral calendar, for every positive horizon. -/
theorem average_bound {p r v : Calendar} {i : Player} (b : Bellman p v) (hr : Legal r)
    (same : SameOpponents p r i) {L : ℕ} {D : ℝ} (hD : D < 1) (B : Blocks p L D)
    (t N : ℕ) (hN : 0 < N) :
    |average p i t N-v t i| ≤ (100*(L/(1-D)))/N ∧
    average r i t N ≤ average p i t N+(100*(L/(1-D)))/N := by
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have upper {a : Calendar} (ha : Legal a) (hs : SameOpponents p a i) :
      average a i t N ≤ v t i := by
    unfold average
    rw [← div_eq_inv_mul,div_le_iff₀ hn]
    simpa [mul_comm] using sum_le_sum (s := range N) (fun j _ ↦ cash_le b ha hs t (j+1))
  have ss : SameOpponents p p i := fun _ _ _ ↦ rfl
  have step (j : ℕ) : survival p t (j+1) ≤ survival p t j := by
    rw [survival_step]
    apply mul_le_of_le_one_right (survival_unit b.legal t j).1
    simpa [survival] using (survival_unit b.legal (t+j) 1).2
  have gap (j : ℕ) : v t i - cash p i t (j+1) ≤ 100*survival p t j := by
    have hh := finite_honest b i t (j+1)
    linarith only [hh,step j,mul_le_mul_of_nonneg_left (b.bounded (t+(j+1)) i).2
      (survival_unit b.legal t (j+1)).1]
  have sum := sum_le_sum (s := range N) (fun j _ ↦ gap j)
  rw [sum_sub_distrib,←mul_sum] at sum
  simp only [sum_const,card_range,nsmul_eq_mul] at sum
  have htotal := sum_survival b.legal ss hD B t N
  have lower : v t i - average p i t N ≤ (100*(L/(1-D)))/N := by
    unfold average
    rw [← div_eq_inv_mul,le_div_iff₀ hn,sub_mul,div_mul_cancel₀ _ hn.ne']
    linarith only [sum,htotal]
  have hp := upper b.legal ss
  have hd := upper hr same
  have err : 0 ≤ (100*((L:ℝ)/(1-D)))/N := by positivity
  exact ⟨abs_le.mpr ⟨by linarith only [lower],by linarith only [hp,err]⟩,by linarith only [lower,hd]⟩


/-- A pure planned date. The top date is the action of never quitting. -/
def deadline (p : Calendar) (i : Player) (d : WithTop ℕ) : Calendar :=
  fun t j ↦ if j = i then (if (t : WithTop ℕ) = d then 1 else 0) else p t j

theorem deadline_bound {p v : Calendar} (b : Bellman p v) (i : Player) (d : WithTop ℕ)
    {L : ℕ} {D : ℝ} (hD : D < 1) (B : Blocks p L D) (t : ℕ) :
    terminal (deadline p i d) i t ≤ terminal p i t := by
  rw [terminal_honest b hD B t i]
  apply terminal_best_reply b _ _ hD B
  · intro t j
    unfold deadline
    split
    · split <;> norm_num
    · exact b.legal t j
  · intro t j hj; simp [deadline,hj]

def shift (p : Calendar) (phase : ℕ) : Calendar := fun t ↦ p (phase+t)

theorem shift_bellman {p v : Calendar} (b : Bellman p v) (phase : ℕ) :
    Bellman (shift p phase) (shift v phase) where
  legal t := b.legal (phase+t)
  bounded t := b.bounded (phase+t)
  continuation t i := by simpa [shift,rivals,Nat.add_assoc] using b.continuation (phase+t) i
  quit_le t i := b.quit_le (phase+t) i
  active t i := b.active (phase+t) i

theorem shift_blocks {p : Calendar} {L : ℕ} {D : ℝ} (B : Blocks p L D) (phase : ℕ) :
    Blocks (shift p phase) L D := by
  intro t i; simpa [shift,rivals,Nat.add_assoc] using B (phase+t) i

/-- Range of the periodic continuation value follows from its Bellman recursion
and strict rival absorption. The range follows without a separate value certificate. -/
theorem periodic_range {p v : Calendar} (hp : Legal p) {L : ℕ} {D : ℝ} (hD : D < 1)
    (B : Blocks p L D) (per : ∀ t, v (t+L) = v t)
    (rec : ∀ t i, 100*p t (i+2) + rivals p t i*v (t+1) i = v t i) (t : ℕ) (i : Player) :
    0 ≤ v t i ∧ v t i ≤ 100 := by
  let S := fun n ↦ ∏ k ∈ range n, rivals p (t+k) i
  have one k : rivals p k i ≤ 1-p k (i+2) := by
    unfold rivals
    apply mul_le_of_le_one_left (sub_nonneg.mpr (hp k _).2)
    exact mul_unit_upper (by linarith only [(hp k (i+3)).1]) (sub_nonneg.mpr (hp k _).2)
      (by linarith only [(hp k (i+1)).1])
  have H (n : ℕ) : 0 ≤ v t i-S n*v (t+n) i ∧ v t i-S n*v (t+n) i ≤ 100*(1-S n) := by
    induction n with
    | zero => simp [S]
    | succ n ih =>
      have hnon : 0 ≤ S n := prod_nonneg (fun k _ ↦ (rival_unit hp _ _).1)
      have eq := congrArg (S n * ·) (rec (t+n) i)
      simp only [Nat.add_assoc] at eq
      have he : S (n+1) = S n*rivals p (t+n) i := prod_range_succ _ _
      rw [he]
      constructor
      · linarith only [ih.1,eq,mul_nonneg hnon (hp (t+n) (i+2)).1]
      · linarith only [ih.2,eq,mul_le_mul_of_nonneg_left (one (t+n)) hnon]
  have hf := H L
  rw [per] at hf
  have hl : 0 < 1-S L := sub_pos.mpr ((B t i).trans_lt hD)
  constructor
  · by_contra! h
    linarith only [hf.1,mul_neg_of_pos_of_neg hl h]
  · by_contra! h
    linarith only [hf.2,mul_pos hl (sub_pos.mpr h)]

theorem uniform_block_from_period (p : Calendar) {L : ℕ} (per : ∀ t, p (t+L) = p t)
    (hs : ∀ i, (∏ k ∈ range L, rivals p k i) < 1) :
    ∃ D : ℝ, D < 1 ∧ Blocks p L D := by
  let d := fun i ↦ ∏ k ∈ range L, rivals p k i
  refine ⟨max (max (d 0) (d 1)) (max (d 2) (d 3)), max_lt (max_lt (hs 0) (hs 1)) (max_lt (hs 2) (hs 3)),?_⟩
  apply blocks_of_period p per
  intro i
  change d i ≤ _
  fin_cases i
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

namespace FC

/-- Extend a finite array of phases by repetition. -/
def cycle {L : ℕ} (hL : 0 < L) (a : Fin L → Player → ℝ) : Calendar :=
  fun n ↦ a ⟨n % L,Nat.mod_lt _ hL⟩

end FC
end
end SimonPeriodic
