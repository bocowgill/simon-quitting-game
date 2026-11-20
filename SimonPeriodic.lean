module

public import FormalConjecturesForMathlib.GameTheory.StochasticGame.Equilibrium
public import SimonCalendar
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-!
# Behavioral-strategy interpretation of Simon's periodic calendar

The four stochastic-game modules are vendored from Formal Conjectures commit
`326cddb8eee07ae19c82d4adee81af8288eac55b`. Theorems `expected_average`
and `actual_terminal` identify the calendar formulas with the trajectory
payoffs, also after every unilateral behavioral deviation.
-/

@[expose] public section
open Finset Filter
open scoped Topology
namespace SimonPeriodic
noncomputable section

namespace FC
open StochasticGame MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev State := Option {q : Finset Player // q.Nonempty}

abbrev Action (_ : Player) : State → Type
  | none => Bool
  | some _ => Unit

instance (i : Player) (s : State) : Fintype (Action i s) := by
  cases s <;> unfold Action <;> infer_instance

instance (i : Player) (s : State) : Nonempty (Action i s) := by
  cases s <;> unfold Action <;> infer_instance

def quitters (a : Player → Bool) : Finset Player := Finset.univ.filter (fun i ↦ a i)

def nextState : (s : State) → (∀ i, Action i s) → State
  | none, a => if h : (quitters a).Nonempty then some ⟨quitters a, h⟩ else none
  | some q, _ => some q

/-- Simon's absorbing coalition reward. An empty coalition gives the live reward zero. -/
def prize (i : Player) (q : Finset Player) : ℝ :=
  if i ∈ q then
    if i+1 ∈ q then -1 else if i+3 ∈ q ∨ i+2 ∈ q then 99 else 1
  else if i+2 ∈ q then 100 else 0

abbrev game : Game Player State where
  Action := Action
  actionFintype := inferInstance
  actionNonempty := inferInstance
  transition s a := PMF.pure (nextState s a)
  reward i s a := match s, a with
    | none, a => prize i (quitters a)
    | some q, _ => prize i q.val

@[simp] theorem nextState_continue : nextState none (fun _ ↦ false) = none := by
  simp [nextState, quitters]

theorem transition_eq (s : State) (a : game.JointAction s) :
    game.transition s a = PMF.pure (nextState s a) := rfl

/-- Feasibility is checked by the PR's own transition-positive-history predicate. -/
theorem feasible_continue (n : ℕ) :
    Game.RawHistory.feasiblePast game
      (List.replicate n (⟨none, fun _ ↦ false⟩ : game.Stage)) none := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [List.replicate_succ']
    apply Game.RawHistory.feasiblePast_append_singleton game ih
    change PMF.pure (nextState none (fun _ ↦ false)) none ≠ 0
    simp

abbrev live (n : ℕ) : game.History :=
  ⟨⟨List.replicate n (⟨none, fun _ ↦ false⟩ : game.Stage), none⟩, feasible_continue n⟩

theorem live_clock (n : ℕ) : (live n).length = n := by
  simp [Game.History.length, Game.History.past]

/-- Every step in the PR's Markov chain selects the prescribed next state. -/
theorem next_state_pmf (σ : game.Profile) (x : game.Turn) :
    (game.nextTurn σ x).map (fun y ↦ y.1.current) = PMF.pure (nextState x.1.current x.2) := by
  let s := nextState x.1.current x.2
  have hs : game.transition x.1.current x.2 s ≠ 0 := by
    change PMF.pure s s ≠ 0
    simp
  have hnext : game.nextTurn σ x = game.initialTurn (x.1.extend x.2 s hs) σ :=
    PMF.pure_bindOnSupport s _
  rw [hnext, Game.initialTurn, PMF.map_comp]
  apply PMF.map_const

/-- The live state is reached exactly for the all-continue action. -/
theorem next_live_iff (a : Player → Bool) : nextState none a = none ↔ a = fun _ ↦ false := by
  classical
  simp only [nextState]
  split_ifs with hn
  · simp only [false_iff]
    intro he
    subst a
    simp [quitters] at hn
  · simp only [true_iff]
    funext i
    cases h : a i
    · rfl
    · exact False.elim (hn ⟨i, by simp [quitters, h]⟩)

theorem previous_live {s : State} (a : ∀ i, Action i s) (hn : nextState s a = none) :
    s = none := by
  cases s with
  | none => rfl
  | some _ => cases hn

/-- All feasible live histories have exactly the canonical public record at that date. -/
theorem unique_live_history (h : game.History) : h.current = none → h = live h.length := by
  induction h using Game.History.induction with
  | init s =>
    intro hs
    change s = none at hs
    subst s
    rfl
  | step h a s hp ih =>
    intro hs
    change s = none at hs
    subst s
    have hn : nextState h.current a = none := by
      by_contra hh
      apply hp
      change PMF.pure (nextState h.current a) none = 0
      simp [PMF.pure_apply, Ne.symm hh]
    have he := ih (previous_live a hn)
    generalize h.length = m at he
    subst h
    have ha := (next_live_iff a).1 hn
    subst a
    rw [Game.History.length_extend, live_clock]
    apply Subtype.ext
    dsimp [Game.History.extend, Game.History.past]
    rw [List.replicate_succ']
    rfl

/-- Every coordinate of the frozen trajectory law advances by its actual turn kernel. -/
theorem marginal_succ {I S : Type} [Fintype I] [Fintype S] (G : Game I S)
    (h : G.History) (σ : G.Profile) (n : ℕ) :
    (G.lawFrom h σ).map (fun ω ↦ ω (n + 1)) =
      G.nextKernel σ ∘ₘ (G.lawFrom h σ).map (fun ω ↦ ω n) := by
  let μ := G.lawFrom h σ
  let π := Preorder.frestrictLe (π := fun _ : ℕ ↦ G.Turn) n
  let ev := fun z : Finset.Iic n → G.Turn ↦ z ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have hπ : Measurable π := by dsimp [π]; fun_prop
  have hev : Measurable ev := by dsimp [ev]; fun_prop
  have hpair : μ.map π ⊗ₘ G.turnKernel σ n = μ.map (fun ω ↦ (π ω, ω (n + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ : ℕ ↦ G.Turn) (κ := G.turnKernel σ)
      (μ₀ := (G.initialTurn h σ).toMeasure) (a := n)
  have hk : G.turnKernel σ n = G.nextKernel σ ∘ₖ Kernel.deterministic ev hev := by
    rw [Kernel.comp_deterministic_eq_comap]
    apply Kernel.ext
    intro x
    rfl
  calc
    _ = (μ.map (fun ω ↦ (π ω, ω (n + 1)))).snd :=
      (Measure.map_map measurable_snd (hπ.prodMk (measurable_pi_apply _))).symm
    _ = G.turnKernel σ n ∘ₘ μ.map π := by rw [← hpair, Measure.snd_compProd]
    _ = G.nextKernel σ ∘ₘ (μ.map π).map ev := by
      rw [← Measure.deterministic_comp_eq_map hev, Measure.comp_assoc, ← hk]
    _ = _ := by rw [Measure.map_map hev hπ]; rfl

theorem continue_probability (q : PMF Bool) : (q false).toReal = 1 - (q true).toReal := by
  have hh := q.tsum_coe
  rw [tsum_fintype, Fintype.sum_bool] at hh
  have hr := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_add (q.apply_ne_top _) (q.apply_ne_top _), ENNReal.toReal_one] at hr
  exact eq_sub_of_add_eq' hr

abbrev liveTurn (n : ℕ) (a : Player → Bool) : game.Turn := ⟨live n, a⟩

theorem initial_turn_atom (σ : game.Profile) (n : ℕ) (a : Player → Bool) :
    game.initialTurn (live n) σ (liveTurn n a) = game.jointPMF σ (live n) a := by
  classical
  rw [Game.initialTurn, PMF.map_apply]
  have he (b : game.JointAction (live n).current) :
      liveTurn n a = ⟨live n, b⟩ ↔ a = b := sigma_mk_injective.eq_iff
  simp only [he, tsum_ite_eq']

theorem only_predecessor (σ : game.Profile) (n : ℕ) (a : Player → Bool) (x : game.Turn)
    (hx : liveTurn (n + 1) a ∈ (game.nextTurn σ x).support) :
    x = liveTurn n (fun _ ↦ false) := by
  have hh := (game.nextTurn_history_of_mem_support σ x _ hx).1
  rcases x with ⟨⟨⟨past, s⟩, hfeas⟩, b⟩
  change List.replicate (n + 1) (⟨none, fun _ ↦ false⟩ : game.Stage) = past ++ [⟨s, b⟩] at hh
  rw [List.replicate_succ', List.append_singleton_inj] at hh
  obtain ⟨rfl, he⟩ := hh
  cases he
  rfl

open scoped Classical in
theorem live_next_atom (σ : game.Profile) (n : ℕ) (a : Player → Bool) (x : game.Turn) :
    game.nextTurn σ x (liveTurn (n + 1) a) =
      if x = liveTurn n (fun _ ↦ false) then game.jointPMF σ (live (n + 1)) a else 0 := by
  classical
  split_ifs with hx
  · subst x
    let b : game.JointAction (live n).current := fun _ ↦ false
    have hs : game.transition (live n).current b none ≠ 0 := by
      change PMF.pure (nextState none (fun _ ↦ false)) none ≠ 0
      simp
    have he : (live n).extend b none hs = live (n + 1) := by
      apply Subtype.ext
      dsimp [Game.History.extend, Game.History.past]
      rw [List.replicate_succ']
      rfl
    have hnext : game.nextTurn σ (liveTurn n b) = game.initialTurn ((live n).extend b none hs) σ := by
      unfold Game.nextTurn
      simp only [game, PMF.pure_bindOnSupport, b]
      congr 1
    rw [hnext, he, initial_turn_atom]
  · by_contra hn
    exact hx (only_predecessor σ n a x ((PMF.mem_support_iff _ _).2 hn))

/-- The exact probability of the finite all-continue prefix followed by action mask a
at date n, under the original play law from the live state. -/
def atom (σ : game.Profile) (n : ℕ) (a : Player → Bool) : ℝ≥0∞ :=
  ((game.law none σ).map (fun ω ↦ ω n)) {liveTurn n a}

theorem atom_zero (σ : game.Profile) (a : Player → Bool) :
    atom σ 0 a = game.jointPMF σ (live 0) a := by
  unfold atom Game.law
  rw [game.map_zero_lawFrom, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact initial_turn_atom σ 0 a

theorem atom_step (σ : game.Profile) (n : ℕ) (a : Player → Bool) :
    atom σ (n + 1) a = atom σ n (fun _ ↦ false) * game.jointPMF σ (live (n + 1)) a := by
  classical
  let μ := (game.law none σ).map (fun ω ↦ ω n)
  let y := liveTurn (n + 1) a
  have hk (x : game.Turn) : game.nextKernel σ x {y} =
      if x = liveTurn n (fun _ ↦ false) then game.jointPMF σ (live (n + 1)) a else 0 := by
    change (game.nextTurn σ x).toMeasure {y} = _
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
    exact live_next_atom σ n a x
  change ((game.lawFrom (Game.History.initial none) σ).map _) {y} = _
  rw [marginal_succ, Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (MeasurableSet.singleton _)]
  simp only [Measure.smul_apply, smul_eq_mul, hk, mul_ite, mul_zero, tsum_ite_eq]
  rfl

/-- The product over all past dates and players, followed by the chosen current mask.
The formula holds for every behavioral profile at every finite date. -/
theorem law_live_atom (σ : game.Profile) (n : ℕ) (a : Player → Bool) :
    atom σ n a = (∏ k ∈ Finset.range n, ∏ i, σ i (live k) false) *
      ∏ i, σ i (live n) (a i) := by
  induction n generalizing a with
  | zero => simpa using atom_zero σ a
  | succ n ih => rw [atom_step, ih, Finset.prod_range_succ]; rfl

abbrev marginal (σ : game.Profile) (n : ℕ) := (game.law none σ).map (fun ω ↦ ω n)

def hazards (σ : game.Profile) : Calendar := fun n i ↦ (σ i (live n) true).toReal

def stored (i : Player) : State → ℝ
  | none => 0
  | some q => prize i q.val

theorem next_value (i : Player) (s : State) (a : ∀ j, Action j s) :
    stored i (nextState s a) = game.reward i s a := by
  cases s with
  | some _ => rfl
  | none =>
    simp only [nextState]
    split_ifs with h
    · rfl
    · have he := Finset.not_nonempty_iff_eq_empty.mp h
      change 0 = prize i (quitters a)
      simp [he, prize]

theorem ae_support (p : PMF game.Turn) : ∀ᵐ y ∂p.toMeasure, y ∈ p.support := by
  rw [ae_iff]
  apply (p.toMeasure_apply_eq_zero_iff (by trivial)).2
  exact Set.disjoint_left.mpr fun _ hy hn ↦ hn hy

theorem clock (σ : game.Profile) (n : ℕ) :
    ∀ᵐ x ∂marginal σ n, x.1.length = n := by
  induction n with
  | zero =>
    change ∀ᵐ x ∂((game.lawFrom _ σ).map (fun ω ↦ ω 0)), _
    rw [game.map_zero_lawFrom]
    filter_upwards [ae_support _] with x hx
    obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
    rfl
  | succ n ih =>
    change ∀ᵐ x ∂((game.lawFrom _ σ).map (fun ω ↦ ω (n + 1))), _
    rw [marginal_succ]
    apply Measure.ae_comp_of_ae_ae (by trivial)
    filter_upwards [ih] with x hx
    filter_upwards [ae_support (game.nextTurn σ x)] with y hy
    rw [(game.nextTurn_history_of_mem_support σ x y hy).2.2.1, hx]

theorem stored_step (σ : game.Profile) (n : ℕ) (i : Player) :
    ∫ x, stored i x.1.current ∂marginal σ (n + 1) =
      ∫ x, game.stageReward i x ∂marginal σ n := by
  let : MeasurableSpace State := ⊤
  let : MeasurableSingletonClass State := ⟨fun _ ↦ trivial⟩
  let cur := fun x : game.Turn ↦ x.1.current
  let next := fun x : game.Turn ↦ nextState x.1.current x.2
  have hc : Measurable cur := measurable_of_countable _
  have hn : Measurable next := measurable_of_countable _
  have hst : Measurable (stored i) := measurable_of_countable _
  have hk : (game.nextKernel σ).map cur = Kernel.deterministic next hn := by
    apply Kernel.ext
    intro x
    rw [Kernel.map_apply _ hc, Kernel.deterministic_apply]
    change ((game.nextTurn σ x).toMeasure.map cur) = _
    rw [PMF.toMeasure_map _ _ hc, next_state_pmf, PMF.toMeasure_pure]
  have hm : (marginal σ (n + 1)).map cur = (marginal σ n).map next := by
    unfold marginal Game.law
    rw [marginal_succ, Measure.map_comp _ _ hc, hk, Measure.deterministic_comp_eq_map hn]
  calc
    _ = ∫ s, stored i s ∂((marginal σ (n + 1)).map cur) :=
      (integral_map hc.aemeasurable hst.aestronglyMeasurable).symm
    _ = ∫ s, stored i s ∂((marginal σ n).map next) := by rw [hm]
    _ = ∫ x, stored i (next x) ∂marginal σ n := integral_map hn.aemeasurable hst.aestronglyMeasurable
    _ = _ := integral_congr_ae (Eventually.of_forall fun x ↦ next_value i x.1.current x.2)

theorem stored_zero (σ : game.Profile) (i : Player) :
    ∫ x, stored i x.1.current ∂marginal σ 0 = 0 := by
  change ∫ x, _ ∂((game.lawFrom _ σ).map (fun ω ↦ ω 0)) = _
  rw [game.map_zero_lawFrom]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_support _] with x hx
  obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
  rfl

def payment (n : ℕ) (i : Player) (a : Player → Bool) (x : game.Turn) : ℝ :=
  Set.indicator {liveTurn n a} (fun _ ↦ prize i (quitters a)) x

theorem reward_split (n : ℕ) (i : Player) (x : game.Turn) (hx : x.1.length = n) :
    game.stageReward i x = stored i x.1.current + ∑ a, payment n i a x := by
  classical
  by_cases hl : x.1.current = none
  · obtain ⟨h, a⟩ := x
    have he := (unique_live_history h hl).trans (congrArg live hx)
    subst h
    change Player → Bool at a
    have hs (b : Player → Bool) :
        payment n i b ⟨live n, a⟩ = if a = b then prize i (quitters b) else 0 := by
      simp only [payment, Set.indicator_apply, Set.mem_singleton_iff]
      have hh : (⟨live n, a⟩ : game.Turn) = liveTurn n b ↔ a = b := sigma_mk_injective.eq_iff
      simp only [hh]
    simp only [hs]
    change prize i (quitters a) = 0 + _
    rw [zero_add]
    exact (Fintype.sum_ite_eq a (fun b ↦ prize i (quitters b))).symm
  · have hs (a : Player → Bool) : payment n i a x = 0 := by
      apply Set.indicator_of_notMem
      intro he
      exact hl (congrArg (fun t : game.Turn ↦ t.1.current) (Set.mem_singleton_iff.1 he))
    simp only [hs, sum_const_zero, add_zero]
    rcases x with ⟨⟨⟨past, s⟩, hf⟩, a⟩
    cases s with
    | none => exact False.elim (hl rfl)
    | some _ => rfl

theorem stage_integral (σ : game.Profile) (n : ℕ) (i : Player) :
    ∫ x, game.stageReward i x ∂marginal σ n =
      (∫ x, stored i x.1.current ∂marginal σ n) +
      ∑ a, (atom σ n a).toReal * prize i (quitters a) := by
  classical
  let μ := marginal σ n
  have hint (a) : Integrable (payment n i a) μ :=
    (integrable_const _).indicator (MeasurableSet.singleton _)
  have hiSt : Integrable (fun x : game.Turn ↦ stored i x.1.current) μ := by
    let : MeasurableSpace State := ⊤
    let : MeasurableSingletonClass State := ⟨fun _ ↦ trivial⟩
    have h : Integrable (stored i) (μ.map (fun x : game.Turn ↦ x.1.current)) := .of_finite
    exact h.comp_measurable (measurable_of_countable _)
  calc
    _ = ∫ x, stored i x.1.current + ∑ a, payment n i a x ∂μ :=
      integral_congr_ae ((clock σ n).mono fun x hx ↦ reward_split n i x hx)
    _ = _ := by
      rw [integral_add hiSt (integrable_finsetSum _ fun a _ ↦ hint a), integral_finsetSum _ fun a _ ↦ hint a]
      congr 1
      apply sum_congr rfl
      intro a _
      change (∫ x, Set.indicator {liveTurn n a} (fun _ ↦ prize i (quitters a)) x ∂μ) = _
      rw [integral_indicator (MeasurableSet.singleton _), integral_singleton]
      rfl

def maskEquiv : (Bool × Bool × Bool × Bool) ≃ (Player → Bool) where
  toFun b := ![b.1,b.2.1,b.2.2.1,b.2.2.2]
  invFun a := (a 0,a 1,a 2,a 3)
  left_inv b := rfl
  right_inv a := by funext i; fin_cases i <;> rfl

theorem sum_masks (f : (Player → Bool) → ℝ) :
    (∑ a, f a) = ∑ w : Bool, ∑ x : Bool, ∑ y : Bool, ∑ z : Bool, f ![w,x,y,z] := by
  rw [← Equiv.sum_comp maskEquiv f, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem mask_yes {P : Prop} [Decidable P] {x y : ℝ} (h : P) :
    (if P then x else y) = x := by simp [h]

private theorem mask_no {P : Prop} [Decidable P] {x y : ℝ} (h : ¬ P) :
    (if P then x else y) = y := by simp [h]

/-- Enumerate all sixteen independent action masks in the actual FC game. -/
theorem local_polynomial (p : Calendar) (n : ℕ) (i : Player) :
    (∑ a : Player → Bool, (∏ j, if a j then p n j else 1-p n j)*prize i (quitters a)) =
      earn p n i := by
  rw [sum_masks]
  fin_cases i <;> first
  | change _ = p n 0*(100*(1-p n 1)-1-98*((1-p n 3)*(1-p n 1)*(1-p n 2)))+(1-p n 0)*(100*p n 2)
  | change _ = p n 1*(100*(1-p n 2)-1-98*((1-p n 0)*(1-p n 2)*(1-p n 3)))+(1-p n 1)*(100*p n 3)
  | change _ = p n 2*(100*(1-p n 3)-1-98*((1-p n 1)*(1-p n 3)*(1-p n 0)))+(1-p n 2)*(100*p n 0)
  | change _ = p n 3*(100*(1-p n 0)-1-98*((1-p n 2)*(1-p n 0)*(1-p n 1)))+(1-p n 3)*(100*p n 1)
  all_goals
    simp (disch := decide) only [Fintype.sum_bool,Fin.prod_univ_four,prize,quitters,mask_yes,mask_no]
    ring

theorem real_atom (σ : game.Profile) (n : ℕ) (a : Player → Bool) :
    (atom σ n a).toReal = survival (hazards σ) 0 n *
      ∏ i, (if a i then hazards σ n i else 1-hazards σ n i) := by
  rw [law_live_atom, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_prod,survival,remain,Nat.zero_add]
  congr 1
  · apply prod_congr rfl
    intro k _
    exact prod_congr rfl fun j _ ↦ continue_probability (σ j (live k))
  · apply prod_congr rfl
    intro j _
    cases ha : a j
    · exact continue_probability (σ j (live n))
    · rfl

theorem stage_increment (σ : game.Profile) (n : ℕ) (i : Player) :
    ∫ x, game.stageReward i x ∂marginal σ n =
      (∫ x, stored i x.1.current ∂marginal σ n) + survival (hazards σ) 0 n*earn (hazards σ) n i := by
  rw [stage_integral,←local_polynomial]
  simp only [real_atom,mul_assoc,Finset.mul_sum]

theorem stage_payoff (σ : game.Profile) (n : ℕ) (i : Player) :
    ∫ x, game.stageReward i x ∂marginal σ n = cash (hazards σ) i 0 (n+1) := by
  induction n with
  | zero => rw [stage_increment,stored_zero,cash_step]; simp [cash,survival]
  | succ n ih => rw [stage_increment,stored_step,ih,cash_step (hazards σ) i 0 (n+1)]; simp

/-- Actual FC expected average for any behavioral profile on the live state. -/
theorem expected_average (σ : game.Profile) (i : Player) (N : ℕ) :
    game.expectedAverage none σ i N = average (hazards σ) i 0 N := by
  rw [Game.expectedAverage,Game.expectedAverageFrom,BoundedPayoffs.Process.expectedAverage_eq]
  apply congrArg ((N:ℝ)⁻¹ * ·)
  apply sum_congr rfl
  intro n _
  calc
    _ = ∫ x, game.stageReward i x ∂marginal σ n :=
      (integral_map (measurable_pi_apply n).aemeasurable
        (game.measurable_stageReward i).aestronglyMeasurable).symm
    _ = _ := stage_payoff σ n i


def binary (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun a ↦ if a then ENNReal.ofReal x else ENNReal.ofReal (1-x)) (by
    rw [Fintype.sum_bool]
    change ENNReal.ofReal x + ENNReal.ofReal (1-x) = 1
    rw [←ENNReal.ofReal_add hx.1 (sub_nonneg.mpr hx.2)]
    simp)

def actionLaw (p : Calendar) (h : Legal p) (t : ℕ) (i : Player) : ∀ s, PMF (Action i s)
  | none => binary (p t i) (h t i)
  | some _ => PMF.pure ()

def profile (p : Calendar) (h : Legal p) : game.Profile :=
  fun i hist ↦ actionLaw p h hist.length i hist.current

theorem profile_hazards (p : Calendar) (h : Legal p) : hazards (profile p h) = p := by
  funext t i
  change ((binary (p (live t).length i) (h _ i)) true).toReal = p t i
  change (ENNReal.ofReal (p (live t).length i)).toReal = p t i
  rw [ENNReal.toReal_ofReal (h _ i).1,live_clock]

theorem hazards_legal (σ : game.Profile) : Legal (hazards σ) := by
  intro t i
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  have h := continue_probability (σ i (live t))
  have h₀ := ENNReal.toReal_nonneg (a := σ i (live t) false)
  change (σ i (live t) true).toReal ≤ 1
  exact sub_nonneg.mp (h ▸ h₀)

theorem revised_opponents (p : Calendar) (h : Legal p) (i : Player) (τ : game.Strategy i) :
    SameOpponents p (hazards (game.revise (profile p h) i τ)) i := by
  intro t j hj
  change (game.revise (profile p h) i τ j (live t) true).toReal = p t j
  rw [Game.revise_other _ _ _ hj]
  exact congrFun (congrFun (profile_hazards p h) t) j

theorem absorbed_average (q : {q : Finset Player // q.Nonempty}) (σ : game.Profile)
    (i : Player) {N : ℕ} (hN : 0 < N) : game.expectedAverage (some q) σ i N = prize i q.val := by
  classical
  let μ := game.law (some q) σ
  let m := fun n : ℕ ↦ μ.map (fun ω ↦ ω n)
  have st (n : ℕ) : ∀ᵐ x ∂m n, x.1.current = some q := by
    induction n with
    | zero =>
      change ∀ᵐ x ∂((game.lawFrom _ σ).map (fun ω ↦ ω 0)), _
      rw [game.map_zero_lawFrom]
      filter_upwards [ae_support _] with x hx
      obtain ⟨a,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
      rfl
    | succ n ih =>
      change ∀ᵐ x ∂((game.lawFrom _ σ).map (fun ω ↦ ω (n+1))), _
      rw [marginal_succ]
      apply Measure.ae_comp_of_ae_ae (by trivial)
      filter_upwards [ih] with x hx
      filter_upwards [ae_support (game.nextTurn σ x)] with y hy
      have h := (game.nextTurn_history_of_mem_support σ x y hy).2.1
      have he (s : State) (a : ∀ j, Action j s) (hs : s = some q) : nextState s a = some q := by
        subst s; rfl
      change PMF.pure (nextState x.1.current x.2) y.1.current ≠ 0 at h
      rw [he _ _ hx] at h
      by_contra hne
      exact h (by simp [PMF.pure_apply,hne])
  have ev (n : ℕ) : ∫ ω, game.stageReward i (ω n) ∂μ = prize i q.val := by
    have : IsProbabilityMeasure (m n) := by
      constructor
      change μ.map _ Set.univ = 1
      rw [Measure.map_apply (measurable_pi_apply n) MeasurableSet.univ]
      exact measure_univ
    have he (s : State) (a : ∀ j, Action j s) (hs : s = some q) : game.reward i s a = prize i q.val := by
      subst s; rfl
    calc
      _ = ∫ x, game.stageReward i x ∂m n :=
        (integral_map (measurable_pi_apply n).aemeasurable (game.measurable_stageReward i).aestronglyMeasurable).symm
      _ = ∫ _x, prize i q.val ∂m n := integral_congr_ae ((st n).mono fun x hx ↦ he _ _ hx)
      _ = _ := by simp
  rw [Game.expectedAverage,Game.expectedAverageFrom,BoundedPayoffs.Process.expectedAverage_eq]
  change (N:ℝ)⁻¹*(∑ n ∈ range N, ∫ ω, game.stageReward i (ω n) ∂μ) = _
  simp only [ev,sum_const,card_range,nsmul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'),one_mul]

def target (v : Calendar) (i : Player) : State → ℝ
  | none => v 0 i
  | some q => prize i q.val

/-- A single behavioral profile, independent of tolerance, is an FC uniform
witness for all initial states and all unilateral behavioral strategies. -/
theorem fixed_uniform {p v : Calendar} (b : Bellman p v) {L : ℕ} {D : ℝ} (hD : D < 1)
    (B : Blocks p L D) {ε : ℝ} (hε : 0 < ε) :
    game.UniformWitness (profile p b.legal) (target v) ε := by
  obtain ⟨k,hk⟩ := exists_nat_gt ((100*((L:ℝ)/(1-D)))/ε)
  refine ⟨k+1,Nat.succ_pos _,?_⟩
  intro s i N hN
  have hn : 0 < N := lt_of_lt_of_le (Nat.succ_pos _) hN
  have cut : 100*((L:ℝ)/(1-D))/(N:ℝ) ≤ ε := by
    have hkn : (k:ℝ) ≤ N := Nat.cast_le.mpr ((Nat.le_succ _).trans hN)
    apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
    simpa [mul_comm] using ((div_lt_iff₀ hε).1 (hk.trans_le hkn)).le
  cases s with
  | some q =>
    rw [absorbed_average q _ i hn]
    refine ⟨by simpa [target] using hε.le,?_⟩
    intro τ
    rw [absorbed_average q _ i hn]
    linarith
  | none =>
    rw [expected_average,profile_hazards]
    refine ⟨((average_bound (i := i) b b.legal (fun _ _ _ ↦ rfl) hD B 0 N hn).1).trans cut,?_⟩
    intro τ
    rw [expected_average]
    exact ((average_bound b (hazards_legal _) (revised_opponents p b.legal i τ) hD B 0 N hn).2).trans
      (add_le_add_right cut _)

theorem has_uniform_payoffs {p v : Calendar} (b : Bellman p v) {L : ℕ} {D : ℝ} (hD : D < 1)
    (B : Blocks p L D) : game.HasUniformPayoffs (fun _ _ ↦ True) :=
  ⟨target v,fun _ hε ↦ ⟨profile p b.legal,trivial,fixed_uniform b hD B hε⟩⟩


theorem all_phases {p v : Calendar} (b : Bellman p v) {L : ℕ} {D : ℝ} (hD : D < 1)
    (B : Blocks p L D) (phase : ℕ) :
    ∃ σ : game.Profile, ∀ ε > 0, game.UniformWitness σ (target (shift v phase)) ε :=
  ⟨profile _ (shift_bellman b phase).legal, fun _ hε ↦
    fixed_uniform (shift_bellman b phase) hD (shift_blocks B phase) hε⟩

/-- Successive turns in the actual frozen Ionescu–Tulcea trajectory obey the
deterministic state update almost surely, simultaneously at all dates. -/
theorem ae_next_states (s : State) (σ : game.Profile) : ∀ᵐ ω ∂game.law s σ, ∀ n : ℕ,
    (ω (n+1)).1.current = nextState (ω n).1.current (ω n).2 := by
  apply ae_all_iff.mpr
  intro n
  let μ := game.law s σ
  let π := Preorder.frestrictLe (π := fun _ : ℕ ↦ game.Turn) n
  let ev := fun z : Finset.Iic n → game.Turn ↦ z ⟨n,Finset.mem_Iic.mpr le_rfl⟩
  let P := fun xy : ((Finset.Iic n → game.Turn) × game.Turn) ↦
    xy.2.1.current = nextState (ev xy.1).1.current (ev xy.1).2
  have hpair : μ.map π ⊗ₘ game.turnKernel σ n = μ.map (fun ω ↦ (π ω,ω (n+1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ : ℕ ↦ game.Turn)
      (κ := game.turnKernel σ) (μ₀ := (game.initialTurn (Game.History.initial s) σ).toMeasure) (a := n)
  have hj : ∀ᵐ xy ∂(μ.map π ⊗ₘ game.turnKernel σ n), P xy := by
    apply Measure.ae_compProd_of_ae_ae (Set.to_countable _).measurableSet
    apply Eventually.of_forall
    intro z
    change ∀ᵐ y ∂(game.nextTurn σ (ev z)).toMeasure, _
    filter_upwards [ae_support _] with y hy
    have h := (game.nextTurn_history_of_mem_support σ _ _ hy).2.1
    change PMF.pure (nextState _ _) y.1.current ≠ 0 at h
    change y.1.current = _
    by_contra hn
    exact h (by simp [PMF.pure_apply,hn])
  rw [hpair] at hj
  have hπ : Measurable π := by dsimp [π]; fun_prop
  exact ae_of_ae_map (hπ.prodMk (measurable_pi_apply (n+1))).aemeasurable hj

private theorem eventually_terminal (i : Player) (ω : ℕ → game.Turn)
    (h : ∀ n, (ω (n+1)).1.current = nextState (ω n).1.current (ω n).2) :
    ∃ c : ℝ, ∀ᶠ n : ℕ in atTop, game.stageReward i (ω n) = c := by
  classical
  by_cases hit : ∃ (n : ℕ) (q : {q : Finset Player // q.Nonempty}), (ω n).1.current = some q
  · obtain ⟨n,q,hq⟩ := hit
    have absorb (s : State) (a : ∀ j, Action j s) (hs : s = some q) : nextState s a = some q := by
      subst s; rfl
    have stable (k : ℕ) : (ω (n+k)).1.current = some q := by
      induction k with
      | zero => exact hq
      | succ k ih => exact (h (n+k)).trans (absorb _ _ ih)
    refine ⟨prize i q.val,eventually_atTop.mpr ⟨n,?_⟩⟩
    intro k hk
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
    unfold Game.stageReward
    rw [← next_value i (ω (n+j)).1.current (ω (n+j)).2,← h (n+j),Nat.add_assoc,stable (j+1)]
    rfl
  · have liveOnly (n : ℕ) : (ω n).1.current = none := by
      cases he : (ω n).1.current with
      | none => rfl
      | some q => exact (hit ⟨n,q,he⟩).elim
    exact ⟨0,Eventually.of_forall fun n ↦ by
      unfold Game.stageReward
      rw [← next_value i (ω n).1.current (ω n).2,← h n,liveOnly (n+1)]; rfl⟩

/-- The frozen API's expected pathwise lower limit is the genuine expected
eventual reward: each coherent quitting-game path has a constant reward tail. -/
theorem actual_terminal {p : Calendar} (σ : game.Profile) (i : Player)
    (same : SameOpponents p (hazards σ) i) {L : ℕ} {D : ℝ} (hD : D < 1) (B : Blocks p L D) :
    game.longRunPayoff .pathLiminf none σ i = terminal (hazards σ) i 0 := by
  let μ := game.law none σ
  let X := game.rewardProcess i
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ game.stageReward i (ω n)) atTop (𝓝 (X.pathLiminf ω)) := by
    filter_upwards [ae_next_states none σ] with ω hw
    obtain ⟨c,hc⟩ := eventually_terminal i ω hw
    have ht : Tendsto (fun n ↦ game.stageReward i (ω n)) atTop (𝓝 c) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hc] with n hn using hn.symm
    have hx : X.pathLiminf ω = c := ht.cesaro.liminf_eq
    rw [hx]; exact ht
  have hd := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ ↦ game.rewardBound)
    (fun n ↦ ((game.measurable_stageReward i).comp (measurable_pi_apply n)).aestronglyMeasurable)
    (integrable_const _) (fun n ↦ Eventually.of_forall (fun ω ↦ game.norm_stageReward_le i (ω n))) hlim
  have he (n : ℕ) : (∫ ω, game.stageReward i (ω n) ∂μ) = cash (hazards σ) i 0 (n+1) :=
    (integral_map (measurable_pi_apply n).aemeasurable
      (game.measurable_stageReward i).aestronglyMeasurable).symm.trans (stage_payoff σ n i)
  change Tendsto (fun n : ℕ ↦ ∫ ω, game.stageReward i (ω n) ∂μ) atTop (𝓝 (∫ ω, X.pathLiminf ω ∂μ)) at hd
  simp only [he] at hd
  have ht := (terminal_limit (hazards_legal σ) same hD B 0).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hd ht

theorem terminal_exact_nash {p v : Calendar} (b : Bellman p v) {L : ℕ} {D : ℝ}
    (hD : D < 1) (B : Blocks p L D) (i : Player) :
    game.longRunPayoff .pathLiminf none (profile p b.legal) i = v 0 i ∧
    ∀ τ : game.Strategy i, game.longRunPayoff .pathLiminf none (game.revise (profile p b.legal) i τ) i ≤ v 0 i := by
  constructor
  · have same : SameOpponents p (hazards (profile p b.legal)) i := by
      rw [profile_hazards]; exact fun _ _ _ ↦ rfl
    rw [actual_terminal _ _ same hD B,profile_hazards,terminal_honest b hD B]
  · intro τ
    have same := revised_opponents p b.legal i τ
    rw [actual_terminal _ _ same hD B]
    exact terminal_best_reply b (hazards_legal _) same hD B 0

/-- Certificate interface. A periodic legal calendar with the three one-stage
Bellman tests and positive probability of at least one rival quit per period
has a single terminal Nash and uniform FC profile from every starting phase. -/
theorem periodic_certificate {p v : Calendar} (hp : Legal p) (L : ℕ)
    (pPeriod : ∀ t, p (t+L) = p t) (vPeriod : ∀ t, v (t+L) = v t)
    (proper : ∀ i, (∏ k ∈ range L, rivals p k i) < 1)
    (cont : ∀ t i, 100*p t (i+2) + rivals p t i*v (t+1) i = v t i)
    (quit_le : ∀ t i, quit p t i ≤ v t i)
    (active : ∀ t i, 0 < p t i → quit p t i = v t i) (phase : ℕ) :
    ∃ σ : game.Profile,
      (∀ i, game.longRunPayoff .pathLiminf none σ i = v phase i ∧
        ∀ τ : game.Strategy i, game.longRunPayoff .pathLiminf none (game.revise σ i τ) i ≤ v phase i) ∧
      ∀ ε > 0, game.UniformWitness σ (target (shift v phase)) ε := by
  obtain ⟨D,hD,B⟩ := uniform_block_from_period p pPeriod proper
  have cert : Bellman p v := ⟨hp,periodic_range hp hD B vPeriod cont,cont,quit_le,active⟩
  have b := shift_bellman cert phase
  have sb := shift_blocks B phase
  exact ⟨profile _ b.legal,fun i ↦ terminal_exact_nash b hD sb i,fun _ hε ↦ fixed_uniform b hD sb hε⟩

/-- Finite-table interface to the analytic certificate. The Bellman test is
quantified over exactly L phases, and the phase after L−1 wraps to zero. -/
theorem finite_certificate {L : ℕ} (hL : 0 < L) (p v : Fin L → Player → ℝ)
    (hp : ∀ j i, 0 ≤ p j i ∧ p j i ≤ 1)
    (proper : ∀ i, (∏ k ∈ range L, rivals (cycle hL p) k i) < 1)
    (cont : ∀ (j : Fin L) i, 100*p j (i+2) +
      rivals (cycle hL p) j.val i*cycle hL v (j.val+1) i = v j i)
    (ql : ∀ (j : Fin L) i, quit (cycle hL p) j.val i ≤ v j i)
    (ac : ∀ (j : Fin L) i, 0 < p j i → quit (cycle hL p) j.val i = v j i) (phase : ℕ) :
    ∃ σ : game.Profile,
      (∀ i, game.longRunPayoff .pathLiminf none σ i = cycle hL v phase i ∧
        ∀ τ : game.Strategy i, game.longRunPayoff .pathLiminf none (game.revise σ i τ) i ≤ cycle hL v phase i) ∧
      ∀ ε > 0, game.UniformWitness σ (target (shift (cycle hL v) phase)) ε := by
  let idx := fun n : ℕ ↦ (⟨n%L,Nat.mod_lt n hL⟩ : Fin L)
  have per (a : Fin L → Player → ℝ) (n : ℕ) : cycle hL a (n+L) = cycle hL a n := by
    simp [cycle]
  have succidx (t : ℕ) : ((t%L)+1)%L = (t+1)%L := Nat.mod_add_mod t L 1
  apply periodic_certificate (fun t i ↦ hp (idx t) i) L (per p) (per v) proper
  · intro t i
    simpa only [idx,rivals,cycle,Nat.mod_mod,succidx] using cont (idx t) i
  · intro t i
    simpa only [idx,quit,rivals,cycle,Nat.mod_mod] using ql (idx t) i
  · intro t i hi
    simpa only [idx,quit,rivals,cycle,Nat.mod_mod] using ac (idx t) i hi

end FC
end
end SimonPeriodic
