/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.ExtendedStochastic
import LeanEconomics.DynamicProgramming.StochasticOptimality

/-!
# The principle of optimality for the extended stochastic program

`StochasticOptimality` proves the principle of optimality for a stochastic program with a
bounded real reward. Every model in this development uses the EXTENDED program instead, whose
reward may be `⊥` — zero consumption with unbounded utility — so that is the version the
household needs, and it is the version here.

## What `⊥` costs, and how little

A plan that ever reaches a `⊥` reward has no real value at all, so the sequence problem has to
be read over plans that avoid it. That is what the field `rewardFloor` does: a plan carries a
real number below which its rewards never fall. It is not a restriction on the agent — the
greedy plan has such a floor automatically, because at the optimum

  `reward (s, a) = V s - β · E V`,

a difference of two bounded reals (`policyPlan_rewardFloor`). So the supremum over floored plans
is still attained, and the theorem has the same shape as the bounded one:

  `valueFunction s₀ = ⨆ { E ∑' n, βⁿ · r (xₙ, aₙ) | floored contingent plans from s₀ }`.

Everything else is the bounded argument unchanged. The only new work is extracting a real
inequality from an extended one, and that is easy here because the objective is
`reward + (real : EReal)`: once the reward is known finite, the comparison is between reals.
-/

open scoped NNReal
open Filter Topology

namespace LeanEconomics

variable {S A Z : Type*} [TopologicalSpace S] [TopologicalSpace A] [Fintype Z]

namespace ExtendedStochasticProgram

variable (D : ExtendedStochasticProgram S A Z)

/-- **A feasible contingent plan with a reward floor.** The floor is what keeps the plan's value
a real number; the greedy plan has one for free. -/
structure Plan (s₀ : S) where
  /-- The state reached after the history `h`. -/
  state : ∀ n : ℕ, (Fin n → Z) → S
  /-- The action taken after the history `h`. -/
  action : ∀ n : ℕ, (Fin n → Z) → A
  state_zero : ∀ h : Fin 0 → Z, state 0 h = s₀
  action_mem : ∀ (n : ℕ) (h : Fin n → Z), action n h ∈ D.feasible (state n h)
  state_succ : ∀ (n : ℕ) (h : Fin n → Z) (z : Z),
    state (n + 1) (Fin.snoc h z) = D.transition z (state n h, action n h)
  /-- A real floor under the rewards the plan collects. -/
  rewardFloor : ℝ
  le_reward : ∀ (n : ℕ) (h : Fin n → Z),
    (rewardFloor : EReal) ≤ D.reward (state n h, action n h)

variable {D}

namespace Plan

variable {s₀ : S} (p : D.Plan s₀)

theorem reward_ne_bot (n : ℕ) (h : Fin n → Z) : D.reward (p.state n h, p.action n h) ≠ ⊥ :=
  fun hbot => by simpa [hbot] using p.le_reward n h

theorem reward_ne_top (n : ℕ) (h : Fin n → Z) : D.reward (p.state n h, p.action n h) ≠ ⊤ :=
  fun htop => by simpa [htop] using D.reward_le _ _ (p.action_mem n h)

theorem coe_reward (n : ℕ) (h : Fin n → Z) :
    (((D.reward (p.state n h, p.action n h)).toReal : ℝ) : EReal)
      = D.reward (p.state n h, p.action n h) :=
  EReal.coe_toReal (p.reward_ne_top n h) (p.reward_ne_bot n h)

/-- The reward the plan collects, as a real number. -/
noncomputable def rewardR (n : ℕ) (h : Fin n → Z) : ℝ :=
  (D.reward (p.state n h, p.action n h)).toReal

theorem rewardR_eq (n : ℕ) (h : Fin n → Z) :
    p.rewardR n h = (D.reward (p.state n h, p.action n h)).toReal := rfl

theorem rewardFloor_le_rewardR (n : ℕ) (h : Fin n → Z) : p.rewardFloor ≤ p.rewardR n h := by
  have := p.le_reward n h
  rw [← p.coe_reward n h, EReal.coe_le_coe_iff] at this
  exact this

theorem rewardR_le (n : ℕ) (h : Fin n → Z) : p.rewardR n h ≤ D.rewardMax := by
  have := D.reward_le _ _ (p.action_mem n h)
  rw [← p.coe_reward n h, EReal.coe_le_coe_iff] at this
  exact this

theorem abs_rewardR_le (n : ℕ) (h : Fin n → Z) :
    |p.rewardR n h| ≤ |p.rewardFloor| + |D.rewardMax| := by
  rw [abs_le]
  constructor
  · have := p.rewardFloor_le_rewardR n h
    have h1 := neg_abs_le p.rewardFloor
    have h2 := abs_nonneg D.rewardMax
    linarith
  · have := p.rewardR_le n h
    have h1 := le_abs_self D.rewardMax
    have h2 := abs_nonneg p.rewardFloor
    linarith

/-- The probability the plan attaches to a shock history. -/
noncomputable def histProb (p : D.Plan s₀) : ∀ (n : ℕ), (Fin n → Z) → ℝ
  | 0, _ => 1
  | n + 1, h => histProb p n (Fin.init h)
      * D.prob (h (Fin.last n)) (p.state n (Fin.init h), p.action n (Fin.init h))

@[simp] theorem histProb_zero (_h : Fin 0 → Z) : p.histProb 0 _h = 1 := rfl

@[simp] theorem histProb_snoc (n : ℕ) (h : Fin n → Z) (z : Z) :
    p.histProb (n + 1) (Fin.snoc h z) = p.histProb n h * D.prob z (p.state n h, p.action n h) := by
  simp only [histProb, Fin.init_snoc, Fin.snoc_last]

theorem histProb_nonneg (p : D.Plan s₀) : ∀ (n : ℕ) (h : Fin n → Z), 0 ≤ p.histProb n h
  | 0, _ => zero_le_one
  | n + 1, h => mul_nonneg (histProb_nonneg p n _) (D.prob_nonneg _ _)

theorem sum_histProb (p : D.Plan s₀) : ∀ n : ℕ, ∑ h : Fin n → Z, p.histProb n h = 1
  | 0 => by simp
  | n + 1 => by
      rw [sum_snoc]
      calc ∑ h : Fin n → Z, ∑ z : Z, p.histProb (n + 1) (Fin.snoc h z)
          = ∑ h : Fin n → Z, p.histProb n h := by
            refine Finset.sum_congr rfl fun h _ => ?_
            simp only [histProb_snoc]
            rw [← Finset.mul_sum, D.prob_sum, mul_one]
        _ = 1 := sum_histProb p n

/-- The expectation over histories of a function of the date-`n` history. -/
noncomputable def expectH (n : ℕ) (f : (Fin n → Z) → ℝ) : ℝ :=
  ∑ h : Fin n → Z, p.histProb n h * f h

theorem abs_expectH_le {n : ℕ} {f : (Fin n → Z) → ℝ} {C : ℝ}
    (hf : ∀ h, |f h| ≤ C) : |p.expectH n f| ≤ C := by
  calc |p.expectH n f| ≤ ∑ h : Fin n → Z, |p.histProb n h * f h| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h : Fin n → Z, p.histProb n h * C := by
        refine Finset.sum_le_sum fun h _ => ?_
        rw [abs_mul, abs_of_nonneg (p.histProb_nonneg n h)]
        exact mul_le_mul_of_nonneg_left (hf _) (p.histProb_nonneg n h)
    _ = C := by rw [← Finset.sum_mul, p.sum_histProb, one_mul]

/-- The expected discounted reward collected at date `n`. -/
noncomputable def payoff (n : ℕ) : ℝ := (D.discount : ℝ) ^ n * p.expectH n (p.rewardR n)

theorem abs_payoff_le (n : ℕ) :
    |p.payoff n| ≤ (D.discount : ℝ) ^ n * (|p.rewardFloor| + |D.rewardMax|) := by
  have hβ : (0 : ℝ) ≤ (D.discount : ℝ) ^ n := by positivity
  rw [payoff, abs_mul, abs_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left
    (p.abs_expectH_le fun h => p.abs_rewardR_le n h) hβ

theorem summable_payoff : Summable p.payoff := by
  have hβ1 : (D.discount : ℝ) < 1 := by exact_mod_cast D.discount_lt_one
  have hgeom : Summable fun n : ℕ => (D.discount : ℝ) ^ n * (|p.rewardFloor| + |D.rewardMax|) :=
    (summable_geometric_of_lt_one D.discount.coe_nonneg hβ1).mul_right _
  exact Summable.of_norm_bounded hgeom fun n => by simpa using p.abs_payoff_le n

/-- **The value of a contingent plan.** -/
noncomputable def value : ℝ := ∑' n, p.payoff n

/-- The expected value function at date `N`. -/
noncomputable def tail (N : ℕ) : ℝ :=
  ∑ h : Fin N → Z, p.histProb N h * D.valueFunction (p.state N h)

theorem abs_tail_le (N : ℕ) : |p.tail N| ≤ ‖D.valueFunction‖ :=
  p.abs_expectH_le (n := N) (f := fun h => D.valueFunction (p.state N h))
    fun h => D.valueFunction.norm_coe_le_norm _

/-- The Bellman inequality along the plan, as a comparison between REALS. -/
theorem step_le (n : ℕ) (h : Fin n → Z) :
    p.rewardR n h + (D.discount : ℝ) * ∑ z : Z, D.prob z (p.state n h, p.action n h)
        * D.valueFunction (p.state (n + 1) (Fin.snoc h z))
      ≤ D.valueFunction (p.state n h) := by
  have hfix : D.bellmanFn D.valueFunction (p.state n h) = D.valueFunction (p.state n h) := by
    conv_rhs => rw [← D.bellman_valueFunction]
    rfl
  have hle := hfix ▸ D.le_bellmanFn D.valueFunction (p.action_mem n h)
  rw [objectiveE, ← p.coe_reward n h, ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
  have hexp : D.expect D.valueFunction (p.state n h, p.action n h)
      = ∑ z : Z, D.prob z (p.state n h, p.action n h)
        * D.valueFunction (p.state (n + 1) (Fin.snoc h z)) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [p.state_succ n h z]
  rw [hexp] at hle
  exact hle

end Plan

/-! ### No plan beats the value function -/

theorem partialSum_add_tail_le {s₀ : S} (p : D.Plan s₀) (N : ℕ) :
    ∑ n ∈ Finset.range N, p.payoff n + (D.discount : ℝ) ^ N * p.tail N
      ≤ D.valueFunction s₀ := by
  induction N with
  | zero => simp [Plan.tail, p.state_zero]
  | succ N ih =>
      have hβ : (0 : ℝ) ≤ (D.discount : ℝ) ^ N := by positivity
      have havg : p.expectH N (p.rewardR N) + (D.discount : ℝ) * p.tail (N + 1) ≤ p.tail N := by
        have hsplit : p.tail (N + 1)
            = ∑ h : Fin N → Z, p.histProb N h
              * ∑ z : Z, D.prob z (p.state N h, p.action N h)
                * D.valueFunction (p.state (N + 1) (Fin.snoc h z)) := by
          rw [Plan.tail, sum_snoc]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Plan.histProb_snoc]
          ring
        rw [Plan.expectH, hsplit, Plan.tail, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun h _ => ?_
        nlinarith [mul_le_mul_of_nonneg_left (p.step_le N h) (p.histProb_nonneg N h)]
      have hscaled := mul_le_mul_of_nonneg_left havg hβ
      rw [Finset.sum_range_succ,
        show p.payoff N = (D.discount : ℝ) ^ N * p.expectH N (p.rewardR N) from rfl,
        show (D.discount : ℝ) ^ (N + 1) = (D.discount : ℝ) ^ N * D.discount from by ring]
      nlinarith [ih, hscaled]

theorem tendsto_tail_zero {s₀ : S} (p : D.Plan s₀) :
    Tendsto (fun N => (D.discount : ℝ) ^ N * p.tail N) atTop (𝓝 0) := by
  have hβ1 : (D.discount : ℝ) < 1 := by exact_mod_cast D.discount_lt_one
  have hgeom : Tendsto (fun N => (D.discount : ℝ) ^ N * ‖D.valueFunction‖) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one D.discount.coe_nonneg hβ1
    simpa using this.mul_const ‖D.valueFunction‖
  refine squeeze_zero_norm' ?_ hgeom
  filter_upwards with N
  have hβ : (0 : ℝ) ≤ (D.discount : ℝ) ^ N := by positivity
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hβ, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (p.abs_tail_le N) hβ

/-- **No floored contingent plan beats the value function.** -/
theorem Plan.value_le {s₀ : S} (p : D.Plan s₀) : p.value ≤ D.valueFunction s₀ := by
  have hsum : Tendsto (fun N => ∑ n ∈ Finset.range N, p.payoff n) atTop (𝓝 p.value) :=
    p.summable_payoff.hasSum.tendsto_sum_nat
  have hcomb : Tendsto (fun N => ∑ n ∈ Finset.range N, p.payoff n
      + (D.discount : ℝ) ^ N * p.tail N) atTop (𝓝 (p.value + 0)) :=
    hsum.add (tendsto_tail_zero p)
  rw [add_zero] at hcomb
  exact le_of_tendsto' hcomb fun N => partialSum_add_tail_le p N

/-! ### The greedy plan attains it -/

/-- The action the value function recommends. -/
noncomputable def policyAction (D : ExtendedStochasticProgram S A Z) (s : S) : A :=
  Classical.choose (D.exists_optimal_policy s)

theorem policyAction_mem (D : ExtendedStochasticProgram S A Z) (s : S) :
    D.policyAction s ∈ D.feasible s :=
  (Classical.choose_spec (D.exists_optimal_policy s)).1

theorem valueFunction_eq_policyAction (D : ExtendedStochasticProgram S A Z) (s : S) :
    ((D.valueFunction s : ℝ) : EReal)
      = D.reward (s, D.policyAction s)
        + ((D.discount * ∑ z, D.prob z (s, D.policyAction s)
            * D.valueFunction (D.transition z (s, D.policyAction s)) : ℝ) : EReal) :=
  (Classical.choose_spec (D.exists_optimal_policy s)).2

/-- **The reward at the recommended action is finite, and bounded below.** This is what gives the
greedy plan its floor: at the optimum the reward is a difference of two bounded reals. -/
theorem reward_policyAction_ge (D : ExtendedStochasticProgram S A Z) (s : S) :
    (-((1 + (D.discount : ℝ)) * ‖D.valueFunction‖) : ℝ)
      ≤ D.reward (s, D.policyAction s) := by
  have heq := D.valueFunction_eq_policyAction s
  set x : ℝ := (D.discount : ℝ) * ∑ z, D.prob z (s, D.policyAction s)
    * D.valueFunction (D.transition z (s, D.policyAction s)) with hx
  have htop : D.reward (s, D.policyAction s) ≠ ⊤ := fun htop => by
    simpa [htop] using D.reward_le _ _ (D.policyAction_mem s)
  have hbot : D.reward (s, D.policyAction s) ≠ ⊥ := fun hbot => by
    rw [hbot] at heq
    simp at heq
  have hcoe : (((D.reward (s, D.policyAction s)).toReal : ℝ) : EReal)
      = D.reward (s, D.policyAction s) := EReal.coe_toReal htop hbot
  rw [← hcoe, ← EReal.coe_add, EReal.coe_eq_coe_iff] at heq
  rw [← hcoe, EReal.coe_le_coe_iff]
  have hV : |D.valueFunction s| ≤ ‖D.valueFunction‖ := D.valueFunction.norm_coe_le_norm s
  have hx' : |x| ≤ (D.discount : ℝ) * ‖D.valueFunction‖ := by
    rw [hx, abs_mul, abs_of_nonneg D.discount.coe_nonneg]
    refine mul_le_mul_of_nonneg_left ?_ D.discount.coe_nonneg
    simpa [ExtendedStochasticProgram.expect] using
      D.abs_expect_le D.valueFunction (s, D.policyAction s)
  have h1 := abs_le.mp hV
  have h2 := abs_le.mp hx'
  nlinarith [h1.1, h1.2, h2.1, h2.2, heq]

/-- The state the recommended actions reach after a history. -/
noncomputable def policyState (D : ExtendedStochasticProgram S A Z) (s₀ : S) :
    ∀ n : ℕ, (Fin n → Z) → S
  | 0, _ => s₀
  | n + 1, h => D.transition (h (Fin.last n))
      (D.policyState s₀ n (Fin.init h), D.policyAction (D.policyState s₀ n (Fin.init h)))

@[simp] theorem policyState_snoc (D : ExtendedStochasticProgram S A Z) (s₀ : S) (n : ℕ)
    (h : Fin n → Z) (z : Z) :
    D.policyState s₀ (n + 1) (Fin.snoc h z)
      = D.transition z (D.policyState s₀ n h, D.policyAction (D.policyState s₀ n h)) := by
  simp only [policyState, Fin.init_snoc, Fin.snoc_last]

/-- **The greedy contingent plan**, with the floor the optimality equation provides. -/
noncomputable def policyPlan (D : ExtendedStochasticProgram S A Z) (s₀ : S) : D.Plan s₀ where
  state := D.policyState s₀
  action := fun n h => D.policyAction (D.policyState s₀ n h)
  state_zero := fun _ => rfl
  action_mem := fun _ _ => D.policyAction_mem _
  state_succ := fun n h z => D.policyState_snoc s₀ n h z
  rewardFloor := -((1 + (D.discount : ℝ)) * ‖D.valueFunction‖)
  le_reward := fun n h => D.reward_policyAction_ge _

theorem policy_partialSum_add_tail (D : ExtendedStochasticProgram S A Z) (s₀ : S) (N : ℕ) :
    ∑ n ∈ Finset.range N, (D.policyPlan s₀).payoff n
        + (D.discount : ℝ) ^ N * (D.policyPlan s₀).tail N
      = D.valueFunction s₀ := by
  have hopt : ∀ (n : ℕ) (h : Fin n → Z),
      ((D.valueFunction ((D.policyPlan s₀).state n h) : ℝ) : EReal)
        = D.reward ((D.policyPlan s₀).state n h, (D.policyPlan s₀).action n h)
          + (((D.discount : ℝ) * ∑ z : Z,
              D.prob z ((D.policyPlan s₀).state n h, (D.policyPlan s₀).action n h)
                * D.valueFunction (D.transition z
                    ((D.policyPlan s₀).state n h, (D.policyPlan s₀).action n h)) : ℝ) : EReal) :=
    fun n h => D.valueFunction_eq_policyAction _
  set p := D.policyPlan s₀ with hp
  induction N with
  | zero => simp [Plan.tail, hp, policyPlan, policyState]
  | succ N ih =>
      have hβ : (0 : ℝ) ≤ (D.discount : ℝ) ^ N := by positivity
      have hstep : ∀ h : Fin N → Z,
          p.rewardR N h + (D.discount : ℝ) * ∑ z : Z, D.prob z (p.state N h, p.action N h)
              * D.valueFunction (p.state (N + 1) (Fin.snoc h z))
            = D.valueFunction (p.state N h) := by
        intro h
        have heq := hopt N h
        rw [← p.coe_reward N h, ← EReal.coe_add, EReal.coe_eq_coe_iff] at heq
        have hexp : ∑ z : Z, D.prob z (p.state N h, p.action N h)
            * D.valueFunction (p.state (N + 1) (Fin.snoc h z))
            = ∑ z : Z, D.prob z (p.state N h, p.action N h)
              * D.valueFunction (D.transition z (p.state N h, p.action N h)) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [p.state_succ N h z]
        rw [hexp, p.rewardR_eq N h]
        linarith [heq]
      have havg : p.expectH N (p.rewardR N) + (D.discount : ℝ) * p.tail (N + 1) = p.tail N := by
        have hsplit : p.tail (N + 1)
            = ∑ h : Fin N → Z, p.histProb N h
              * ∑ z : Z, D.prob z (p.state N h, p.action N h)
                * D.valueFunction (p.state (N + 1) (Fin.snoc h z)) := by
          rw [Plan.tail, sum_snoc]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Plan.histProb_snoc]
          ring
        rw [Plan.expectH, hsplit, Plan.tail, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun h _ => ?_
        linear_combination (p.histProb N h) * hstep h
      have hscaled : (D.discount : ℝ) ^ N * (p.expectH N (p.rewardR N)
          + (D.discount : ℝ) * p.tail (N + 1))
          = (D.discount : ℝ) ^ N * p.tail N := by rw [havg]
      rw [Finset.sum_range_succ,
        show p.payoff N = (D.discount : ℝ) ^ N * p.expectH N (p.rewardR N) from rfl,
        show (D.discount : ℝ) ^ (N + 1) = (D.discount : ℝ) ^ N * D.discount from by ring]
      nlinarith [ih, hscaled]

/-- **The greedy plan attains the value function.** -/
theorem policyPlan_value (D : ExtendedStochasticProgram S A Z) (s₀ : S) :
    (D.policyPlan s₀).value = D.valueFunction s₀ := by
  have hsum : Tendsto (fun N => ∑ n ∈ Finset.range N, (D.policyPlan s₀).payoff n) atTop
      (𝓝 (D.policyPlan s₀).value) :=
    (D.policyPlan s₀).summable_payoff.hasSum.tendsto_sum_nat
  have hcomb : Tendsto (fun N => ∑ n ∈ Finset.range N, (D.policyPlan s₀).payoff n
      + (D.discount : ℝ) ^ N * (D.policyPlan s₀).tail N) atTop
      (𝓝 ((D.policyPlan s₀).value + 0)) :=
    hsum.add (tendsto_tail_zero (D.policyPlan s₀))
  rw [add_zero] at hcomb
  exact tendsto_nhds_unique (hcomb.congr fun N => D.policy_partialSum_add_tail s₀ N)
    tendsto_const_nhds

/-! ### The principle of optimality -/

/-- **The value function is the greatest value any floored contingent plan achieves, and it is
achieved.** -/
theorem isGreatest_planValue (s₀ : S) :
    IsGreatest (Set.range (Plan.value : D.Plan s₀ → ℝ)) (D.valueFunction s₀) :=
  ⟨⟨D.policyPlan s₀, D.policyPlan_value s₀⟩, by
    rintro x ⟨p, rfl⟩
    exact p.value_le⟩

/-- **The stochastic sequence problem**, for the extended program. -/
noncomputable def seqValue (s₀ : S) : ℝ := ⨆ p : D.Plan s₀, p.value

/-- **The principle of optimality, with shocks and `⊥` rewards.** -/
theorem valueFunction_eq_seqValue (s₀ : S) : D.valueFunction s₀ = D.seqValue s₀ :=
  ((D.isGreatest_planValue s₀).csSup_eq).symm

/-- **Acting greedily on the value function solves the sequence problem.** -/
theorem policyPlan_isOptimal (s₀ : S) : (D.policyPlan s₀).value = D.seqValue s₀ := by
  rw [D.policyPlan_value, D.valueFunction_eq_seqValue]

end ExtendedStochasticProgram

end LeanEconomics
