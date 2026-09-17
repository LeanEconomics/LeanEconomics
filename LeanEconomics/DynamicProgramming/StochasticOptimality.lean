/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Stochastic
import LeanEconomics.DynamicProgramming.Optimality

/-!
# The principle of optimality, with shocks

`DynamicProgramming.Optimality` identifies the fixed point of the deterministic Bellman operator
with the value of the sequence problem. Every model in this development is stochastic, so that
identification does not reach them: the income-fluctuation household faces a shock, and what it
chooses is not a sequence of actions but a CONTINGENT PLAN.

This file supplies the stochastic statement.

  `valueFunction s₀ = ⨆ { E ∑' n, βⁿ · r (xₙ, aₙ) | contingent plans from s₀ }`

with the supremum attained by the plan that acts greedily on the value function.

## What changes, and what does not

A plan is now indexed by shock histories: at date `n` the agent has seen `h : Fin n → Z` and
picks `action n h`, feasible at `state n h`, and the state it reaches after one more shock `z` is
`transition z` applied to where it was (`Fin.snoc h z` is the history extended by `z`). The
weight attached to a history is the product of the one-step probabilities along it
(`histProb`), and the date-`n` payoff is the EXPECTATION of the reward over histories.

Two facts about those weights carry the whole argument, and they are the same two that make the
operator a contraction: they are non-negative, so the Bellman inequality survives averaging, and
they sum to one, so the expected value of a bounded function is bounded by the same bound. The
telescoping is then verbatim the deterministic one with `V (state N)` replaced by its
expectation over histories.

The ordering of the sum is where the work is. Splitting a history of length `n + 1` into its
first `n` shocks and its last one (`Fin.snocEquiv`) is what turns the date-`n` expectation of the
one-step expectation into the date-`(n+1)` expectation, and that identity is the only real
content below.
-/

open scoped NNReal
open Filter Topology

namespace LeanEconomics

variable {S A Z : Type*} [TopologicalSpace S] [TopologicalSpace A] [Fintype Z]

/-- Splitting a history into its past and its last shock. This is the only combinatorial fact
the argument needs. -/
theorem sum_snoc {n : ℕ} (f : (Fin (n + 1) → Z) → ℝ) :
    ∑ h : Fin (n + 1) → Z, f h = ∑ h : Fin n → Z, ∑ z : Z, f (Fin.snoc h z) := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ : Fin (n + 1) => Z)
    (fun p : Z × (Fin n → Z) => f (Fin.snoc p.2 p.1)) f fun p => rfl]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

namespace StochasticDynamicProgram

variable (D : StochasticDynamicProgram S A Z)

/-- **A feasible contingent plan from `s₀`**: a state and an action for every shock history,
each action feasible where it is taken, each state produced by the law of motion. -/
structure Plan (s₀ : S) where
  /-- The state reached after the history `h`. -/
  state : ∀ n : ℕ, (Fin n → Z) → S
  /-- The action taken after the history `h`. -/
  action : ∀ n : ℕ, (Fin n → Z) → A
  state_zero : ∀ h : Fin 0 → Z, state 0 h = s₀
  action_mem : ∀ (n : ℕ) (h : Fin n → Z), action n h ∈ D.feasible (state n h)
  state_succ : ∀ (n : ℕ) (h : Fin n → Z) (z : Z),
    state (n + 1) (Fin.snoc h z) = D.transition z (state n h, action n h)

variable {D}

namespace Plan

variable {s₀ : S} (p : D.Plan s₀)

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

/-- The expectation of a function of the date-`n` state and action. -/
noncomputable def expect (n : ℕ) (f : S → A → ℝ) : ℝ :=
  ∑ h : Fin n → Z, p.histProb n h * f (p.state n h) (p.action n h)

theorem abs_expect_le {n : ℕ} {f : S → A → ℝ} {C : ℝ} (hf : ∀ s a, |f s a| ≤ C) :
    |p.expect n f| ≤ C := by
  calc |p.expect n f| ≤ ∑ h : Fin n → Z, |p.histProb n h * f (p.state n h) (p.action n h)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h : Fin n → Z, p.histProb n h * C := by
        refine Finset.sum_le_sum fun h _ => ?_
        rw [abs_mul, abs_of_nonneg (p.histProb_nonneg n h)]
        exact mul_le_mul_of_nonneg_left (hf _ _) (p.histProb_nonneg n h)
    _ = C := by rw [← Finset.sum_mul, p.sum_histProb, one_mul]

/-- The expected discounted reward collected at date `n`. -/
noncomputable def payoff (n : ℕ) : ℝ :=
  (D.discount : ℝ) ^ n * p.expect n fun s a => D.reward (s, a)

theorem abs_payoff_le (n : ℕ) : |p.payoff n| ≤ (D.discount : ℝ) ^ n * ‖D.reward‖ := by
  have hβ : (0 : ℝ) ≤ (D.discount : ℝ) ^ n := by positivity
  rw [payoff, abs_mul, abs_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left
    (p.abs_expect_le fun s a => D.reward.norm_coe_le_norm (s, a)) hβ

theorem summable_payoff : Summable p.payoff := by
  have hβ1 : (D.discount : ℝ) < 1 := by exact_mod_cast D.discount_lt_one
  have hgeom : Summable fun n : ℕ => (D.discount : ℝ) ^ n * ‖D.reward‖ :=
    (summable_geometric_of_lt_one D.discount.coe_nonneg hβ1).mul_right _
  exact Summable.of_norm_bounded hgeom fun n => by simpa using p.abs_payoff_le n

/-- **The value of a contingent plan**: its expected discounted reward stream. -/
noncomputable def value : ℝ := ∑' n, p.payoff n

/-- The expected value function at date `N`. -/
noncomputable def tail (N : ℕ) : ℝ :=
  ∑ h : Fin N → Z, p.histProb N h * D.valueFunction (p.state N h)

theorem abs_tail_le (N : ℕ) : |p.tail N| ≤ ‖D.valueFunction‖ := by
  have := p.abs_expect_le (n := N) (f := fun s _ => D.valueFunction s)
    (fun s _ => D.valueFunction.norm_coe_le_norm s)
  simpa [expect, tail] using this

end Plan

/-! ### No plan beats the value function -/

theorem partialSum_add_tail_le {s₀ : S} (p : D.Plan s₀) (N : ℕ) :
    ∑ n ∈ Finset.range N, p.payoff n + (D.discount : ℝ) ^ N * p.tail N
      ≤ D.valueFunction s₀ := by
  induction N with
  | zero => simp [Plan.tail, p.state_zero]
  | succ N ih =>
      have hβ : (0 : ℝ) ≤ (D.discount : ℝ) ^ N := by positivity
      have hβ0 : (0 : ℝ) ≤ (D.discount : ℝ) := D.discount.coe_nonneg
      -- the Bellman inequality, history by history
      have hstep : ∀ h : Fin N → Z,
          D.reward (p.state N h, p.action N h)
            + (D.discount : ℝ) * ∑ z : Z, D.prob z (p.state N h, p.action N h)
              * D.valueFunction (p.state (N + 1) (Fin.snoc h z))
            ≤ D.valueFunction (p.state N h) := by
        intro h
        have hfix : D.bellmanFn D.valueFunction (p.state N h) = D.valueFunction (p.state N h) := by
          conv_rhs => rw [← D.bellman_valueFunction]
          rfl
        have hle := hfix ▸ D.le_bellmanFn D.valueFunction (p.action_mem N h)
        simp only [objective, expectation] at hle
        refine le_trans (le_of_eq ?_) hle
        refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun z _ => ?_))
        rw [p.state_succ N h z]
      -- average it over histories
      have havg : p.expect N (fun s a => D.reward (s, a))
          + (D.discount : ℝ) * p.tail (N + 1) ≤ p.tail N := by
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
        rw [Plan.expect, hsplit, Plan.tail, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun h _ => ?_
        have := mul_le_mul_of_nonneg_left (hstep h) (p.histProb_nonneg N h)
        nlinarith [this]
      have hscaled := mul_le_mul_of_nonneg_left havg hβ
      rw [Finset.sum_range_succ,
        show p.payoff N = (D.discount : ℝ) ^ N * p.expect N (fun s a => D.reward (s, a)) from rfl,
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

/-- **No contingent plan beats the value function.** -/
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
noncomputable def policyAction (D : StochasticDynamicProgram S A Z) (s : S) : A :=
  Classical.choose (D.exists_optimal_policy s)

theorem policyAction_mem (D : StochasticDynamicProgram S A Z) (s : S) :
    D.policyAction s ∈ D.feasible s :=
  (Classical.choose_spec (D.exists_optimal_policy s)).1

theorem valueFunction_eq_policyAction (D : StochasticDynamicProgram S A Z) (s : S) :
    D.valueFunction s = D.reward (s, D.policyAction s)
      + D.discount * ∑ z, D.prob z (s, D.policyAction s)
        * D.valueFunction (D.transition z (s, D.policyAction s)) :=
  (Classical.choose_spec (D.exists_optimal_policy s)).2

/-- The state the recommended actions reach after a history. -/
noncomputable def policyState (D : StochasticDynamicProgram S A Z) (s₀ : S) :
    ∀ n : ℕ, (Fin n → Z) → S
  | 0, _ => s₀
  | n + 1, h => D.transition (h (Fin.last n))
      (D.policyState s₀ n (Fin.init h), D.policyAction (D.policyState s₀ n (Fin.init h)))

@[simp] theorem policyState_snoc (D : StochasticDynamicProgram S A Z) (s₀ : S) (n : ℕ)
    (h : Fin n → Z) (z : Z) :
    D.policyState s₀ (n + 1) (Fin.snoc h z)
      = D.transition z (D.policyState s₀ n h, D.policyAction (D.policyState s₀ n h)) := by
  simp only [policyState, Fin.init_snoc, Fin.snoc_last]

/-- **The greedy contingent plan.** -/
noncomputable def policyPlan (D : StochasticDynamicProgram S A Z) (s₀ : S) : D.Plan s₀ where
  state := D.policyState s₀
  action := fun n h => D.policyAction (D.policyState s₀ n h)
  state_zero := fun _ => rfl
  action_mem := fun _ _ => D.policyAction_mem _
  state_succ := fun n h z => D.policyState_snoc s₀ n h z

theorem policy_partialSum_add_tail (D : StochasticDynamicProgram S A Z) (s₀ : S) (N : ℕ) :
    ∑ n ∈ Finset.range N, (D.policyPlan s₀).payoff n
        + (D.discount : ℝ) ^ N * (D.policyPlan s₀).tail N
      = D.valueFunction s₀ := by
  -- the Bellman EQUATION holds along the greedy plan, history by history
  have hopt : ∀ (n : ℕ) (h : Fin n → Z),
      D.valueFunction ((D.policyPlan s₀).state n h)
        = D.reward ((D.policyPlan s₀).state n h, (D.policyPlan s₀).action n h)
          + (D.discount : ℝ) * ∑ z : Z,
              D.prob z ((D.policyPlan s₀).state n h, (D.policyPlan s₀).action n h)
                * D.valueFunction (D.transition z
                    ((D.policyPlan s₀).state n h, (D.policyPlan s₀).action n h)) :=
    fun n h => D.valueFunction_eq_policyAction _
  set p := D.policyPlan s₀ with hp
  induction N with
  | zero => simp [Plan.tail, hp, policyPlan, policyState]
  | succ N ih =>
      have hβ : (0 : ℝ) ≤ (D.discount : ℝ) ^ N := by positivity
      have hstep : ∀ h : Fin N → Z,
          D.reward (p.state N h, p.action N h)
            + (D.discount : ℝ) * ∑ z : Z, D.prob z (p.state N h, p.action N h)
              * D.valueFunction (p.state (N + 1) (Fin.snoc h z))
            = D.valueFunction (p.state N h) := by
        intro h
        rw [hopt N h]
        refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun z _ => ?_))
        rw [p.state_succ N h z]
      have havg : p.expect N (fun s a => D.reward (s, a))
          + (D.discount : ℝ) * p.tail (N + 1) = p.tail N := by
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
        rw [Plan.expect, hsplit, Plan.tail, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun h _ => ?_
        linear_combination (p.histProb N h) * hstep h
      have hscaled : (D.discount : ℝ) ^ N * (p.expect N (fun s a => D.reward (s, a))
          + (D.discount : ℝ) * p.tail (N + 1))
          = (D.discount : ℝ) ^ N * p.tail N := by rw [havg]
      rw [Finset.sum_range_succ,
        show p.payoff N = (D.discount : ℝ) ^ N * p.expect N (fun s a => D.reward (s, a)) from rfl,
        show (D.discount : ℝ) ^ (N + 1) = (D.discount : ℝ) ^ N * D.discount from by ring]
      nlinarith [ih, hscaled]

/-- **The greedy plan attains the value function.** -/
theorem policyPlan_value (D : StochasticDynamicProgram S A Z) (s₀ : S) :
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

/-- **The value function is the greatest value any contingent plan achieves, and it is
achieved.** -/
theorem isGreatest_planValue (s₀ : S) :
    IsGreatest (Set.range (Plan.value : D.Plan s₀ → ℝ)) (D.valueFunction s₀) :=
  ⟨⟨D.policyPlan s₀, D.policyPlan_value s₀⟩, by
    rintro x ⟨p, rfl⟩
    exact p.value_le⟩

/-- **The stochastic sequence problem.** -/
noncomputable def seqValue (s₀ : S) : ℝ := ⨆ p : D.Plan s₀, p.value

/-- **The principle of optimality, with shocks.** The fixed point of the stochastic Bellman
operator IS the value of the contingent-plan problem. -/
theorem valueFunction_eq_seqValue (s₀ : S) : D.valueFunction s₀ = D.seqValue s₀ :=
  ((D.isGreatest_planValue s₀).csSup_eq).symm

/-- **Acting greedily on the value function solves the stochastic sequence problem.** -/
theorem policyPlan_isOptimal (s₀ : S) : (D.policyPlan s₀).value = D.seqValue s₀ := by
  rw [D.policyPlan_value, D.valueFunction_eq_seqValue]

end StochasticDynamicProgram

end LeanEconomics
