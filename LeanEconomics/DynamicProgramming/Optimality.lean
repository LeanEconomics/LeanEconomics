/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Bellman
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The principle of optimality

Everything proved so far is about the fixed point of an operator. That is not, on its face, a
statement about an economic agent: nothing yet says the fixed point is the best the agent can do
over an infinite horizon. This file supplies the missing identification.

  `valueFunction s₀ = ⨆ { ∑' n, βⁿ · r (xₙ, aₙ) | (x, a) a feasible plan from s₀ }`

and the supremum is ATTAINED, by the plan that acts greedily on the value function at every date.

## Why this is the load-bearing theorem

Without it, `bellman_valueFunction` says only that a certain functional equation has a solution.
A reader is entitled to ask why that solution is the household's lifetime utility, and the answer
is not definitional -- it is `valueFunction_eq_seqValue` below. Every downstream result about
policies, distributions and equilibria inherits its economic reading from this one theorem.

## The two halves

The easy half is that no plan beats the value function. Iterating the Bellman inequality
`V s ≥ r (s, a) + β V (g (s, a))` along any feasible plan gives

  `V s₀ ≥ ∑_{n < N} βⁿ rₙ + βᴺ V xₙ`,

and the tail `βᴺ V xₙ` vanishes because `V` is BOUNDED and `β < 1`. This is where boundedness of
the value function earns its keep: for an unbounded `V` the tail need not vanish, plans of
infinite value become possible, and the principle of optimality genuinely fails.

The other half needs the supremum to be attained at each date, which is Berge's theorem again,
already available as `exists_optimal_policy`. Acting on it turns the Bellman INEQUALITY into an
equality at every step, so the same telescoping gives `V s₀ = plan value` exactly.

## Main results

* `LeanEconomics.DynamicProgram.Plan` : a feasible infinite-horizon plan.
* `LeanEconomics.DynamicProgram.Plan.value_le` : no plan beats the value function.
* `LeanEconomics.DynamicProgram.policyPlan_value` : the greedy plan attains it.
* `LeanEconomics.DynamicProgram.isGreatest_planValue` : both halves at once.
* `LeanEconomics.DynamicProgram.valueFunction_eq_seqValue` : the principle of optimality.

## Reference

Stokey, Lucas and Prescott, *Recursive Methods in Economic Dynamics*, theorems 4.2--4.5.
-/

open scoped NNReal
open Filter Topology

namespace LeanEconomics

variable {S A : Type*} [TopologicalSpace S] [TopologicalSpace A]

namespace DynamicProgram

variable (D : DynamicProgram S A)

/-- **A feasible plan from `s₀`**: the states it visits and the actions it takes, with each
action feasible at the state it is taken in and each state produced by the law of motion. -/
structure Plan (s₀ : S) where
  /-- The state at each date. -/
  state : ℕ → S
  /-- The action taken at each date. -/
  action : ℕ → A
  state_zero : state 0 = s₀
  action_mem : ∀ n, action n ∈ D.feasible (state n)
  state_succ : ∀ n, state (n + 1) = D.transition (state n, action n)

variable {D}

namespace Plan

variable {s₀ : S} (p : D.Plan s₀)

/-- The discounted reward collected at date `n`. -/
noncomputable def payoff (n : ℕ) : ℝ :=
  (D.discount : ℝ) ^ n * D.reward (p.state n, p.action n)

theorem abs_payoff_le (n : ℕ) : |p.payoff n| ≤ (D.discount : ℝ) ^ n * ‖D.reward‖ := by
  have hβ : (0 : ℝ) ≤ (D.discount : ℝ) ^ n := by positivity
  rw [payoff, abs_mul, abs_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left (D.reward.norm_coe_le_norm _) hβ

/-- The reward stream is absolutely summable: the rewards are bounded and the discounting is
geometric. -/
theorem summable_payoff : Summable p.payoff := by
  have hβ1 : (D.discount : ℝ) < 1 := by exact_mod_cast D.discount_lt_one
  have hgeom : Summable fun n : ℕ => (D.discount : ℝ) ^ n * ‖D.reward‖ :=
    (summable_geometric_of_lt_one D.discount.coe_nonneg hβ1).mul_right _
  exact Summable.of_norm_bounded hgeom fun n => by simpa using p.abs_payoff_le n

/-- **The value of a plan**: its discounted reward stream. -/
noncomputable def value : ℝ := ∑' n, p.payoff n

end Plan

/-! ### No plan beats the value function -/

/-- The telescoping identity, as an inequality. Along any feasible plan the value function
dominates the rewards collected so far plus the discounted value of where the plan has got to. -/
theorem partialSum_add_tail_le {s₀ : S} (p : D.Plan s₀) (N : ℕ) :
    ∑ n ∈ Finset.range N, p.payoff n
        + (D.discount : ℝ) ^ N * D.valueFunction (p.state N)
      ≤ D.valueFunction s₀ := by
  induction N with
  | zero => simp [p.state_zero]
  | succ N ih =>
      have hβ : (0 : ℝ) ≤ (D.discount : ℝ) ^ N := by positivity
      -- the value function is its own Bellman value at the state the plan has reached
      have hfix : D.bellmanFn D.valueFunction (p.state N) = D.valueFunction (p.state N) := by
        conv_rhs => rw [← D.bellman_valueFunction]
        rfl
      have hstep : D.objective D.valueFunction (p.state N) (p.action N)
          ≤ D.valueFunction (p.state N) :=
        hfix ▸ D.le_bellmanFn D.valueFunction (p.action_mem N)
      have hexp : D.objective D.valueFunction (p.state N) (p.action N)
          = D.reward (p.state N, p.action N)
            + D.discount * D.valueFunction (p.state (N + 1)) := by
        rw [objective, p.state_succ N]
      rw [hexp] at hstep
      have hscaled : (D.discount : ℝ) ^ N * D.reward (p.state N, p.action N)
            + (D.discount : ℝ) ^ N * D.discount * D.valueFunction (p.state (N + 1))
          ≤ (D.discount : ℝ) ^ N * D.valueFunction (p.state N) := by
        nlinarith [mul_le_mul_of_nonneg_left hstep hβ]
      rw [Finset.sum_range_succ,
        show p.payoff N = (D.discount : ℝ) ^ N * D.reward (p.state N, p.action N) from rfl,
        show (D.discount : ℝ) ^ (N + 1) = (D.discount : ℝ) ^ N * D.discount from by ring]
      linarith [ih, hscaled]

/-- The discounted tail vanishes, because the value function is bounded and `β < 1`. -/
theorem tendsto_tail_zero {s₀ : S} (p : D.Plan s₀) :
    Tendsto (fun N => (D.discount : ℝ) ^ N * D.valueFunction (p.state N)) atTop (𝓝 0) := by
  have hβ1 : (D.discount : ℝ) < 1 := by exact_mod_cast D.discount_lt_one
  have hgeom : Tendsto (fun N => (D.discount : ℝ) ^ N * ‖D.valueFunction‖) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one D.discount.coe_nonneg hβ1
    simpa using this.mul_const ‖D.valueFunction‖
  refine squeeze_zero_norm' ?_ hgeom
  filter_upwards with N
  have hβ : (0 : ℝ) ≤ (D.discount : ℝ) ^ N := by positivity
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hβ, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (D.valueFunction.norm_coe_le_norm _) hβ

/-- **No feasible plan beats the value function.** -/
theorem Plan.value_le {s₀ : S} (p : D.Plan s₀) : p.value ≤ D.valueFunction s₀ := by
  have hsum : Tendsto (fun N => ∑ n ∈ Finset.range N, p.payoff n) atTop (𝓝 p.value) :=
    p.summable_payoff.hasSum.tendsto_sum_nat
  have hcomb : Tendsto (fun N => ∑ n ∈ Finset.range N, p.payoff n
      + (D.discount : ℝ) ^ N * D.valueFunction (p.state N)) atTop (𝓝 (p.value + 0)) :=
    hsum.add (tendsto_tail_zero p)
  rw [add_zero] at hcomb
  exact le_of_tendsto' hcomb fun N => partialSum_add_tail_le p N

/-! ### The greedy plan attains it

`exists_optimal_policy` picks, at every state, an action attaining the Bellman value. Following
it turns the inequality above into an equality at every date. -/

/-- The action the value function recommends. -/
noncomputable def policyAction (D : DynamicProgram S A) (s : S) : A :=
  Classical.choose (D.exists_optimal_policy s)

theorem policyAction_mem (D : DynamicProgram S A) (s : S) :
    D.policyAction s ∈ D.feasible s :=
  (Classical.choose_spec (D.exists_optimal_policy s)).1

theorem valueFunction_eq_policyAction (D : DynamicProgram S A) (s : S) :
    D.valueFunction s = D.reward (s, D.policyAction s)
      + D.discount * D.valueFunction (D.transition (s, D.policyAction s)) :=
  (Classical.choose_spec (D.exists_optimal_policy s)).2

/-- The state path the recommended actions trace out. -/
noncomputable def policyState (D : DynamicProgram S A) (s₀ : S) : ℕ → S
  | 0 => s₀
  | n + 1 => D.transition (policyState D s₀ n, D.policyAction (policyState D s₀ n))

@[simp] theorem policyState_zero (D : DynamicProgram S A) (s₀ : S) :
    D.policyState s₀ 0 = s₀ := rfl

@[simp] theorem policyState_succ (D : DynamicProgram S A) (s₀ : S) (n : ℕ) :
    D.policyState s₀ (n + 1)
      = D.transition (D.policyState s₀ n, D.policyAction (D.policyState s₀ n)) := rfl

/-- **The greedy plan**: act on the value function's recommendation at every date. -/
noncomputable def policyPlan (D : DynamicProgram S A) (s₀ : S) : D.Plan s₀ where
  state := D.policyState s₀
  action := fun n => D.policyAction (D.policyState s₀ n)
  state_zero := rfl
  action_mem := fun _ => D.policyAction_mem _
  state_succ := fun _ => rfl

@[simp] theorem policyPlan_state (D : DynamicProgram S A) (s₀ : S) (n : ℕ) :
    (D.policyPlan s₀).state n = D.policyState s₀ n := rfl

/-- The telescoping identity, as an equality: along the greedy plan nothing is given up. -/
theorem policy_partialSum_add_tail (D : DynamicProgram S A) (s₀ : S) (N : ℕ) :
    ∑ n ∈ Finset.range N, (D.policyPlan s₀).payoff n
        + (D.discount : ℝ) ^ N * D.valueFunction (D.policyState s₀ N)
      = D.valueFunction s₀ := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hstep := D.valueFunction_eq_policyAction (D.policyState s₀ N)
      have hpay : (D.policyPlan s₀).payoff N = (D.discount : ℝ) ^ N
          * D.reward (D.policyState s₀ N, D.policyAction (D.policyState s₀ N)) := rfl
      rw [Finset.sum_range_succ, hpay, D.policyState_succ s₀ N,
        show (D.discount : ℝ) ^ (N + 1) = (D.discount : ℝ) ^ N * D.discount from by ring]
      have hscaled : (D.discount : ℝ) ^ N
            * D.reward (D.policyState s₀ N, D.policyAction (D.policyState s₀ N))
            + (D.discount : ℝ) ^ N * D.discount
              * D.valueFunction (D.transition (D.policyState s₀ N,
                  D.policyAction (D.policyState s₀ N)))
          = (D.discount : ℝ) ^ N * D.valueFunction (D.policyState s₀ N) := by
        rw [hstep]; ring
      linarith [ih, hscaled]

/-- **The greedy plan attains the value function.** -/
theorem policyPlan_value (D : DynamicProgram S A) (s₀ : S) :
    (D.policyPlan s₀).value = D.valueFunction s₀ := by
  have hsum : Tendsto (fun N => ∑ n ∈ Finset.range N, (D.policyPlan s₀).payoff n) atTop
      (𝓝 (D.policyPlan s₀).value) :=
    (D.policyPlan s₀).summable_payoff.hasSum.tendsto_sum_nat
  have hcomb : Tendsto (fun N => ∑ n ∈ Finset.range N, (D.policyPlan s₀).payoff n
      + (D.discount : ℝ) ^ N * D.valueFunction ((D.policyPlan s₀).state N)) atTop
      (𝓝 ((D.policyPlan s₀).value + 0)) :=
    hsum.add (tendsto_tail_zero (D.policyPlan s₀))
  rw [add_zero] at hcomb
  exact tendsto_nhds_unique (hcomb.congr fun N => D.policy_partialSum_add_tail s₀ N)
    tendsto_const_nhds

/-! ### The principle of optimality -/

/-- **The value function is the greatest value any feasible plan achieves, and it is achieved.**
Both halves of the principle of optimality in one statement. -/
theorem isGreatest_planValue (s₀ : S) :
    IsGreatest (Set.range (Plan.value : D.Plan s₀ → ℝ)) (D.valueFunction s₀) :=
  ⟨⟨D.policyPlan s₀, D.policyPlan_value s₀⟩, by
    rintro x ⟨p, rfl⟩
    exact p.value_le⟩

/-- **The sequence problem**: the best an agent can do from `s₀` over the infinite horizon. -/
noncomputable def seqValue (s₀ : S) : ℝ := ⨆ p : D.Plan s₀, p.value

/-- **The principle of optimality.** The fixed point of the Bellman operator IS the value of the
sequence problem. This is what licenses reading every downstream result -- policies, stationary
distributions, equilibria -- as statements about optimising agents. -/
theorem valueFunction_eq_seqValue (s₀ : S) : D.valueFunction s₀ = D.seqValue s₀ :=
  ((D.isGreatest_planValue s₀).csSup_eq).symm

/-- **Acting greedily on the value function solves the sequence problem.** The operational form:
one need never reason about infinite-horizon plans, only about a functional equation. -/
theorem policyPlan_isOptimal (s₀ : S) : (D.policyPlan s₀).value = D.seqValue s₀ := by
  rw [D.policyPlan_value, D.valueFunction_eq_seqValue]

end DynamicProgram

end LeanEconomics
