/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuation
import LeanEconomics.DynamicProgramming.ExtendedStochasticOptimality

/-!
# The household's problem is a sequence problem

Everything in this development about the income-fluctuation household is stated about the fixed
point of a Bellman operator. `DynamicProgramming.ExtendedStochasticOptimality` identifies that
fixed point with the value of the contingent-plan problem, and this file records the
identification for the household itself:

  `valueFunction (a, z) = ⨆ { E ∑' t, βᵗ u(cₜ) | feasible contingent plans from (a, z) }`,

attained by the plan that saves `policy` every period. So the policy function, the stationary
distribution built from it, the aggregate capital it implies and the equilibrium rate that
clears the market are all statements about a household maximising expected discounted utility
over the infinite horizon — not merely about a functional equation.

The plan carries a reward floor, which for this model says the household never chooses a
consumption at which utility is `-∞`. Nothing is lost: the optimal plan has such a floor
automatically, since at the optimum the reward is the value function minus a discounted
continuation, and both are bounded.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **The principle of optimality for the household.** The value function is the best expected
discounted utility any feasible contingent plan achieves. -/
theorem valueFunction_eq_seqValue (s : ℝ × Z) :
    P.toExtended.valueFunction s = P.toExtended.seqValue s :=
  P.toExtended.valueFunction_eq_seqValue s

/-- **The greedy plan solves it.** Saving `policy` every period is optimal over the infinite
horizon, not just one step at a time. -/
theorem policyPlan_isOptimal (s : ℝ × Z) :
    (P.toExtended.policyPlan s).value = P.toExtended.seqValue s :=
  P.toExtended.policyPlan_isOptimal s

/-- **The supremum is attained**, and nothing beats it. -/
theorem isGreatest_planValue (s : ℝ × Z) :
    IsGreatest (Set.range
      (ExtendedStochasticProgram.Plan.value : P.toExtended.Plan s → ℝ))
      (P.toExtended.valueFunction s) :=
  P.toExtended.isGreatest_planValue s

end IncomeFluctuation

end LeanEconomics
