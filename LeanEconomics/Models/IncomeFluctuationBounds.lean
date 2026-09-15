/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuation

/-!
# Consumption at the optimum is bounded away from zero

Positivity of optimal consumption is already known pointwise: a zero would make the reward
`⊥` and the value could not be real. What is needed for comparative statics is a UNIFORM
bound, a single `δ > 0` working at every state.

The bound proved here is explicit rather than compactness-based, and that is the whole point.
A compactness argument would say that optimal consumption is continuous and positive on a
compact state space, hence has a positive minimum — true, and recorded below as a sanity
check, but useless for the parametric problem. There the bound has to be uniform over an
interval of interest rates as well, and the corresponding compactness argument would need
joint continuity in `(r, s)`, which is precisely what the bound is wanted to prove. It would
be circular.

The explicit route avoids that. At the optimum the Bellman equation reads

  V s = u c* + β · E[V]

so `u c* ≥ -(1 + β)‖V‖`, a lower bound on the UTILITY of optimal consumption depending only
on the sup norm of the value function. Since `u` falls to `-∞` at zero, that pins consumption
away from zero. Nothing in the argument refers to the state, so the bound is automatically
uniform in the state; and when `r` varies, `‖V‖` is controlled by the reward bounds, which are
themselves uniform over a compact interval of rates.
-/

open Set Filter Topology

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable (P : IncomeFluctuation Z)

/-- The expected continuation value is bounded by the sup norm of the value function. -/
theorem abs_expectation_le (a : ℝ) (z : Z) :
    |∑ z', P.transitionMatrix z z' * P.toExtended.valueFunction (a, z')|
      ≤ ‖P.toExtended.valueFunction‖ := by
  calc |∑ z', P.transitionMatrix z z' * P.toExtended.valueFunction (a, z')|
      ≤ ∑ z', |P.transitionMatrix z z' * P.toExtended.valueFunction (a, z')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z', P.transitionMatrix z z' * ‖P.toExtended.valueFunction‖ := by
        refine Finset.sum_le_sum fun z' _ => ?_
        rw [abs_mul, abs_of_nonneg (P.transitionMatrix_nonneg z z')]
        exact mul_le_mul_of_nonneg_left
          (P.toExtended.valueFunction.norm_coe_le_norm _) (P.transitionMatrix_nonneg z z')
    _ = ‖P.toExtended.valueFunction‖ := by rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]

/-- **The utility of optimal consumption is bounded below**, by a quantity depending only on
the sup norm of the value function — not on the state. -/
theorem le_utility_consumption_policy {s : ℝ × Z} (hs : s.1 ∈ Icc 0 P.assetCap) :
    -(1 + P.discount) * ‖P.toExtended.valueFunction‖
      ≤ P.u (P.consumption s (P.policy s)) := by
  have hbell := P.valueFunction_eq_policy hs
  have hexp := P.abs_expectation_le (P.policy s) s.2
  have hV : |P.toExtended.valueFunction s| ≤ ‖P.toExtended.valueFunction‖ :=
    P.toExtended.valueFunction.norm_coe_le_norm _
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  rw [abs_le] at hexp hV
  nlinarith [hexp.1, hexp.2, hV.1, hV.2, hbell]

/-- **The utility bound in terms of the reward bounds alone** — no fixed point on the right.

This is the form that survives into a parametric statement. A family of programs sharing a
utility function and a common bound on `max |u minIncome| |u maxConsumption| / (1 - β)` has a
common `L`, and then `exists_lower_bound_of_utility_ge` hands it a single `δ`. -/
theorem le_utility_consumption_policy_of_bounds {s : ℝ × Z} (hs : s.1 ∈ Icc 0 P.assetCap) :
    -(1 + P.discount) * (max |P.u P.minIncome| |P.u P.maxConsumption| / (1 - P.discount))
      ≤ P.u (P.consumption s (P.policy s)) := by
  refine le_trans ?_ (P.le_utility_consumption_policy hs)
  have hnorm := P.toExtended.norm_valueFunction_le
  have hmin : P.toExtended.rewardMin = P.u P.minIncome := rfl
  have hmax : P.toExtended.rewardMax = P.u P.maxConsumption := rfl
  have hdisc : P.toExtended.discount = P.discount := rfl
  rw [hmin, hmax, hdisc] at hnorm
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  nlinarith [hnorm]

/-- **From a lower bound on utility to a lower bound on consumption.** The resulting `δ`
depends only on `u` and on `L` — NOT on the state, and not on anything that moves with the
interest rate. That is the property the parametric argument needs. -/
theorem exists_lower_bound_of_utility_ge (L : ℝ)
    (hL : ∀ s : ℝ × Z, s.1 ∈ Icc 0 P.assetCap → L ≤ P.u (P.consumption s (P.policy s))) :
    ∃ δ > 0, ∀ s : ℝ × Z, s.1 ∈ Icc 0 P.assetCap → δ ≤ P.consumption s (P.policy s) := by
  have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), P.u c < L - 1 :=
    P.tendsto_atBot_u (eventually_lt_atBot (L - 1))
  obtain ⟨ε, hε, hsub⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  refine ⟨ε, hε, fun s hs => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < P.consumption s (P.policy s) := P.consumption_policy_pos hs
  have hbad : P.u (P.consumption s (P.policy s)) < L - 1 := hsub ⟨hpos, hlt⟩
  linarith [hL s hs]

/-- **Consumption at the optimum is bounded away from zero, uniformly in the state.**

No compactness and no continuity of the policy are used, which is exactly what lets the same
argument run uniformly in the interest rate: a compactness proof would need joint continuity
in `(r, s)`, which is what such a bound is wanted to prove in the first place. -/
theorem exists_consumption_policy_lower_bound :
    ∃ δ > 0, ∀ s : ℝ × Z, s.1 ∈ Icc 0 P.assetCap → δ ≤ P.consumption s (P.policy s) :=
  P.exists_lower_bound_of_utility_ge _ fun _ hs => P.le_utility_consumption_policy_of_bounds hs

end IncomeFluctuation

end LeanEconomics
