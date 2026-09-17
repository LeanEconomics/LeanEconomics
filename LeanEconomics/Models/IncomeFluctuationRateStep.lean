/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationIterate
import LeanEconomics.Models.IncomeFluctuationRateMonotone

/-!
# Light (2018), step 5: increasing differences propagate across rates

`IncomeFluctuationRateMonotone` reduces Theorem 1 to one hypothesis, `ContIncreasingDifferences`,
and records that propagating it needs two things this development did not have: the envelope
condition as an EQUALITY, and concavity of the consumption function. Both are now proved
(`hasDerivAt_bellman`, `concaveOn_consumptionFnOf_bellman`), so the step is available.

## The identity the whole thing rests on

Two rates share a budget set: cash on hand at `(a, R₁)` equals cash on hand at `(t a, R₂)` for
`t = R₁ / R₂`, and the saving cap is the same because it is `min assetCap (cash on hand)`. So the
two maximisations are literally the same maximisation, and `lazyValue_withRate` says so. Hence
`bellmanFn_withRate`, `policyOf_withRate` and `consumptionFnOf_withRate`: the whole solution at
`(a, R₁)` is the solution at `(t a, R₂)`.

That turns the difference `(T_{R₂} f)(a) - (T_{R₁} f)(a)` into `(T_{R₂} f)(a) - (T_{R₂} f)(t a)`,
a statement about ONE economy, and increasing differences across rates becomes monotonicity of
that difference in `a`. The envelope makes its derivative `R₂ u'(σ(a)) - R₁ u'(σ(t a))`, and
`mul_marginal_le_of_scale` signs it: concavity of `σ` for one factor, relative risk aversion at
most one for the other.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### The two rates solve the same problem at rescaled assets -/

variable {r₁ r₂ : ℝ}

/-- **The objective at `(a, r₁)` is the objective at `(t a, r₂)`**, action for action. -/
theorem lazyValue_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (v : (ℝ × Z) →ᵇ ℝ) (z : Z)
    (x : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (P.withRate r₁ h₁).lazyValue v z x a
      = (P.withRate r₂ h₂).lazyValue v z x ((1 + r₁) / (1 + r₂) * a) := by
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hscale : (0 : ℝ) ≤ (1 + r₁) / (1 + r₂) * a := by
    have : (0 : ℝ) < 1 + r₁ := h₁.1
    positivity
  have harg : P.income z + (1 + r₂) * ((1 + r₁) / (1 + r₂) * a)
      = P.income z + (1 + r₁) * a := by field_simp
  simp only [lazyValue, resources, IncomeFluctuation.withRate_income,
    IncomeFluctuation.withRate_interest, IncomeFluctuation.withRate_discount,
    IncomeFluctuation.withRate_transitionMatrix, IncomeFluctuation.withRate_u,
    max_eq_right ha, max_eq_right hscale, harg]

/-- The feasible sets coincide. -/
theorem feasible_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (z : Z) {a : ℝ} (ha : 0 ≤ a) :
    (P.withRate r₁ h₁).toExtended.feasible (a, z)
      = (P.withRate r₂ h₂).toExtended.feasible ((1 + r₁) / (1 + r₂) * a, z) := by
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hscale : (0 : ℝ) ≤ (1 + r₁) / (1 + r₂) * a := by
    have : (0 : ℝ) < 1 + r₁ := h₁.1
    positivity
  have hres : (P.withRate r₁ h₁).resources (a, z)
      = (P.withRate r₂ h₂).resources ((1 + r₁) / (1 + r₂) * a, z) := by
    have harg : P.income z + (1 + r₂) * ((1 + r₁) / (1 + r₂) * a)
        = P.income z + (1 + r₁) * a := by field_simp
    simp only [resources, IncomeFluctuation.withRate_income,
      IncomeFluctuation.withRate_interest, max_eq_right ha, max_eq_right hscale, harg]
  rw [(P.withRate r₁ h₁).feasible_eq, (P.withRate r₂ h₂).feasible_eq,
    (P.withRate r₁ h₁).maxSaving_eq, (P.withRate r₂ h₂).maxSaving_eq, hres]

/-- Consumption at a given action coincides. -/
theorem consumption_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (z : Z) (x : ℝ) {a : ℝ}
    (ha : 0 ≤ a) :
    (P.withRate r₁ h₁).consumption (a, z) x
      = (P.withRate r₂ h₂).consumption ((1 + r₁) / (1 + r₂) * a, z) x := by
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hscale : (0 : ℝ) ≤ (1 + r₁) / (1 + r₂) * a := by
    have : (0 : ℝ) < 1 + r₁ := h₁.1
    positivity
  have harg : P.income z + (1 + r₂) * ((1 + r₁) / (1 + r₂) * a)
      = P.income z + (1 + r₁) * a := by field_simp
  simp only [consumption, resources, IncomeFluctuation.withRate_income,
    IncomeFluctuation.withRate_interest, max_eq_right ha, max_eq_right hscale, harg]


/-- **The whole solution at `(a, r₁)` is the solution at `(t a, r₂)`.** -/
theorem bellmanFn_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (v : (ℝ × Z) →ᵇ ℝ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).toExtended.bellmanFn v (a, z)
      = (P.withRate r₂ h₂).toExtended.bellmanFn v ((1 + r₁) / (1 + r₂) * a, z) := by
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have ht1 : (1 + r₁) / (1 + r₂) ≤ 1 := by rw [div_le_one hR₂]; linarith
  have hscale : (1 + r₁) / (1 + r₂) * a ∈ Icc (0 : ℝ) assetCap := by
    refine ⟨mul_nonneg (le_of_lt (div_pos hR₁ hR₂)) ha.1, ?_⟩
    nlinarith [ha.1, ha.2, div_pos hR₁ hR₂]
  have hback : (1 + r₂) / (1 + r₁) * ((1 + r₁) / (1 + r₂) * a) = a := by field_simp
  refine le_antisymm ?_ ?_
  · set b := (P.withRate r₁ h₁).policyOf v (a, z) with hb
    have heq := (P.withRate r₁ h₁).lazyValue_eq_dom v z ha
      ((P.withRate r₁ h₁).policyOf_mem v (a, z))
      ((P.withRate r₁ h₁).consumption_policyOf_mem_dom v ha)
      ((P.withRate r₁ h₁).policyOf_optimal v (a, z))
    have hfe : b ∈ (P.withRate r₂ h₂).toExtended.feasible ((1 + r₁) / (1 + r₂) * a, z) := by
      rw [← P.feasible_withRate h₁ h₂ z ha.1]
      exact (P.withRate r₁ h₁).policyOf_mem v (a, z)
    have hcd : (P.withRate r₂ h₂).consumption ((1 + r₁) / (1 + r₂) * a, z) b
        ∈ (P.withRate r₂ h₂).dom := by
      rw [← P.consumption_withRate h₁ h₂ z b ha.1]
      exact (P.withRate r₁ h₁).consumption_policyOf_mem_dom v ha
    have hle := (P.withRate r₂ h₂).lazyValue_le_dom v z hscale hfe hcd
    rw [← P.lazyValue_withRate h₁ h₂ v z b ha.1, heq] at hle
    exact hle
  · set b := (P.withRate r₂ h₂).policyOf v ((1 + r₁) / (1 + r₂) * a, z) with hb
    have heq := (P.withRate r₂ h₂).lazyValue_eq_dom v z hscale
      ((P.withRate r₂ h₂).policyOf_mem v _)
      ((P.withRate r₂ h₂).consumption_policyOf_mem_dom v hscale)
      ((P.withRate r₂ h₂).policyOf_optimal v _)
    have hfe : b ∈ (P.withRate r₁ h₁).toExtended.feasible (a, z) := by
      rw [P.feasible_withRate h₁ h₂ z ha.1]
      exact (P.withRate r₂ h₂).policyOf_mem v _
    have hcd : (P.withRate r₁ h₁).consumption (a, z) b ∈ (P.withRate r₁ h₁).dom := by
      rw [P.consumption_withRate h₁ h₂ z b ha.1]
      exact (P.withRate r₂ h₂).consumption_policyOf_mem_dom v hscale
    have hle := (P.withRate r₁ h₁).lazyValue_le_dom v z ha hfe hcd
    rw [P.lazyValue_withRate h₁ h₂ v z b ha.1, heq] at hle
    exact hle

/-- **The saving chosen at `(a, r₁)` is the saving chosen at `(t a, r₂)`.** -/
theorem policyOf_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices (0 : ℝ) assetCap v) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).policyOf v (a, z)
      = (P.withRate r₂ h₂).policyOf v ((1 + r₁) / (1 + r₂) * a, z) := by
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have ht1 : (1 + r₁) / (1 + r₂) ≤ 1 := by rw [div_le_one hR₂]; linarith
  have hscale : (1 + r₁) / (1 + r₂) * a ∈ Icc (0 : ℝ) assetCap := by
    refine ⟨mul_nonneg (le_of_lt (div_pos hR₁ hR₂)) ha.1, ?_⟩
    nlinarith [ha.1, ha.2, div_pos hR₁ hR₂]
  set b := (P.withRate r₁ h₁).policyOf v (a, z) with hb
  have hfe : b ∈ (P.withRate r₂ h₂).toExtended.feasible ((1 + r₁) / (1 + r₂) * a, z) := by
    rw [← P.feasible_withRate h₁ h₂ z ha.1]
    exact (P.withRate r₁ h₁).policyOf_mem v (a, z)
  have hcd : (P.withRate r₂ h₂).consumption ((1 + r₁) / (1 + r₂) * a, z) b
      ∈ (P.withRate r₂ h₂).dom := by
    rw [← P.consumption_withRate h₁ h₂ z b ha.1]
    exact (P.withRate r₁ h₁).consumption_policyOf_mem_dom v ha
  refine (P.withRate r₂ h₂).optimal_action_unique_of_concaveSlices hv
    (s := ((1 + r₁) / (1 + r₂) * a, z)) hscale hfe
    ((P.withRate r₂ h₂).policyOf_mem v _) ?_ ((P.withRate r₂ h₂).policyOf_optimal v _)
  rw [(P.withRate r₂ h₂).objectiveE_eq_coe_of v hscale hfe hcd,
    ← P.bellmanFn_withRate h₁ h₂ hr v z ha]
  have hobj : (P.withRate r₂ h₂).objROf v ((1 + r₁) / (1 + r₂) * a, z) b
      = (P.withRate r₁ h₁).lazyValue v z b a := by
    show (P.withRate r₂ h₂).lazyValue v z b ((1 + r₁) / (1 + r₂) * a) = _
    rw [P.lazyValue_withRate h₁ h₂ v z b ha.1]
  rw [hobj]
  exact congrArg _ ((P.withRate r₁ h₁).lazyValue_eq_dom v z ha
    ((P.withRate r₁ h₁).policyOf_mem v (a, z))
    ((P.withRate r₁ h₁).consumption_policyOf_mem_dom v ha)
    ((P.withRate r₁ h₁).policyOf_optimal v (a, z)))

/-- **Consumption too.** This is the function `mul_marginal_le_of_scale` is applied to. -/
theorem consumptionFnOf_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices (0 : ℝ) assetCap v) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).consumptionFnOf v z a
      = (P.withRate r₂ h₂).consumptionFnOf v z ((1 + r₁) / (1 + r₂) * a) := by
  simp only [consumptionFnOf]
  rw [P.policyOf_withRate h₁ h₂ hr hv z ha, P.consumption_withRate h₁ h₂ z _ ha.1]

end IncomeFluctuation

end LeanEconomics
