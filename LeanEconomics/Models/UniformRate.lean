/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.NaturalAssetBound
import LeanEconomics.Models.IncomeFluctuationRate

/-!
# The corner and decline conditions, uniformly in the interest rate

Uniqueness of the stationary distribution needs the constraint to bind below an asset level and
assets to fall above one, and the equilibrium needs that at EVERY rate in an interval, not at one
rate. This file makes both uniform, and the shape of the answer is that neither condition has to
be rechecked: both are monotone in the rate, and both are worst at the TOP of the interval.

* The corner threshold `β · logLipschitz < 1 / resources` degrades on both sides as `r` rises —
  `logLipschitz` carries a factor `(1+r)/(1 - β(1+r))`, which grows, and resources
  `income + (1+r) a` grow too. `logLipschitz_le_of_le` and `resources_le_of_le` are the two
  halves.
* The decline condition `(1-ε) income < (1 - (1-ε)(1+r)) a` degrades because the coefficient on
  the right falls with `r`. `policy_lt_self_of_rate_le` carries it down the interval.

The consumption bound `ε` also moves with the rate, through `‖V‖`, and the fix is not to track it
but to remove it: `log_consumption_lower_bound_of_norm` restates the bound against ANY upper bound
on the value function, so a single `N` covering the interval gives a single `ε`.

So a user checks one corner inequality and one decline inequality, both at `rhi`, and gets the
hypotheses of `exists_exhaust_of_decline` at every rate below.

That the conditions bind at the top is the direction one would hope for, and it is the opposite of
the supply floor, which by `gain_term_mono` binds at the BOTTOM. The interval is squeezed from
both ends, which is why it is narrow.
-/

open Set Filter Topology

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
-- The uniform-rate bounds are calibrated statements about a household whose borrowing limit is
-- at zero, matching the witnesses that consume them.
variable {assetCap : ℝ}
variable (P : IncomeFluctuation Z 0 assetCap)

/-! ### The consumption bound, against any bound on the value function -/

/-- The linear consumption bound stated against an arbitrary upper bound `N` on the value
function, so that one `N` covering a rate interval gives one `ε` covering it. -/
theorem log_consumption_lower_bound_of_norm (hpc : P.PositiveConsumption) (hu : P.u = Real.log)
    {N : ℝ}
    (hN : ‖P.toExtended.valueFunction‖ ≤ N) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.resources (a, z) / (1 + 4 * P.discount * N) ≤ P.consumptionFn z a := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hgap : P.deviationGap ≤ 2 * P.discount * N := by
    simp only [IncomeFluctuation.deviationGap]
    nlinarith [hN, hβ]
  have hG : 0 ≤ P.deviationGap := P.deviationGap_nonneg
  refine le_trans ?_ (P.log_consumption_linear_lower_bound' hpc hu ha z)
  rw [sub_zero]
  refine div_le_div_of_nonneg_left (P.assetFloor_lt_resources (a, z)).le (by linarith) ?_
  linarith

/-! ### The corner condition rises with the rate -/

theorem logLipschitz_le_of_le {r₀ r₁ : ℝ} (h₀ : P.RateOK r₀) (h₁ : P.RateOK r₁)
    (hle : r₀ ≤ r₁) (hβ₁ : (P.discount : ℝ) * (1 + r₁) < 1) :
    (P.withRate r₀ h₀).logLipschitz ≤ (P.withRate r₁ h₁).logLipschitz := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hm := P.minIncome_pos
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hβ₀ : (P.discount : ℝ) * (1 + r₀) < 1 := by nlinarith
  have hmc : (P.withRate r₀ h₀).minConsumption = P.minConsumption := rfl
  have hmc' : (P.withRate r₁ h₁).minConsumption = P.minConsumption := rfl
  simp only [IncomeFluctuation.logLipschitz, hmc, hmc', withRate_interest, withRate_discount]
  rw [div_le_div_iff₀ (by linarith [h₀.1]) (by linarith [h₁.1])]
  have hK : (0 : ℝ) ≤ 2 * Real.log 2 / P.minConsumption := by
    have := P.minConsumption_pos
    positivity
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) + r₀ ≤ 1 + r₁) hK, hβ, h₀.1.le]

theorem resources_le_of_le {r₀ r₁ : ℝ} (h₀ : P.RateOK r₀) (h₁ : P.RateOK r₁) (hle : r₀ ≤ r₁)
    {a : ℝ} (ha : 0 ≤ a) (z : Z) :
    (P.withRate r₀ h₀).resources (a, z) ≤ (P.withRate r₁ h₁).resources (a, z) := by
  simp only [resources, withRate_income, withRate_interest, max_eq_right ha]
  nlinarith

/-- **The corner condition, checked once at the top of the interval.** -/
theorem log_policy_eq_zero_uniform (hdom : P.Unbounded) (hu : P.u = Real.log) {r₀ r₁ : ℝ}
    (h₀ : P.RateOK r₀)
    (h₁ : P.RateOK r₁) (hle : r₀ ≤ r₁) (hβ₁ : (P.discount : ℝ) * (1 + r₁) < 1)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (hlt : (P.withRate r₁ h₁).discount * (P.withRate r₁ h₁).logLipschitz
      < 1 / (P.withRate r₁ h₁).resources (a, z)) :
    (P.withRate r₀ h₀).policy (a, z) = 0 := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hβ₀ : (P.discount : ℝ) * (1 + r₀) < 1 := by nlinarith
  refine (P.withRate r₀ h₀).log_policy_eq_zero_of_resources hdom (by simpa using hu)
    (by simpa using hβ₀) ha ?_
  rw [sub_zero]
  have hlip := P.logLipschitz_le_of_le h₀ h₁ hle hβ₁
  have hres := P.resources_le_of_le h₀ h₁ hle ha.1 z
  have hpos₀ : 0 < (P.withRate r₀ h₀).resources (a, z) :=
    (P.withRate r₀ h₀).assetFloor_lt_resources _
  have hlipβ : (P.withRate r₀ h₀).discount * (P.withRate r₀ h₀).logLipschitz
      ≤ (P.withRate r₁ h₁).discount * (P.withRate r₁ h₁).logLipschitz := by
    simp only [withRate_discount]
    exact mul_le_mul_of_nonneg_left hlip hβ
  have hinv : 1 / (P.withRate r₁ h₁).resources (a, z)
      ≤ 1 / (P.withRate r₀ h₀).resources (a, z) :=
    one_div_le_one_div_of_le hpos₀ hres
  linarith

/-! ### The decline condition falls with the rate -/

/-- **The decline condition, checked once at the top of the interval.** -/
theorem policy_lt_self_of_rate_le {r₀ r₁ : ℝ} (h₀ : P.RateOK r₀) (hle : r₀ ≤ r₁)
    {z : Z} {ε a : ℝ} (hε : ε ≤ 1) (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hlb : ε * ((P.withRate r₀ h₀).resources (a, z) - 0) ≤ (P.withRate r₀ h₀).consumptionFn z a)
    (hgt : (1 - ε) * P.income z < (1 - (1 - ε) * (1 + r₁)) * a) :
    (P.withRate r₀ h₀).policy (a, z) < a := by
  refine (P.withRate r₀ h₀).policy_lt_self_of_consumption_lower_bound ha hlb ?_
  simp only [withRate_income, withRate_interest, mul_zero, add_zero]
  have h1e : (0 : ℝ) ≤ 1 - ε := by linarith
  nlinarith [hgt, mul_nonneg (mul_nonneg h1e ha.1) (sub_nonneg.mpr hle)]

end IncomeFluctuation

end LeanEconomics
