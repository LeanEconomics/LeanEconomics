/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Weighted
import LeanEconomics.Topology.IccCorrespondence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Consumption and savings with no cap on assets

The same problem as `LeanEconomics.Models.ConsumptionSavings` -- constant income, CES
utility with `σ < 1` -- but with the artificial upper bound on assets removed. Assets range
over all of `ℝ` and consumption is unbounded above, so utility is too.

## What replaces the cap

A weight `w a = weightBase + a⁺` and the drift condition of
`LeanEconomics.DynamicProgramming.Weighted`. Utility grows like `c ^ (1 - σ)`, which is
sublinear in consumption and so is dominated by the linear weight; the drift condition then
holds exactly when the household is impatient enough, and it splits into two readable
inequalities:

* `drift_slope : β * (1 + r) ≤ modulus` -- the **impatience condition**. Assets earn
  `1 + r` per period, so the weight grows by that factor at best; the household must
  discount faster than its assets compound. Without it a household would accumulate
  without bound and the value would be infinite, so this is the economics of the problem
  rather than an artefact of the method.
* `drift_const : β * (weightBase + y) ≤ modulus * weightBase` -- satisfied by taking
  `weightBase` large, and constraining nothing else.

Both can be met whenever `β * (1 + r) < 1`, which is the standard condition.

## The one clamp that remains

The reward must be bounded *relative to the weight* over all of `ℝ × ℝ`, including
infeasible actions. Saving a very negative amount would finance unbounded consumption, so
the reward is defined with the action clamped below at `0`. `rewardFn_eq_utility` proves
this is inactive at every feasible action, so `exists_optimal_saving` carries honest CES
utility of actual consumption.

Note there is no floor on utility here, unlike the `σ ≥ 1` files: for `σ < 1`, `u 0 = 0` is
perfectly finite and `u` is continuous on all of `[0, ∞)`.
-/

open scoped NNReal
open Set BoundedContinuousFunction

namespace LeanEconomics

/-- Parameters of the uncapped consumption-savings problem. -/
structure ConsumptionSavingsUncapped where
  /-- Constant labour income. -/
  income : ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The CES parameter `σ`, strictly below one. -/
  crra : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  /-- The constant term of the weight `w a = weightBase + a⁺`. -/
  weightBase : ℝ
  /-- The contraction modulus delivered by the drift condition. -/
  modulus : ℝ≥0
  income_pos : 0 < income
  interest_gt_neg_one : 0 < 1 + interest
  crra_nonneg : 0 ≤ crra
  crra_lt_one : crra < 1
  one_le_weightBase : 1 ≤ weightBase
  modulus_lt_one : modulus < 1
  /-- Met by taking `weightBase` large. -/
  drift_const : discount * (weightBase + income) ≤ modulus * weightBase
  /-- **The impatience condition** `β (1 + r) ≤ modulus`. -/
  drift_slope : discount * (1 + interest) ≤ modulus

namespace ConsumptionSavingsUncapped

variable (P : ConsumptionSavingsUncapped)

/-- Cash on hand. -/
noncomputable def resources (a : ℝ) : ℝ := P.income + (1 + P.interest) * a

/-- Consumption implied by the budget constraint, with saving clamped below at `0` so that
the reward is bounded relative to the weight even at infeasible actions. -/
noncomputable def consumptionClamped (a a' : ℝ) : ℝ := max 0 (P.resources a - max 0 a')

/-- Consumption on the budget line. -/
noncomputable def consumption (a a' : ℝ) : ℝ := P.resources a - a'

/-- CES period utility. With `σ < 1` this is finite at zero consumption, so no floor is
needed. -/
noncomputable def utility (c : ℝ) : ℝ := c ^ (1 - P.crra) / (1 - P.crra)

/-- The weight: linear in assets, which dominates the sublinear growth of utility. -/
noncomputable def weight (a : ℝ) : ℝ := P.weightBase + max 0 a

/-- The largest asset holding the household can carry forward. -/
noncomputable def maxSaving (a : ℝ) : ℝ := max 0 (P.resources a)

theorem one_sub_crra_pos : 0 < 1 - P.crra := by linarith [P.crra_lt_one]

theorem weight_pos (a : ℝ) : 0 < P.weight a := by
  have := P.one_le_weightBase
  have : (0 : ℝ) ≤ max 0 a := le_max_left _ _
  simp only [weight]; linarith [P.one_le_weightBase]

theorem weightBase_pos : 0 < P.weightBase := by linarith [P.one_le_weightBase]

/-- Sublinearity of `x ↦ x ^ p` for `p ≤ 1`: this is why a linear weight suffices. -/
theorem rpow_le_one_add {x p : ℝ} (hx : 0 ≤ x) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    x ^ p ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · calc x ^ p ≤ 1 := Real.rpow_le_one hx h hp0
      _ ≤ 1 + x := by linarith
  · calc x ^ p ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hp1
      _ = x := Real.rpow_one x
      _ ≤ 1 + x := by linarith

/-- Cash on hand grows at most linearly in assets. -/
theorem maxSaving_le (a : ℝ) : P.maxSaving a ≤ P.income + (1 + P.interest) * max 0 a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_right h]
    refine max_le ?_ (le_refl _)
    have : 0 ≤ (1 + P.interest) * a := mul_nonneg P.interest_gt_neg_one.le h
    linarith [P.income_pos]
  · rw [max_eq_left h]
    refine max_le (by linarith [P.income_pos]) ?_
    have : (1 + P.interest) * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos P.interest_gt_neg_one.le h
    simp only [resources]; linarith

theorem consumptionClamped_nonneg (a a' : ℝ) : 0 ≤ P.consumptionClamped a a' := le_max_left _ _

theorem consumptionClamped_le (a a' : ℝ) : P.consumptionClamped a a' ≤ P.maxSaving a := by
  refine max_le (le_max_left _ _) ?_
  have : (0 : ℝ) ≤ max 0 a' := le_max_left _ _
  exact le_trans (by linarith) (le_max_right 0 (P.resources a))

/-- The reward divided by the weight, which the weighted theory requires to be bounded. -/
noncomputable def rewardOverWeightFn (p : ℝ × ℝ) : ℝ :=
  P.utility (P.consumptionClamped p.1 p.2) / P.weight p.1

/-- The uniform bound on the normalised reward. -/
noncomputable def rewardBound : ℝ :=
  ((1 + P.income) / P.weightBase + (1 + P.interest)) / (1 - P.crra)

theorem rewardOverWeightFn_nonneg (p : ℝ × ℝ) : 0 ≤ P.rewardOverWeightFn p :=
  div_nonneg
    (div_nonneg (Real.rpow_nonneg (P.consumptionClamped_nonneg _ _) _) P.one_sub_crra_pos.le)
    (P.weight_pos _).le

theorem rewardOverWeightFn_le (p : ℝ × ℝ) : P.rewardOverWeightFn p ≤ P.rewardBound := by
  have hK := P.weightBase_pos
  have hσ := P.one_sub_crra_pos
  have hw := P.weight_pos p.1
  have ht : (0 : ℝ) ≤ max 0 p.1 := le_max_left _ _
  have hy : (0 : ℝ) < 1 + P.income := by linarith [P.income_pos]
  have hr := P.interest_gt_neg_one
  -- utility is at most `(1 + cash on hand) / (1 - σ)`, by sublinearity of `x ^ (1 - σ)`
  have hu : P.utility (P.consumptionClamped p.1 p.2)
      ≤ (1 + (P.income + (1 + P.interest) * max 0 p.1)) / (1 - P.crra) := by
    have h1 : P.consumptionClamped p.1 p.2 ^ (1 - P.crra) ≤ 1 + P.consumptionClamped p.1 p.2 :=
      rpow_le_one_add (P.consumptionClamped_nonneg _ _) hσ.le (by linarith [P.crra_nonneg])
    have h2 := (P.consumptionClamped_le p.1 p.2).trans (P.maxSaving_le p.1)
    simp only [utility]
    exact div_le_div_of_nonneg_right (by linarith) hσ.le
  -- and cash on hand is linear in assets, which the linear weight absorbs
  have hmain : 1 + (P.income + (1 + P.interest) * max 0 p.1)
      ≤ ((1 + P.income) / P.weightBase + (1 + P.interest)) * (P.weightBase + max 0 p.1) := by
    have hexp : ((1 + P.income) / P.weightBase + (1 + P.interest)) * (P.weightBase + max 0 p.1)
        = (1 + P.income) + (1 + P.income) * max 0 p.1 / P.weightBase
          + (1 + P.interest) * P.weightBase + (1 + P.interest) * max 0 p.1 := by
      field_simp; ring
    have h1 : 0 ≤ (1 + P.income) * max 0 p.1 / P.weightBase :=
      div_nonneg (mul_nonneg hy.le ht) hK.le
    have h2 : 0 ≤ (1 + P.interest) * P.weightBase := mul_nonneg hr.le hK.le
    rw [hexp]; linarith
  rw [rewardOverWeightFn, div_le_iff₀ hw]
  refine hu.trans ?_
  rw [rewardBound, weight, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hmain hσ.le

theorem abs_rewardOverWeightFn_le (p : ℝ × ℝ) : |P.rewardOverWeightFn p| ≤ P.rewardBound :=
  abs_le.mpr ⟨by linarith [P.rewardOverWeightFn_nonneg p, P.rewardOverWeightFn_le p],
    P.rewardOverWeightFn_le p⟩

theorem continuous_resources : Continuous P.resources :=
  continuous_const.add (continuous_const.mul continuous_id)

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max P.continuous_resources

theorem continuous_weight : Continuous P.weight :=
  continuous_const.add (continuous_const.max continuous_id)

theorem continuous_utility : Continuous P.utility :=
  (Real.continuous_rpow_const P.one_sub_crra_pos.le).div_const _

theorem continuous_rewardOverWeightFn : Continuous P.rewardOverWeightFn := by
  have hc : Continuous fun p : ℝ × ℝ => P.consumptionClamped p.1 p.2 :=
    continuous_const.max
      ((P.continuous_resources.comp continuous_fst).sub (continuous_const.max continuous_snd))
  exact (P.continuous_utility.comp hc).div (P.continuous_weight.comp continuous_fst)
    fun p => ne_of_gt (P.weight_pos p.1)

/-- The uncapped problem as a weighted dynamic program. There is a single, certain shock. -/
noncomputable def toWeighted : WeightedDynamicProgram ℝ ℝ (Fin 1) where
  feasible a := Icc 0 (P.maxSaving a)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  w := ⟨P.weight, P.continuous_weight⟩
  one_le_w a := by
    simp only [ContinuousMap.coe_mk, weight]
    linarith [P.one_le_weightBase, le_max_left (0 : ℝ) a]
  rewardOverWeight := BoundedContinuousFunction.ofNormedAddCommGroup P.rewardOverWeightFn
    P.continuous_rewardOverWeightFn P.rewardBound fun p => by
      simpa [Real.norm_eq_abs] using P.abs_rewardOverWeightFn_le p
  transition _ := ⟨fun p => p.2, continuous_snd⟩
  prob _ := ⟨fun _ => 1, continuous_const⟩
  prob_nonneg _ _ := zero_le_one
  discount := P.discount
  modulus := P.modulus
  modulus_lt_one := P.modulus_lt_one
  drift a a' ha' := by
    obtain ⟨ha'0, ha'max⟩ := ha'
    have ht : (0 : ℝ) ≤ max 0 a := le_max_left _ _
    have hbound : a' ≤ P.income + (1 + P.interest) * max 0 a :=
      ha'max.trans (P.maxSaving_le a)
    have hslope : (P.discount : ℝ) * (1 + P.interest) * max 0 a ≤ P.modulus * max 0 a :=
      mul_le_mul_of_nonneg_right P.drift_slope ht
    have hconst := P.drift_const
    have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
    simp only [Fin.sum_univ_one, ContinuousMap.coe_mk, one_mul, weight, max_eq_right ha'0]
    linarith [mul_le_mul_of_nonneg_left hbound hβ, hslope, hconst]

@[simp]
theorem feasible_eq (a : ℝ) : P.toWeighted.feasible a = Icc 0 (P.maxSaving a) := rfl

/-- **The clamp on saving does not bind at a feasible action.** From nonnegative assets,
every feasible choice leaves nonnegative consumption, so the reward really is CES utility
of consumption. -/
theorem consumptionClamped_eq {a a' : ℝ} (ha : 0 ≤ a) (ha' : a' ∈ Icc 0 (P.maxSaving a)) :
    P.consumptionClamped a a' = P.consumption a a' := by
  obtain ⟨ha'0, ha'max⟩ := ha'
  have hres : 0 ≤ P.resources a := by
    have : 0 ≤ (1 + P.interest) * a := mul_nonneg P.interest_gt_neg_one.le ha
    simp only [resources]; linarith [P.income_pos]
  have : a' ≤ P.resources a := ha'max.trans (by simp [maxSaving, max_eq_right hres])
  simp only [consumptionClamped, consumption, max_eq_right ha'0]
  exact max_eq_right (by linarith)

/-- **The Bellman equation of the uncapped problem**, with honest CES utility of actual
consumption. Assets are unbounded: the hypothesis is only that they are nonnegative, with
no upper cap anywhere. -/
theorem exists_optimal_saving {a : ℝ} (ha : 0 ≤ a) :
    ∃ a' ∈ Icc 0 (P.maxSaving a),
      P.toWeighted.valueFunction a
        = P.utility (P.consumption a a') + P.discount * P.toWeighted.valueFunction a' := by
  obtain ⟨a', ha', heq⟩ := P.toWeighted.exists_optimal_policy a
  refine ⟨a', ha', ?_⟩
  have hw := P.weight_pos a
  have key : P.toWeighted.rewardOverWeight (a, a') * P.toWeighted.w a
      = P.utility (P.consumption a a') := by
    have h : P.rewardOverWeightFn (a, a') * P.weight a = P.utility (P.consumption a a') := by
      rw [rewardOverWeightFn, div_mul_cancel₀ _ (ne_of_gt hw),
        P.consumptionClamped_eq ha (show a' ∈ Icc 0 (P.maxSaving a) from ha')]
    exact h
  rw [heq, key]
  simp [toWeighted]

/-- A calibration: income 1, interest 5%, `σ = 1/2`, `β = 0.9`. The impatience condition
`β (1 + r) = 0.945 < 1` holds, and `weightBase = 20` makes the other drift inequality hold.
Recorded to witness that the drift conditions are satisfiable. -/
noncomputable def calibrated : ConsumptionSavingsUncapped where
  income := 1
  interest := 1 / 20
  crra := 1 / 2
  discount := 9 / 10
  weightBase := 20
  modulus := 24 / 25
  income_pos := by norm_num
  interest_gt_neg_one := by norm_num
  crra_nonneg := by norm_num
  crra_lt_one := by norm_num
  one_le_weightBase := by norm_num
  modulus_lt_one := by norm_num
  drift_const := by push_cast; norm_num
  drift_slope := by push_cast; norm_num

end ConsumptionSavingsUncapped

end LeanEconomics
