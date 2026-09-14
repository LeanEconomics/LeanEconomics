/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.ConsumptionSavingsUncapped
import LeanEconomics.Models.IncomeFluctuation

/-!
# The income fluctuation problem with no cap on assets

Markov income and unbounded assets together: the model of
`LeanEconomics.Models.IncomeFluctuation` with the artificial asset cap removed by the
weighted theory of `LeanEconomics.DynamicProgramming.Weighted`.

  `V (a, z) = max { u c + β * ∑ z', P z z' * V (a', z') }`,  `a' + c = y z + (1 + r) a`,

with `a` ranging over all of `ℝ`.

## What composing the two mechanisms costs

Almost nothing, and it is worth saying why. The weighted framework was already stochastic,
so the shock structure needed no change. The weight `w (a, z) = weightBase + a⁺` depends
only on assets, so the expected weight of tomorrow's state collapses:
`∑ z', P z z' * w (a', z') = w (a', ·)` because the probabilities sum to one. The drift
condition therefore reduces to the same two inequalities as in the deterministic uncapped
model, with `maxIncome` in place of the constant income.

The one genuine change is that the reward bound and the drift must hold for every income
state at once, which is what `le_maxIncome` supplies.

## Scope

Period utility is CES with `σ < 1`, as in the deterministic uncapped model: `u 0 = 0` is
finite, so no floor is needed. Combining the weight with the *floor* machinery of
`LeanEconomics.Models.ConsumptionSavingsUnbounded`, to get an uncapped `σ ≥ 1` model, is
still not done -- the two mechanisms are independent, but nothing here checks they compose.
-/

open scoped NNReal
open Set BoundedContinuousFunction

namespace LeanEconomics

/-- The income fluctuation problem with unbounded assets. -/
structure IncomeFluctuationUncapped (Z : Type*) [Fintype Z] [Nonempty Z] [TopologicalSpace Z]
    [DiscreteTopology Z] where
  /-- Income in each state. -/
  income : Z → ℝ
  /-- The Markov transition matrix on income states. -/
  transitionMatrix : Z → Z → ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The CES parameter `σ`, strictly below one. -/
  crra : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  /-- The constant term of the weight `w (a, z) = weightBase + a⁺`. -/
  weightBase : ℝ
  /-- The contraction modulus delivered by the drift condition. -/
  modulus : ℝ≥0
  /-- An upper bound on income, which the reward bound and the drift both need. -/
  maxIncome : ℝ
  income_pos : ∀ z, 0 < income z
  le_maxIncome : ∀ z, income z ≤ maxIncome
  transitionMatrix_nonneg : ∀ z z', 0 ≤ transitionMatrix z z'
  transitionMatrix_sum : ∀ z, ∑ z', transitionMatrix z z' = 1
  interest_gt_neg_one : 0 < 1 + interest
  crra_nonneg : 0 ≤ crra
  crra_lt_one : crra < 1
  one_le_weightBase : 1 ≤ weightBase
  modulus_lt_one : modulus < 1
  /-- Met by taking `weightBase` large. -/
  drift_const : discount * (weightBase + maxIncome) ≤ modulus * weightBase
  /-- **The impatience condition.** -/
  drift_slope : discount * (1 + interest) ≤ modulus

namespace IncomeFluctuationUncapped

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable (P : IncomeFluctuationUncapped Z)

/-- Cash on hand. -/
noncomputable def resources (s : ℝ × Z) : ℝ := P.income s.2 + (1 + P.interest) * s.1

/-- Consumption on the budget line. -/
noncomputable def consumption (s : ℝ × Z) (a' : ℝ) : ℝ := P.resources s - a'

/-- Consumption with saving clamped below at `0`, so the reward is bounded relative to the
weight even at infeasible actions. -/
noncomputable def consumptionClamped (s : ℝ × Z) (a' : ℝ) : ℝ :=
  max 0 (P.resources s - max 0 a')

/-- CES period utility. -/
noncomputable def utility (c : ℝ) : ℝ := c ^ (1 - P.crra) / (1 - P.crra)

/-- The weight, linear in assets and independent of the income state. -/
noncomputable def weight (s : ℝ × Z) : ℝ := P.weightBase + max 0 s.1

/-- The largest asset holding that can be carried forward. -/
noncomputable def maxSaving (s : ℝ × Z) : ℝ := max 0 (P.resources s)

/-- The reward divided by the weight. -/
noncomputable def rewardOverWeightFn (p : (ℝ × Z) × ℝ) : ℝ :=
  P.utility (P.consumptionClamped p.1 p.2) / P.weight p.1

/-- The uniform bound on the normalised reward. -/
noncomputable def rewardBound : ℝ :=
  ((1 + P.maxIncome) / P.weightBase + (1 + P.interest)) / (1 - P.crra)

theorem one_sub_crra_pos : 0 < 1 - P.crra := by linarith [P.crra_lt_one]

theorem weightBase_pos : 0 < P.weightBase := by linarith [P.one_le_weightBase]

theorem weight_pos (s : ℝ × Z) : 0 < P.weight s := by
  have : (0 : ℝ) ≤ max 0 s.1 := le_max_left _ _
  simp only [weight]; linarith [P.one_le_weightBase]

theorem maxIncome_pos : 0 < P.maxIncome :=
  lt_of_lt_of_le (P.income_pos Classical.ofNonempty) (P.le_maxIncome _)

/-- Cash on hand grows at most linearly in assets, uniformly over income states. -/
theorem maxSaving_le (s : ℝ × Z) :
    P.maxSaving s ≤ P.maxIncome + (1 + P.interest) * max 0 s.1 := by
  rcases le_total 0 s.1 with h | h
  · rw [max_eq_right h]
    refine max_le ?_ ?_
    · have : 0 ≤ (1 + P.interest) * s.1 := mul_nonneg P.interest_gt_neg_one.le h
      linarith [P.maxIncome_pos]
    · simp only [resources]; linarith [P.le_maxIncome s.2]
  · rw [max_eq_left h]
    refine max_le (by linarith [P.maxIncome_pos]) ?_
    have : (1 + P.interest) * s.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos P.interest_gt_neg_one.le h
    simp only [resources]; linarith [P.le_maxIncome s.2]

theorem consumptionClamped_nonneg (s : ℝ × Z) (a' : ℝ) : 0 ≤ P.consumptionClamped s a' :=
  le_max_left _ _

theorem consumptionClamped_le (s : ℝ × Z) (a' : ℝ) :
    P.consumptionClamped s a' ≤ P.maxSaving s := by
  refine max_le (le_max_left _ _) ?_
  have : (0 : ℝ) ≤ max 0 a' := le_max_left _ _
  exact le_trans (by linarith) (le_max_right 0 (P.resources s))

theorem rewardOverWeightFn_nonneg (p : (ℝ × Z) × ℝ) : 0 ≤ P.rewardOverWeightFn p :=
  div_nonneg
    (div_nonneg (Real.rpow_nonneg (P.consumptionClamped_nonneg _ _) _) P.one_sub_crra_pos.le)
    (P.weight_pos _).le

theorem rewardOverWeightFn_le (p : (ℝ × Z) × ℝ) : P.rewardOverWeightFn p ≤ P.rewardBound := by
  have hK := P.weightBase_pos
  have hσ := P.one_sub_crra_pos
  have hw := P.weight_pos p.1
  have ht : (0 : ℝ) ≤ max 0 p.1.1 := le_max_left _ _
  have hy : (0 : ℝ) < 1 + P.maxIncome := by linarith [P.maxIncome_pos]
  have hr := P.interest_gt_neg_one
  have hu : P.utility (P.consumptionClamped p.1 p.2)
      ≤ (1 + (P.maxIncome + (1 + P.interest) * max 0 p.1.1)) / (1 - P.crra) := by
    have h1 : P.consumptionClamped p.1 p.2 ^ (1 - P.crra) ≤ 1 + P.consumptionClamped p.1 p.2 :=
      ConsumptionSavingsUncapped.rpow_le_one_add (P.consumptionClamped_nonneg _ _) hσ.le
        (by linarith [P.crra_nonneg])
    have h2 := (P.consumptionClamped_le p.1 p.2).trans (P.maxSaving_le p.1)
    simp only [utility]
    exact div_le_div_of_nonneg_right (by linarith) hσ.le
  have hmain : 1 + (P.maxIncome + (1 + P.interest) * max 0 p.1.1)
      ≤ ((1 + P.maxIncome) / P.weightBase + (1 + P.interest)) * (P.weightBase + max 0 p.1.1) := by
    have hexp : ((1 + P.maxIncome) / P.weightBase + (1 + P.interest))
          * (P.weightBase + max 0 p.1.1)
        = (1 + P.maxIncome) + (1 + P.maxIncome) * max 0 p.1.1 / P.weightBase
          + (1 + P.interest) * P.weightBase + (1 + P.interest) * max 0 p.1.1 := by
      field_simp; ring
    have h1 : 0 ≤ (1 + P.maxIncome) * max 0 p.1.1 / P.weightBase :=
      div_nonneg (mul_nonneg hy.le ht) hK.le
    have h2 : 0 ≤ (1 + P.interest) * P.weightBase := mul_nonneg hr.le hK.le
    rw [hexp]; linarith
  rw [rewardOverWeightFn, div_le_iff₀ hw]
  refine hu.trans ?_
  rw [rewardBound, weight, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hmain hσ.le

theorem abs_rewardOverWeightFn_le (p : (ℝ × Z) × ℝ) :
    |P.rewardOverWeightFn p| ≤ P.rewardBound :=
  abs_le.mpr ⟨by linarith [P.rewardOverWeightFn_nonneg p, P.rewardOverWeightFn_le p],
    P.rewardOverWeightFn_le p⟩

theorem continuous_resources : Continuous P.resources :=
  (continuous_of_discreteTopology.comp continuous_snd).add
    (continuous_const.mul continuous_fst)

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max P.continuous_resources

theorem continuous_weight : Continuous P.weight :=
  continuous_const.add (continuous_const.max continuous_fst)

theorem continuous_utility : Continuous P.utility :=
  (Real.continuous_rpow_const P.one_sub_crra_pos.le).div_const _

theorem continuous_rewardOverWeightFn : Continuous P.rewardOverWeightFn := by
  have hc : Continuous fun p : (ℝ × Z) × ℝ => P.consumptionClamped p.1 p.2 :=
    continuous_const.max
      ((P.continuous_resources.comp continuous_fst).sub (continuous_const.max continuous_snd))
  exact (P.continuous_utility.comp hc).div (P.continuous_weight.comp continuous_fst)
    fun p => ne_of_gt (P.weight_pos p.1)

/-- The uncapped income fluctuation problem as a weighted dynamic program. -/
noncomputable def toWeighted : WeightedDynamicProgram (ℝ × Z) ℝ Z where
  feasible s := Icc 0 (P.maxSaving s)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  w := ⟨P.weight, P.continuous_weight⟩
  one_le_w s := by
    simp only [ContinuousMap.coe_mk, weight]
    linarith [P.one_le_weightBase, le_max_left (0 : ℝ) s.1]
  rewardOverWeight := BoundedContinuousFunction.ofNormedAddCommGroup P.rewardOverWeightFn
    P.continuous_rewardOverWeightFn P.rewardBound fun p => by
      simpa [Real.norm_eq_abs] using P.abs_rewardOverWeightFn_le p
  transition z' := ⟨fun p => (p.2, z'), continuous_snd.prodMk continuous_const⟩
  prob z' := ⟨fun p => P.transitionMatrix p.1.2 z',
    (continuous_of_discreteTopology (f := fun z => P.transitionMatrix z z')).comp
      (continuous_snd.comp continuous_fst)⟩
  prob_nonneg z' p := P.transitionMatrix_nonneg _ _
  discount := P.discount
  modulus := P.modulus
  modulus_lt_one := P.modulus_lt_one
  drift s a' ha' := by
    obtain ⟨ha'0, ha'max⟩ := ha'
    have ht : (0 : ℝ) ≤ max 0 s.1 := le_max_left _ _
    have hbound : a' ≤ P.maxIncome + (1 + P.interest) * max 0 s.1 :=
      ha'max.trans (P.maxSaving_le s)
    have hslope : (P.discount : ℝ) * (1 + P.interest) * max 0 s.1 ≤ P.modulus * max 0 s.1 :=
      mul_le_mul_of_nonneg_right P.drift_slope ht
    have hconst := P.drift_const
    have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
    -- the weight does not depend on the income state, so the expectation collapses
    have hcollapse : ∑ z', P.transitionMatrix s.2 z' * P.weight (a', z')
        = P.weightBase + max 0 a' := by
      have : ∀ z' : Z, P.transitionMatrix s.2 z' * P.weight (a', z')
          = P.transitionMatrix s.2 z' * (P.weightBase + max 0 a') := fun z' => rfl
      rw [Finset.sum_congr rfl fun z' _ => this z', ← Finset.sum_mul,
        P.transitionMatrix_sum, one_mul]
    simp only [ContinuousMap.coe_mk]
    rw [hcollapse, max_eq_right ha'0]
    simp only [weight]
    linarith [mul_le_mul_of_nonneg_left hbound hβ, hslope, hconst]

@[simp]
theorem feasible_eq (s : ℝ × Z) : P.toWeighted.feasible s = Icc 0 (P.maxSaving s) := rfl

/-- The clamp on saving does not bind at a feasible action. -/
theorem consumptionClamped_eq {s : ℝ × Z} {a' : ℝ} (hs : 0 ≤ s.1)
    (ha' : a' ∈ Icc 0 (P.maxSaving s)) : P.consumptionClamped s a' = P.consumption s a' := by
  obtain ⟨ha'0, ha'max⟩ := ha'
  have hres : 0 ≤ P.resources s := by
    have : 0 ≤ (1 + P.interest) * s.1 := mul_nonneg P.interest_gt_neg_one.le hs
    simp only [resources]; linarith [P.income_pos s.2]
  have : a' ≤ P.resources s := ha'max.trans (by simp [maxSaving, max_eq_right hres])
  simp only [consumptionClamped, consumption, max_eq_right ha'0]
  exact max_eq_right (by linarith)

/-- **The Bellman equation of the uncapped income fluctuation problem**, with honest CES
utility of actual consumption and no bound on assets. -/
theorem exists_optimal_saving {s : ℝ × Z} (hs : 0 ≤ s.1) :
    ∃ a' ∈ Icc 0 (P.maxSaving s),
      P.toWeighted.valueFunction s
        = P.utility (P.consumption s a')
          + P.discount * ∑ z', P.transitionMatrix s.2 z'
              * P.toWeighted.valueFunction (a', z') := by
  obtain ⟨a', ha', heq⟩ := P.toWeighted.exists_optimal_policy s
  refine ⟨a', ha', ?_⟩
  have hw := P.weight_pos s
  have key : P.toWeighted.rewardOverWeight (s, a') * P.toWeighted.w s
      = P.utility (P.consumption s a') := by
    have h : P.rewardOverWeightFn (s, a') * P.weight s = P.utility (P.consumption s a') := by
      rw [rewardOverWeightFn, div_mul_cancel₀ _ (ne_of_gt hw),
        P.consumptionClamped_eq hs (show a' ∈ Icc 0 (P.maxSaving s) from ha')]
    exact h
  rw [heq, key]
  simp [toWeighted]

/-- A two-state calibration: income `1/2` or `3/2`, drawn i.i.d., interest 5%, `σ = 1/2`,
`β = 0.9`, so the impatience condition `β (1 + r) = 0.945 ≤ modulus` holds. -/
noncomputable def calibrated : IncomeFluctuationUncapped (Fin 2) where
  income z := if z = 0 then 1 / 2 else 3 / 2
  transitionMatrix _ _ := 1 / 2
  interest := 1 / 20
  crra := 1 / 2
  discount := 9 / 10
  weightBase := 40
  modulus := 24 / 25
  maxIncome := 3 / 2
  income_pos z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  crra_nonneg := by norm_num
  crra_lt_one := by norm_num
  one_le_weightBase := by norm_num
  modulus_lt_one := by norm_num
  drift_const := by push_cast; norm_num
  drift_slope := by push_cast; norm_num

end IncomeFluctuationUncapped

end LeanEconomics
