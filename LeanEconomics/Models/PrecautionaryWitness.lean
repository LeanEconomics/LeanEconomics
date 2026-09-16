/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.PositiveCapital
import LeanEconomics.Models.CRRA
import LeanEconomics.Distribution.Stationary

/-!
# An economy whose stationary distribution carries positive capital

`aggregateCapital_pos_of_primitives` has all its hypotheses in primitives, so they can be
checked. This file checks them, and the development finally has an economy with a stationary
agent distribution and strictly positive aggregate capital.

## The witness is IMPATIENT, and that is the point

`β (1 + r) = 1/2 < 1`, so the household discounts the future faster than the market rewards
waiting. A deterministic household with these parameters would run its assets down and hold
nothing. This one holds strictly positive assets, and the only reason is the income process: with
probability `1/2` it lands in the low state, where income is `1/100` against `1` in the high
state, and there consumption is small and the marginal value of a unit of assets is large.

All the work is done by DISPERSION, exactly as `log_cont_sub_ge` predicted. The gain from saving
`h = 1/2` out of high income is `β · P · log (1 + (1+r) h / income_low) = (1/4) log 51`, against a
cost of `log (1 / (1 - 1/2)) = log 2`, and `4 log 2 = log 16 < log 51`. Had the low income been
close to the high one the logarithm would have collapsed and the comparison failed.

So this is a precautionary saver in the strict sense: impatient, and saving only against the bad
draw. The name `patient` would be wrong.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

/-- An impatient household with log utility and DISPERSED income: `β = 1/2`, `r = 0`, income in
`{1/100, 1}` with iid draws, asset cap `1`. -/
noncomputable def precautionary : IncomeFluctuation (Fin 2) 1 where
  income z := if z = 0 then 1 / 100 else 1
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 2
  u := crraUtility 1
  minIncome := 1 / 100
  maxIncome := 1
  minIncome_pos := by norm_num
  minIncome_le z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  assetCap_nonneg := by norm_num
  discount_lt_one := by norm_num
  dom := Ioi 0
  Ioi_subset_dom := subset_rfl
  dom_subset_Ici := Ioi_subset_Ici_self
  continuousOn_u_dom := continuousOn_crraUtility 1
  monotoneOn_u_dom := monotoneOn_crraUtility 1
  strictConcaveOn_u_dom := strictConcaveOn_crraUtility one_pos
  continuousOn_extendDom :=
    continuousOn_extendDom_Ioi (continuousOn_crraUtility 1) (tendsto_atBot_crraUtility le_rfl)

@[simp] theorem precautionary_u : precautionary.u = Real.log := crraUtility_one
@[simp] theorem precautionary_income_zero : precautionary.income 0 = 1 / 100 := rfl
@[simp] theorem precautionary_income_one : precautionary.income 1 = 1 := rfl
@[simp] theorem precautionary_interest : precautionary.interest = 0 := rfl
@[simp] theorem precautionary_discount : (precautionary.discount : ℝ) = 1 / 2 := rfl
@[simp] theorem precautionary_transitionMatrix (z z' : Fin 2) :
    precautionary.transitionMatrix z z' = 1 / 2 := rfl

/-- The comparison the whole thing turns on: `log 2 < (1/4) log 51`, which is `log 16 < log 51`. -/
theorem precautionary_gain : Real.log 2 < 1 / 2 * (1 / 2 * Real.log 51) := by
  have hlt : Real.log 16 < Real.log 51 := Real.log_lt_log (by norm_num) (by norm_num)
  have heq : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [heq] at hlt
  linarith

/-- **Aggregate capital is strictly positive in this economy**, at every stationary
distribution. -/
theorem precautionary_aggregateCapital_pos
    {μ : ProbabilityMeasure precautionary.State} (hμ : precautionary.IsStationary μ) :
    0 < precautionary.aggregateCapital μ := by
  refine precautionary.aggregateCapital_pos_of_primitives
    (precautionary.positiveConsumption_of_unbounded rfl) precautionary_u hμ
    (z₁ := 1) (z₀ := 0) (p₀ := 1 / 2) (by norm_num) (fun z => by norm_num)
    (h := 1 / 2) (by norm_num) (by norm_num) (by norm_num) ?_
  have hgain := precautionary_gain
  norm_num
  convert hgain using 3

/-- **An economy with a stationary agent distribution and strictly positive aggregate capital.**
The first in this development: existence from Krylov–Bogolyubov, positivity from the
precautionary motive. -/
theorem precautionary_exists_positive_capital :
    ∃ μ : ProbabilityMeasure precautionary.State,
      precautionary.IsStationary μ ∧ 0 < precautionary.aggregateCapital μ := by
  obtain ⟨s₀⟩ : Nonempty precautionary.State := inferInstance
  obtain ⟨μ, hμ⟩ := precautionary.exists_isStationary ⟨Measure.dirac s₀, inferInstance⟩
  exact ⟨μ, hμ, precautionary_aggregateCapital_pos hμ⟩

end LeanEconomics
