/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.NaturalAssetBound
import LeanEconomics.Equilibrium.PositiveCapital
import LeanEconomics.Distribution.Uniqueness
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# One economy where everything holds at once

The pieces have been accumulating conditionally: a corner condition, a decline condition, a
uniqueness theorem that needs both, and a positive-capital theorem that needs a third. This file
picks parameters at which all of them fire together, so the development has a single economy with
a UNIQUE stationary distribution carrying STRICTLY POSITIVE aggregate capital.

## The parameters and why they are these

`β = 1/8`, `r = 0`, income `{1/100, 1}` drawn iid with probability `1/2`, asset cap `1`.

Three conditions have to hold at once and they pull against each other.

* **Corner** (`log_policy_eq_zero_of_resources`): `β · logLipschitz < 1 / resources`, which here is
  `200 log 2 / 7 < 300/13`, i.e. `log 2 < 21/26`. It bounds resources, hence assets, ABOVE.
* **Decline** (`policy_lt_self_of_consumption_lower_bound`): needs `ε > 3/13` at `a ≥ 1/30`, where
  `ε = exp (-2 β ‖V‖)` is the linear consumption bound. It bounds assets BELOW.
* **Gain** (`aggregateCapital_pos_of_primitives`): saving `h = 1/16` out of high income must pay.

The two asset bounds must overlap, and `a₀ = 1/30` is in the gap. Raising `β` tightens the corner
and the decline together while loosening the gain; lowering it does the reverse. The window closes
around `β ≈ 0.15`, which is why the household is impatient. Narrowing the income spread closes it
too, which is why the spread is `100:1`.

## Everything reduces to integers

No numerical analysis is involved. The decline condition becomes `10000 < (13/3)^7`, the gain
condition `(16/15)^16 < 29/4`, and only the corner needs a transcendental fact at all —
`log 2 < 21/26`, which Mathlib's `Real.log_two_lt_d9` settles with room to spare.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

/-- An impatient household with log utility and 100:1 income dispersion. -/
noncomputable def dispersed : IncomeFluctuation (Fin 2) 1 where
  income z := if z = 0 then 1 / 100 else 1
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 8
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
  continuousOn_u := continuousOn_crraUtility 1
  monotoneOn_u := monotoneOn_crraUtility 1
  tendsto_atBot_u := tendsto_atBot_crraUtility le_rfl
  strictConcaveOn_u := strictConcaveOn_crraUtility one_pos

@[simp] theorem dispersed_u : dispersed.u = Real.log := crraUtility_one
@[simp] theorem dispersed_income_zero : dispersed.income 0 = 1 / 100 := rfl
@[simp] theorem dispersed_income_one : dispersed.income 1 = 1 := rfl
@[simp] theorem dispersed_interest : dispersed.interest = 0 := rfl
@[simp] theorem dispersed_discount : (dispersed.discount : ℝ) = 1 / 8 := rfl
@[simp] theorem dispersed_minIncome : dispersed.minIncome = 1 / 100 := rfl
@[simp] theorem dispersed_maxIncome : dispersed.maxIncome = 1 := rfl
@[simp] theorem dispersed_transitionMatrix (z z' : Fin 2) :
    dispersed.transitionMatrix z z' = 1 / 2 := rfl

theorem dispersed_maxConsumption : dispersed.maxConsumption = 2 := by
  simp only [IncomeFluctuation.maxConsumption, dispersed_maxIncome, dispersed_interest]
  norm_num

theorem dispersed_resources {a : ℝ} (ha : 0 ≤ a) (z : Fin 2) :
    dispersed.resources (a, z) = dispersed.income z + a := by
  simp only [IncomeFluctuation.resources, dispersed_interest, max_eq_right ha]
  ring

/-! ### The size of the value function -/

theorem dispersed_norm_le : ‖dispersed.toExtended.valueFunction‖ ≤ 8 / 7 * Real.log 100 := by
  have h := dispersed.toExtended.norm_valueFunction_le
  have hmin : dispersed.toExtended.rewardMin = dispersed.u dispersed.minIncome := rfl
  have hmax : dispersed.toExtended.rewardMax = dispersed.u dispersed.maxConsumption := rfl
  have hdisc : (dispersed.toExtended.discount : ℝ) = (dispersed.discount : ℝ) := rfl
  rw [hmin, hmax, hdisc, dispersed_maxConsumption, dispersed_u, dispersed_minIncome,
    dispersed_discount] at h
  have h1 : |Real.log (1 / 100)| = Real.log 100 := by
    rw [show (1 : ℝ) / 100 = (100 : ℝ)⁻¹ by norm_num, Real.log_inv, abs_neg,
      abs_of_nonneg (Real.log_nonneg (by norm_num))]
  have h2 : |Real.log 2| = Real.log 2 := abs_of_nonneg (Real.log_nonneg (by norm_num))
  have h3 : Real.log 2 ≤ Real.log 100 := Real.log_le_log (by norm_num) (by norm_num)
  rw [h1, h2, max_eq_left h3] at h
  calc ‖dispersed.toExtended.valueFunction‖ ≤ Real.log 100 / (1 - 1 / 8) := h
    _ = 8 / 7 * Real.log 100 := by ring

/-! ### The decline half -/

theorem dispersed_gap_lt : dispersed.deviationGap < Real.log (13 / 3) := by
  have hnorm := dispersed_norm_le
  have hlog100 : (0 : ℝ) ≤ Real.log 100 := Real.log_nonneg (by norm_num)
  have hkey : 2 * Real.log 100 < 7 * Real.log (13 / 3) := by
    have e1 : 2 * Real.log 100 = Real.log (100 ^ (2 : ℕ)) := by
      rw [Real.log_pow]; push_cast; ring
    have e2 : 7 * Real.log (13 / 3) = Real.log ((13 / 3 : ℝ) ^ (7 : ℕ)) := by
      rw [Real.log_pow]; push_cast; ring
    rw [e1, e2]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  simp only [IncomeFluctuation.deviationGap, dispersed_discount]
  nlinarith [hnorm, hkey]

theorem dispersed_eps_gt : 3 / 13 < Real.exp (-dispersed.deviationGap) := by
  have h := dispersed_gap_lt
  have h13 : (0 : ℝ) < 13 / 3 := by norm_num
  have hexp : Real.exp (-Real.log (13 / 3)) = 3 / 13 := by
    rw [Real.exp_neg, Real.exp_log h13]
    norm_num
  rw [← hexp]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem dispersed_decline {a : ℝ} (ha : a ∈ Icc (1 / 30 : ℝ) 1) :
    dispersed.policy (a, 0) < a := by
  have hmem : a ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ha.1], ha.2⟩
  have hlb := dispersed.log_consumption_linear_lower_bound dispersed_u hmem 0
  have heps := dispersed_eps_gt
  refine dispersed.policy_lt_self_of_consumption_lower_bound hmem hlb ?_
  simp only [dispersed_income_zero, dispersed_interest]
  nlinarith [heps, ha.1]

/-! ### The corner half -/

theorem dispersed_logLipschitz : dispersed.logLipschitz = 1600 * Real.log 2 / 7 := by
  simp only [IncomeFluctuation.logLipschitz, dispersed_minIncome, dispersed_interest,
    dispersed_discount]
  norm_num
  ring

theorem dispersed_corner {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (1 / 30)) :
    dispersed.policy (a, 0) = 0 := by
  have hmem : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
  have hlog2 : Real.log 2 < 21 / 26 := lt_trans Real.log_two_lt_d9 (by norm_num)
  refine dispersed.log_policy_eq_zero_of_resources dispersed_u (by norm_num) hmem ?_
  rw [dispersed_resources ha.1, dispersed_logLipschitz, dispersed_income_zero, dispersed_discount]
  rw [lt_div_iff₀ (by linarith [ha.1])]
  nlinarith [hlog2, ha.1, ha.2]

/-! ### Everything at once -/

theorem dispersed_exists_exhaust :
    ∃ N : ℕ, (dispersed.gBad 0)^[N] dispersed.topState = dispersed.botState :=
  dispersed.exists_exhaust_of_decline (by norm_num) (by norm_num)
    (fun a ha => dispersed_corner ha) (fun a ha => dispersed_decline ha)

/-- **A unique stationary agent distribution.** -/
theorem dispersed_existsUnique_isStationary :
    ∃! μ : ProbabilityMeasure dispersed.State, dispersed.IsStationary μ := by
  obtain ⟨N, hN⟩ := dispersed_exists_exhaust
  exact dispersed.existsUnique_isStationary (z₀ := 0) (N := N) (fun z => by norm_num) hN

/-- **Strictly positive aggregate capital**, at the stationary distribution. -/
theorem dispersed_aggregateCapital_pos {μ : ProbabilityMeasure dispersed.State}
    (hμ : dispersed.IsStationary μ) : 0 < dispersed.aggregateCapital μ := by
  refine dispersed.aggregateCapital_pos_of_primitives dispersed_u hμ
    (z₁ := 1) (z₀ := 0) (p₀ := 1 / 2) (by norm_num) (fun z => by norm_num)
    (h := 1 / 16) (by norm_num) (by norm_num) (by norm_num) ?_
  have hkey : Real.log (16 / 15) < 1 / 16 * Real.log (29 / 4) := by
    have e1 : (16 : ℝ) * Real.log (16 / 15) = Real.log ((16 / 15 : ℝ) ^ (16 : ℕ)) := by
      rw [Real.log_pow]; push_cast; ring
    have hlt : Real.log ((16 / 15 : ℝ) ^ (16 : ℕ)) < Real.log (29 / 4) :=
      Real.log_lt_log (by positivity) (by norm_num)
    rw [← e1] at hlt
    linarith
  simp only [dispersed_income_zero, dispersed_income_one, dispersed_interest,
    dispersed_discount, dispersed_transitionMatrix]
  norm_num
  linarith [hkey]

/-- **One economy, everything at once**: a unique stationary agent distribution, carrying
strictly positive aggregate capital. -/
theorem dispersed_unique_stationary_positive_capital :
    ∃! μ : ProbabilityMeasure dispersed.State,
      dispersed.IsStationary μ ∧ 0 < dispersed.aggregateCapital μ := by
  obtain ⟨μ, hμ, huniq⟩ := dispersed_existsUnique_isStationary
  exact ⟨μ, ⟨hμ, dispersed_aggregateCapital_pos hμ⟩, fun ν hν => huniq ν hν.1⟩

end LeanEconomics
