/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.CESWitness

/-!
# Pushing `γ` toward 1: the CES witness at the log calibration

`cesWitness` runs at `γ = 1/2`, and it pays for it. The gain condition reduces to
`income_low + h < (β p (1+r)/2) ^ (1/γ) · (1 - h)`, so the tolerable low income falls like the
`1/γ` power of the discount factor: at `γ = 1/2` that is a SQUARE, and `β = 1/16` with
`p = 1/2` forces `income_low` below about `1/1000`. Hence the `5000 : 1` income spread, against
`100 : 1` for log.

Raising `γ` softens exactly that exponent. At `γ = 15/16` the same condition tolerates
`income_low` up to about `1/40`, and the witness can be run at the LOG witness's own numbers:
`β = 1/8`, income `{1/100, 1}`, drawn iid with probability `1/2`.

## What widens, and what pays for it

| | `cesWitness` (`γ = 1/2`) | this (`γ = 15/16`) | `dispersed` (log) |
|---|---|---|---|
| discount factor | `1/16` | `1/8` | `1/8` |
| income spread | `5000 : 1` | `100 : 1` | `100 : 1` |
| asset cap | `1/10` | `1` | `1` |
| cap reached? | not known | NO, provably | not known |
| rate interval | `[0, 1/100]` | `[0, 1/200]` | `[0, 1/20]` |

The preferences and the income process are the log witness's own; what is new is that
`nearLog_policy_lt_cap` shows saving never reaches the cap, so
`not_concaveOn_consumptionFn_of_cap_binds` -- which makes Carroll and Kimball's conclusion FALSE
wherever the cap binds -- cannot fire anywhere in this economy. That is what turns the localised
uniqueness hypothesis into a statement about a real calibration.

The rate interval pays for it. A cap saving never reaches has to be large, and a large cap widens
the decline threshold as the rate rises, so the interval narrows. That is the trade between the
cap and the interval, not slack in the estimates.

## The arithmetic

`γ = 15/16` means every exponent is `m/16`, and `rpow_le_of_pow_le` turns each comparison into
one of sixteenth powers of rationals, which `norm_num` settles. The four facts that carry the
file are `100 ^ 15 ≤ 80 ^ 16`, `2 ≤ (209/200) ^ 16`, `(7498/10000) ^ 16 ≤ 1/100` and
`261/250 ≤ (10027/10000) ^ 16`. There is no `√2` and no logarithm anywhere.
-/

open scoped NNReal
open Set Filter Topology MeasureTheory

namespace LeanEconomics

/-- Utility at `γ = 15/16`: `16 c ^ (1/16)`, bounded below by `0`. -/
theorem crraUtility_fifteen_sixteenths (c : ℝ) :
    crraUtility (15 / 16) c = 16 * c ^ ((1 : ℝ) / 16) := by
  rw [crraUtility_of_ne (by norm_num), show (1 : ℝ) - 15 / 16 = 1 / 16 from by norm_num]
  ring

/-- A household with CES utility at `γ = 15/16` and the log witness's own calibration. -/
noncomputable def nearLog : IncomeFluctuation (Fin 2) 1 where
  income z := if z = 0 then 1 / 100 else 1
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 8
  u := crraUtility (15 / 16)
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
  dom := Ici 0
  Ioi_subset_dom := Ioi_subset_Ici_self
  dom_subset_Ici := subset_rfl
  continuousOn_u_dom := continuousOn_crraUtility_Ici (by norm_num)
  monotoneOn_u_dom := monotoneOn_crraUtility_Ici (by norm_num)
  strictConcaveOn_u_dom := strictConcaveOn_crraUtility_Ici (by norm_num) (by norm_num)
  continuousOn_extendDom := continuousOn_extendDom_Ici (continuousOn_crraUtility_Ici (by norm_num))

@[simp] theorem nearLog_u : nearLog.u = crraUtility (15 / 16) := rfl
@[simp] theorem nearLog_income_zero : nearLog.income 0 = 1 / 100 := rfl
@[simp] theorem nearLog_income_one : nearLog.income 1 = 1 := rfl
@[simp] theorem nearLog_interest : nearLog.interest = 0 := rfl
@[simp] theorem nearLog_discount : (nearLog.discount : ℝ) = 1 / 8 := rfl
@[simp] theorem nearLog_minIncome : nearLog.minIncome = 1 / 100 := rfl
@[simp] theorem nearLog_maxIncome : nearLog.maxIncome = 1 := rfl
@[simp] theorem nearLog_transitionMatrix (z z' : Fin 2) :
    nearLog.transitionMatrix z z' = 1 / 2 := rfl

theorem nearLog_bounded : nearLog.Bounded := rfl

theorem nearLog_positiveConsumption : nearLog.PositiveConsumption :=
  nearLog.positiveConsumption_of_bounded_crra (by norm_num) (by norm_num) rfl rfl

theorem nearLog_withRate_positiveConsumption {r : ℝ} (hrr : 0 < 1 + r) :
    (nearLog.withRate r hrr).PositiveConsumption :=
  (nearLog.withRate r hrr).positiveConsumption_of_bounded_crra (γ := 15 / 16) (by norm_num)
    (by norm_num) rfl rfl

/-- Utility is finite at zero consumption, so this economy too is outside the unbounded
structure. -/
theorem nearLog_u_zero : nearLog.u 0 = 0 := crraUtility_zero (by norm_num)

theorem nearLog_not_unbounded : ¬ nearLog.Unbounded := by
  intro h
  have hz : (0 : ℝ) ∈ nearLog.dom := mem_Ici.mpr le_rfl
  rw [h] at hz
  exact absurd hz (by simp)

/-! ### The oscillation gap

`oscGap = 16 (maxConsumption ^ (1/16) - minIncome ^ (1/16)) / (1 - β)`, pinned by
`401/200 ≤ (10445/10000) ^ 16` and `(7498/10000) ^ 16 ≤ 1/100`. -/

theorem nearLog_oscGap_le_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200)) (hrr : 0 < 1 + r) :
    (nearLog.withRate r hrr).oscGap ≤ 27 / 5 := by
  have hmaxpos : (0 : ℝ) ≤ (nearLog.withRate r hrr).maxConsumption :=
    (nearLog.withRate r hrr).maxConsumption_pos.le
  have hmax : (nearLog.withRate r hrr).maxConsumption ≤ 401 / 200 := by
    simp only [IncomeFluctuation.maxConsumption, IncomeFluctuation.withRate_maxIncome,
      IncomeFluctuation.withRate_interest, nearLog_maxIncome]
    linarith [hr.2]
  have hhi : (nearLog.withRate r hrr).maxConsumption ^ ((1 : ℝ) / 16) ≤ 10445 / 10000 := by
    refine rpow_le_of_pow_le (m := 1) (n := 16) (by norm_num) hmaxpos (by norm_num)
      (by norm_num) ?_
    simpa using le_trans hmax (by norm_num)
  have hlo : (7498 : ℝ) / 10000 ≤ (1 / 100 : ℝ) ^ ((1 : ℝ) / 16) :=
    le_rpow_of_pow_le (m := 1) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  simp only [IncomeFluctuation.oscGap, IncomeFluctuation.withRate_u,
    IncomeFluctuation.withRate_minIncome, IncomeFluctuation.withRate_discount,
    nearLog_u, nearLog_minIncome, nearLog_discount, crraUtility_fifteen_sixteenths]
  rw [div_le_iff₀ (by norm_num)]
  linarith [hhi, hlo]

/-- The coefficient `β · oscGap / θ` that multiplies every saving bound. -/
theorem nearLog_coef_le (hrhi : 0 < 1 + (1 / 200 : ℝ)) :
    ((nearLog.withRate (1 / 200) hrhi).discount : ℝ)
        * (nearLog.withRate (1 / 200) hrhi).oscGap / (999 / 1000) ≤ 25 / 37 := by
  have hosc := nearLog_oscGap_le_uniform (r := 1 / 200) (by norm_num) hrhi
  rw [show (((nearLog.withRate (1 / 200) hrhi).discount : ℝ)) = 1 / 8 from rfl,
    div_le_iff₀ (by norm_num)]
  linarith [hosc]

theorem nearLog_coef_nonneg (hrhi : 0 < 1 + (1 / 200 : ℝ)) :
    (0 : ℝ) ≤ ((nearLog.withRate (1 / 200) hrhi).discount : ℝ)
        * (nearLog.withRate (1 / 200) hrhi).oscGap / (999 / 1000) := by
  rw [show (((nearLog.withRate (1 / 200) hrhi).discount : ℝ)) = 1 / 8 from rfl]
  have := (nearLog.withRate (1 / 200) hrhi).oscGap_nonneg
  positivity

/-! ### The asset cap never binds

This is what makes the localised Carroll–Kimball hypothesis a statement about a real economy.
Saving would have to reach `1` for `not_concaveOn_consumptionFn_of_cap_binds` to fire; if it did,
consumption would be at most `1 + (1 + r - θ) · 1 = 503/500`, and the saving bound there is
`503/740 < 1`. -/

theorem nearLog_policy_lt_cap {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200)) (hrr : 0 < 1 + r)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 2) :
    (nearLog.withRate r hrr).policy (a, z) < 1 := by
  refine (nearLog.withRate r hrr).crra_policy_lt_assetCap (γ := 15 / 16) (θ := 999 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rfl rfl (nearLog_withRate_positiveConsumption hrr) ?_ ha z
  have hosc := nearLog_oscGap_le_uniform hr hrr
  have hosc0 := (nearLog.withRate r hrr).oscGap_nonneg
  have hcoef : ((nearLog.withRate r hrr).discount : ℝ)
      * (nearLog.withRate r hrr).oscGap / (999 / 1000) ≤ 25 / 37 := by
    rw [show (((nearLog.withRate r hrr).discount : ℝ)) = 1 / 8 from rfl,
      div_le_iff₀ (by norm_num)]
    linarith [hosc]
  have hcoef0 : (0 : ℝ) ≤ ((nearLog.withRate r hrr).discount : ℝ)
      * (nearLog.withRate r hrr).oscGap / (999 / 1000) := by
    rw [show (((nearLog.withRate r hrr).discount : ℝ)) = 1 / 8 from rfl]; positivity
  have hbase : (nearLog.withRate r hrr).maxIncome
      + (1 + (nearLog.withRate r hrr).interest - 999 / 1000) * 1 ≤ 503 / 500 := by
    simp only [IncomeFluctuation.withRate_maxIncome, IncomeFluctuation.withRate_interest,
      nearLog_maxIncome]
    linarith [hr.2]
  have hbase0 : (0 : ℝ) ≤ (nearLog.withRate r hrr).maxIncome
      + (1 + (nearLog.withRate r hrr).interest - 999 / 1000) * 1 := by
    simp only [IncomeFluctuation.withRate_maxIncome, IncomeFluctuation.withRate_interest,
      nearLog_maxIncome]
    linarith [hr.1]
  have hpow : ((nearLog.withRate r hrr).maxIncome
      + (1 + (nearLog.withRate r hrr).interest - 999 / 1000) * 1) ^ ((15 : ℝ) / 16)
      ≤ 503 / 500 := by
    refine le_trans (Real.rpow_le_rpow hbase0 hbase (by norm_num)) ?_
    exact rpow_le_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hpow0 : (0 : ℝ) ≤ ((nearLog.withRate r hrr).maxIncome
      + (1 + (nearLog.withRate r hrr).interest - 999 / 1000) * 1) ^ ((15 : ℝ) / 16) :=
    Real.rpow_nonneg hbase0 _
  nlinarith [hcoef, hpow, hcoef0, hpow0]

/-! ### Decline above `1/50`, uniformly in the rate -/

theorem nearLog_decline_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200)) (hrr : 0 < 1 + r)
    {a : ℝ} (ha : a ∈ Icc (1 / 50 : ℝ) 1) :
    (nearLog.withRate r hrr).policy (a, 0) < a := by
  have hrhi : (0 : ℝ) < 1 + 1 / 200 := by norm_num
  have hmem : a ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ha.1], ha.2⟩
  refine nearLog.crra_policy_lt_self_uniform (γ := 15 / 16) (θ := 999 / 1000) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) rfl rfl hrr hrhi hr.2 (by linarith [hr.1])
    (nearLog_withRate_positiveConsumption hrr) hmem 0 ?_
  have harg : nearLog.income 0 + (1 + 1 / 200 - 999 / 1000) * 1 = 2 / 125 := by
    simp only [nearLog_income_zero]; norm_num
  rw [harg]
  have hs : (2 / 125 : ℝ) ^ ((15 : ℝ) / 16) ≤ 21 / 1000 :=
    rpow_le_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hs0 : (0 : ℝ) ≤ (2 / 125 : ℝ) ^ ((15 : ℝ) / 16) := Real.rpow_nonneg (by norm_num) _
  calc (((nearLog.withRate (1 / 200) hrhi).discount : ℝ))
        * (nearLog.withRate (1 / 200) hrhi).oscGap / (999 / 1000)
        * (2 / 125 : ℝ) ^ ((15 : ℝ) / 16)
      ≤ (25 / 37) * (21 / 1000) := by
        nlinarith [nearLog_coef_le hrhi, hs, hs0, nearLog_coef_nonneg hrhi]
    _ < 1 / 50 := by norm_num
    _ ≤ a := ha.1

/-! ### Corner below `1/50`, uniformly in the rate -/

theorem nearLog_crraSlopeBound_le : crraSlopeBound (15 / 16) (1 / 100) ≤ 111 := by
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 16) ≤ 209 / 200 :=
    rpow_le_of_pow_le (m := 1) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos (by norm_num) _
  have h2ge : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 16) :=
    Real.one_le_rpow (by norm_num) (by norm_num)
  have hinv : (200 : ℝ) / 209 ≤ ((2 : ℝ) ^ ((1 : ℝ) / 16))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ h2pos]; nlinarith [h2]
  have hinv1 : ((2 : ℝ) ^ ((1 : ℝ) / 16))⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one h2pos]; linarith [h2ge]
  have hm : (1 : ℝ) / 80 ≤ ((1 : ℝ) / 100) ^ ((15 : ℝ) / 16) :=
    le_rpow_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmpos : (0 : ℝ) < ((1 : ℝ) / 100) ^ ((15 : ℝ) / 16) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hminv : (((1 : ℝ) / 100) ^ ((15 : ℝ) / 16))⁻¹ ≤ 80 := by
    rw [inv_eq_one_div, div_le_iff₀ hmpos]; nlinarith [hm]
  have hneg : ((1 : ℝ) / 100) ^ (-(15 / 16) : ℝ) = (((1 : ℝ) / 100) ^ ((15 : ℝ) / 16))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  simp only [crraSlopeBound, show (1 : ℝ) - 15 / 16 = 1 / 16 from by norm_num, hneg]
  rw [div_le_iff₀ (by norm_num)]
  nlinarith [hminv, hinv, hinv1, inv_nonneg.mpr hmpos.le]

theorem nearLog_corner_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200)) (hrr : 0 < 1 + r)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (1 / 50)) :
    (nearLog.withRate r hrr).policy (a, 0) = 0 := by
  have hrhi : (0 : ℝ) < 1 + 1 / 200 := by norm_num
  have hmem : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
  refine nearLog.crra_policy_eq_zero_uniform (γ := 15 / 16) (by norm_num) (by norm_num)
    rfl rfl hrr hrhi hr.2 (by norm_num) hmem 0 ?_
  have hlip : (nearLog.withRate (1 / 200) hrhi).crraLipschitz (15 / 16) ≤ 128 := by
    simp only [IncomeFluctuation.crraLipschitz, IncomeFluctuation.withRate_minIncome,
      IncomeFluctuation.withRate_interest, IncomeFluctuation.withRate_discount,
      nearLog_minIncome, nearLog_discount]
    rw [div_le_iff₀ (by norm_num)]
    linarith [nearLog_crraSlopeBound_le]
  have hres : (nearLog.withRate (1 / 200) hrhi).resources (a, 0)
      = 1 / 100 + (1 + 1 / 200) * a := by
    simp only [IncomeFluctuation.resources, IncomeFluctuation.withRate_income,
      IncomeFluctuation.withRate_interest, nearLog_income_zero, max_eq_right ha.1]
  have hres0 : (0 : ℝ) < 1 / 100 + (1 + 1 / 200) * a := by nlinarith [ha.1]
  have hresle : 1 / 100 + (1 + 1 / 200) * a ≤ 301 / 10000 := by nlinarith [ha.2]
  have hup : (1 / 100 + (1 + 1 / 200) * a) ^ ((15 : ℝ) / 16) ≤ 1 / 25 := by
    refine le_trans (Real.rpow_le_rpow hres0.le hresle (by norm_num)) ?_
    exact rpow_le_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have huppos : (0 : ℝ) < (1 / 100 + (1 + 1 / 200) * a) ^ ((15 : ℝ) / 16) :=
    Real.rpow_pos_of_pos hres0 _
  have hge : (25 : ℝ) ≤ ((1 / 100 + (1 + 1 / 200) * a) ^ ((15 : ℝ) / 16))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ huppos]; nlinarith [hup]
  rw [hres, Real.rpow_neg hres0.le,
    show (((nearLog.withRate (1 / 200) hrhi).discount : ℝ)) = 1 / 8 from rfl]
  nlinarith [hlip, hge]

/-- **A unique stationary distribution at every rate in `[0, 1/200]`.** -/
theorem nearLog_existsUnique_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200)) (hrr : 0 < 1 + r) :
    ∃! μ : ProbabilityMeasure nearLog.State, (nearLog.withRate r hrr).IsStationary μ := by
  obtain ⟨N, hN⟩ := (nearLog.withRate r hrr).exists_exhaust_of_decline (z₀ := 0)
    (a₀ := 1 / 50) (by norm_num) (by norm_num)
    (fun a ha => nearLog_corner_uniform hr hrr ha)
    (fun a ha => nearLog_decline_uniform hr hrr ha)
  exact (nearLog.withRate r hrr).existsUnique_isStationary (z₀ := 0) (N := N)
    (fun z => by norm_num) hN

/-! ### The supply floor, and the equilibrium

At `r = 1/200` the gain condition is `6400 · A⁻¹ < 201 · B⁻¹` for the two sixteenth-root
quantities, pinned by `(2000201/200000000) ^ 15 ≤ (1/74) ^ 16` and
`(9/10) ^ 16 ≤ (999999/1000000) ^ 15`. -/

theorem nearLog_floor_top (hrhi : 0 < 1 + (1 / 200 : ℝ))
    (μ : ProbabilityMeasure nearLog.State)
    (hμ : (nearLog.withRate (1 / 200) hrhi).IsStationary μ) :
    1 / 4000000 ≤ nearLog.aggregateCapital μ := by
  have hkey := (nearLog.withRate (1 / 200) hrhi).crra_le_aggregateCapital_of_gain
    (γ := 15 / 16) (by norm_num) (by norm_num) rfl
    (nearLog_withRate_positiveConsumption hrhi) hμ
    (z₁ := 1) (z₀ := 0) (p₀ := 1 / 2) (h := 1 / 1000000) (by norm_num) (by norm_num)
    (by norm_num) (fun z => by norm_num) ?_
  · have heq : (nearLog.withRate (1 / 200) hrhi).aggregateCapital μ
        = nearLog.aggregateCapital μ := rfl
    rw [heq] at hkey
    linarith [hkey]
  · simp only [IncomeFluctuation.withRate_income, IncomeFluctuation.withRate_interest,
      IncomeFluctuation.withRate_discount, nearLog_income_zero, nearLog_income_one,
      nearLog_discount]
    rw [show (nearLog.withRate (1 / 200) hrhi).transitionMatrix 1 0 = 1 / 2 from rfl,
      show (1 : ℝ) - 1 / 1000000 = 999999 / 1000000 from by norm_num,
      show (1 : ℝ) / 100 + (1 + 1 / 200) * (1 / 1000000) = 2000201 / 200000000 from by norm_num,
      show (1 + (1 : ℝ) / 200) * (1 / 1000000 / 2) = 201 / 400000000 from by norm_num,
      Real.rpow_neg (show (0:ℝ) ≤ 999999 / 1000000 by norm_num),
      Real.rpow_neg (show (0:ℝ) ≤ 2000201 / 200000000 by norm_num)]
    have hA : (9 : ℝ) / 10 ≤ (999999 / 1000000 : ℝ) ^ ((15 : ℝ) / 16) :=
      le_rpow_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    have hApos : (0 : ℝ) < (999999 / 1000000 : ℝ) ^ ((15 : ℝ) / 16) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hB : (2000201 / 200000000 : ℝ) ^ ((15 : ℝ) / 16) ≤ 1 / 74 :=
      rpow_le_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    have hBpos : (0 : ℝ) < (2000201 / 200000000 : ℝ) ^ ((15 : ℝ) / 16) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hAinv : ((999999 / 1000000 : ℝ) ^ ((15 : ℝ) / 16))⁻¹ ≤ 10 / 9 := by
      rw [inv_eq_one_div, div_le_iff₀ hApos]; nlinarith [hA]
    have hBinv : (74 : ℝ) ≤ ((2000201 / 200000000 : ℝ) ^ ((15 : ℝ) / 16))⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hBpos]; nlinarith [hB]
    nlinarith [hAinv, hBinv]

/-- **An Aiyagari equilibrium at the log calibration, with the asset cap provably slack.**
Discount factor `1/8` and a `100 : 1` income spread, as before, but now with a cap that saving
never reaches -- so `not_concaveOn_consumptionFn_of_cap_binds` cannot fire anywhere in this
economy, and the localised Carroll-Kimball hypothesis is a statement about it rather than a
hypothetical.

The rate interval pays for the cap. A cap saving never reaches has to be large, and a large cap
widens the decline threshold as the rate rises, so `[0, 1/10]` becomes `[0, 1/200]`. That is the
trade, not a weakness of the estimates. -/
theorem nearLog_exists_equilibrium :
    ∃ A δ : ℝ, 0 < A ∧ 0 < 0 + δ ∧ ∃ r ∈ Icc (0 : ℝ) (1 / 200),
      IsAiyagariEquilibrium
        (nearLog.rateFamily (by norm_num : (0:ℝ) < 1 + 0) (by norm_num : (0:ℝ) ≤ 1 / 200))
        (capitalDemand A δ) r :=
  nearLog.exists_equilibrium_of_uniqueness_and_floor (by norm_num) (by norm_num)
    (fun r hr hrr => nearLog_existsUnique_uniform hr hrr) (by norm_num)
    (fun hrr μ hμ => nearLog_floor_top hrr μ hμ)

/-- The same equilibrium in implied-rate form. -/
theorem nearLog_exists_equilibrium_impliedRate :
    ∃ A δ : ℝ, 0 < A ∧ ∃ r ∈ Icc (0 : ℝ) (1 / 200),
      ∃ μ : ProbabilityMeasure nearLog.State,
        ((nearLog.rateFamily (by norm_num : (0:ℝ) < 1 + 0)
          (by norm_num : (0:ℝ) ≤ 1 / 200)) r).IsStationary μ ∧
        0 < ((nearLog.rateFamily (by norm_num : (0:ℝ) < 1 + 0)
          (by norm_num : (0:ℝ) ≤ 1 / 200)) r).aggregateCapital μ ∧
        impliedRate A δ (((nearLog.rateFamily (by norm_num : (0:ℝ) < 1 + 0)
          (by norm_num : (0:ℝ) ≤ 1 / 200)) r).aggregateCapital μ) = r := by
  obtain ⟨A, δ, hA, hrδ, r, hr, heq⟩ := nearLog_exists_equilibrium
  refine ⟨A, δ, hA, r, hr, ?_⟩
  have hrpos : 0 < r + δ := by linarith [hr.1]
  exact (isAiyagariEquilibrium_iff_impliedRate hA hrpos).mp heq

end LeanEconomics
