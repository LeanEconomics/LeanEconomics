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

## What widens

| | `cesWitness` (`γ = 1/2`) | this (`γ = 15/16`) | `dispersed` (log) |
|---|---|---|---|
| discount factor | `1/16` | `1/8` | `1/8` |
| income spread | `5000 : 1` | `100 : 1` | `100 : 1` |
| rate interval | `[0, 1/100]` | `[0, 1/10]` | `[0, 1/20]` |

So the rate interval is ten times wider than the `γ = 1/2` witness's and twice the log one's, at
fifty times less dispersion. Nothing about the CONSTANTS changed; what changed is that `γ` near 1
makes CES behave like log, which is the sanity check one wants on them.

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
noncomputable def nearLog : IncomeFluctuation (Fin 2) (1 / 25) where
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

`oscGap = 16 (maxConsumption ^ (1/16) - minIncome ^ (1/16)) / (1 - β)`, and the two sixteenth
roots are pinned by `261/250 ≤ (10027/10000) ^ 16` and `(7498/10000) ^ 16 ≤ 1/100`. -/

theorem nearLog_oscGap_le_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 10)) (hrr : 0 < 1 + r) :
    (nearLog.withRate r hrr).oscGap ≤ 47 / 10 := by
  have hmaxpos : (0 : ℝ) ≤ (nearLog.withRate r hrr).maxConsumption :=
    (nearLog.withRate r hrr).maxConsumption_pos.le
  have hmax : (nearLog.withRate r hrr).maxConsumption ≤ 261 / 250 := by
    simp only [IncomeFluctuation.maxConsumption, IncomeFluctuation.withRate_maxIncome,
      IncomeFluctuation.withRate_interest, nearLog_maxIncome]
    linarith [hr.2]
  have hhi : (nearLog.withRate r hrr).maxConsumption ^ ((1 : ℝ) / 16) ≤ 10027 / 10000 := by
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

/-! ### Decline above `1/50`, uniformly in the rate -/

theorem nearLog_decline_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 10)) (hrr : 0 < 1 + r)
    {a : ℝ} (ha : a ∈ Icc (1 / 50 : ℝ) (1 / 25)) :
    (nearLog.withRate r hrr).policy (a, 0) < a := by
  have hrhi : (0 : ℝ) < 1 + 1 / 10 := by norm_num
  have hmem : a ∈ Icc (0 : ℝ) (1 / 25) := ⟨by linarith [ha.1], ha.2⟩
  refine nearLog.crra_policy_lt_self_uniform (γ := 15 / 16) (θ := 49 / 50) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) rfl rfl hrr hrhi hr.2 (by linarith [hr.1])
    (nearLog_withRate_positiveConsumption hrr) hmem 0 ?_
  have hosc := nearLog_oscGap_le_uniform (r := 1 / 10) (by norm_num) hrhi
  have hosc0 := (nearLog.withRate (1 / 10) hrhi).oscGap_nonneg
  have harg : nearLog.income 0 + (1 + 1 / 10 - 49 / 50) * (1 / 25) = 37 / 2500 := by
    simp only [nearLog_income_zero]; norm_num
  rw [harg]
  have hs : (37 / 2500 : ℝ) ^ ((15 : ℝ) / 16) ≤ 1 / 50 :=
    rpow_le_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hs0 : (0 : ℝ) ≤ (37 / 2500 : ℝ) ^ ((15 : ℝ) / 16) := Real.rpow_nonneg (by norm_num) _
  have hcoef : (((nearLog.withRate (1 / 10) hrhi).discount : ℝ))
      * (nearLog.withRate (1 / 10) hrhi).oscGap / (49 / 50) ≤ 235 / 392 := by
    rw [show (((nearLog.withRate (1 / 10) hrhi).discount : ℝ)) = 1 / 8 from rfl,
      div_le_iff₀ (by norm_num)]
    linarith [hosc]
  have hcoef0 : (0 : ℝ) ≤ (((nearLog.withRate (1 / 10) hrhi).discount : ℝ))
      * (nearLog.withRate (1 / 10) hrhi).oscGap / (49 / 50) := by
    rw [show (((nearLog.withRate (1 / 10) hrhi).discount : ℝ)) = 1 / 8 from rfl]
    positivity
  calc (((nearLog.withRate (1 / 10) hrhi).discount : ℝ))
        * (nearLog.withRate (1 / 10) hrhi).oscGap / (49 / 50)
        * (37 / 2500 : ℝ) ^ ((15 : ℝ) / 16)
      ≤ (235 / 392) * (1 / 50) := by nlinarith [hcoef, hs, hs0, hcoef0]
    _ < 1 / 50 := by norm_num
    _ ≤ a := ha.1

/-! ### Corner below `1/50`, uniformly in the rate

The slope bound at the income floor is `32 · 100 ^ (15/16) · (1 - 2 ^ (-1/16))`, pinned by
`100 ^ 15 ≤ 80 ^ 16` and `2 ≤ (209/200) ^ 16`. Compare the log constant `2 log 2 / minIncome =
200 log 2 ≈ 139`: at `γ = 15/16` it is about 110, already close. -/

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

theorem nearLog_corner_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 10)) (hrr : 0 < 1 + r)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (1 / 50)) :
    (nearLog.withRate r hrr).policy (a, 0) = 0 := by
  have hrhi : (0 : ℝ) < 1 + 1 / 10 := by norm_num
  have hmem : a ∈ Icc (0 : ℝ) (1 / 25) := ⟨ha.1, by linarith [ha.2]⟩
  refine nearLog.crra_policy_eq_zero_uniform (γ := 15 / 16) (by norm_num) (by norm_num)
    rfl rfl hrr hrhi hr.2 (by norm_num) hmem 0 ?_
  -- the Lipschitz constant at the top of the interval
  have hlip : (nearLog.withRate (1 / 10) hrhi).crraLipschitz (15 / 16) ≤ 142 := by
    simp only [IncomeFluctuation.crraLipschitz, IncomeFluctuation.withRate_minIncome,
      IncomeFluctuation.withRate_interest, IncomeFluctuation.withRate_discount,
      nearLog_minIncome, nearLog_discount]
    rw [div_le_iff₀ (by norm_num)]
    linarith [nearLog_crraSlopeBound_le]
  -- resources, and its negative power
  have hres : (nearLog.withRate (1 / 10) hrhi).resources (a, 0)
      = 1 / 100 + (1 + 1 / 10) * a := by
    simp only [IncomeFluctuation.resources, IncomeFluctuation.withRate_income,
      IncomeFluctuation.withRate_interest, nearLog_income_zero, max_eq_right ha.1]
  have hres0 : (0 : ℝ) < 1 / 100 + (1 + 1 / 10) * a := by nlinarith [ha.1]
  have hresle : 1 / 100 + (1 + 1 / 10) * a ≤ 4 / 125 := by nlinarith [ha.2]
  have hup : (1 / 100 + (1 + 1 / 10) * a) ^ ((15 : ℝ) / 16) ≤ 1 / 25 := by
    refine le_trans (Real.rpow_le_rpow hres0.le hresle (by norm_num)) ?_
    exact rpow_le_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have huppos : (0 : ℝ) < (1 / 100 + (1 + 1 / 10) * a) ^ ((15 : ℝ) / 16) :=
    Real.rpow_pos_of_pos hres0 _
  have hge : (25 : ℝ) ≤ ((1 / 100 + (1 + 1 / 10) * a) ^ ((15 : ℝ) / 16))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ huppos]; nlinarith [hup]
  rw [hres, Real.rpow_neg hres0.le,
    show (((nearLog.withRate (1 / 10) hrhi).discount : ℝ)) = 1 / 8 from rfl]
  nlinarith [hlip, hge]

/-- **A unique stationary distribution at every rate in `[0, 1/10]`.** -/
theorem nearLog_existsUnique_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 10)) (hrr : 0 < 1 + r) :
    ∃! μ : ProbabilityMeasure nearLog.State, (nearLog.withRate r hrr).IsStationary μ := by
  obtain ⟨N, hN⟩ := (nearLog.withRate r hrr).exists_exhaust_of_decline (z₀ := 0)
    (a₀ := 1 / 50) (by norm_num) (by norm_num)
    (fun a ha => nearLog_corner_uniform hr hrr ha)
    (fun a ha => nearLog_decline_uniform hr hrr ha)
  exact (nearLog.withRate r hrr).existsUnique_isStationary (z₀ := 0) (N := N)
    (fun z => by norm_num) hN

/-! ### The supply floor, and the equilibrium

At `r = 1/10` the whole gain condition is `320 · A⁻¹ < 11 · B⁻¹` for the two sixteenth-root
quantities, pinned by `(1011/100000) ^ 15 ≤ (1/70) ^ 16` and `(9/10) ^ 16 ≤ (9999/10000) ^ 15`. -/

theorem nearLog_floor_top (hrhi : 0 < 1 + (1 / 10 : ℝ))
    (μ : ProbabilityMeasure nearLog.State)
    (hμ : (nearLog.withRate (1 / 10) hrhi).IsStationary μ) :
    1 / 40000 ≤ nearLog.aggregateCapital μ := by
  have hkey := (nearLog.withRate (1 / 10) hrhi).crra_le_aggregateCapital_of_gain
    (γ := 15 / 16) (by norm_num) (by norm_num) rfl
    (nearLog_withRate_positiveConsumption hrhi) hμ
    (z₁ := 1) (z₀ := 0) (p₀ := 1 / 2) (h := 1 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (fun z => by norm_num) ?_
  · have heq : (nearLog.withRate (1 / 10) hrhi).aggregateCapital μ
        = nearLog.aggregateCapital μ := rfl
    rw [heq] at hkey
    linarith [hkey]
  · simp only [IncomeFluctuation.withRate_income, IncomeFluctuation.withRate_interest,
      IncomeFluctuation.withRate_discount, nearLog_income_zero, nearLog_income_one,
      nearLog_discount]
    rw [show (nearLog.withRate (1 / 10) hrhi).transitionMatrix 1 0 = 1 / 2 from rfl,
      show (1 : ℝ) - 1 / 10000 = 9999 / 10000 from by norm_num,
      show (1 : ℝ) / 100 + (1 + 1 / 10) * (1 / 10000) = 1011 / 100000 from by norm_num,
      show (1 + (1 : ℝ) / 10) * (1 / 10000 / 2) = 11 / 200000 from by norm_num,
      Real.rpow_neg (show (0:ℝ) ≤ 9999 / 10000 by norm_num),
      Real.rpow_neg (show (0:ℝ) ≤ 1011 / 100000 by norm_num)]
  -- `A` is near one and `B` is near `1/70`
    have hA : (9 : ℝ) / 10 ≤ (9999 / 10000 : ℝ) ^ ((15 : ℝ) / 16) :=
      le_rpow_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    have hApos : (0 : ℝ) < (9999 / 10000 : ℝ) ^ ((15 : ℝ) / 16) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hB : (1011 / 100000 : ℝ) ^ ((15 : ℝ) / 16) ≤ 1 / 70 :=
      rpow_le_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    have hBpos : (0 : ℝ) < (1011 / 100000 : ℝ) ^ ((15 : ℝ) / 16) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hAinv : ((9999 / 10000 : ℝ) ^ ((15 : ℝ) / 16))⁻¹ ≤ 10 / 9 := by
      rw [inv_eq_one_div, div_le_iff₀ hApos]; nlinarith [hA]
    have hBinv : (70 : ℝ) ≤ ((1011 / 100000 : ℝ) ^ ((15 : ℝ) / 16))⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hBpos]; nlinarith [hB]
    nlinarith [hAinv, hBinv]

/-- **An Aiyagari equilibrium at the log calibration, with CES utility bounded below.** Discount
factor `1/8` and a `100 : 1` income spread -- the numbers of the log witness -- over a rate
interval `[0, 1/10]`, ten times the width the `γ = 1/2` witness could carry. -/
theorem nearLog_exists_equilibrium :
    ∃ A δ : ℝ, 0 < A ∧ 0 < 0 + δ ∧ ∃ r ∈ Icc (0 : ℝ) (1 / 10),
      IsAiyagariEquilibrium
        (nearLog.rateFamily (by norm_num : (0:ℝ) < 1 + 0) (by norm_num : (0:ℝ) ≤ 1 / 10))
        (capitalDemand A δ) r :=
  nearLog.exists_equilibrium_of_uniqueness_and_floor (by norm_num) (by norm_num)
    (fun r hr hrr => nearLog_existsUnique_uniform hr hrr) (by norm_num)
    (fun hrr μ hμ => nearLog_floor_top hrr μ hμ)

/-- The same equilibrium in implied-rate form. -/
theorem nearLog_exists_equilibrium_impliedRate :
    ∃ A δ : ℝ, 0 < A ∧ ∃ r ∈ Icc (0 : ℝ) (1 / 10),
      ∃ μ : ProbabilityMeasure nearLog.State,
        ((nearLog.rateFamily (by norm_num : (0:ℝ) < 1 + 0)
          (by norm_num : (0:ℝ) ≤ 1 / 10)) r).IsStationary μ ∧
        0 < ((nearLog.rateFamily (by norm_num : (0:ℝ) < 1 + 0)
          (by norm_num : (0:ℝ) ≤ 1 / 10)) r).aggregateCapital μ ∧
        impliedRate A δ (((nearLog.rateFamily (by norm_num : (0:ℝ) < 1 + 0)
          (by norm_num : (0:ℝ) ≤ 1 / 10)) r).aggregateCapital μ) = r := by
  obtain ⟨A, δ, hA, hrδ, r, hr, heq⟩ := nearLog_exists_equilibrium
  refine ⟨A, δ, hA, r, hr, ?_⟩
  have hrpos : 0 < r + δ := by linarith [hr.1]
  exact (isAiyagariEquilibrium_iff_impliedRate hA hrpos).mp heq

end LeanEconomics
