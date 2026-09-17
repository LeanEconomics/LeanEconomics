/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationIterate
import LeanEconomics.Models.CESNearLogWitness

/-!
# Carroll and Kimball at a concrete CES calibration

`concaveOn_consumptionFn_of_oscSpread` asks for exactly the calibration inequality that
`crra_policy_lt_assetCap` asks for, so the witnesses that already discharge that one discharge
this one. `nearLog` — CES with `γ = 15/16`, `β = 1/8`, income in `{1/100, 1}`, cap `1` — is the
calibration built for the localised Carroll–Kimball hypothesis, and it is the one where the
whole chain closes: the consumption function of a concrete incomplete-markets household, at
every rate in `[0, 1/200]`, is concave.
-/

open Set

namespace LeanEconomics

/-- **The consumption function of `nearLog` is concave**, at every rate the equilibrium argument
uses. Carroll and Kimball (1996) for an economy that exists. -/
theorem nearLog_concaveOn_consumptionFn {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : nearLog.RateOK r) (z : Fin 2) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) ((nearLog.withRate r hrr).consumptionFn z) := by
  refine (nearLog.withRate r hrr).concaveOn_consumptionFn_of_oscSpread
    (γ := 15 / 16) (θ := 999 / 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show (((nearLog.withRate r hrr).discount : ℝ)) = 1 / 8 from rfl]; norm_num)
    rfl rfl ?_ z
  rw [IncomeFluctuation.oscSpread_eq_oscGap]
  simp only [mul_zero, sub_zero]
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

end LeanEconomics
