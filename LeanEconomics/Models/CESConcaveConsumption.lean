/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationIterate
import LeanEconomics.Models.CESNearLogWitness
import LeanEconomics.Models.CESWitness

/-!
# Carroll and Kimball at a concrete CES calibration

`concaveOn_consumptionFn_of_oscSpread` asks for exactly the calibration inequality that
`crra_policy_lt_assetCap` asks for, so the witnesses that already discharge that one discharge
this one. Two do:

* `nearLog` — CES with `γ = 15/16`, `β = 1/8`, income `{1/100, 1}`, cap `1` — at every rate in
  `[0, 1/200]`, which is the range the equilibrium argument uses;
* `sqrtCES` — CES with `γ = 1/2`, `β = 1/8`, income `{1/100, 1}`, cap `1`.

`cesWitness` does not, and `cesWitness_not_calibrated` says so: it is the same curvature as
`sqrtCES` with a cap of `1/10` instead of `1`, and the saving bound `β · oscGap` exceeds that
cap outright, for every `θ`. The cap is small relative to income, and no choice of deviation
repairs that. -/

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


/-! ### `γ = 1/2`: `sqrtCES`

The other bounded CES witness, at the square-root calibration. Its cap is `1`, and the
calibration goes through with room to spare. -/

theorem le_sqrt_of_sq {x c : ℝ} (hc : 0 ≤ c) (h : c ^ 2 ≤ x) : c ≤ Real.sqrt x :=
  le_trans (le_of_eq (Real.sqrt_sq hc).symm) (Real.sqrt_le_sqrt h)

@[simp] theorem sqrtCES_discount : (sqrtCES.discount : ℝ) = 1 / 8 := rfl
@[simp] theorem sqrtCES_interest : sqrtCES.interest = 0 := rfl
@[simp] theorem sqrtCES_maxIncome : sqrtCES.maxIncome = 1 := rfl

theorem sqrtCES_maxConsumption : sqrtCES.maxConsumption = 2 := by
  simp only [IncomeFluctuation.maxConsumption, sqrtCES_maxIncome, sqrtCES_interest]
  norm_num [sqrtCES]

@[simp] theorem sqrtCES_minConsumption : sqrtCES.minConsumption = 1 / 100 := by
  norm_num [sqrtCES]

theorem sqrtCES_oscGap_le : sqrtCES.oscGap ≤ 4 := by
  have h1 : Real.sqrt 2 ≤ 3 / 2 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) ≤ Real.sqrt (1 / 100) := Real.sqrt_nonneg _
  simp only [IncomeFluctuation.oscGap, sqrtCES_u, sqrtCES_maxConsumption,
    sqrtCES_minConsumption, sqrtCES_discount, crraUtility_half]
  rw [div_le_iff₀ (by norm_num)]
  nlinarith [h1, h2]

/-- **The consumption function of `sqrtCES` is concave.** CES with `γ = 1/2`, `β = 1/8`, income
in `{1/100, 1}`, cap `1` — utility bounded below, borrowing limit at zero, and nothing assumed. -/
theorem sqrtCES_concaveOn_consumptionFn (z : Fin 2) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (sqrtCES.consumptionFn z) := by
  refine sqrtCES.concaveOn_consumptionFn_of_oscSpread (γ := 1 / 2) (θ := 9 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show ((sqrtCES.discount : ℝ)) = 1 / 8 from rfl]; norm_num) rfl rfl ?_ z
  rw [IncomeFluctuation.oscSpread_eq_oscGap]
  have hosc := sqrtCES_oscGap_le
  have hosc0 := sqrtCES.oscGap_nonneg
  have hbase : sqrtCES.maxIncome + (1 + sqrtCES.interest - 9 / 10) * 1 - (1 - 9 / 10) * 0
      = 11 / 10 := by simp only [sqrtCES_maxIncome, sqrtCES_interest]; norm_num
  rw [hbase]
  have hpow : ((11 : ℝ) / 10) ^ ((1 : ℝ) / 2) ≤ 21 / 20 := by
    rw [← Real.sqrt_eq_rpow]
    exact sqrt_le_of_sq (by norm_num) (by norm_num)
  have hpow0 : (0 : ℝ) ≤ ((11 : ℝ) / 10) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hcoef : ((sqrtCES.discount : ℝ)) * sqrtCES.oscGap / (9 / 10) ≤ 5 / 9 := by
    rw [show ((sqrtCES.discount : ℝ)) = 1 / 8 from rfl, div_le_iff₀ (by norm_num)]
    linarith
  have hcoef0 : (0 : ℝ) ≤ ((sqrtCES.discount : ℝ)) * sqrtCES.oscGap / (9 / 10) := by
    rw [show ((sqrtCES.discount : ℝ)) = 1 / 8 from rfl]; positivity
  nlinarith [hcoef, hpow, hcoef0, hpow0]

/-! ### Why not `cesWitness`

`cesWitness` is the same CES curvature as `sqrtCES` with a much smaller cap, `1/10`, and it
cannot be calibrated: the saving bound is at best `β · oscGap`, which exceeds the cap outright.
Raising `θ` does not help, because `θ ≤ 1` only makes the coefficient larger, and the base
`maxIncome + (1 + r - θ) · assetCap` never falls below `maxIncome = 1`.

This is not a defect of the bound: it is the cap being small relative to income. It is also why
`nearLog` was built — the docstring of `IncomeFluctuationCarrollKimball` calls it a
recalibration, and this is what it is a recalibration FOR. -/

theorem cesWitness_oscGap_ge : (2 : ℝ) ≤ cesWitness.oscGap := by
  have h1 : (131 : ℝ) / 125 ≤ Real.sqrt (11 / 10) := le_sqrt_of_sq (by norm_num) (by norm_num)
  have h2 : Real.sqrt (1 / 5000) ≤ 3 / 200 := sqrt_le_of_sq (by norm_num) (by norm_num)
  simp only [IncomeFluctuation.oscGap, cesWitness_u, cesWitness_maxConsumption,
    cesWitness_minConsumption, cesWitness_discount, crraUtility_half]
  rw [le_div_iff₀ (by norm_num)]
  nlinarith [h1, h2]

/-- **`cesWitness` cannot satisfy the cap calibration, whatever `θ`.** -/
theorem cesWitness_not_calibrated {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ¬ (((cesWitness.discount : ℝ) * cesWitness.oscGap / θ)
        * (cesWitness.maxIncome + (1 + cesWitness.interest - θ) * (1 / 10))
            ^ ((1 : ℝ) / 2) < 1 / 10) := by
  have hosc := cesWitness_oscGap_ge
  have hbase : (1 : ℝ) ≤ cesWitness.maxIncome + (1 + cesWitness.interest - θ) * (1 / 10) := by
    simp only [cesWitness_maxIncome, cesWitness_interest]
    linarith
  have hpow : (1 : ℝ)
      ≤ (cesWitness.maxIncome + (1 + cesWitness.interest - θ) * (1 / 10)) ^ ((1 : ℝ) / 2) := by
    have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [Real.one_rpow] at this
  have hcoef : (1 : ℝ) / 8 ≤ ((cesWitness.discount : ℝ)) * cesWitness.oscGap / θ := by
    rw [cesWitness_discount, le_div_iff₀ hθ0]
    nlinarith [hosc, hθ1, hθ0]
  intro hlt
  nlinarith [hcoef, hpow, hlt]

end LeanEconomics
