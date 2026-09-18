/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.UniquenessClass
import LeanEconomics.Models.IncomeFluctuationPatience

/-!
# Patience, at a witness

`IncomeFluctuationPatience` proves that a more patient household saves more, and that a more
patient population therefore faces a lower equilibrium interest rate. Both were stated about
abstract economies. This file instantiates them.

## The family

`nearLogBeta β` is the `nearLog` calibration with the discount factor left free, subject only to
`β ≤ 1/8`. Every estimate `nearLog` needs is MONOTONE in `β` in the right direction — the
oscillation gap, the saving bound, the Lipschitz constant and the impatience condition all get
easier as `β` falls — so the whole `Calibrated` instance goes through for the family at once, and
`nearLogBeta (1/8)` is `nearLog` itself.

That is what makes the comparative static instantiable: two economies differing ONLY in the
discount factor, each with a unique stationary distribution at each rate and a policy monotone in
the rate, are exactly what `equilibriumRate_le_of_policy_le` asks for.

## What is concluded

At every rate in `[0, 1/200]` the more patient household saves at least as much
(`nearLogBeta_policy_le_of_morePatient`), and if each economy has an equilibrium rate in that
interval then the patient one's is the lower (`nearLogBeta_equilibriumRate_le`). No restriction on
relative risk aversion enters: raising `β` does not move the budget set.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction
open scoped NNReal

namespace LeanEconomics

open IncomeFluctuation

/-- **The `nearLog` calibration with the discount factor free.** Identical to `nearLog` in every
field but `discount`; `nearLogBeta (1/8) le_rfl = nearLog` definitionally. -/
noncomputable def nearLogBeta (β : ℝ≥0) (hβ : β ≤ 1 / 8) : IncomeFluctuation (Fin 2) 0 1 where
  income z := if z = 0 then 1 / 100 else 1
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := β
  u := crraUtility (15 / 16)
  minIncome := 1 / 100
  maxIncome := 1
  minIncome_pos := by norm_num
  minIncome_le z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  assetFloor_le_assetCap := by norm_num
  assetCap_nonneg := by norm_num
  minConsumption_pos := by norm_num
  minConsumption_le_floor := le_rfl
  discount_lt_one := lt_of_le_of_lt hβ (by norm_num)
  dom := Ici 0
  Ioi_subset_dom := Ioi_subset_Ici_self
  dom_subset_Ici := subset_rfl
  continuousOn_u_dom := continuousOn_crraUtility_Ici (by norm_num)
  monotoneOn_u_dom := monotoneOn_crraUtility_Ici (by norm_num)
  strictConcaveOn_u_dom := strictConcaveOn_crraUtility_Ici (by norm_num) (by norm_num)
  continuousOn_extendDom := continuousOn_extendDom_Ici (continuousOn_crraUtility_Ici (by norm_num))

variable {β : ℝ≥0} {hβ : β ≤ 1 / 8}

@[simp] theorem nearLogBeta_u : (nearLogBeta β hβ).u = crraUtility (15 / 16) := rfl
@[simp] theorem nearLogBeta_income_zero : (nearLogBeta β hβ).income 0 = 1 / 100 := rfl
@[simp] theorem nearLogBeta_interest : (nearLogBeta β hβ).interest = 0 := rfl
@[simp] theorem nearLogBeta_discount : ((nearLogBeta β hβ).discount : ℝ) = (β : ℝ) := rfl
@[simp] theorem nearLogBeta_minIncome : (nearLogBeta β hβ).minIncome = 1 / 100 := rfl
@[simp] theorem nearLogBeta_maxIncome : (nearLogBeta β hβ).maxIncome = 1 := rfl
@[simp] theorem nearLogBeta_minConsumption : (nearLogBeta β hβ).minConsumption = 1 / 100 := by
  norm_num [nearLogBeta]
@[simp] theorem nearLogBeta_transitionMatrix (z z' : Fin 2) :
    (nearLogBeta β hβ).transitionMatrix z z' = 1 / 2 := rfl

theorem nearLogBeta_bounded (β : ℝ≥0) (hβ : β ≤ 1 / 8) : (nearLogBeta β hβ).Bounded := rfl

/-- The family really does contain `nearLog`. -/
theorem nearLogBeta_eight : nearLogBeta (1 / 8) le_rfl = nearLog := rfl

/-- The discount factor as a real number, with the bound the estimates use. -/
theorem nearLogBeta_discount_le (hβ : β ≤ 1 / 8) : (β : ℝ) ≤ 1 / 8 := by
  exact_mod_cast hβ

/-! ### The estimates, uniformly in `β`

Each one is `nearLog`'s, with `β = 1/8` replaced by `β ≤ 1/8`. That the same constants survive is
not luck: the oscillation gap carries `1/(1-β)`, the saving bound and the corner condition carry
`β` itself, and all three are monotone the easy way. The slack constant `25/37` is attained
exactly at `β = 1/8`, so the family is as patient as these estimates allow. -/

theorem nearLogBeta_withRate_positiveConsumptionAll {r : ℝ} (hrr : (nearLogBeta β hβ).RateOK r) :
    ((nearLogBeta β hβ).withRate r hrr).PositiveConsumptionAll := by
  refine ((nearLogBeta β hβ).withRate r hrr).positiveConsumptionAll_of_marginalInada ?_
  rw [show ((nearLogBeta β hβ).withRate r hrr).dom = Ici 0 from nearLogBeta_bounded β hβ,
    show ((nearLogBeta β hβ).withRate r hrr).u = crraUtility (15 / 16) from rfl]
  exact marginalInadaOn_Ici_crraUtility (by norm_num) (by norm_num)

theorem nearLogBeta_oscGap_le_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : (nearLogBeta β hβ).RateOK r) :
    ((nearLogBeta β hβ).withRate r hrr).oscGap ≤ 27 / 5 := by
  have hβr : (β : ℝ) ≤ 1 / 8 := nearLogBeta_discount_le hβ
  have hβ0 : (0 : ℝ) ≤ (β : ℝ) := β.coe_nonneg
  have hmaxpos : (0 : ℝ) ≤ ((nearLogBeta β hβ).withRate r hrr).maxConsumption :=
    ((nearLogBeta β hβ).withRate r hrr).maxConsumption_pos.le
  have hmax : ((nearLogBeta β hβ).withRate r hrr).maxConsumption ≤ 401 / 200 := by
    simp only [IncomeFluctuation.maxConsumption, IncomeFluctuation.withRate_maxIncome,
      IncomeFluctuation.withRate_interest, nearLogBeta_maxIncome]
    linarith [hr.2]
  have hhi : ((nearLogBeta β hβ).withRate r hrr).maxConsumption ^ ((1 : ℝ) / 16)
      ≤ 10445 / 10000 := by
    refine rpow_le_of_pow_le (m := 1) (n := 16) (by norm_num) hmaxpos (by norm_num)
      (by norm_num) ?_
    simpa using le_trans hmax (by norm_num)
  have hlo : (7498 : ℝ) / 10000 ≤ (1 / 100 : ℝ) ^ ((1 : ℝ) / 16) :=
    le_rpow_of_pow_le (m := 1) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  simp only [IncomeFluctuation.oscGap, IncomeFluctuation.withRate_u,
    IncomeFluctuation.withRate_minConsumption, IncomeFluctuation.withRate_discount,
    nearLogBeta_u, nearLogBeta_minConsumption, nearLogBeta_discount,
    crraUtility_fifteen_sixteenths]
  rw [div_le_iff₀ (by linarith)]
  linarith [hhi, hlo]

/-- **The calibration inequality**, for any oscillation bound at most `27/5` and any `β ≤ 1/8`.
The coefficient `βG/θ` is at most `25/37`, with equality exactly at `β = 1/8`, `G = 27/5`. -/
theorem nearLogBeta_calibration {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : (nearLogBeta β hβ).RateOK r) {G : ℝ} (hG0 : 0 ≤ G) (hG : G ≤ 27 / 5) :
    ((((nearLogBeta β hβ).withRate r hrr).discount : ℝ) * G / (999 / 1000))
        * (((nearLogBeta β hβ).withRate r hrr).maxIncome
          + (1 + ((nearLogBeta β hβ).withRate r hrr).interest - 999 / 1000) * 1
          - (1 - 999 / 1000) * 0) ^ ((15 : ℝ) / 16)
      < 1 - 0 := by
  have hβr : (β : ℝ) ≤ 1 / 8 := nearLogBeta_discount_le hβ
  have hβ0 : (0 : ℝ) ≤ (β : ℝ) := β.coe_nonneg
  have hcoef : (((nearLogBeta β hβ).withRate r hrr).discount : ℝ) * G / (999 / 1000) ≤ 25 / 37 := by
    rw [show ((((nearLogBeta β hβ).withRate r hrr).discount : ℝ)) = (β : ℝ) from rfl,
      div_le_iff₀ (by norm_num)]
    nlinarith [mul_le_mul hβr hG hG0 (by norm_num : (0:ℝ) ≤ 1 / 8)]
  have hcoef0 : (0 : ℝ)
      ≤ (((nearLogBeta β hβ).withRate r hrr).discount : ℝ) * G / (999 / 1000) := by
    rw [show ((((nearLogBeta β hβ).withRate r hrr).discount : ℝ)) = (β : ℝ) from rfl]; positivity
  have hbase : ((nearLogBeta β hβ).withRate r hrr).maxIncome
      + (1 + ((nearLogBeta β hβ).withRate r hrr).interest - 999 / 1000) * 1 - (1 - 999 / 1000) * 0
      ≤ 503 / 500 := by
    simp only [IncomeFluctuation.withRate_maxIncome, IncomeFluctuation.withRate_interest,
      nearLogBeta_maxIncome]
    linarith [hr.2]
  have hbase0 : (0 : ℝ) ≤ ((nearLogBeta β hβ).withRate r hrr).maxIncome
      + (1 + ((nearLogBeta β hβ).withRate r hrr).interest - 999 / 1000) * 1
      - (1 - 999 / 1000) * 0 := by
    simp only [IncomeFluctuation.withRate_maxIncome, IncomeFluctuation.withRate_interest,
      nearLogBeta_maxIncome]
    linarith [hr.1]
  have hpow : (((nearLogBeta β hβ).withRate r hrr).maxIncome
      + (1 + ((nearLogBeta β hβ).withRate r hrr).interest - 999 / 1000) * 1
      - (1 - 999 / 1000) * 0) ^ ((15 : ℝ) / 16) ≤ 503 / 500 := by
    refine le_trans (Real.rpow_le_rpow hbase0 hbase (by norm_num)) ?_
    exact rpow_le_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hpow0 : (0 : ℝ) ≤ (((nearLogBeta β hβ).withRate r hrr).maxIncome
      + (1 + ((nearLogBeta β hβ).withRate r hrr).interest - 999 / 1000) * 1
      - (1 - 999 / 1000) * 0) ^ ((15 : ℝ) / 16) := Real.rpow_nonneg hbase0 _
  nlinarith [hcoef, hpow, hcoef0, hpow0]

theorem nearLogBeta_policyOf_lt_cap {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : (nearLogBeta β hβ).RateOK r) {v : (ℝ × Fin 2) →ᵇ ℝ} (hv : ConcaveSlices (0 : ℝ) 1 v)
    (hosc : ((nearLogBeta β hβ).withRate r hrr).OscOn v (27 / 5)) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (z : Fin 2) : ((nearLogBeta β hβ).withRate r hrr).policyOf v (a, z) < 1 :=
  ((nearLogBeta β hβ).withRate r hrr).crra_policyOf_lt_assetCap (γ := 15 / 16) (θ := 999 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl
    (nearLogBeta_withRate_positiveConsumptionAll hrr) hv (by norm_num) hosc
    (nearLogBeta_calibration hr hrr (by norm_num) le_rfl) ha z

theorem nearLogBeta_corner_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : (nearLogBeta β hβ).RateOK r) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (1 / 50)) :
    ((nearLogBeta β hβ).withRate r hrr).policy (a, 0) = 0 := by
  have hβr : (β : ℝ) ≤ 1 / 8 := nearLogBeta_discount_le hβ
  have hβ0 : (0 : ℝ) ≤ (β : ℝ) := β.coe_nonneg
  have hrhi : (nearLogBeta β hβ).RateOK (1 / 200 : ℝ) :=
    IncomeFluctuation.rateOK_of_floor_zero (by norm_num)
  have hmem : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
  refine (nearLogBeta β hβ).crra_policy_eq_zero_uniform (γ := 15 / 16) (by norm_num) (by norm_num)
    rfl rfl hrr hrhi hr.2 (by rw [nearLogBeta_discount]; nlinarith) hmem 0 ?_
  have hlippos : (0 : ℝ) ≤ ((nearLogBeta β hβ).withRate (1 / 200) hrhi).crraLipschitz (15 / 16) :=
    ((nearLogBeta β hβ).withRate (1 / 200) hrhi).crraLipschitz_nonneg (by norm_num) (by norm_num)
      (by rw [show ((((nearLogBeta β hβ).withRate (1 / 200) hrhi).discount : ℝ)) = (β : ℝ) from rfl,
        show (((nearLogBeta β hβ).withRate (1 / 200) hrhi).interest) = 1 / 200 from rfl]; nlinarith)
  have hlip : ((nearLogBeta β hβ).withRate (1 / 200) hrhi).crraLipschitz (15 / 16) ≤ 128 := by
    simp only [IncomeFluctuation.crraLipschitz, IncomeFluctuation.withRate_minConsumption,
      IncomeFluctuation.withRate_interest, IncomeFluctuation.withRate_discount,
      nearLogBeta_minConsumption, nearLogBeta_discount]
    rw [div_le_iff₀ (by nlinarith)]
    linarith [nearLog_crraSlopeBound_le]
  have hres : ((nearLogBeta β hβ).withRate (1 / 200) hrhi).resources (a, 0)
      = 1 / 100 + (1 + 1 / 200) * a := by
    simp only [IncomeFluctuation.resources, IncomeFluctuation.withRate_income,
      IncomeFluctuation.withRate_interest, nearLogBeta_income_zero, max_eq_right ha.1]
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
    show ((((nearLogBeta β hβ).withRate (1 / 200) hrhi).discount : ℝ)) = (β : ℝ) from rfl]
  nlinarith [hlip, hge, hlippos]

/-- **`1 - κ ≤ 111/1000` for the whole family**, as for `nearLog`: the patience factor is
increasing in `β`, so the bound at `β = 1/8` serves every member. -/
theorem nearLogBeta_one_sub_minMPC_le {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : (nearLogBeta β hβ).RateOK r) :
    1 - ((nearLogBeta β hβ).withRate r hrr).minMPC (15 / 16) ≤ 111 / 1000 := by
  have hβr : (β : ℝ) ≤ 1 / 8 := nearLogBeta_discount_le hβ
  have hβ0 : (0 : ℝ) ≤ (β : ℝ) := β.coe_nonneg
  have hR1 : (1 : ℝ) ≤ 1 + r := by linarith [hr.1]
  have hd : (((nearLogBeta β hβ).withRate r hrr).discount : ℝ) = (β : ℝ) := rfl
  have hint : ((nearLogBeta β hβ).withRate r hrr).interest = r := rfl
  have hexp : (1 : ℝ) / (15 / 16) = 16 / 15 := by norm_num
  simp only [IncomeFluctuation.minMPC, hd, hint, sub_sub_cancel, hexp]
  have hbase : (0 : ℝ) ≤ (β : ℝ) * (1 + r) := by positivity
  have hle : (β : ℝ) * (1 + r) ≤ 201 / 1600 := by nlinarith [hr.2]
  have hmono : ((β : ℝ) * (1 + r)) ^ (16 / 15 : ℝ) ≤ (201 / 1600 : ℝ) ^ (16 / 15 : ℝ) :=
    Real.rpow_le_rpow hbase hle (by norm_num)
  have hnum : (201 / 1600 : ℝ) ^ (16 / 15 : ℝ) ≤ 111 / 1000 :=
    rpow_le_of_pow_le (m := 16) (n := 15) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) ≤ ((β : ℝ) * (1 + r)) ^ (16 / 15 : ℝ) := Real.rpow_nonneg hbase _
  rw [div_le_iff₀ (by linarith)]
  nlinarith [hmono, hnum, hpos, hR1]

/-- **The whole family is calibrated**, at every `0 < β ≤ 1/8`. -/
theorem nearLogBeta_calibrated (hβpos : 0 < β) :
    (nearLogBeta β hβ).Calibrated (15 / 16) 0 (27 / 5) (1 / 50) 0 0 (1 / 200) where
  gamma_pos := by norm_num
  gamma_le_one := by norm_num
  eta_nonneg := le_rfl
  utility := by rw [haraUtility_zero_shift]; rfl
  discount_pos := by rw [nearLogBeta_discount]; exact_mod_cast hβpos
  positive := fun r _ hrr v hv _ z a ha =>
    nearLogBeta_withRate_positiveConsumptionAll hrr v hv z a ha
  rlo_nonneg := le_rfl
  rate_le := by norm_num
  income_min := fun z => by fin_cases z <;> norm_num [nearLogBeta]
  reach := fun z => by rw [nearLogBeta_transitionMatrix]; norm_num
  impatient := fun r hr => by
    rw [nearLogBeta_discount]; nlinarith [nearLogBeta_discount_le hβ, β.coe_nonneg, hr.2]
  osc_nonneg := by norm_num
  osc_le := fun r hr hrr => by
    rw [IncomeFluctuation.oscSpread_eq_oscGap]
    exact nearLogBeta_oscGap_le_uniform hr hrr
  slack := fun r hr hrr v hv hosc a ha z => nearLogBeta_policyOf_lt_cap hr hrr hv hosc ha z
  a₀_pos := by norm_num
  a₀_le := by norm_num
  corner := fun r hr hrr a ha => nearLogBeta_corner_uniform hr hrr ha
  decline := fun r hr hrr => by
    have hone := nearLogBeta_one_sub_minMPC_le (hβ := hβ) hr hrr
    have hle1 : ((nearLogBeta β hβ).withRate r hrr).minMPC (15 / 16) ≤ 1 :=
      IncomeFluctuation.minMPC_le_one (γ := 15 / 16) (by norm_num)
        (by
          rw [show (((nearLogBeta β hβ).withRate r hrr).discount : ℝ) = (β : ℝ) from rfl]
          exact_mod_cast hβpos)
    rw [show (nearLogBeta β hβ).income 0 = 1 / 100 from rfl]
    nlinarith [hone, hle1, hr.1, hr.2]

/-! ### The comparative static

Two members of the family differ only in `β`, which is exactly `MorePatientThan`. Everything else
is `rfl`. -/

theorem nearLogBeta_morePatient {β₁ β₂ : ℝ≥0} {h₁ : β₁ ≤ 1 / 8} {h₂ : β₂ ≤ 1 / 8} (hle : β₁ ≤ β₂)
    {r : ℝ} (hr₁ : (nearLogBeta β₁ h₁).RateOK r) (hr₂ : (nearLogBeta β₂ h₂).RateOK r) :
    ((nearLogBeta β₁ h₁).withRate r hr₁).MorePatientThan ((nearLogBeta β₂ h₂).withRate r hr₂) where
  discount_le := by exact_mod_cast hle
  same_income := fun _ => rfl
  same_maxIncome := rfl
  same_minIncome := rfl
  same_interest := rfl
  same_transition := fun _ _ => rfl
  same_u := rfl
  same_dom := rfl

/-- **A more patient household saves more**, at this calibration, at every rate in `[0, 1/200]`,
every asset level and every income state. Relative risk aversion is `15/16`, but nothing here
uses that: `policy_le_of_morePatient_crra` holds at every `γ > 0`, because raising `β` does not
move the budget set. -/
theorem nearLogBeta_policy_le_of_morePatient {β₁ β₂ : ℝ≥0} {h₁ : β₁ ≤ 1 / 8} {h₂ : β₂ ≤ 1 / 8}
    (hp₁ : 0 < β₁) (hp₂ : 0 < β₂) (hle : β₁ ≤ β₂) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hr₁ : (nearLogBeta β₁ h₁).RateOK r) (hr₂ : (nearLogBeta β₂ h₂).RateOK r)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 2) :
    ((nearLogBeta β₁ h₁).withRate r hr₁).policy (a, z)
      ≤ ((nearLogBeta β₂ h₂).withRate r hr₂).policy (a, z) :=
  IncomeFluctuation.policy_le_of_morePatient_crra (γ := 15 / 16) (by norm_num) rfl
    (nearLogBeta_morePatient hle hr₁ hr₂)
    (nearLogBeta_withRate_positiveConsumptionAll hr₁)
    (nearLogBeta_withRate_positiveConsumptionAll hr₂)
    (fun n x hx z' =>
      (nearLogBeta_calibrated (hβ := h₁) hp₁).policyOf_iterate_lt_cap hr hr₁ hr hr₁ n hx z')
    (fun n x hx z' =>
      (nearLogBeta_calibrated (hβ := h₂) hp₂).policyOf_iterate_lt_cap hr hr₂ hr hr₂ n hx z')
    ha z

/-! ### The equilibrium rate

Uniqueness of the stationary distribution at each rate is what makes "the" equilibrium rate a
number, and `Calibrated` supplies it for every member of the family. With that, the two schedules
are ordered by `nearLogBeta_policy_le_of_morePatient`, the patient one's lying above, and demand is
strictly decreasing — so the patient economy clears at the lower rate. -/

/-- **A more patient population faces a lower equilibrium interest rate**, at this calibration.
`r₁` clears the market for the impatient economy and `r₂` for the patient one; the conclusion is
`r₂ ≤ r₁`.

Nothing is assumed about the two rates beyond membership in `[0, 1/200]` and market clearing:
existence comes from `nearLog_exists_equilibrium` and its family analogues, and uniqueness from
`Calibrated.equilibriumRate_unique`, so this is a statement about the equilibrium rates
themselves, not about a selection. -/
theorem nearLogBeta_equilibriumRate_le {β₁ β₂ : ℝ≥0} {h₁ : β₁ ≤ 1 / 8} {h₂ : β₂ ≤ 1 / 8}
    (hp₁ : 0 < β₁) (hp₂ : 0 < β₂) (hle : β₁ ≤ β₂) {A δ : ℝ} (hA : A ≠ 0) (hδ : 0 < δ)
    (μ₀ : ProbabilityMeasure (nearLogBeta β₁ h₁).State)
    {r₁ r₂ : ℝ} (hm₁ : r₁ ∈ Icc (0 : ℝ) (1 / 200)) (hm₂ : r₂ ∈ Icc (0 : ℝ) (1 / 200))
    (he₁ : (nearLogBeta β₁ h₁).aggregateCapital
        ((nearLogBeta_calibrated (hβ := h₁) hp₁).stationary r₁) = capitalDemand A δ r₁)
    (he₂ : (nearLogBeta β₁ h₁).aggregateCapital
        ((nearLogBeta_calibrated (hβ := h₂) hp₂).stationary r₂) = capitalDemand A δ r₂) :
    r₂ ≤ r₁ := by
  have c₁ := nearLogBeta_calibrated (hβ := h₁) hp₁
  have c₂ := nearLogBeta_calibrated (hβ := h₂) hp₂
  refine IncomeFluctuation.equilibriumRate_le_of_policy_le (P := nearLogBeta β₁ h₁)
    hA (by linarith) c₁.family c₂.family (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) ?_ ?_
    μ₀ c₁.stationary c₂.stationary (c₁.tendsto_stationary μ₀) (c₂.tendsto_stationary μ₀)
    hm₁ hm₂ he₁ he₂
  · intro r hr r' hr' hle' s hs
    rw [c₁.family_eq hr, c₁.family_eq hr']
    exact c₁.policy_mono hr hr' hle' hs s.2
  · intro r hr s hs
    rw [c₁.family_eq hr, c₂.family_eq hr]
    exact nearLogBeta_policy_le_of_morePatient hp₁ hp₂ hle hr (c₁.rateOK hr) (c₂.rateOK hr) hs s.2

/-! ### Two concrete economies

`nearLog` has `β = 1/8`. `nearLogImpatient` halves it and changes nothing else, so the pair is a
literal instance of the comparative static: same income process, same interest rate, same
utility, same asset cap. -/

theorem nnreal_inv16_le_inv8 : (1 / 16 : ℝ≥0) ≤ 1 / 8 := by
  rw [← NNReal.coe_le_coe]; push_cast; norm_num

theorem nnreal_inv16_pos : (0 : ℝ≥0) < 1 / 16 := by
  rw [← NNReal.coe_pos]; push_cast; norm_num

theorem nnreal_inv8_pos : (0 : ℝ≥0) < 1 / 8 := by
  rw [← NNReal.coe_pos]; push_cast; norm_num

/-- `nearLog` with the discount factor halved. -/
noncomputable def nearLogImpatient : IncomeFluctuation (Fin 2) 0 1 :=
  nearLogBeta (1 / 16) nnreal_inv16_le_inv8

/-- **The impatient twin saves less**, at every rate in `[0, 1/200]`, every asset level and every
income state. -/
theorem nearLogImpatient_policy_le {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr₁ : nearLogImpatient.RateOK r) (hrr₂ : nearLog.RateOK r)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 2) :
    (nearLogImpatient.withRate r hrr₁).policy (a, z) ≤ (nearLog.withRate r hrr₂).policy (a, z) :=
  nearLogBeta_policy_le_of_morePatient (h₁ := nnreal_inv16_le_inv8) (h₂ := le_rfl)
    nnreal_inv16_pos nnreal_inv8_pos nnreal_inv16_le_inv8 hr hrr₁ hrr₂ ha z

/-- **The impatient twin's equilibrium rate is the higher one.** Both economies have a unique
stationary distribution at each rate in `[0, 1/200]` and a capital supply monotone in the rate;
if `r₁` clears the market for `nearLogImpatient` and `r₂` for `nearLog`, then `r₂ ≤ r₁`.

This is the first comparative static in the development about an EQUILIBRIUM rather than a
policy. -/
theorem nearLogImpatient_equilibriumRate_le {A δ : ℝ} (hA : A ≠ 0) (hδ : 0 < δ)
    (μ₀ : ProbabilityMeasure nearLogImpatient.State)
    {r₁ r₂ : ℝ} (hm₁ : r₁ ∈ Icc (0 : ℝ) (1 / 200)) (hm₂ : r₂ ∈ Icc (0 : ℝ) (1 / 200))
    (he₁ : nearLogImpatient.aggregateCapital
        ((nearLogBeta_calibrated (β := 1 / 16) (hβ := nnreal_inv16_le_inv8)
          nnreal_inv16_pos).stationary r₁)
      = capitalDemand A δ r₁)
    (he₂ : nearLogImpatient.aggregateCapital
        ((nearLogBeta_calibrated (β := 1 / 8) (hβ := le_rfl) nnreal_inv8_pos).stationary r₂)
      = capitalDemand A δ r₂) : r₂ ≤ r₁ :=
  nearLogBeta_equilibriumRate_le (h₁ := nnreal_inv16_le_inv8) (h₂ := le_rfl)
    nnreal_inv16_pos nnreal_inv8_pos nnreal_inv16_le_inv8 hA hδ μ₀ hm₁ hm₂ he₁ he₂

end LeanEconomics
