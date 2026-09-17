/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.UniquenessClass
import LeanEconomics.Models.CESConcaveConsumption

/-!
# A Stone–Geary economy with a unique equilibrium interest rate

The uniqueness chain has run at one calibration, `nearLog`, which is CRRA. This file runs it at a
STONE–GEARY economy — CRRA over consumption above a subsistence level —

  `u c = crraUtility (1/2) (1/10 + c) = 2 √(1/10 + c)`,

income in `{2, 21/10}`, borrowing limit `0`, asset cap `19/10`, discount `21/50`, and interest
rates in `[0, 1/100]`. It is the first non-CRRA economy here with a unique Aiyagari equilibrium
rate.

## What the calibration has to buy

Two things fight each other, and the parameters are chosen to satisfy both.

* **The cap has to be slack**, which bounds saving from above. The level-based bound is far too
  crude for that at any interesting discount factor; `hara_policyOf_lt_assetCap` — the
  proportional bound — is what makes `β = 21/50` admissible.
* **Consumption has to be positive**, which a subsistence level does not give for free, since
  marginal utility at zero is finite (`(1/10) ^ (-1/2)`, about three). Here it comes from the
  budget: the asset cap `19/10` is worth less than one period's minimum consumption `2`, so no
  feasible saving can exhaust resources (`positiveConsumptionAll_of_rich`).

The borrowing constraint binds below `a₀ = 1/20` and the corner test fails well before the cap,
so the household is not trivially hand-to-mouth — `βL = 63/100` against a marginal value of
about `0.68` at `a₀`, and about `0.50` at the cap.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

open IncomeFluctuation

/-! ### Shifted CRRA on the non-negative half-line -/

theorem continuousOn_haraUtility_Ici {γ η : ℝ} (hγ1 : γ < 1) (hη : 0 ≤ η) :
    ContinuousOn (haraUtility γ η) (Ici 0) := by
  refine (continuousOn_crraUtility_Ici hγ1).comp (Continuous.continuousOn (by fun_prop)) ?_
  intro c hc
  simp only [mem_Ici] at *
  linarith

theorem monotoneOn_haraUtility_Ici {γ η : ℝ} (hγ1 : γ < 1) (hη : 0 ≤ η) :
    MonotoneOn (haraUtility γ η) (Ici 0) := fun x hx y hy hxy =>
  monotoneOn_crraUtility_Ici hγ1 (by simp only [mem_Ici] at *; linarith)
    (by simp only [mem_Ici] at *; linarith) (by linarith)

theorem strictConcaveOn_haraUtility_Ici {γ η : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 ≤ η) :
    StrictConcaveOn ℝ (Ici 0) (haraUtility γ η) := by
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have h := (strictConcaveOn_crraUtility_Ici hγ0 hγ1).2 (x := η + x) (y := η + y)
    (by simp only [mem_Ici] at *; linarith) (by simp only [mem_Ici] at *; linarith)
    (by intro hcon; exact hxy (by linarith)) ha hb hab
  simp only [haraUtility, smul_eq_mul] at h ⊢
  have he : a * (η + x) + b * (η + y) = η + (a * x + b * y) := by nlinarith [hab]
  rwa [he] at h

/-! ### The economy -/

/-- **A Stone–Geary economy.** -/
noncomputable def stoneGeary : IncomeFluctuation (Fin 2) 0 (19 / 10) where
  income z := if z = 0 then 2 else 21 / 10
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 21 / 50
  u := haraUtility (1 / 2) (1 / 10)
  minIncome := 2
  maxIncome := 21 / 10
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
  discount_lt_one := by norm_num
  dom := Ici 0
  Ioi_subset_dom := Ioi_subset_Ici_self
  dom_subset_Ici := subset_rfl
  continuousOn_u_dom := continuousOn_haraUtility_Ici (by norm_num) (by norm_num)
  monotoneOn_u_dom := monotoneOn_haraUtility_Ici (by norm_num) (by norm_num)
  strictConcaveOn_u_dom := strictConcaveOn_haraUtility_Ici (by norm_num) (by norm_num)
    (by norm_num)
  continuousOn_extendDom :=
    continuousOn_extendDom_Ici (continuousOn_haraUtility_Ici (by norm_num) (by norm_num))

@[simp] theorem stoneGeary_u : stoneGeary.u = haraUtility (1 / 2) (1 / 10) := rfl
@[simp] theorem stoneGeary_discount : (stoneGeary.discount : ℝ) = 21 / 50 := rfl
@[simp] theorem stoneGeary_interest : stoneGeary.interest = 0 := rfl
@[simp] theorem stoneGeary_maxIncome : stoneGeary.maxIncome = 21 / 10 := rfl
@[simp] theorem stoneGeary_minConsumption : stoneGeary.minConsumption = 2 := by
  norm_num [stoneGeary]

theorem stoneGeary_bounded : stoneGeary.Bounded := rfl

/-- Utility in closed form. -/
theorem stoneGeary_u_eq (c : ℝ) : stoneGeary.u c = 2 * Real.sqrt (1 / 10 + c) := by
  rw [stoneGeary_u]
  simp only [haraUtility]
  exact crraUtility_half _

/-- It is not CRRA: every CRRA with `γ < 1` vanishes at zero consumption, and this does not. -/
theorem stoneGeary_ne_crra {γ : ℝ} (hγ : γ < 1) : stoneGeary.u ≠ crraUtility γ := by
  intro h
  have hz := congrFun h 0
  rw [stoneGeary_u_eq, crraUtility_zero hγ] at hz
  have h10 : (0 : ℝ) < Real.sqrt (1 / 10 + 0) := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-! ### The calibration

Every bound below is crude and has room: the arithmetic is two square roots and some rationals.
-/

theorem stoneGeary_maxConsumption_le {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 100))
    (hrr : stoneGeary.RateOK r) :
    (stoneGeary.withRate r hrr).maxConsumption ≤ 4019 / 1000 := by
  simp only [IncomeFluctuation.maxConsumption, IncomeFluctuation.withRate_maxIncome,
    IncomeFluctuation.withRate_interest, stoneGeary_maxIncome]
  nlinarith [hr.1, hr.2]

theorem stoneGeary_maxConsumption_nonneg {r : ℝ} (hrr : stoneGeary.RateOK r) :
    (0 : ℝ) ≤ (stoneGeary.withRate r hrr).maxConsumption :=
  (stoneGeary.withRate r hrr).maxConsumption_pos.le

/-- `u` at the top of the consumption range. -/
theorem stoneGeary_u_maxConsumption_le {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 100))
    (hrr : stoneGeary.RateOK r) :
    (stoneGeary.withRate r hrr).u (stoneGeary.withRate r hrr).maxConsumption ≤ 203 / 50 := by
  have hu : (stoneGeary.withRate r hrr).u = stoneGeary.u := rfl
  have hle := stoneGeary_maxConsumption_le hr hrr
  have h0 := stoneGeary_maxConsumption_nonneg hrr
  rw [hu, stoneGeary_u_eq]
  have hs : Real.sqrt (1 / 10 + (stoneGeary.withRate r hrr).maxConsumption)
      ≤ Real.sqrt (4119 / 1000) := Real.sqrt_le_sqrt (by linarith)
  have hb : Real.sqrt (4119 / 1000 : ℝ) ≤ 203 / 100 := sqrt_le_of_sq (by norm_num) (by norm_num)
  linarith

/-- `u` at the bottom. -/
theorem stoneGeary_u_minConsumption_ge {r : ℝ} (hrr : stoneGeary.RateOK r) :
    (1449 : ℝ) / 500 ≤ (stoneGeary.withRate r hrr).u
      (stoneGeary.withRate r hrr).minConsumption := by
  have hu : (stoneGeary.withRate r hrr).u = stoneGeary.u := rfl
  have hm : (stoneGeary.withRate r hrr).minConsumption = 2 := stoneGeary_minConsumption
  rw [hu, hm, stoneGeary_u_eq]
  have hb : (1449 : ℝ) / 1000 ≤ Real.sqrt (1 / 10 + 2) :=
    le_sqrt_of_sq (by norm_num) (by norm_num)
  linarith

theorem stoneGeary_oscSpread_le {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 100))
    (hrr : stoneGeary.RateOK r) : (stoneGeary.withRate r hrr).oscSpread ≤ 11 / 5 := by
  have hmax := stoneGeary_u_maxConsumption_le hr hrr
  have hmin := stoneGeary_u_minConsumption_ge hrr
  have hβ : ((stoneGeary.withRate r hrr).discount : ℝ) = 21 / 50 := rfl
  simp only [IncomeFluctuation.oscSpread, hβ]
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- **Positive consumption, from the budget.** The asset cap is worth less than one period's
minimum consumption, so no feasible saving can exhaust resources. -/
theorem stoneGeary_positiveConsumptionAll {r : ℝ} (hrr : stoneGeary.RateOK r) :
    (stoneGeary.withRate r hrr).PositiveConsumptionAll := by
  refine (stoneGeary.withRate r hrr).positiveConsumptionAll_of_rich ?_
  rw [show (stoneGeary.withRate r hrr).minConsumption = 2 from stoneGeary_minConsumption]
  norm_num

/-- **The cap is slack**, against every continuation whose oscillation is at most `11/5`. -/
theorem stoneGeary_slack {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 100)) (hrr : stoneGeary.RateOK r)
    {v : (ℝ × Fin 2) →ᵇ ℝ} (hv : ConcaveSlices (0 : ℝ) (19 / 10) v)
    (hosc : (stoneGeary.withRate r hrr).OscOn v (11 / 5)) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) (19 / 10)) (z : Fin 2) :
    (stoneGeary.withRate r hrr).policyOf v (a, z) < 19 / 10 := by
  refine (stoneGeary.withRate r hrr).hara_policyOf_lt_assetCap (γ := 1 / 2) (η := 1 / 10)
    (θ := 9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl
    (stoneGeary_positiveConsumptionAll hrr) hv (by norm_num) hosc ?_ ha z
  -- the calibration inequality
  have hβ : ((stoneGeary.withRate r hrr).discount : ℝ) = 21 / 50 := rfl
  have hinc : (stoneGeary.withRate r hrr).maxIncome = 21 / 10 := rfl
  have hint : (stoneGeary.withRate r hrr).interest = r := rfl
  rw [hβ, hinc, hint]
  have hbase : (1 : ℝ) / 10 + 21 / 10 + (1 + r - 9 / 10) * (19 / 10) - (1 - 9 / 10) * 0
      ≤ 2409 / 1000 := by nlinarith [hr.1, hr.2]
  have hbase0 : (0 : ℝ) ≤ 1 / 10 + 21 / 10 + (1 + r - 9 / 10) * (19 / 10) - (1 - 9 / 10) * 0 := by
    nlinarith [hr.1]
  have hpow : ((1 : ℝ) / 10 + 21 / 10 + (1 + r - 9 / 10) * (19 / 10) - (1 - 9 / 10) * 0)
      ^ ((1 : ℝ) / 2) ≤ 39 / 25 := by
    refine le_trans (Real.rpow_le_rpow hbase0 hbase (by norm_num)) ?_
    rw [show ((1 : ℝ) / 2) = 1 / 2 from rfl, ← Real.sqrt_eq_rpow]
    exact sqrt_le_of_sq (by norm_num) (by norm_num)
  have hpow0 : (0 : ℝ) ≤ ((1 : ℝ) / 10 + 21 / 10 + (1 + r - 9 / 10) * (19 / 10)
      - (1 - 9 / 10) * 0) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hbase0 _
  nlinarith [hpow, hpow0]

/-! ### The corner

Below `a₀ = 1/20` the household saves nothing. The test is `β L < m`: the discounted slope of
the value function against the marginal value of consumption, and here it is `63/100` against
about `68/100`. At the cap the same test reads `63/100` against about `50/100` and FAILS, so the
household is not hand-to-mouth throughout — the corner region is genuinely a region. -/

theorem stoneGeary_slopeBoundU_le {r : ℝ} (hrr : stoneGeary.RateOK r) :
    (stoneGeary.withRate r hrr).slopeBoundU ≤ 41 / 50 := by
  have hu : (stoneGeary.withRate r hrr).u = stoneGeary.u := rfl
  have hm : (stoneGeary.withRate r hrr).minConsumption = 2 := stoneGeary_minConsumption
  simp only [IncomeFluctuation.slopeBoundU, slopeBound, hu, hm]
  rw [stoneGeary_u_eq, stoneGeary_u_eq]
  have h1 : Real.sqrt ((1 : ℝ) / 10 + 2) ≤ 145 / 100 :=
    sqrt_le_of_sq (by norm_num) (by norm_num)
  have h2 : (104 : ℝ) / 100 ≤ Real.sqrt ((1 : ℝ) / 10 + 2 / 2) :=
    le_sqrt_of_sq (by norm_num) (by norm_num)
  rw [div_le_iff₀ (by norm_num)]
  linarith

theorem stoneGeary_lipschitz {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 100))
    (hrr : stoneGeary.RateOK r) :
    ∀ z : Fin 2, ∀ x ∈ Icc (0 : ℝ) (19 / 10), ∀ y ∈ Icc (0 : ℝ) (19 / 10),
      |(stoneGeary.withRate r hrr).toExtended.valueFunction (x, z)
        - (stoneGeary.withRate r hrr).toExtended.valueFunction (y, z)| ≤ (3 / 2) * |x - y| := by
  refine (stoneGeary.withRate r hrr).valueFunction_lipschitz (by norm_num) ?_
  have hslope := stoneGeary_slopeBoundU_le hrr
  have hslope0 : (0 : ℝ) ≤ (stoneGeary.withRate r hrr).slopeBoundU :=
    (stoneGeary.withRate r hrr).slopeBoundU_nonneg
  have hβ : ((stoneGeary.withRate r hrr).discount : ℝ) = 21 / 50 := rfl
  have hint : (stoneGeary.withRate r hrr).interest = r := rfl
  rw [hβ, hint]
  nlinarith [hr.1, hr.2, hslope, hslope0]

/-- **The corner condition.** -/
theorem stoneGeary_corner {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 100)) (hrr : stoneGeary.RateOK r)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (1 / 20)) :
    (stoneGeary.withRate r hrr).policy (a, 0) = 0 := by
  have hres : (stoneGeary.withRate r hrr).resources (a, 0) ≤ 4101 / 2000 := by
    simp only [IncomeFluctuation.resources, IncomeFluctuation.withRate_income,
      IncomeFluctuation.withRate_interest, max_eq_right ha.1]
    have hinc : stoneGeary.income (0 : Fin 2) = 2 := rfl
    rw [hinc]
    nlinarith [ha.1, ha.2, hr.1, hr.2]
  refine (stoneGeary.withRate r hrr).policy_eq_zero_of_corner_at (L := 3 / 2) (m := 17 / 25)
    (stoneGeary_lipschitz hr hrr) (s := (a, 0)) ⟨ha.1, by linarith [ha.2]⟩ ?_ ?_
  · -- the marginal bound over the consumption range available at `(a, 0)`
    intro c d hd hdc hc
    have hd0 : (0 : ℝ) ≤ d := (stoneGeary.withRate r hrr).nonneg_of_mem_dom hd
    have hcR : c ≤ (stoneGeary.withRate r hrr).resources (a, 0) - 0 := hc
    have hbound := haraUtility_marginal_bound (γ := 1 / 2) (η := 1 / 10)
      (R := (stoneGeary.withRate r hrr).resources (a, 0) - 0) (by norm_num) (by norm_num)
      (by norm_num) hd0 hdc hcR
    have hu : (stoneGeary.withRate r hrr).u = haraUtility (1 / 2) (1 / 10) := rfl
    rw [hu]
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (by linarith)) hbound
    -- `17/25 ≤ (1/10 + R) ^ (-(1/2))`
    have hR0 : (0 : ℝ) ≤ 1 / 10 + ((stoneGeary.withRate r hrr).resources (a, 0) - 0) := by
      have := (stoneGeary.withRate r hrr).assetFloor_lt_resources (a, 0)
      linarith
    rw [show -((1 : ℝ) / 2) = -(1 / 2) from rfl, rpow_neg_half hR0]
    have hsq : Real.sqrt (1 / 10 + ((stoneGeary.withRate r hrr).resources (a, 0) - 0))
        ≤ 25 / 17 := by
      refine sqrt_le_of_sq (by norm_num) ?_
      linarith [hres]
    have hpos : (0 : ℝ) < Real.sqrt (1 / 10
        + ((stoneGeary.withRate r hrr).resources (a, 0) - 0)) := by
      refine Real.sqrt_pos.mpr ?_
      have := (stoneGeary.withRate r hrr).assetFloor_lt_resources (a, 0)
      linarith
    rw [le_inv_comm₀ (by norm_num) hpos]
    linarith
  · -- `β L < m`
    have hβ : ((stoneGeary.withRate r hrr).discount : ℝ) = 21 / 50 := rfl
    rw [hβ]
    norm_num

/-! ### The economy is calibrated, and its equilibrium rate is unique -/

theorem stoneGeary_calibrated :
    stoneGeary.Calibrated (1 / 2) (1 / 10) (11 / 5) (1 / 20) 0 0 (1 / 100) where
  gamma_pos := by norm_num
  gamma_lt_one := by norm_num
  eta_nonneg := by norm_num
  utility := rfl
  discount_pos := by rw [stoneGeary_discount]; norm_num
  positive := fun r _ hrr => stoneGeary_positiveConsumptionAll hrr
  rlo_nonneg := le_rfl
  rate_le := by norm_num
  iid := fun _ _ _ => rfl
  income_min := fun z => by fin_cases z <;> norm_num [stoneGeary]
  reach := fun z => by
    rw [show stoneGeary.transitionMatrix z 0 = 1 / 2 from rfl]
    norm_num
  impatient := fun r hr => by rw [stoneGeary_discount]; nlinarith [hr.1, hr.2]
  osc_nonneg := by norm_num
  osc_le := fun r hr hrr => stoneGeary_oscSpread_le hr hrr
  slack := fun r hr hrr v hv hosc a ha z => stoneGeary_slack hr hrr hv hosc ha z
  a₀_pos := by norm_num
  a₀_le := by norm_num
  corner := fun r hr hrr a ha => stoneGeary_corner hr hrr ha

/-- **Carroll and Kimball for this economy**, at every rate in the interval. -/
theorem stoneGeary_concaveOn_consumptionFn {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 100))
    (hrr : stoneGeary.RateOK r) (z : Fin 2) :
    ConcaveOn ℝ (Icc (0 : ℝ) (19 / 10)) ((stoneGeary.withRate r hrr).consumptionFn z) :=
  stoneGeary_calibrated.concaveOn_consumptionFn hr hrr z

/-- **Light's Theorem 1 for this economy**: a higher rate means at least as much saving. -/
theorem stoneGeary_policy_mono {r r' : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 100))
    (hr' : r' ∈ Icc (0 : ℝ) (1 / 100)) (hle : r ≤ r') {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (19 / 10))
    (z : Fin 2) :
    (stoneGeary.withRate r (stoneGeary_calibrated.rateOK hr)).policy (a, z)
      ≤ (stoneGeary.withRate r' (stoneGeary_calibrated.rateOK hr')).policy (a, z) :=
  stoneGeary_calibrated.policy_mono hr hr' hle ha z

/-- **Capital supply is a monotone function of the rate.** -/
theorem stoneGeary_monotoneOn_capitalSupply :
    MonotoneOn (fun r => stoneGeary.aggregateCapital (stoneGeary_calibrated.stationary r))
      (Icc (0 : ℝ) (1 / 100)) :=
  stoneGeary_calibrated.monotoneOn_capitalSupply

/-- **Uniqueness of the equilibrium interest rate for a Stone–Geary economy.** The first
non-CRRA economy in this development with a unique Aiyagari equilibrium rate. -/
theorem stoneGeary_equilibriumRate_unique {A δ : ℝ} (hA : A ≠ 0) (hδ : 0 < δ)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc (0 : ℝ) (1 / 100)) (h₂ : r₂ ∈ Icc (0 : ℝ) (1 / 100))
    (he₁ : stoneGeary.aggregateCapital (stoneGeary_calibrated.stationary r₁)
      = capitalDemand A δ r₁)
    (he₂ : stoneGeary.aggregateCapital (stoneGeary_calibrated.stationary r₂)
      = capitalDemand A δ r₂) : r₁ = r₂ :=
  stoneGeary_calibrated.equilibriumRate_unique hA (by linarith) h₁ h₂ he₁ he₂

/-- The same in `IsAiyagariEquilibrium` form. -/
theorem stoneGeary_isAiyagariEquilibrium_unique {A δ : ℝ} (hA : A ≠ 0) (hδ : 0 < δ)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc (0 : ℝ) (1 / 100)) (h₂ : r₂ ∈ Icc (0 : ℝ) (1 / 100))
    (he₁ : IsAiyagariEquilibrium stoneGeary_calibrated.family (capitalDemand A δ) r₁)
    (he₂ : IsAiyagariEquilibrium stoneGeary_calibrated.family (capitalDemand A δ) r₂) :
    r₁ = r₂ :=
  stoneGeary_calibrated.isAiyagariEquilibrium_unique hA (by linarith) h₁ h₂ he₁ he₂

end LeanEconomics
