/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.UniquenessClass
import LeanEconomics.Models.CESConcaveConsumption
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A Stone–Geary economy: existence and uniqueness of the equilibrium rate

`u c = log (1/1000 + c)` — log utility over consumption above a subsistence level — with income
in `{1/100, 1}`, borrowing limit `0`, asset cap `1`, discount `1/8`, and interest rates in
`[0, 1/200]`.

This is `nearLog`'s calibration with a subsistence level added, and that is deliberate: the
subsistence level is what makes the utility BOUNDED at zero consumption, so `γ = 1` becomes
admissible where CRRA needs `γ < 1`, and Light's condition `γ ≤ 1` holds with equality.

## What the subsistence level costs and buys

It costs the Inada condition: marginal utility at zero consumption is `1000`, finite, so
consumption is not positive for free. It is kept positive by the oscillation bound instead
(`consumptionFnOf_pos_of_marginal`), and `β · oscSlopeConst ≤ 175` against a marginal value of
`500` is the inequality that does it.

It buys the whole `γ = 1` case. Relative risk aversion is `c / (η + c) < 1`, so Light's Theorem 1
applies; and the marginal bounds are RATIONAL — `(η + c)⁻¹` rather than a sixteenth root — which
is why this calibration is where the arithmetic is easy.

## What comes out

`stoneGeary_equilibriumRate_unique` and `stoneGeary_floor_top` together give
`stoneGeary_exists_equilibrium`: a technology at which this economy has an Aiyagari equilibrium,
and at most one equilibrium rate in the interval. The first non-CRRA economy here with both.
-/

open scoped NNReal
open Set MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

open IncomeFluctuation

/-! ### Shifted CRRA with a positive subsistence level -/

theorem continuousOn_haraUtility_Ici_pos {γ η : ℝ} (hη : 0 < η) :
    ContinuousOn (haraUtility γ η) (Ici 0) := by
  refine (continuousOn_crraUtility γ).comp (Continuous.continuousOn (by fun_prop)) ?_
  intro c hc
  simp only [mem_Ici] at hc
  exact mem_Ioi.mpr (by linarith)

theorem monotoneOn_haraUtility_Ici_pos {γ η : ℝ} (hη : 0 < η) :
    MonotoneOn (haraUtility γ η) (Ici 0) := fun x hx y hy hxy =>
  monotoneOn_crraUtility γ (mem_Ioi.mpr (by simp only [mem_Ici] at hx; linarith))
    (mem_Ioi.mpr (by simp only [mem_Ici] at hy; linarith)) (by linarith)

theorem strictConcaveOn_haraUtility_Ici_pos {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 < η) :
    StrictConcaveOn ℝ (Ici 0) (haraUtility γ η) := by
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have h := (strictConcaveOn_crraUtility hγ0).2 (x := η + x) (y := η + y)
    (mem_Ioi.mpr (by simp only [mem_Ici] at hx; linarith))
    (mem_Ioi.mpr (by simp only [mem_Ici] at hy; linarith))
    (by intro hcon; exact hxy (by linarith)) ha hb hab
  simp only [haraUtility, smul_eq_mul] at h ⊢
  have he : a * (η + x) + b * (η + y) = η + (a * x + b * y) := by nlinarith [hab]
  rwa [he] at h

/-! ### The economy -/

/-- **A Stone–Geary economy**: log utility over consumption above a subsistence level. -/
noncomputable def stoneGeary : IncomeFluctuation (Fin 2) 0 1 where
  income z := if z = 0 then 1 / 100 else 1
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 8
  u := haraUtility 1 (1 / 1000)
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
  discount_lt_one := by norm_num
  dom := Ici 0
  Ioi_subset_dom := Ioi_subset_Ici_self
  dom_subset_Ici := subset_rfl
  continuousOn_u_dom := continuousOn_haraUtility_Ici_pos (by norm_num)
  monotoneOn_u_dom := monotoneOn_haraUtility_Ici_pos (by norm_num)
  strictConcaveOn_u_dom := strictConcaveOn_haraUtility_Ici_pos (by norm_num) (by norm_num)
  continuousOn_extendDom :=
    continuousOn_extendDom_Ici (continuousOn_haraUtility_Ici_pos (by norm_num))

@[simp] theorem stoneGeary_u : stoneGeary.u = haraUtility 1 (1 / 1000) := rfl
@[simp] theorem stoneGeary_discount : (stoneGeary.discount : ℝ) = 1 / 8 := rfl
@[simp] theorem stoneGeary_interest : stoneGeary.interest = 0 := rfl
@[simp] theorem stoneGeary_maxIncome : stoneGeary.maxIncome = 1 := rfl
@[simp] theorem stoneGeary_income_zero : stoneGeary.income (0 : Fin 2) = 1 / 100 := rfl
@[simp] theorem stoneGeary_income_one : stoneGeary.income (1 : Fin 2) = 1 := rfl
@[simp] theorem stoneGeary_minConsumption : stoneGeary.minConsumption = 1 / 100 := by
  norm_num [stoneGeary]

theorem stoneGeary_bounded : stoneGeary.Bounded := rfl

/-- Utility in closed form: the logarithm of consumption above subsistence. -/
theorem stoneGeary_u_eq (c : ℝ) : stoneGeary.u c = Real.log (1 / 1000 + c) := by
  rw [stoneGeary_u]
  simp only [haraUtility]
  rw [crraUtility_one]

/-- It is not CRRA: every CRRA with `γ < 1` vanishes at zero consumption, and `log (1/1000)`
does not; and CRRA with `γ ≥ 1` is `-∞` there. -/
theorem stoneGeary_ne_crra {γ : ℝ} (hγ : γ < 1) : stoneGeary.u ≠ crraUtility γ := by
  intro h
  have hz := congrFun h 0
  rw [stoneGeary_u_eq, crraUtility_zero hγ] at hz
  have hlt : Real.log (1 / 1000 + 0) < 0 := Real.log_neg (by norm_num) (by norm_num)
  linarith

/-! ### The calibration

The only irrational quantities are two logarithms, and both are bounded crudely: `log x ≤ x - 1`
above, and `log (1000/11) ≤ log 128 = 7 log 2` below. -/

theorem stoneGeary_log_upper : Real.log (2006 / 1000 : ℝ) ≤ 1006 / 1000 := by
  have := Real.log_le_sub_one_of_pos (x := (2006 / 1000 : ℝ)) (by norm_num)
  linarith

theorem stoneGeary_log_lower : (-4853 : ℝ) / 1000 ≤ Real.log (11 / 1000 : ℝ) := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hpow : Real.log ((2 : ℝ) ^ (7 : ℕ)) = 7 * Real.log 2 := Real.log_pow 2 7
  have hle : Real.log (1000 / 11 : ℝ) ≤ Real.log ((2 : ℝ) ^ (7 : ℕ)) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [hpow] at hle
  have hinv : Real.log (11 / 1000 : ℝ) = -Real.log (1000 / 11 : ℝ) := by
    rw [← Real.log_inv]
    norm_num
  rw [hinv]
  linarith

theorem stoneGeary_maxConsumption_le {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : stoneGeary.RateOK r) :
    (stoneGeary.withRate r hrr).maxConsumption ≤ 2005 / 1000 := by
  simp only [IncomeFluctuation.maxConsumption, IncomeFluctuation.withRate_maxIncome,
    IncomeFluctuation.withRate_interest, stoneGeary_maxIncome]
  nlinarith [hr.1, hr.2]

theorem stoneGeary_oscSpread_le {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : stoneGeary.RateOK r) : (stoneGeary.withRate r hrr).oscSpread ≤ 7 := by
  have hu : (stoneGeary.withRate r hrr).u = stoneGeary.u := rfl
  have hmaxle := stoneGeary_maxConsumption_le hr hrr
  have hmax0 : (0 : ℝ) ≤ (stoneGeary.withRate r hrr).maxConsumption :=
    (stoneGeary.withRate r hrr).maxConsumption_pos.le
  have hmin : (stoneGeary.withRate r hrr).minConsumption = 1 / 100 := stoneGeary_minConsumption
  have hβ : ((stoneGeary.withRate r hrr).discount : ℝ) = 1 / 8 := rfl
  have hupper : (stoneGeary.withRate r hrr).u (stoneGeary.withRate r hrr).maxConsumption
      ≤ 1006 / 1000 := by
    rw [hu, stoneGeary_u_eq]
    refine le_trans (Real.log_le_log (by linarith) (show (1 : ℝ) / 1000
      + (stoneGeary.withRate r hrr).maxConsumption ≤ 2006 / 1000 by linarith)) ?_
    exact stoneGeary_log_upper
  have hlower : (-4853 : ℝ) / 1000
      ≤ (stoneGeary.withRate r hrr).u (stoneGeary.withRate r hrr).minConsumption := by
    rw [hu, hmin, stoneGeary_u_eq]
    refine le_trans stoneGeary_log_lower (le_of_eq ?_)
    norm_num
  simp only [IncomeFluctuation.oscSpread, hβ]
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- **Positive consumption**, against every continuation the iteration produces. Marginal utility
at zero is `1000`, and the discounted slope of the continuation is at most `175`. -/
theorem stoneGeary_positive {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200)) (hrr : stoneGeary.RateOK r)
    (v : (ℝ × Fin 2) →ᵇ ℝ) (hv : ConcaveSlices (0 : ℝ) 1 v)
    (hosc : (stoneGeary.withRate r hrr).OscOn v 7) (z : Fin 2) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) : 0 < (stoneGeary.withRate r hrr).consumptionFnOf v z a := by
  have hM : MarginalBoundOn (stoneGeary.withRate r hrr).dom (stoneGeary.withRate r hrr).u
      (((1 : ℝ) / 1000 + 1 / 1000) ^ (-(1 : ℝ))) := by
    rw [show (stoneGeary.withRate r hrr).dom = Ici 0 from stoneGeary_bounded,
      show (stoneGeary.withRate r hrr).u = haraUtility 1 (1 / 1000) from rfl]
    exact marginalBoundOn_haraUtility_pos (by norm_num) (by norm_num) (by norm_num)
  refine (stoneGeary.withRate r hrr).consumptionFnOf_pos_of_marginal hM (by norm_num) hv hosc
    ?_ z ha
  have hβ : ((stoneGeary.withRate r hrr).discount : ℝ) = 1 / 8 := rfl
  have hmin : (stoneGeary.withRate r hrr).minConsumption = 1 / 100 := stoneGeary_minConsumption
  have hM500 : (((1 : ℝ) / 1000 + 1 / 1000) ^ (-(1 : ℝ))) = 500 := by
    rw [show (1 : ℝ) / 1000 + 1 / 1000 = (1 : ℝ) / 500 by norm_num, Real.rpow_neg_one]
    norm_num
  rw [hM500, IncomeFluctuation.oscSlopeConst, hβ, hmin]
  norm_num

/-- **The cap is slack.** -/
theorem stoneGeary_slack {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200)) (hrr : stoneGeary.RateOK r)
    {v : (ℝ × Fin 2) →ᵇ ℝ} (hv : ConcaveSlices (0 : ℝ) 1 v)
    (hosc : (stoneGeary.withRate r hrr).OscOn v 7) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 2) :
    (stoneGeary.withRate r hrr).policyOf v (a, z) < 1 := by
  refine (stoneGeary.withRate r hrr).hara_policyOf_lt_assetCap (γ := 1) (η := 1 / 1000)
    (θ := 999 / 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl
    hv (by norm_num) hosc (fun z' b hb => stoneGeary_positive hr hrr v hv hosc z' hb) ?_ ha z
  · have hβ : ((stoneGeary.withRate r hrr).discount : ℝ) = 1 / 8 := rfl
    have hinc : (stoneGeary.withRate r hrr).maxIncome = 1 := rfl
    have hint : (stoneGeary.withRate r hrr).interest = r := rfl
    rw [hβ, hinc, hint, Real.rpow_one]
    nlinarith [hr.1, hr.2]

/-! ### The corner -/

theorem stoneGeary_slopeBoundU_le {r : ℝ} (hrr : stoneGeary.RateOK r) :
    (stoneGeary.withRate r hrr).slopeBoundU ≤ 139 := by
  have hu : (stoneGeary.withRate r hrr).u = stoneGeary.u := rfl
  have hm : (stoneGeary.withRate r hrr).minConsumption = 1 / 100 := stoneGeary_minConsumption
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  simp only [IncomeFluctuation.slopeBoundU, slopeBound, hu, hm]
  rw [stoneGeary_u_eq, stoneGeary_u_eq]
  have hdiv : Real.log ((1 : ℝ) / 1000 + 1 / 100) - Real.log ((1 : ℝ) / 1000 + 1 / 100 / 2)
      = Real.log (11 / 6 : ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [hdiv]
  have hle : Real.log (11 / 6 : ℝ) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
  rw [div_le_iff₀ (by norm_num)]
  linarith

theorem stoneGeary_lipschitz {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : stoneGeary.RateOK r) :
    ∀ z : Fin 2, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |(stoneGeary.withRate r hrr).toExtended.valueFunction (x, z)
        - (stoneGeary.withRate r hrr).toExtended.valueFunction (y, z)| ≤ 170 * |x - y| := by
  refine (stoneGeary.withRate r hrr).valueFunction_lipschitz (by norm_num) ?_
  have hslope := stoneGeary_slopeBoundU_le hrr
  have hslope0 : (0 : ℝ) ≤ (stoneGeary.withRate r hrr).slopeBoundU :=
    (stoneGeary.withRate r hrr).slopeBoundU_nonneg
  have hβ : ((stoneGeary.withRate r hrr).discount : ℝ) = 1 / 8 := rfl
  have hint : (stoneGeary.withRate r hrr).interest = r := rfl
  rw [hβ, hint]
  nlinarith [hr.1, hr.2, hslope, hslope0]

/-- **The corner condition**: below `1/40` the household saves nothing. -/
theorem stoneGeary_corner {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200)) (hrr : stoneGeary.RateOK r)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (1 / 40)) :
    (stoneGeary.withRate r hrr).policy (a, 0) = 0 := by
  have hres : (stoneGeary.withRate r hrr).resources (a, 0) ≤ 39 / 1000 := by
    simp only [IncomeFluctuation.resources, IncomeFluctuation.withRate_income,
      IncomeFluctuation.withRate_interest, max_eq_right ha.1, stoneGeary_income_zero]
    nlinarith [ha.1, ha.2, hr.1, hr.2]
  refine (stoneGeary.withRate r hrr).policy_eq_zero_of_corner_at (L := 170) (m := 25)
    (stoneGeary_lipschitz hr hrr) (s := (a, 0)) ⟨ha.1, by linarith [ha.2]⟩ ?_ (by norm_num)
  intro c d hd hdc hc
  have hd0 : (0 : ℝ) ≤ d := (stoneGeary.withRate r hrr).nonneg_of_mem_dom hd
  have hbound := haraUtility_marginal_bound_pos (γ := 1) (η := 1 / 1000)
    (R := (stoneGeary.withRate r hrr).resources (a, 0) - 0) (by norm_num)
    (show (0 : ℝ) < 1 / 1000 + d by linarith) hdc hc
  have hu : (stoneGeary.withRate r hrr).u = haraUtility 1 (1 / 1000) := rfl
  rw [hu]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (by linarith)) hbound
  have hR0 : (0 : ℝ) < 1 / 1000 + ((stoneGeary.withRate r hrr).resources (a, 0) - 0) := by
    have := (stoneGeary.withRate r hrr).assetFloor_lt_resources (a, 0)
    linarith
  rw [Real.rpow_neg_one, le_inv_comm₀ (by norm_num) hR0]
  linarith

/-! ### The economy is calibrated -/

theorem stoneGeary_calibrated :
    stoneGeary.Calibrated 1 (1 / 1000) 7 (1 / 40) 0 0 (1 / 200) where
  gamma_pos := by norm_num
  gamma_le_one := le_rfl
  eta_nonneg := by norm_num
  utility := rfl
  discount_pos := by rw [stoneGeary_discount]; norm_num
  positive := fun r hr hrr v hv hosc z a ha => stoneGeary_positive hr hrr v hv hosc z ha
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
theorem stoneGeary_concaveOn_consumptionFn {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : stoneGeary.RateOK r) (z : Fin 2) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) ((stoneGeary.withRate r hrr).consumptionFn z) :=
  stoneGeary_calibrated.concaveOn_consumptionFn hr hrr z

/-- **Uniqueness of the equilibrium interest rate.** -/
theorem stoneGeary_equilibriumRate_unique {A δ : ℝ} (hA : A ≠ 0) (hδ : 0 < δ)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc (0 : ℝ) (1 / 200)) (h₂ : r₂ ∈ Icc (0 : ℝ) (1 / 200))
    (he₁ : stoneGeary.aggregateCapital (stoneGeary_calibrated.stationary r₁)
      = capitalDemand A δ r₁)
    (he₂ : stoneGeary.aggregateCapital (stoneGeary_calibrated.stationary r₂)
      = capitalDemand A δ r₂) : r₁ = r₂ :=
  stoneGeary_calibrated.equilibriumRate_unique hA (by linarith) h₁ h₂ he₁ he₂

/-! ### The supply floor, and existence

At the top of the rate interval the household strictly prefers saving `1/100000` to saving
nothing: the cost, priced at the margin in the good income state, is at most `h`, and the gain,
priced at the margin in the bad one, is at least `2.8 h`. So aggregate capital is at least
`1/400000` at every stationary distribution there, and with uniqueness that is what the
intermediate-value argument needs. -/

theorem stoneGeary_positiveConsumption {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : stoneGeary.RateOK r) : (stoneGeary.withRate r hrr).PositiveConsumption := by
  intro s hs
  exact stoneGeary_positive hr hrr _ (stoneGeary.withRate r hrr).concaveSlices_valueFunction
    (IncomeFluctuation.OscOn.mono (stoneGeary.withRate r hrr)
      (stoneGeary.withRate r hrr).oscOn_valueFunction (stoneGeary_oscSpread_le hr hrr)) s.2 hs

/-- **The supply floor at the top rate.** -/
theorem stoneGeary_floor_top (hrhi : stoneGeary.RateOK (1 / 200 : ℝ))
    (μ : ProbabilityMeasure stoneGeary.State)
    (hμ : (stoneGeary.withRate (1 / 200) hrhi).IsStationary μ) :
    1 / 400000 ≤ stoneGeary.aggregateCapital μ := by
  have hkey := (stoneGeary.withRate (1 / 200) hrhi).hara_le_aggregateCapital_of_gain
    (γ := 1) (η := 1 / 1000) (by norm_num) (by norm_num) rfl rfl
    (stoneGeary_positiveConsumption (by norm_num) hrhi) hμ
    (z₁ := 1) (z₀ := 0) (p₀ := 1 / 2) (h := 1 / 100000) (by norm_num) (by norm_num)
    (by rw [show (stoneGeary.withRate (1 / 200) hrhi).income 1 = 1 from rfl]; norm_num)
    (fun z => by rw [show (stoneGeary.withRate (1 / 200) hrhi).transitionMatrix z 1 = 1 / 2
      from rfl]) ?_
  · have heq : (stoneGeary.withRate (1 / 200) hrhi).aggregateCapital μ
        = stoneGeary.aggregateCapital μ := rfl
    rw [heq] at hkey
    linarith [hkey]
  · have hinc1 : (stoneGeary.withRate (1 / 200) hrhi).income 1 = 1 := rfl
    have hinc0 : (stoneGeary.withRate (1 / 200) hrhi).income 0 = 1 / 100 := rfl
    have hπ : (stoneGeary.withRate (1 / 200) hrhi).transitionMatrix 1 0 = 1 / 2 := rfl
    have hβ : ((stoneGeary.withRate (1 / 200) hrhi).discount : ℝ) = 1 / 8 := rfl
    have hint : (stoneGeary.withRate (1 / 200) hrhi).interest = 1 / 200 := rfl
    rw [hinc1, hinc0, hπ, hβ, hint, Real.rpow_neg_one, Real.rpow_neg_one]
    have hcost : ((1 : ℝ) / 1000 + 1 - 1 / 100000)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right; norm_num
    have hgain : (90 : ℝ) ≤ ((1 : ℝ) / 1000 + 1 / 100 + (1 + 1 / 200) * (1 / 100000))⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by norm_num)]
      norm_num
    nlinarith [hcost, hgain]

/-- **An Aiyagari equilibrium exists** for this economy, and by
`stoneGeary_equilibriumRate_unique` the rate is unique. -/
theorem stoneGeary_exists_equilibrium :
    ∃ A δ : ℝ, 0 < A ∧ 0 < 0 + δ ∧ ∃ r ∈ Icc (0 : ℝ) (1 / 200),
      IsAiyagariEquilibrium
        (stoneGeary.rateFamily (by norm_num : (0:ℝ) < 1 + 0) (by norm_num : (0:ℝ) ≤ 1 / 200))
        (capitalDemand A δ) r :=
  stoneGeary.exists_equilibrium_of_uniqueness_and_floor (by norm_num) (by norm_num)
    (fun r hr hrr => stoneGeary_calibrated.existsUnique_stationary hr hrr)
    (m := 1 / 400000) (by norm_num) (fun hrhi μ hμ => stoneGeary_floor_top hrhi μ hμ)

end LeanEconomics
