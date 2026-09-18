/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.CRRAConstants
import LeanEconomics.Models.UniformRate
import LeanEconomics.Equilibrium.SignChange

/-!
# The CES conditions, uniformly over a rate interval

`UniformRate` does this for log: each condition is monotone in the interest rate, so one check at
the right endpoint covers the whole interval. The same is true of the CES conditions, and one of
them gets markedly easier along the way.

The log route has to bound `‖V‖` uniformly in `r` before it can say anything, because
`deviationGap = 2 β ‖V‖`. The CES route does not: `oscGap` is a formula in the primitives, and its
only rate dependence is through `maxConsumption = maxIncome + (1 + r) · assetCap`. So it is
monotone in `r` for free, with no estimate of the value function at all.
-/

open scoped NNReal
open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
-- Calibrated CES bounds, stated at a zero borrowing limit like the rest of the quantitative
-- layer (`CRRAConstants`).
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

@[simp] theorem withRate_dom (r : ℝ) (hr : P.RateOK r) : (P.withRate r hr).dom = P.dom := rfl

/-! ### The oscillation gap rises with the rate -/

theorem oscGap_le_of_le {r₀ r₁ : ℝ} (h₀ : P.RateOK r₀) (h₁ : P.RateOK r₁) (hle : r₀ ≤ r₁) :
    (P.withRate r₀ h₀).oscGap ≤ (P.withRate r₁ h₁).oscGap := by
  have hβ : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
  have hmax : (P.withRate r₀ h₀).maxConsumption ≤ (P.withRate r₁ h₁).maxConsumption := by
    simp only [maxConsumption, withRate_maxIncome, withRate_interest]
    nlinarith [P.assetCap_nonneg]
  have hu : P.u ((P.withRate r₀ h₀).maxConsumption) ≤ P.u ((P.withRate r₁ h₁).maxConsumption) :=
    P.monotoneOn_u_dom (P.mem_dom_of_pos (P.withRate r₀ h₀).maxConsumption_pos)
      (P.mem_dom_of_pos (P.withRate r₁ h₁).maxConsumption_pos) hmax
  have hmc₀ : (P.withRate r₀ h₀).minConsumption = P.minConsumption := rfl
  have hmc₁ : (P.withRate r₁ h₁).minConsumption = P.minConsumption := rfl
  simp only [oscGap, withRate_u, hmc₀, hmc₁, withRate_discount]
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  linarith

/-! ### The corner condition rises with the rate -/

theorem crraLipschitz_le_of_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {r₀ r₁ : ℝ}
    (h₀ : P.RateOK r₀) (h₁ : P.RateOK r₁) (hle : r₀ ≤ r₁)
    (hβ₁ : (P.discount : ℝ) * (1 + r₁) < 1) :
    (P.withRate r₀ h₀).crraLipschitz γ ≤ (P.withRate r₁ h₁).crraLipschitz γ := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hβ₀ : (P.discount : ℝ) * (1 + r₀) < 1 := by nlinarith
  have hK : (0 : ℝ) ≤ crraSlopeBound γ P.minConsumption :=
    crraSlopeBound_nonneg hγ0 hγ1 P.minConsumption_pos
  have hmc₀ : (P.withRate r₀ h₀).minConsumption = P.minConsumption := rfl
  have hmc₁ : (P.withRate r₁ h₁).minConsumption = P.minConsumption := rfl
  simp only [crraLipschitz, hmc₀, hmc₁, withRate_interest, withRate_discount]
  rw [div_le_div_iff₀ (by linarith [h₀.1]) (by linarith [h₁.1])]
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) + r₀ ≤ 1 + r₁) hK, hβ, h₀.1.le]

/-- **The CES corner condition, checked once at the top of the interval.** -/
theorem crra_policy_eq_zero_uniform {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : P.Bounded)
    (hu : P.u = crraUtility γ) {r₀ r₁ : ℝ} (h₀ : P.RateOK r₀) (h₁ : P.RateOK r₁) (hle : r₀ ≤ r₁)
    (hβ₁ : (P.discount : ℝ) * (1 + r₁) < 1)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (hlt : (P.withRate r₁ h₁).discount * (P.withRate r₁ h₁).crraLipschitz γ
      < (P.withRate r₁ h₁).resources (a, z) ^ (-γ)) :
    (P.withRate r₀ h₀).policy (a, z) = 0 := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hβ₀ : (P.discount : ℝ) * (1 + r₀) < 1 := by nlinarith
  refine (P.withRate r₀ h₀).crra_policy_eq_zero_of_resources hγ0 hγ1 hb (by simpa using hu)
    (by simpa using hβ₀) ha ?_
  have hlip := P.crraLipschitz_le_of_le hγ0 hγ1 h₀ h₁ hle hβ₁
  have hres := P.resources_le_of_le h₀ h₁ hle ha.1 z
  have hpos₀ : 0 < (P.withRate r₀ h₀).resources (a, z) :=
    (P.withRate r₀ h₀).assetFloor_lt_resources _
  have hlipβ : (P.withRate r₀ h₀).discount * (P.withRate r₀ h₀).crraLipschitz γ
      ≤ (P.withRate r₁ h₁).discount * (P.withRate r₁ h₁).crraLipschitz γ := by
    simp only [withRate_discount]
    exact mul_le_mul_of_nonneg_left hlip hβ
  have hanti : (P.withRate r₁ h₁).resources (a, z) ^ (-γ)
      ≤ (P.withRate r₀ h₀).resources (a, z) ^ (-γ) := rpow_neg_antitone hγ0 hpos₀ hres
  linarith

/-! ### The decline condition also rises with the rate

Both factors of the threshold move the same way -- a higher rate raises the oscillation gap and
widens `1 + r - θ` -- so this endpoint is the top of the interval too. -/

theorem crra_policy_lt_self_uniform {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hb : P.Bounded) (hu : P.u = crraUtility γ) {r₀ r₁ : ℝ}
    (h₀ : P.RateOK r₀) (h₁ : P.RateOK r₁) (hle : r₀ ≤ r₁) (hθr : θ ≤ 1 + r₀)
    (hpc : (P.withRate r₀ h₀).PositiveConsumption)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (hlt : ((P.withRate r₁ h₁).discount * (P.withRate r₁ h₁).oscGap / θ)
        * (P.income z + (1 + r₁ - θ) * assetCap) ^ γ < a) :
    (P.withRate r₀ h₀).policy (a, z) < a := by
  have hcap := P.assetCap_nonneg
  have hinc : 0 < P.income z := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z)
  refine (P.withRate r₀ h₀).crra_policy_lt_self hγ0 hγ1 hθ0 hθ1 (by simpa using hθr)
    hb (by simpa using hu) hpc ha z ?_
  refine lt_of_le_of_lt ?_ hlt
  have hosc := P.oscGap_le_of_le h₀ h₁ hle
  have hosc0 := (P.withRate r₀ h₀).oscGap_nonneg
  have hbase0 : (0 : ℝ) ≤ P.income z + (1 + r₀ - θ) * assetCap := by
    have : 0 ≤ (1 + r₀ - θ) * assetCap := mul_nonneg (by linarith) hcap
    linarith
  have hbasele : P.income z + (1 + r₀ - θ) * assetCap ≤ P.income z + (1 + r₁ - θ) * assetCap := by
    have : (1 + r₀ - θ) * assetCap ≤ (1 + r₁ - θ) * assetCap :=
      mul_le_mul_of_nonneg_right (by linarith) hcap
    linarith
  have hrpow : (P.income z + (1 + r₀ - θ) * assetCap) ^ γ
      ≤ (P.income z + (1 + r₁ - θ) * assetCap) ^ γ :=
    Real.rpow_le_rpow hbase0 hbasele hγ0.le
  have hcoef : ((P.withRate r₀ h₀).discount : ℝ) * (P.withRate r₀ h₀).oscGap / θ
      ≤ ((P.withRate r₁ h₁).discount : ℝ) * (P.withRate r₁ h₁).oscGap / θ := by
    simp only [withRate_discount]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hosc P.discount.coe_nonneg) hθ0.le
  have hcoef0 : (0 : ℝ) ≤ ((P.withRate r₀ h₀).discount : ℝ) * (P.withRate r₀ h₀).oscGap / θ := by
    simp only [withRate_discount]
    positivity
  have hrpow0 : (0 : ℝ) ≤ (P.income z + (1 + r₀ - θ) * assetCap) ^ γ :=
    Real.rpow_nonneg hbase0 γ
  simp only [withRate_income]
  calc ((P.withRate r₀ h₀).discount : ℝ) * (P.withRate r₀ h₀).oscGap / θ
        * (P.income z + (1 + r₀ - θ) * assetCap) ^ γ
      ≤ ((P.withRate r₁ h₁).discount : ℝ) * (P.withRate r₁ h₁).oscGap / θ
        * (P.income z + (1 + r₀ - θ) * assetCap) ^ γ :=
        mul_le_mul_of_nonneg_right hcoef hrpow0
    _ ≤ ((P.withRate r₁ h₁).discount : ℝ) * (P.withRate r₁ h₁).oscGap / θ
        * (P.income z + (1 + r₁ - θ) * assetCap) ^ γ :=
        mul_le_mul_of_nonneg_left hrpow (le_trans hcoef0 hcoef)

/-! ### The supply floor in primitives, CES version -/

theorem crra_le_aggregateCapital_of_gain {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumption)
    [MeasurableSpace Z] [BorelSpace Z] {μ : ProbabilityMeasure P.State}
    (hμ : P.IsStationary μ) {z₁ z₀ : Z} {p₀ h : ℝ} (hh0 : 0 < h)
    (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    (hgain : (P.income z₁ - h) ^ (-γ) * h
      < P.discount * (P.transitionMatrix z₁ z₀
          * ((P.income z₀ + (1 + P.interest) * h) ^ (-γ) * ((1 + P.interest) * (h / 2))))) :
    h / 2 * p₀ ≤ P.aggregateCapital μ := by
  refine P.le_aggregateCapital hμ (by linarith) hp fun a ha => ?_
  refine P.crra_policy_ge_of_gain hγ0 hu hpc z₁ hh0 hhcap hhinc ?_ ha
  refine lt_of_lt_of_le hgain (mul_le_mul_of_nonneg_left ?_ P.discount.coe_nonneg)
  have hhalf : h / 2 ∈ Icc (0 : ℝ) assetCap := ⟨by linarith, by linarith⟩
  have hfull : h ∈ Icc (0 : ℝ) assetCap := ⟨hh0.le, hhcap⟩
  have hgen := P.crra_cont_sub_ge_gen hγ0 hγ1 hu hpc z₁ z₀ hhalf hfull (by linarith)
  rw [show h - h / 2 = h / 2 from by ring] at hgen
  exact hgen

/-- **The supply floor with the two powers bounded separately**, CES version. The gain condition
compares the marginal cost of saving `h` in the high state against its marginal value in the low
state; bounding each power separately leaves one inequality among the bounds.

A base above one needs no root (`rpow_neg_le_one_of_one_le`), and a base just below one needs
only its reciprocal (`rpow_neg_le_inv_of_le_one`) — which is the cost side of every calibration
so far. Only the gain side, where the base is small and the bound large, still goes through a
root. -/
theorem crra_le_aggregateCapital_of_bounds {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumption)
    [MeasurableSpace Z] [BorelSpace Z] {μ : ProbabilityMeasure P.State}
    (hμ : P.IsStationary μ) {z₁ z₀ : Z} {p₀ h U L : ℝ} (hh0 : 0 < h)
    (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    (hU : (P.income z₁ - h) ^ (-γ) ≤ U)
    (hL : L ≤ (P.income z₀ + (1 + P.interest) * h) ^ (-γ))
    (hcond : U * h
      < (P.discount : ℝ) * (P.transitionMatrix z₁ z₀ * (L * ((1 + P.interest) * (h / 2))))) :
    h / 2 * p₀ ≤ P.aggregateCapital μ := by
  refine P.crra_le_aggregateCapital_of_gain hγ0 hγ1 hu hpc hμ (z₀ := z₀) hh0 hhcap hhinc hp ?_
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hπ : (0 : ℝ) ≤ P.transitionMatrix z₁ z₀ := P.transitionMatrix_nonneg _ _
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hcost : (P.income z₁ - h) ^ (-γ) * h ≤ U * h := mul_le_mul_of_nonneg_right hU hh0.le
  have hgainL : (P.discount : ℝ) * (P.transitionMatrix z₁ z₀ * (L * ((1 + P.interest) * (h / 2))))
      ≤ (P.discount : ℝ) * (P.transitionMatrix z₁ z₀
          * ((P.income z₀ + (1 + P.interest) * h) ^ (-γ) * ((1 + P.interest) * (h / 2)))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL (by positivity)) hπ) hβ
  linarith

end IncomeFluctuation

end LeanEconomics
