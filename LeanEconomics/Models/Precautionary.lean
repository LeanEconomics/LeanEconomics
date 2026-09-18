/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.CESNearLogWitness

/-!
# All capital is precautionary

`nearLog_floor_top` says the `nearLog` economy holds at least `1/400` of capital at every
stationary distribution. This file shows what that capital is FOR, by taking the risk away and
leaving everything else alone.

`riskless` is `nearLog` with its two income states replaced by their mean `101/200` — same
discount factor, same relative risk aversion, same interest rate, same asset cap, same expected
income, no risk. Its household saves NOTHING at any asset level, so its capital supply is
exactly zero.

## Why nothing, rather than merely less

With `β(1+r) < 1` a household facing no risk wants a declining consumption path, and a liquidity
constraint is the only thing stopping it borrowing. Saving would make consumption rise, which it
does not want at any margin. The corner condition is the formal version: `β L < m`, the
discounted slope of the value function against marginal utility at current resources. What is
special about the riskless calibration is that this holds at EVERY asset level in the region,
not just below a threshold — `β L ≤ 3/7` while `m ≥ 1/2` even at the top of the asset range.

In `nearLog` the same test fails above `1/50`, and it fails because the value function is
steeper: the household is buying insurance against the `1/100` income state. The gap between the
two economies is the precautionary motive, and `1/400` is a lower bound on what it is worth.

## What is not claimed

That capital is monotone in risk. That would need the two economies to be ordered by a
mean-preserving spread and the saving rule to be convex in income — prudence — which is not
formalised here. This is the endpoint comparison: all of it, against none of it.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction
open scoped NNReal

namespace LeanEconomics

open IncomeFluctuation

/-- **`nearLog` with the risk removed**: one income state, at the mean of the two `nearLog`
states, and every other primitive unchanged. -/
noncomputable def riskless : IncomeFluctuation (Fin 1) 0 1 where
  income _ := 101 / 200
  transitionMatrix _ _ := 1
  interest := 0
  discount := 1 / 8
  u := crraUtility (15 / 16)
  minIncome := 101 / 200
  maxIncome := 101 / 200
  minIncome_pos := by norm_num
  minIncome_le _ := le_rfl
  le_maxIncome _ := le_rfl
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
  continuousOn_u_dom := continuousOn_crraUtility_Ici (by norm_num)
  monotoneOn_u_dom := monotoneOn_crraUtility_Ici (by norm_num)
  strictConcaveOn_u_dom := strictConcaveOn_crraUtility_Ici (by norm_num) (by norm_num)
  continuousOn_extendDom := continuousOn_extendDom_Ici (continuousOn_crraUtility_Ici (by norm_num))

@[simp] theorem riskless_u : riskless.u = crraUtility (15 / 16) := rfl
@[simp] theorem riskless_income (z : Fin 1) : riskless.income z = 101 / 200 := rfl
@[simp] theorem riskless_interest : riskless.interest = 0 := rfl
@[simp] theorem riskless_discount : (riskless.discount : ℝ) = 1 / 8 := rfl
@[simp] theorem riskless_minConsumption : riskless.minConsumption = 101 / 200 := by
  norm_num [riskless]

theorem riskless_bounded : riskless.Bounded := rfl

/-- The expected income of `riskless` is that of `nearLog`: `(1/100 + 1)/2`. -/
theorem riskless_income_eq_mean :
    riskless.income 0 = (nearLog.income 0 + nearLog.income 1) / 2 := by norm_num

/-! ### The slope of the value function

`crraSlopeBound (15/16) (101/200) ≤ 3`, pinned by `(101/200)^15 ≥ (1/2)^16` and
`2 ≤ (64/61)^16`. -/

theorem riskless_crraSlopeBound_le : crraSlopeBound (15 / 16) (101 / 200) ≤ 3 := by
  have hm : ((101 : ℝ) / 200) ^ (-(15 / 16) : ℝ) ≤ 2 := by
    have h : (1 : ℝ) / 2 ≤ ((101 : ℝ) / 200) ^ ((15 : ℝ) / 16) :=
      le_rpow_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    have hpos : (0 : ℝ) < ((101 : ℝ) / 200) ^ ((15 : ℝ) / 16) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [Real.rpow_neg (by norm_num), inv_le_comm₀ hpos (by norm_num)]
    linarith
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 16) ≤ 64 / 61 :=
    rpow_le_of_pow_le (m := 1) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : ((2 : ℝ) ^ ((1 : ℝ) / 16))⁻¹ ≥ 61 / 64 := by
    rw [ge_iff_le, le_inv_comm₀ (by norm_num) h2pos]
    linarith
  have hmpos : (0 : ℝ) ≤ ((101 : ℝ) / 200) ^ (-(15 / 16) : ℝ) := Real.rpow_nonneg (by norm_num) _
  simp only [crraSlopeBound, show (1 : ℝ) - 15 / 16 = 1 / 16 from by norm_num]
  rw [div_le_iff₀ (by norm_num)]
  nlinarith [hm, hinv, hmpos]

/-! ### The household saves nothing, anywhere -/

/-- **The riskless household never saves.** At every asset level in the region the corner
condition holds: `β L ≤ 3/7` against a marginal utility of at least `1/2`. -/
theorem riskless_policy_eq_zero {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 1) :
    riskless.policy (a, z) = 0 := by
  refine riskless.crra_policy_eq_zero_of_resources (γ := 15 / 16) (by norm_num) (by norm_num)
    riskless_bounded rfl (by rw [riskless_discount]; norm_num) (s := (a, z)) ha ?_
  have hres : riskless.resources (a, z) = 101 / 200 + a := by
    simp only [IncomeFluctuation.resources, riskless_income, riskless_interest,
      max_eq_right ha.1]
    ring
  have hres0 : (0 : ℝ) < 101 / 200 + a := by linarith [ha.1]
  have hresle : (101 : ℝ) / 200 + a ≤ 301 / 200 := by linarith [ha.2]
  -- the marginal utility at the top of the asset range is still at least a half
  have hup : ((101 : ℝ) / 200 + a) ^ ((15 : ℝ) / 16) ≤ 2 := by
    refine le_trans (Real.rpow_le_rpow hres0.le hresle (by norm_num)) ?_
    exact rpow_le_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have huppos : (0 : ℝ) < ((101 : ℝ) / 200 + a) ^ ((15 : ℝ) / 16) :=
    Real.rpow_pos_of_pos hres0 _
  have hge : (1 : ℝ) / 2 ≤ (((101 : ℝ) / 200 + a) ^ ((15 : ℝ) / 16))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) huppos]; linarith
  -- and the discounted slope of the value function is at most `3/7`
  have hlip : riskless.crraLipschitz (15 / 16) ≤ 24 / 7 := by
    simp only [IncomeFluctuation.crraLipschitz, riskless_minConsumption, riskless_interest,
      riskless_discount]
    rw [div_le_iff₀ (by norm_num)]
    linarith [riskless_crraSlopeBound_le]
  have hlip0 : (0 : ℝ) ≤ riskless.crraLipschitz (15 / 16) :=
    riskless.crraLipschitz_nonneg (by norm_num) (by norm_num)
      (by rw [riskless_discount, riskless_interest]; norm_num)
  rw [hres, Real.rpow_neg hres0.le, riskless_discount]
  linarith [hge, hlip, hlip0]

/-- **Capital supply is exactly zero.** Capital is mean saving, and nobody saves. -/
theorem riskless_aggregateCapital_eq_zero {μ : ProbabilityMeasure riskless.State}
    (hμ : riskless.IsStationary μ) : riskless.aggregateCapital μ = 0 := by
  rw [riskless.aggregateCapital_eq_integral_policy hμ]
  have hz : ∀ s : riskless.State, riskless.policyCoord s = 0 := by
    intro s
    have hmem : ((s.1 : ℝ)) ∈ Icc (0 : ℝ) 1 := s.1.2
    simp only [IncomeFluctuation.policyCoord_apply, IncomeFluctuation.incl]
    exact riskless_policy_eq_zero hmem s.2
  simp only [hz, integral_zero]

/-- **All capital is precautionary.** Two economies with the same preferences, the same discount
factor, the same interest rate, the same asset cap and the same EXPECTED income: the one with
income risk holds at least `1/400` of capital, the one without holds none. -/
theorem precautionary_gap (hrhi : nearLog.RateOK (1 / 200 : ℝ))
    (μ : ProbabilityMeasure nearLog.State)
    (hμ : (nearLog.withRate (1 / 200) hrhi).IsStationary μ)
    {ν : ProbabilityMeasure riskless.State} (hν : riskless.IsStationary ν) :
    riskless.aggregateCapital ν = 0 ∧ 1 / 400 ≤ nearLog.aggregateCapital μ :=
  ⟨riskless_aggregateCapital_eq_zero hν, nearLog_floor_top hrhi μ hμ⟩

end LeanEconomics
