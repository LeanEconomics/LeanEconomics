/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationHARA
import LeanEconomics.Models.CESConcaveConsumption

/-!
# A Stone–Geary economy with a concave consumption function

`IncomeFluctuationHARA` proves the Carroll–Kimball induction step for shifted CRRA and reduces
the assembled statement to two inequalities. This file discharges them, at

  `u c = crraUtility (1/2) (1 + c) = 2 √(1 + c)`,

subsistence level `η = 1`, income in `{3/2, 2}`, gross return `1`, discount `1/1000`, borrowing
limit `0` and asset cap `1`.

## Why the calibration looks like this

Both inequalities are about the two artefacts of the capped, floored formulation, and both are
harder the closer consumption gets to zero — which is exactly where a FINITE marginal utility is
weakest. Income at least `3/2` keeps the consumption floor well away from zero, and `β = 1/1000`
keeps the bound on saving far below the cap. The margins are two orders of magnitude, so nothing
here is delicate.

`η = 1` and `γ = 1/2` make the arithmetic exact where it matters: `(η + maxConsumption) ^ (-γ)`
is `4 ^ (-1/2) = 1/2`, and `u maxConsumption` is `2 √4 = 4`.
-/

open Set

namespace LeanEconomics

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

/-- **A Stone–Geary economy**: CRRA with `γ = 1/2` over consumption above a subsistence shift
of `1`. -/
noncomputable def stoneGeary : IncomeFluctuation (Fin 2) 0 1 where
  income z := if z = 0 then 3 / 2 else 2
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 1000
  u := haraUtility (1 / 2) 1
  minIncome := 3 / 2
  maxIncome := 2
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

@[simp] theorem stoneGeary_u : stoneGeary.u = haraUtility (1 / 2) 1 := rfl
@[simp] theorem stoneGeary_discount : (stoneGeary.discount : ℝ) = 1 / 1000 := rfl
@[simp] theorem stoneGeary_interest : stoneGeary.interest = 0 := rfl
@[simp] theorem stoneGeary_minConsumption : stoneGeary.minConsumption = 3 / 2 := by
  norm_num [stoneGeary]

theorem stoneGeary_bounded : stoneGeary.Bounded := rfl

theorem stoneGeary_maxConsumption : stoneGeary.maxConsumption = 3 := by
  simp only [IncomeFluctuation.maxConsumption]
  norm_num [stoneGeary]

/-- Utility in closed form: `2 √(1 + c)`. -/
theorem stoneGeary_u_eq (c : ℝ) : stoneGeary.u c = 2 * Real.sqrt (1 + c) := by
  rw [stoneGeary_u]
  simp only [haraUtility]
  exact crraUtility_half _

theorem stoneGeary_u_maxConsumption : stoneGeary.u stoneGeary.maxConsumption = 4 := by
  rw [stoneGeary_maxConsumption, stoneGeary_u_eq]
  rw [show (1 : ℝ) + 3 = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

theorem stoneGeary_u_minConsumption_bounds :
    3 ≤ stoneGeary.u stoneGeary.minConsumption ∧ stoneGeary.u stoneGeary.minConsumption ≤ 4 := by
  rw [stoneGeary_minConsumption, stoneGeary_u_eq]
  constructor
  · have := le_sqrt_of_sq (x := (1 : ℝ) + 3 / 2) (c := 3 / 2) (by norm_num) (by norm_num)
    linarith
  · have := sqrt_le_of_sq (x := (1 : ℝ) + 3 / 2) (c := 2) (by norm_num) (by norm_num)
    linarith

/-- Utility at zero consumption is `2`, not `0`: this is genuinely a SHIFTED CRRA. -/
theorem stoneGeary_u_zero : stoneGeary.u 0 = 2 := by
  rw [stoneGeary_u_eq]
  norm_num

/-- **It is not CRRA.** Every CRRA with `γ < 1` vanishes at zero consumption; this does not. -/
theorem stoneGeary_ne_crra {γ : ℝ} (hγ : γ < 1) : stoneGeary.u ≠ crraUtility γ := by
  intro h
  have hz := congrFun h 0
  rw [stoneGeary_u_zero, crraUtility_zero hγ] at hz
  norm_num at hz

/-! ### The two inequalities -/

theorem stoneGeary_oscSpread_le : stoneGeary.oscSpread ≤ 2 := by
  have hmax := stoneGeary_u_maxConsumption
  have hmin := stoneGeary_u_minConsumption_bounds
  simp only [IncomeFluctuation.oscSpread, hmax, stoneGeary_discount]
  rw [div_le_iff₀ (by norm_num)]
  linarith [hmin.1]

theorem stoneGeary_floor_cond :
    (stoneGeary.discount : ℝ) * stoneGeary.oscSlopeConst stoneGeary.oscSpread
      < ((1 : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
  have hosc := stoneGeary_oscSpread_le
  have hosc0 := stoneGeary.oscSpread_nonneg
  have hrhs : ((1 : ℝ) + 1) ^ (-(1 / 2) : ℝ) = (Real.sqrt 2)⁻¹ := by
    rw [show (1 : ℝ) + 1 = 2 from by norm_num]
    exact rpow_neg_half (by norm_num)
  have hs2 : Real.sqrt 2 ≤ 2 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hhalf : (1 : ℝ) / 2 ≤ (Real.sqrt 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs2pos]
    linarith
  simp only [IncomeFluctuation.oscSlopeConst, stoneGeary_minConsumption, stoneGeary_discount,
    hrhs]
  nlinarith [hosc, hosc0, hhalf]

theorem stoneGeary_cap_cond :
    (0 : ℝ) + 4 * (stoneGeary.discount : ℝ)
        * (max |stoneGeary.toExtended.rewardMin| |stoneGeary.toExtended.rewardMax|
            / (1 - stoneGeary.discount))
        / ((1 : ℝ) + stoneGeary.maxConsumption) ^ (-(1 / 2) : ℝ) < 1 := by
  have hmax := stoneGeary_u_maxConsumption
  have hmin := stoneGeary_u_minConsumption_bounds
  have hrmin : |stoneGeary.toExtended.rewardMin| ≤ 4 := by
    have he : stoneGeary.toExtended.rewardMin = stoneGeary.u stoneGeary.minConsumption := rfl
    rw [he, abs_of_nonneg (by linarith [hmin.1])]
    exact hmin.2
  have hrmax : |stoneGeary.toExtended.rewardMax| ≤ 4 := by
    have he : stoneGeary.toExtended.rewardMax = stoneGeary.u stoneGeary.maxConsumption := rfl
    rw [he, hmax]
    norm_num
  have hm : ((1 : ℝ) + stoneGeary.maxConsumption) ^ (-(1 / 2) : ℝ) = 1 / 2 := by
    rw [stoneGeary_maxConsumption, show (1 : ℝ) + 3 = 4 from by norm_num,
      rpow_neg_half (by norm_num), show (4 : ℝ) = 2 ^ 2 from by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  have hmaxle : max |stoneGeary.toExtended.rewardMin| |stoneGeary.toExtended.rewardMax| ≤ 4 :=
    max_le hrmin hrmax
  have hmax0 : (0 : ℝ) ≤ max |stoneGeary.toExtended.rewardMin| |stoneGeary.toExtended.rewardMax| :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  rw [hm, stoneGeary_discount, zero_add]
  have hdiv : max |stoneGeary.toExtended.rewardMin| |stoneGeary.toExtended.rewardMax|
      / (1 - (1 : ℝ) / 1000) ≤ 5 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  rw [div_lt_one (by norm_num)]
  nlinarith [hdiv, hmax0]

/-- **Carroll and Kimball at a Stone–Geary calibration, with nothing assumed.** A second
non-CRRA economy — the other branch of HARA from `caraCal` — whose consumption function is
concave outright. -/
theorem stoneGeary_concaveOn_consumptionFn (z : Fin 2) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (stoneGeary.consumptionFn z) :=
  stoneGeary.concaveOn_consumptionFn_of_hara (γ := 1 / 2) (η := 1) (δ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [stoneGeary_discount]; norm_num) stoneGeary_bounded rfl
    stoneGeary_floor_cond stoneGeary_cap_cond z

end LeanEconomics
