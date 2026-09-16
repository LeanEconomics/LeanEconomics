/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.CRRAConstants
import LeanEconomics.Distribution.Uniqueness

/-!
# One CES economy where everything holds at once

`dispersed` does this for log. This is the same theorem for CES with `γ = 1/2` — square-root
utility, bounded below, and inadmissible under the old structure — reached through the CES
constants rather than the log ones.

## The parameters and why they are these

`γ = 1/2`, `β = 1/16`, `r = 0`, income `{1/5000, 1}` drawn iid with probability `1/2`, asset cap
`1/10`, deviation share `θ = 39/40`.

The three conditions pull against each other exactly as in the log case, but the trade is priced
differently.

* **Corner** (`crra_policy_eq_zero_of_resources`): `β · crraLipschitz < resources ^ (-γ)`. The
  Lipschitz constant runs on `minIncome ^ (-γ)`, so it grows like `minIncome ^ (-1/2)` rather than
  log's `1 / minIncome`. That is SLOWER, and the corner is the condition CES finds easier.
* **Decline** (`crra_policy_lt_self`): threshold `(β · oscGap / θ) · (income + (1+r-θ) cap) ^ γ`.
  With `θ` near one the second factor is nearly `income ^ γ`, so the threshold shrinks with the
  income of the state, which is what lets the corner reach it.
* **Gain** (`crra_aggregateCapital_pos_of_primitives`): here CES is strictly harder. The condition
  reduces to `income z₀ + h < (β · P z₁ z₀) ^ (1/γ) · (1 - h)`, which at `γ = 1/2` is QUADRATIC in
  the discount factor where the log condition is only logarithmic in the dispersion. A `100 : 1`
  income spread is enough for log at `β = 1/8`; at `γ = 1/2` the same job needs `5000 : 1`.

That last point is the economics, not slack in the constants: marginal utility `c ^ (-1/2)`
explodes far more slowly at zero than `1 / c` does, so the precautionary motive is weaker and the
dispersion has to make up the difference.

## Everything reduces to integers

The only transcendental input is `√2`, and only through `1 - 2 ^ (γ - 1)` in the slope bound.
Everything else is a square root of a rational compared against a rational, which is a squaring.
-/

open scoped NNReal
open Set Filter Topology MeasureTheory

namespace LeanEconomics

/-- An impatient household with CES utility at `γ = 1/2` and 5000:1 income dispersion. -/
noncomputable def cesWitness : IncomeFluctuation (Fin 2) (1 / 10) where
  income z := if z = 0 then 1 / 5000 else 1
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 16
  u := crraUtility (1 / 2)
  minIncome := 1 / 5000
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

@[simp] theorem cesWitness_u : cesWitness.u = crraUtility (1 / 2) := rfl
@[simp] theorem cesWitness_income_zero : cesWitness.income 0 = 1 / 5000 := rfl
@[simp] theorem cesWitness_income_one : cesWitness.income 1 = 1 := rfl
@[simp] theorem cesWitness_interest : cesWitness.interest = 0 := rfl
@[simp] theorem cesWitness_discount : (cesWitness.discount : ℝ) = 1 / 16 := rfl
@[simp] theorem cesWitness_minIncome : cesWitness.minIncome = 1 / 5000 := rfl
@[simp] theorem cesWitness_maxIncome : cesWitness.maxIncome = 1 := rfl
@[simp] theorem cesWitness_transitionMatrix (z z' : Fin 2) :
    cesWitness.transitionMatrix z z' = 1 / 2 := rfl

theorem cesWitness_bounded : cesWitness.Bounded := rfl

theorem cesWitness_maxConsumption : cesWitness.maxConsumption = 11 / 10 := by
  simp only [IncomeFluctuation.maxConsumption, cesWitness_maxIncome, cesWitness_interest]
  norm_num

theorem cesWitness_resources {a : ℝ} (ha : 0 ≤ a) (z : Fin 2) :
    cesWitness.resources (a, z) = cesWitness.income z + a := by
  simp only [IncomeFluctuation.resources, cesWitness_interest, max_eq_right ha]
  ring

/-- **Positive consumption, from the margin.** `sqrtCES`'s argument, at these parameters. -/
theorem cesWitness_positiveConsumption : cesWitness.PositiveConsumption :=
  cesWitness.positiveConsumption_of_bounded_crra (by norm_num) (by norm_num) rfl rfl

/-! ### Square roots

At `γ = 1/2` every `rpow` in the CES constants is a square root, so every numeric obligation is a
squaring. These two rewrites are the whole bridge. -/

theorem crraUtility_half (c : ℝ) : crraUtility (1 / 2) c = 2 * Real.sqrt c := by
  rw [crraUtility_of_ne (by norm_num), Real.sqrt_eq_rpow,
    show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num]
  ring

theorem rpow_half (x : ℝ) : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm

theorem rpow_neg_half {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 / 2) : ℝ) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

theorem sqrt_le_of_sq {x c : ℝ} (hc : 0 ≤ c) (h : x ≤ c ^ 2) : Real.sqrt x ≤ c := by
  rw [show c = Real.sqrt (c ^ 2) from (Real.sqrt_sq hc).symm]
  exact Real.sqrt_le_sqrt h

/-! ### The size of the value function -/

/-- The oscillation gap, bounded by dropping the (nonnegative) floor term and rounding
`√(11/10)` up to `21/20`. -/
theorem cesWitness_oscGap_le : cesWitness.oscGap ≤ 56 / 25 := by
  have h1 : Real.sqrt (11 / 10) ≤ 21 / 20 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) ≤ Real.sqrt (1 / 5000) := Real.sqrt_nonneg _
  simp only [IncomeFluctuation.oscGap, cesWitness_u, cesWitness_maxConsumption,
    cesWitness_minIncome, cesWitness_discount, crraUtility_half]
  rw [div_le_iff₀ (by norm_num)]
  nlinarith [h1, h2]

theorem cesWitness_oscGap_nonneg : 0 ≤ cesWitness.oscGap := cesWitness.oscGap_nonneg

/-! ### The decline half

Above `1/128` the household in the bad income state runs its assets down. -/

theorem cesWitness_decline {a : ℝ} (ha : a ∈ Icc (1 / 128 : ℝ) (1 / 10)) :
    cesWitness.policy (a, 0) < a := by
  have hmem : a ∈ Icc (0 : ℝ) (1 / 10) := ⟨by linarith [ha.1], ha.2⟩
  refine cesWitness.crra_policy_lt_self (γ := 1 / 2) (θ := 39 / 40) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) rfl rfl cesWitness_positiveConsumption hmem 0 ?_
  have hosc := cesWitness_oscGap_le
  have hosc0 := cesWitness_oscGap_nonneg
  have harg : cesWitness.income 0 + (1 + cesWitness.interest - 39 / 40) * (1 / 10)
      = 27 / 10000 := by
    simp only [cesWitness_income_zero, cesWitness_interest]; norm_num
  rw [harg, rpow_half]
  have hs : Real.sqrt (27 / 10000) ≤ 53 / 1000 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt (27 / 10000) := Real.sqrt_nonneg _
  have hcoef : ((cesWitness.discount : ℝ)) * cesWitness.oscGap / (39 / 40) ≤ 28 / 195 := by
    rw [cesWitness_discount, div_le_iff₀ (by norm_num)]
    linarith [hosc]
  have hcoef0 : (0 : ℝ) ≤ ((cesWitness.discount : ℝ)) * cesWitness.oscGap / (39 / 40) := by
    rw [cesWitness_discount]; positivity
  calc ((cesWitness.discount : ℝ)) * cesWitness.oscGap / (39 / 40) * Real.sqrt (27 / 10000)
      ≤ (28 / 195) * (53 / 1000) := by nlinarith [hcoef, hs, hs0, hcoef0]
    _ < 1 / 128 := by norm_num
    _ ≤ a := ha.1

/-! ### The corner half

Below `1/128` the borrowing constraint binds in the bad income state. The Lipschitz constant runs
on `minIncome ^ (-1/2) = √5000`, where the log constant would run on `1 / minIncome = 5000`; that
slower growth is why the corner is the condition CES finds easy. -/

theorem cesWitness_crraLipschitz_le : cesWitness.crraLipschitz (1 / 2) ≤ 377152 / 4245 := by
  have h2 : Real.sqrt 2 ≤ 1415 / 1000 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (200 : ℝ) / 283 ≤ (Real.sqrt 2)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ h2pos]
    nlinarith [h2]
  have hmpos : (0 : ℝ) < Real.sqrt (1 / 5000) := Real.sqrt_pos.mpr (by norm_num)
  have hm : (1 : ℝ) / 71 ≤ Real.sqrt (1 / 5000) := by
    rw [show (1 : ℝ) / 71 = Real.sqrt ((1 / 71) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hminv : (Real.sqrt (1 / 5000))⁻¹ ≤ 71 := by
    rw [inv_eq_one_div, div_le_iff₀ hmpos]
    nlinarith [hm]
  have hinv1 : (Real.sqrt 2)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one h2pos]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), h2pos]
  simp only [IncomeFluctuation.crraLipschitz, cesWitness_minIncome, cesWitness_interest,
    cesWitness_discount, crraSlopeBound, show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num,
    rpow_neg_half (show (0:ℝ) ≤ 1 / 5000 by norm_num), ← Real.sqrt_eq_rpow]
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith [hminv, hinv, hinv1, hmpos, h2pos, inv_nonneg.mpr hmpos.le]

theorem cesWitness_corner {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (1 / 128)) :
    cesWitness.policy (a, 0) = 0 := by
  have hmem : a ∈ Icc (0 : ℝ) (1 / 10) := ⟨ha.1, by linarith [ha.2]⟩
  refine cesWitness.crra_policy_eq_zero_of_resources (γ := 1 / 2) (by norm_num) (by norm_num)
    rfl rfl (by norm_num) hmem ?_
  have hres : cesWitness.resources (a, 0) = 1 / 5000 + a := by
    rw [cesWitness_resources ha.1, cesWitness_income_zero]
  have hres0 : (0 : ℝ) < 1 / 5000 + a := by linarith [ha.1]
  rw [hres, rpow_neg_half hres0.le]
  have hsq : Real.sqrt (1 / 5000 + a) ≤ 9 / 100 :=
    sqrt_le_of_sq (by norm_num) (by nlinarith [ha.2])
  have hspos : (0 : ℝ) < Real.sqrt (1 / 5000 + a) := Real.sqrt_pos.mpr hres0
  have hge : (100 : ℝ) / 9 ≤ (Real.sqrt (1 / 5000 + a))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hspos]
    nlinarith [hsq]
  have hlip := cesWitness_crraLipschitz_le
  rw [cesWitness_discount]
  nlinarith [hlip, hge]

/-! ### Everything at once -/

theorem cesWitness_exists_exhaust :
    ∃ N : ℕ, (cesWitness.gBad 0)^[N] cesWitness.topState = cesWitness.botState :=
  cesWitness.exists_exhaust_of_decline (a₀ := 1 / 128) (by norm_num) (by norm_num)
    (fun a ha => cesWitness_corner ha) (fun a ha => cesWitness_decline ha)

/-- **A unique stationary agent distribution**, for CES with `γ = 1/2`. -/
theorem cesWitness_existsUnique_isStationary :
    ∃! μ : ProbabilityMeasure cesWitness.State, cesWitness.IsStationary μ := by
  obtain ⟨N, hN⟩ := cesWitness_exists_exhaust
  exact cesWitness.existsUnique_isStationary (z₀ := 0) (N := N) (fun z => by norm_num) hN

/-- **Strictly positive aggregate capital.** The saving is purely precautionary: `β (1 + r) =
1/16 < 1`, so the household is impatient and holds assets only against the bad draw. -/
theorem cesWitness_aggregateCapital_pos {μ : ProbabilityMeasure cesWitness.State}
    (hμ : cesWitness.IsStationary μ) : 0 < cesWitness.aggregateCapital μ := by
  refine cesWitness.crra_aggregateCapital_pos_of_primitives (γ := 1 / 2) (by norm_num)
    (by norm_num) rfl cesWitness_positiveConsumption hμ
    (z₁ := 1) (z₀ := 0) (p₀ := 1 / 2) (by norm_num) (fun z => by norm_num)
    (h := 1 / 100000) (by norm_num) (by norm_num) (by norm_num) ?_
  simp only [cesWitness_income_zero, cesWitness_income_one, cesWitness_interest,
    cesWitness_discount, cesWitness_transitionMatrix]
  rw [show (1 : ℝ) - 1 / 100000 = 99999 / 100000 from by norm_num,
    show (1 : ℝ) / 5000 + (1 + 0) * (1 / 100000) = 21 / 100000 from by norm_num,
    rpow_neg_half (show (0:ℝ) ≤ 99999 / 100000 by norm_num),
    rpow_neg_half (show (0:ℝ) ≤ 21 / 100000 by norm_num)]
  have hA : (0 : ℝ) < Real.sqrt (99999 / 100000) := Real.sqrt_pos.mpr (by norm_num)
  have hB : (0 : ℝ) < Real.sqrt (21 / 100000) := Real.sqrt_pos.mpr (by norm_num)
  have hAsq : Real.sqrt (99999 / 100000) ^ 2 = 99999 / 100000 :=
    Real.sq_sqrt (by norm_num)
  have hBsq : Real.sqrt (21 / 100000) ^ 2 = 21 / 100000 := Real.sq_sqrt (by norm_num)
  -- the whole condition is `1024 · 21 < 99999`
  have hkey : 32 * Real.sqrt (21 / 100000) < Real.sqrt (99999 / 100000) := by
    nlinarith [hAsq, hBsq, hA, hB]
  have hinvA : (Real.sqrt (99999 / 100000))⁻¹ * Real.sqrt (99999 / 100000) = 1 :=
    inv_mul_cancel₀ hA.ne'
  have hinvB : (Real.sqrt (21 / 100000))⁻¹ * Real.sqrt (21 / 100000) = 1 :=
    inv_mul_cancel₀ hB.ne'
  have h32B : (0 : ℝ) < 32 * Real.sqrt (21 / 100000) := by positivity
  have hmain : (Real.sqrt (99999 / 100000))⁻¹ < 1 / 32 * (Real.sqrt (21 / 100000))⁻¹ := by
    rw [show (1 / 32 : ℝ) * (Real.sqrt (21 / 100000))⁻¹
        = (32 * Real.sqrt (21 / 100000))⁻¹ from by rw [mul_inv]; ring,
      inv_lt_inv₀ hA h32B]
    exact hkey
  nlinarith [hmain]

/-- Utility is FINITE at zero consumption. -/
theorem cesWitness_u_zero : cesWitness.u 0 = 0 := crraUtility_zero (by norm_num)

/-- **This economy is not expressible in the unbounded structure.** `dispersed` lives at
`dom = Ioi 0`; this one does not, which is exactly what `crra_pinch` used to forbid. -/
theorem cesWitness_not_unbounded : ¬ cesWitness.Unbounded := by
  intro h
  have hz : (0 : ℝ) ∈ cesWitness.dom := mem_Ici.mpr le_rfl
  rw [h] at hz
  exact absurd hz (by simp)

/-- **One CES economy, everything at once**: a unique stationary agent distribution carrying
strictly positive aggregate capital, with utility BOUNDED BELOW. -/
theorem cesWitness_unique_stationary_positive_capital :
    ∃! μ : ProbabilityMeasure cesWitness.State,
      cesWitness.IsStationary μ ∧ 0 < cesWitness.aggregateCapital μ := by
  obtain ⟨μ, hμ, huniq⟩ := cesWitness_existsUnique_isStationary
  exact ⟨μ, ⟨hμ, cesWitness_aggregateCapital_pos hμ⟩, fun ν hν => huniq ν hν.1⟩

end LeanEconomics
