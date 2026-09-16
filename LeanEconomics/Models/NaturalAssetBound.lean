/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.ConsumptionFloor
import LeanEconomics.Models.IncomeFluctuationLipschitz

/-!
# A natural asset bound for log utility

`exists_decline_of_consumption_lower_bound` turns a LINEAR lower bound on consumption into the
statement that assets above an explicit threshold decline — the natural asset bound, which is
what `assetCap` has been standing in for, and what
`not_concaveOn_consumptionFn_of_cap_binds` says has to hold before the Carroll–Kimball
hypothesis is even true. Its input, the linear bound, has been missing. This file supplies it
for log utility.

## The argument is the crudest possible deviation

Saving nothing is always feasible. Comparing the optimum with it,

  `u (resources) + β · cont 0 ≤ u (consumption) + β · cont (policy)`,

so `u resources - u consumption ≤ β (cont (policy) - cont 0) ≤ 2 β ‖V‖`. For LOG utility that
reads `log (resources / consumption) ≤ 2 β ‖V‖`, which is a linear bound outright:

  `consumption ≥ exp (-2 β ‖V‖) · resources`.

## Why this works for log and for nothing else

The deviation is informative only because log is UNBOUNDED ABOVE, so `u resources` grows without
limit and drags `u consumption` up with it. With CRRA `γ > 1` utility is bounded above, the same
comparison gives only `c^(1-γ)` bounded, hence a constant floor and no linear bound at all — the
crude deviation says nothing about rich households. That is another face of the same split
`crra_pinch` found, and it is the case the structure leaves us with anyway.

## What is honest about the constant

`exp (-2 β ‖V‖)` is very lossy. The sharp constant is Ma and Toda's asymptotic MPC
`c̄ = 1 - (β R^(1-γ))^(1/γ)`, at which the decline condition becomes exactly `β R < 1`
(`one_sub_mpc_mul_of_asymptotic`). Getting it needs the Euler equation, hence the envelope
condition, hence the machinery that `IncomeFluctuationEnvelope` supplies only under side
conditions. So the bound proved here is qualitatively right and quantitatively weak: it
establishes a natural asset bound, but only for interest rates small relative to `exp (-2 β ‖V‖)`,
where the sharp argument would ask only for impatience.
-/

open Set Filter Topology

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ}
variable (P : IncomeFluctuation Z assetCap)

/-- The slack in the "save nothing" comparison: twice the size of the value function, discounted. -/
noncomputable def deviationGap : ℝ := 2 * P.discount * ‖P.toExtended.valueFunction‖

theorem deviationGap_nonneg : 0 ≤ P.deviationGap := by
  have : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have := norm_nonneg P.toExtended.valueFunction
  simp only [deviationGap]
  positivity

/-- **The optimum beats saving nothing, so utility cannot fall far short of the utility of
eating everything.** This holds for any utility function; it is the log case that turns it into
a linear bound. -/
theorem utility_resources_sub_le {a : ℝ} (ha : a ∈ Icc 0 assetCap) (z : Z) :
    P.u (P.resources (a, z)) - P.u (P.consumptionFn z a) ≤ P.deviationGap := by
  have hmem0 : (0 : ℝ) ∈ P.toExtended.feasible (a, z) := ⟨le_rfl, le_max_left _ _⟩
  have hc0 : 0 < P.consumption (a, z) 0 := by
    simpa only [consumption, sub_zero] using P.resources_pos (a, z)
  have hopt := P.objR_le_of_mem ha hmem0 hc0
  simp only [objR, consumption, sub_zero] at hopt
  have hb1 := abs_le.mp (P.abs_cont_le z (P.policy (a, z)))
  have hb2 := abs_le.mp (P.abs_cont_le z 0)
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hgap : (P.discount : ℝ) * (P.cont z (P.policy (a, z)) - P.cont z 0) ≤ P.deviationGap := by
    simp only [deviationGap]
    nlinarith [hb1.2, hb2.1, hβ]
  simp only [consumptionFn, consumption]
  nlinarith [hopt, hgap]

/-- **A linear lower bound on consumption, for log utility.** The one place the development gets
a bound that scales with resources rather than being a constant. -/
theorem log_consumption_linear_lower_bound (hu : P.u = Real.log) {a : ℝ}
    (ha : a ∈ Icc 0 assetCap) (z : Z) :
    Real.exp (-P.deviationGap) * P.resources (a, z) ≤ P.consumptionFn z a := by
  have hm : 0 < P.resources (a, z) := P.resources_pos (a, z)
  have hc : 0 < P.consumptionFn z a := P.consumptionFn_pos ha z
  have hkey := P.utility_resources_sub_le ha z
  rw [hu] at hkey
  have hdiv : Real.log (P.resources (a, z) / P.consumptionFn z a) ≤ P.deviationGap := by
    rw [Real.log_div hm.ne' hc.ne']
    exact hkey
  have hle : P.resources (a, z) / P.consumptionFn z a ≤ Real.exp P.deviationGap :=
    (Real.log_le_iff_le_exp (by positivity)).mp hdiv
  rw [div_le_iff₀ hc] at hle
  rw [Real.exp_neg]
  rw [inv_mul_le_iff₀ (Real.exp_pos _)]
  linarith

/-- **The natural asset bound for log utility.** Assets above an explicit threshold decline, so
the household never accumulates without limit and the asset cap can be justified rather than
imposed.

The hypothesis on the interest rate is the price of the crude constant: the sharp argument would
ask only for `β (1 + r) < 1`. -/
theorem exists_natural_asset_bound_log (hu : P.u = Real.log) (z : Z)
    (hr : (1 - Real.exp (-P.deviationGap)) * (1 + P.interest) < 1) :
    ∃ ā : ℝ, ∀ a ∈ Icc (0 : ℝ) assetCap, ā < a → P.policy (a, z) < a :=
  P.exists_decline_of_consumption_lower_bound hr
    fun _ ha => P.log_consumption_linear_lower_bound hu ha z

/-! ### The other half of exhaustion: the corner, for log

`exists_decline_of_consumption_lower_bound` gives assets falling above a threshold. The ergodic
argument also needs the constraint to BIND below one — `policy = 0` on `[0, a₀]` at the bad income
state — and `policy_eq_zero_of_corner_at` supplies that from two explicit constants: a Lipschitz
bound `L` on the value function and a lower bound `m` on the secant slope of `u`, with `β L < m`.

Both are computable for log. The secant slope of `log` on `(0, R]` is at least `1/R`, from
`log x ≤ x - 1`. The Lipschitz constant is the fixed point of the operator's own estimate,
`L = K (1+r) / (1 - β(1+r))` with `K = slopeBound log minIncome = 2 log 2 / minIncome`, so `β L < m`
reads

  `resources · β · 2 log 2 (1+r) / (minIncome (1 - β(1+r)))  <  1`,

a condition on the state's resources alone. Since resources at the bad state are
`minIncome + (1+r) a`, it cuts out an interval of low assets — exactly what the ergodic argument
wants, and exactly why the condition has to be state-dependent rather than global. -/

/-- The secant slope of `log` on `(0, R]` is at least `1 / R`. -/
theorem log_marginal_bound {R : ℝ} (hR : 0 < R) {c d : ℝ} (hd : 0 < d) (hdc : d ≤ c)
    (hcR : c ≤ R) : 1 / R * (c - d) ≤ Real.log c - Real.log d := by
  have hc : 0 < c := lt_of_lt_of_le hd hdc
  have hkey : Real.log (d / c) ≤ d / c - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hd hc)
  rw [Real.log_div hd.ne' hc.ne'] at hkey
  have hstep : (c - d) / c ≤ Real.log c - Real.log d := by
    rw [sub_div, div_self hc.ne']
    linarith
  refine le_trans ?_ hstep
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hR hc]
  nlinarith [sub_nonneg.mpr hdc]

/-- The slope bound of `log` at the income floor, in closed form. -/
theorem log_slopeBoundU (hu : P.u = Real.log) :
    P.slopeBoundU = 2 * Real.log 2 / P.minIncome := by
  have hm := P.minIncome_pos
  simp only [slopeBoundU, slopeBound, hu]
  rw [← Real.log_div hm.ne' (by positivity), show P.minIncome / (P.minIncome / 2) = 2 by
    field_simp]
  field_simp

/-- The Lipschitz constant the operator's own estimate is a fixed point of. -/
noncomputable def logLipschitz : ℝ :=
  2 * Real.log 2 / P.minIncome * (1 + P.interest) / (1 - P.discount * (1 + P.interest))

theorem logLipschitz_nonneg (hβR : P.discount * (1 + P.interest) < 1) :
    0 ≤ P.logLipschitz := by
  have hm := P.minIncome_pos
  have hr := P.interest_gt_neg_one
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine div_nonneg (by positivity) (by linarith)

/-- **The value function is Lipschitz with the explicit log constant.** -/
theorem log_valueFunction_lipschitz (hu : P.u = Real.log)
    (hβR : P.discount * (1 + P.interest) < 1) :
    ∀ z : Z, ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ y ∈ Icc (0 : ℝ) assetCap,
      |P.toExtended.valueFunction (x, z) - P.toExtended.valueFunction (y, z)|
        ≤ P.logLipschitz * |x - y| := by
  refine P.valueFunction_lipschitz (P.logLipschitz_nonneg hβR) (le_of_eq ?_)
  have hne : (1 : ℝ) - P.discount * (1 + P.interest) ≠ 0 := by linarith
  simp only [logLipschitz, P.log_slopeBoundU hu]
  field_simp
  ring

/-- **The borrowing constraint binds where resources are small**, with an explicit threshold in
the primitives. -/
theorem log_policy_eq_zero_of_resources (hu : P.u = Real.log)
    (hβR : P.discount * (1 + P.interest) < 1) {s : ℝ × Z} (hs : s.1 ∈ Icc (0 : ℝ) assetCap)
    (hlt : P.discount * P.logLipschitz < 1 / P.resources s) :
    P.policy s = 0 :=
  P.policy_eq_zero_of_corner_at (P.log_valueFunction_lipschitz hu hβR) hs
    (fun c d hd hdc hc => by
      rw [hu]; exact log_marginal_bound (P.resources_pos s) hd hdc hc)
    hlt



end IncomeFluctuation

/-- **The bound is not vacuous.** At `r = 0` the interest-rate hypothesis holds automatically,
since `exp` is positive, so the log witness has a natural asset bound outright. -/
theorem logImpatient_natural_asset_bound (z : Fin 2) :
    ∃ ā : ℝ, ∀ a ∈ Icc (0 : ℝ) 1, ā < a → logImpatient.policy (a, z) < a := by
  refine logImpatient.exists_natural_asset_bound_log logImpatient_u z ?_
  have hpos := Real.exp_pos (-logImpatient.deviationGap)
  have hint : logImpatient.interest = 0 := rfl
  rw [hint]
  linarith


end LeanEconomics
