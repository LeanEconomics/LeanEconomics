/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.ConsumptionFloor

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
