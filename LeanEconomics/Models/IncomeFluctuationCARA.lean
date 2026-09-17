/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationEuler
import LeanEconomics.Models.CARA
import LeanEconomics.Models.BoundedIncomeFluctuation
import LeanEconomics.Analysis.SoftMin

/-!
# Carroll and Kimball for CARA: the other branch of HARA

`IncomeFluctuationHARA` covers the `b ≠ 0` branch, `u c = crraUtility γ (η + c)`, where the
Euler equation makes consumption a multiple of a POWER MEAN of next period's consumptions. The
`b = 0` branch is CARA, and it is not a limit of that argument: with `u' c = exp (-α c)` the
Euler equation

  `exp (-α c) = β R · ∑ π exp (-α c')`

makes consumption a TRANSLATE of the soft minimum,

  `c = -(1/α) log (β R) + softMin π α c'`,

and what carries the induction is the concavity of that aggregator rather than of a power mean.
`Analysis.SoftMin` supplies it, from Hölder's inequality — equivalently, convexity of
log-sum-exp.

## What is the same and what is different

The same: the endogenous-gridpoint transfer (`concaveOn_of_egm`) is untouched, because it is
about writing the budget against end-of-period assets and knows nothing about preferences. So
once the aggregator is concave and nondecreasing the induction step is the CRRA proof verbatim.

Different: no positivity. The power mean is defined only for positive arguments and the CRRA
machinery carries positive consumption through every step; the soft minimum is defined for
consumptions of either sign. Positivity is still ASSUMED here, because `euler_eq` needs it for
the derivative of the reward at an interior optimum, but the aggregator does not.

Also different: CARA is outside Light's uniqueness condition, since relative risk aversion `α c`
is unbounded (`not_monotoneOn_mul_deriv_caraUtility`). Carroll–Kimball and uniqueness are
separate requirements, and this file is about the first.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **The endogenous-gridpoint map for CARA**: a translate of the soft minimum of next period's
consumptions. -/
noncomputable def caraEgmMap (v : (ℝ × Z) →ᵇ ℝ) (α : ℝ) (z : Z) (A : ℝ) : ℝ :=
  softMin (P.transitionMatrix z) α (fun z' => P.consumptionFnOf v z' A)
    - (1 / α) * Real.log ((P.discount : ℝ) * (1 + P.interest))

theorem concaveOn_caraEgmMap {α : ℝ} (hα : 0 < α) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z')) :
    ConcaveOn ℝ (Icc assetFloor assetCap) (P.caraEgmMap v α z) := by
  have hmean := concaveOn_softMin_comp (convex_Icc assetFloor assetCap) hα
    (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z)
    (f := fun z' a => P.consumptionFnOf v z' a) hconc
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  have hstep := hmean.2 hx hy hθ hφ hθφ
  simp only [smul_eq_mul] at hstep ⊢
  simp only [caraEgmMap]
  have hk : θ * ((1 / α) * Real.log ((P.discount : ℝ) * (1 + P.interest)))
      + φ * ((1 / α) * Real.log ((P.discount : ℝ) * (1 + P.interest)))
      = (1 / α) * Real.log ((P.discount : ℝ) * (1 + P.interest)) := by
    rw [← add_mul, hθφ, one_mul]
  linarith [hstep, hk]

theorem monotoneOn_caraEgmMap {α : ℝ} (hα : 0 < α) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap)) :
    MonotoneOn (P.caraEgmMap v α z) (Icc assetFloor assetCap) := by
  have hmean := monotoneOn_softMin_comp (D := Icc assetFloor assetCap) hα
    (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z)
    (f := fun z' a => P.consumptionFnOf v z' a) hmono
  intro x hx y hy hxy
  simp only [caraEgmMap]
  linarith [hmean hx hy hxy]

/-- **The Euler equation puts consumption on the endogenous grid**, for CARA. -/
theorem cara_egm_of_euler {α : ℝ} (hα : 0 < α) (hβ : 0 < (P.discount : ℝ))
    {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (heuler : Real.exp (-α * P.consumptionFnOf (P.toExtended.bellman v) z a)
      = (P.discount : ℝ) * ((1 + P.interest)
        * ∑ z' : Z, P.transitionMatrix z z'
            * Real.exp (-α * P.consumptionFnOf v z' A))) :
    P.consumptionFnOf (P.toExtended.bellman v) z a = P.caraEgmMap v α z A := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hK : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hS : (0 : ℝ) < ∑ z' : Z, P.transitionMatrix z z'
      * Real.exp (-α * P.consumptionFnOf v z' A) :=
    sum_exp_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) α _
  have hlog := congrArg Real.log heuler
  rw [Real.log_exp, show (P.discount : ℝ) * ((1 + P.interest)
      * ∑ z' : Z, P.transitionMatrix z z' * Real.exp (-α * P.consumptionFnOf v z' A))
      = ((P.discount : ℝ) * (1 + P.interest))
        * ∑ z' : Z, P.transitionMatrix z z' * Real.exp (-α * P.consumptionFnOf v z' A) from by
      ring, Real.log_mul (ne_of_gt hK) (ne_of_gt hS)] at hlog
  simp only [caraEgmMap, softMin]
  have hαne : α ≠ 0 := ne_of_gt hα
  field_simp at hlog ⊢
  linarith

/-- **The Euler hypothesis discharged**, for CARA: interiority is all that is left. -/
theorem cara_egmMap_consumptionFnOf {α : ℝ} (hα : 0 < α) (hβ : 0 < (P.discount : ℝ))
    (hu : P.u = caraUtility α) {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hA0 : assetFloor < A) (hAmax : A < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hint' : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z'))
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A) :
    P.consumptionFnOf (P.toExtended.bellman v) z a = P.caraEgmMap v α z A := by
  have hd : HasDerivAt P.u (Real.exp (-α * P.consumptionFnOf (P.toExtended.bellman v) z a))
      (P.consumptionFnOf (P.toExtended.bellman v) z a) := by
    rw [hu]; exact hasDerivAt_caraUtility (ne_of_gt hα) _
  have hd' : ∀ z' : Z, HasDerivAt P.u (Real.exp (-α * P.consumptionFnOf v z' A))
      (P.consumptionFnOf v z' A) := fun z' => by
    rw [hu]; exact hasDerivAt_caraUtility (ne_of_gt hα) _
  exact P.cara_egm_of_euler hα hβ (P.euler_eq ha hA hA0 hAmax hint' hc hd hc' hd')

/-- **Carroll and Kimball (1996), the induction step for CARA.** Given the Euler equation, the
Bellman operator carries a concave consumption function to a concave one. -/
theorem concaveOn_consumptionFnOf_bellman_of_cara_euler {α : ℝ} (hα : 0 < α)
    {v : (ℝ × Z) →ᵇ ℝ}
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap)) (z : Z)
    (hEuler : ∀ a ∈ Icc assetFloor assetCap,
      P.consumptionFnOf (P.toExtended.bellman v) z a
        = P.caraEgmMap v α z (P.policyOf (P.toExtended.bellman v) (a, z))) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_of_egm (z := z) (g := fun a => P.policyOf (P.toExtended.bellman v) (a, z))
    (C := P.caraEgmMap v α z) (P.concaveOn_caraEgmMap hα z hconc)
    (strictMonoOn_add_egm (P.monotoneOn_caraEgmMap hα z hmono))
    (fun a _ => P.feasible_subset_region (P.policyOf_mem _ (a, z))) (fun a ha => ?_)
    (fun a ha => hEuler a ha)
  rw [← hEuler a ha]
  have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
    simp only [resources, max_eq_right ha.1]
  simp only [consumptionFnOf, consumption, hres]
  ring

/-- **The induction step for CARA, with the Euler equation proved.** What is assumed is
interiority, a property of the state, not of the model — the same hypothesis the CRRA and
shifted-CRRA versions carry. -/
theorem concaveOn_consumptionFnOf_bellman_of_cara {α : ℝ} (hα : 0 < α)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = caraUtility α) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap))
    (hcpos : ∀ a ∈ Icc assetFloor assetCap,
      0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hint : ∀ a ∈ Icc assetFloor assetCap, P.EulerInterior v z a) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_consumptionFnOf_bellman_of_cara_euler hα hconc hmono z fun a ha => ?_
  obtain ⟨hA0, hAmax, hint'⟩ := hint a ha
  exact P.cara_egmMap_consumptionFnOf hα hβ hu ha rfl hA0 hAmax (hcpos a ha) hint'
    (fun z' => hpos z' _ (P.feasible_subset_region (P.policyOf_mem _ (a, z))))

end IncomeFluctuation

/-! ### A capped model with CARA utility exists

`Analysis.HARA` set the CARA branch aside, saying no capped model admits it. That is not so: on
`Ici 0` CARA is bounded on both sides — `u 0 = -1/α` and `u c ↗ 0` — which is exactly what the
extended program asks for. The witness below is `nearLog`'s calibration with CARA preferences,
and it type-checks, which is the whole claim.

What DOES exclude CARA is Light's condition, not boundedness:
`not_monotoneOn_mul_deriv_caraUtility`. -/

/-- **A capped income-fluctuation model with CARA utility.** -/
noncomputable def caraWitness : IncomeFluctuation (Fin 2) 0 1 where
  income z := if z = 0 then 1 / 100 else 1
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 8
  u := caraUtility 1
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
  continuousOn_u_dom := (continuous_caraUtility one_ne_zero).continuousOn
  monotoneOn_u_dom := monotoneOn_caraUtility one_pos _
  strictConcaveOn_u_dom := (strictConcaveOn_caraUtility one_pos).subset (subset_univ _)
    (convex_Ici 0)
  continuousOn_extendDom :=
    continuousOn_extendDom_Ici (continuous_caraUtility one_ne_zero).continuousOn

@[simp] theorem caraWitness_u : caraWitness.u = caraUtility 1 := rfl

theorem caraWitness_bounded : caraWitness.Bounded := rfl

/-- **CARA is outside Light's condition**, which is the real reason the uniqueness argument does
not reach it. -/
theorem caraWitness_not_relativeRiskAversionLeOne :
    ¬ MonotoneOn (fun c => c * Real.exp (-(1 : ℝ) * c)) (Ioi (0 : ℝ)) :=
  not_monotoneOn_mul_deriv_caraUtility one_pos

end LeanEconomics
