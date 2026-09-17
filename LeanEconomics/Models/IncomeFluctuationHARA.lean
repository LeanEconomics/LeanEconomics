/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationEuler
import LeanEconomics.Analysis.HARA

/-!
# Carroll and Kimball beyond CRRA: the HARA induction step

`IncomeFluctuationCarrollKimball` proves the induction step for `u = crraUtility γ`, where the
Euler equation makes consumption a multiple of the power mean of next period's consumptions and
`powerMean_concave` — Kimball's risk-tolerance aggregation — does the rest. Carroll and Kimball's
theorem is not about CRRA but about HARA, and this file covers the `b ≠ 0` branch,
`u c = crraUtility γ (η + c)`: CRRA with a subsistence level, which includes CRRA itself at
`η = 0`.

## Nothing new is needed

Marginal utility is `(η + c) ^ (-γ)`, so the Euler equation reads

  `(η + C(A)) ^ (-γ) = β R · Σ_{z'} π_{z z'} (η + c_{z'}(A)) ^ (-γ)`,

which is the CRRA equation in the variable `η + c`. So the endogenous-gridpoint map is the CRRA
one applied to SHIFTED consumptions, with the shift removed at the end (`haraEgmMap`), and it is
concave for exactly the same reason: `η + c_{z'}` is concave when `c_{z'}` is, the power mean of
concave positive functions is concave, and a constant shift changes nothing.

That the shift is harmless is the content of "linear risk tolerance". Risk tolerance
`-u' / u''` is `(η + c) / γ`, affine in consumption, and Kimball's aggregation theorem needs
precisely affineness — the level `η` rides through untouched.

## What is and is not covered

The induction STEP is here, for the whole `b ≠ 0` HARA branch. What is not is the assembled
statement: the iteration also needs positive consumption and the asset cap slack, and those are
proved in `IncomeFluctuationIterate` through CRRA-specific bounds (`crra_policyOf_le_mul` and the
oscillation machinery). The CARA branch `b = 0`, where marginal utility is `exp (-α c)`, needs a
different aggregator — the soft minimum `-(1/α) log Σ π exp (-α c)` — and is not here.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **The endogenous-gridpoint map for shifted CRRA.** The CRRA map in the variable `η + c`. -/
noncomputable def haraEgmMap (v : (ℝ × Z) →ᵇ ℝ) (γ η : ℝ) (z : Z) (A : ℝ) : ℝ :=
  ((P.discount : ℝ) * (1 + P.interest)) ^ (-(1 / γ))
      * powerMean (P.transitionMatrix z) (-γ) (fun z' => η + P.consumptionFnOf v z' A) - η

@[simp] theorem haraEgmMap_zero_shift (v : (ℝ × Z) →ᵇ ℝ) (γ : ℝ) (z : Z) (A : ℝ) :
    P.haraEgmMap v γ 0 z A = P.egmMap v γ z A := by
  simp only [haraEgmMap, egmMap, zero_add, sub_zero]

theorem concaveOn_haraEgmMap {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z')) :
    ConcaveOn ℝ (Icc assetFloor assetCap) (P.haraEgmMap v γ η z) := by
  have hmean := concaveOn_powerMean_comp (convex_Icc assetFloor assetCap)
    (neg_neg_of_pos hγ) (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z)
    (f := fun z' a => η + P.consumptionFnOf v z' a)
    (fun z' A hA => by linarith [hpos z' A hA])
    (fun z' => ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => by
      have h := (hconc z').2 hx hy hθ hφ hθφ
      simp only [smul_eq_mul] at h ⊢
      nlinarith [h, hθφ]⟩)
  have hk : (0 : ℝ) ≤ ((P.discount : ℝ) * (1 + P.interest)) ^ (-(1 / γ)) :=
    Real.rpow_nonneg (mul_nonneg P.discount.coe_nonneg P.interest_gt_neg_one.le) _
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  have hstep := hmean.2 hx hy hθ hφ hθφ
  simp only [smul_eq_mul] at hstep ⊢
  simp only [haraEgmMap]
  nlinarith [mul_le_mul_of_nonneg_left hstep hk, hθφ]

theorem monotoneOn_haraEgmMap {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap)) :
    MonotoneOn (P.haraEgmMap v γ η z) (Icc assetFloor assetCap) := by
  have hmean := monotoneOn_powerMean_comp (D := Icc assetFloor assetCap)
    (neg_neg_of_pos hγ) (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z)
    (f := fun z' a => η + P.consumptionFnOf v z' a)
    (fun z' A hA => by linarith [hpos z' A hA])
    (fun z' x hx y hy hxy => by linarith [hmono z' hx hy hxy])
  intro x hx y hy hxy
  simp only [haraEgmMap]
  have := mul_le_mul_of_nonneg_left (hmean hx hy hxy)
    (Real.rpow_nonneg (mul_nonneg P.discount.coe_nonneg P.interest_gt_neg_one.le)
      (-(1 / γ)))
  linarith

/-- **The Euler equation puts consumption on the endogenous grid**, for shifted CRRA. -/
theorem hara_egm_of_euler {γ η : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (hc : 0 < η + P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hc' : ∀ z' : Z, 0 < η + P.consumptionFnOf v z' A)
    (heuler : (η + P.consumptionFnOf (P.toExtended.bellman v) z a) ^ (-γ)
      = (P.discount : ℝ) * ((1 + P.interest)
        * ∑ z' : Z, P.transitionMatrix z z' * (η + P.consumptionFnOf v z' A) ^ (-γ))) :
    P.consumptionFnOf (P.toExtended.bellman v) z a = P.haraEgmMap v γ η z A := by
  have hγn : γ ≠ 0 := ne_of_gt hγ0
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hK : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hS : (0 : ℝ)
      < ∑ z' : Z, P.transitionMatrix z z' * (η + P.consumptionFnOf v z' A) ^ (-γ) :=
    sum_rpow_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hc'
  have hprod : (η + P.consumptionFnOf (P.toExtended.bellman v) z a) ^ (-γ)
      = ((P.discount : ℝ) * (1 + P.interest))
        * ∑ z' : Z, P.transitionMatrix z z' * (η + P.consumptionFnOf v z' A) ^ (-γ) := by
    rw [heuler]; ring
  have hexp : (-γ) * (-(1 / γ)) = 1 := by field_simp
  have hinv : ((η + P.consumptionFnOf (P.toExtended.bellman v) z a) ^ (-γ)) ^ (-(1 / γ))
      = η + P.consumptionFnOf (P.toExtended.bellman v) z a := by
    rw [← Real.rpow_mul hc.le, hexp, Real.rpow_one]
  have hkey : η + P.consumptionFnOf (P.toExtended.bellman v) z a
      = ((P.discount : ℝ) * (1 + P.interest)) ^ (-(1 / γ))
        * powerMean (P.transitionMatrix z) (-γ)
          (fun z' => η + P.consumptionFnOf v z' A) := by
    rw [← hinv, hprod, Real.mul_rpow hK.le hS.le]
    simp only [powerMean]
    congr 1
    rw [show -(1 / γ) = 1 / (-γ) by field_simp]
  simp only [haraEgmMap]
  linarith

/-- **The Euler hypothesis discharged**, for shifted CRRA: interiority is all that is left. -/
theorem hara_egmMap_consumptionFnOf {γ η : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hu : P.u = haraUtility γ η) {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (hη : 0 ≤ η) (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hA0 : assetFloor < A) (hAmax : A < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hint' : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z'))
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A) :
    P.consumptionFnOf (P.toExtended.bellman v) z a = P.haraEgmMap v γ η z A := by
  have hcη : 0 < η + P.consumptionFnOf (P.toExtended.bellman v) z a := by linarith
  have hcη' : ∀ z' : Z, 0 < η + P.consumptionFnOf v z' A := fun z' => by linarith [hc' z']
  have hd : HasDerivAt P.u ((η + P.consumptionFnOf (P.toExtended.bellman v) z a) ^ (-γ))
      (P.consumptionFnOf (P.toExtended.bellman v) z a) := by
    rw [hu]; exact hasDerivAt_haraUtility γ hcη
  have hd' : ∀ z' : Z, HasDerivAt P.u ((η + P.consumptionFnOf v z' A) ^ (-γ))
      (P.consumptionFnOf v z' A) := fun z' => by
    rw [hu]; exact hasDerivAt_haraUtility γ (hcη' z')
  exact P.hara_egm_of_euler hγ0 hβ hcη hcη'
    (P.euler_eq ha hA hA0 hAmax hint' hc hd hc' hd')

/-- **Carroll and Kimball (1996), the induction step for shifted CRRA.** Given the Euler
equation, the Bellman operator carries a concave consumption function to a concave one. -/
theorem concaveOn_consumptionFnOf_bellman_of_hara_euler {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    {v : (ℝ × Z) →ᵇ ℝ}
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap)) (z : Z)
    (hEuler : ∀ a ∈ Icc assetFloor assetCap,
      P.consumptionFnOf (P.toExtended.bellman v) z a
        = P.haraEgmMap v γ η z (P.policyOf (P.toExtended.bellman v) (a, z))) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_of_egm (z := z) (g := fun a => P.policyOf (P.toExtended.bellman v) (a, z))
    (C := P.haraEgmMap v γ η z) (P.concaveOn_haraEgmMap hγ hη z hpos hconc)
    (strictMonoOn_add_egm (P.monotoneOn_haraEgmMap hγ hη z hpos hmono))
    (fun a _ => P.feasible_subset_region (P.policyOf_mem _ (a, z))) (fun a ha => ?_)
    (fun a ha => hEuler a ha)
  rw [← hEuler a ha]
  have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
    simp only [resources, max_eq_right ha.1]
  simp only [consumptionFnOf, consumption, hres]
  ring

/-- **The induction step for shifted CRRA, with the Euler equation proved**, exactly as
`concaveOn_consumptionFnOf_bellman_of_interior` does it for CRRA: what is assumed is interiority,
a property of the state, not of the model. -/
theorem concaveOn_consumptionFnOf_bellman_of_hara {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = haraUtility γ η) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap))
    (hcpos : ∀ a ∈ Icc assetFloor assetCap,
      0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hint : ∀ a ∈ Icc assetFloor assetCap, P.EulerInterior v z a) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_consumptionFnOf_bellman_of_hara_euler hγ hη hpos hconc hmono z
    fun a ha => ?_
  obtain ⟨hA0, hAmax, hint'⟩ := hint a ha
  exact P.hara_egmMap_consumptionFnOf hγ hβ hu hη ha rfl hA0 hAmax (hcpos a ha) hint'
    (fun z' => hpos z' _ (P.feasible_subset_region (P.policyOf_mem _ (a, z))))


/-- **CRRA is the `η = 0` member**, so the HARA step really does generalise the CRRA one rather
than sitting beside it. -/
theorem concaveOn_consumptionFnOf_bellman_of_crra_via_hara {γ : ℝ} (hγ : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap))
    (hcpos : ∀ a ∈ Icc assetFloor assetCap,
      0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hint : ∀ a ∈ Icc assetFloor assetCap, P.EulerInterior v z a) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) :=
  P.concaveOn_consumptionFnOf_bellman_of_hara hγ le_rfl hβ
    (by rw [hu, haraUtility_zero_shift]) z hpos hconc hmono hcpos hint

end IncomeFluctuation

end LeanEconomics
