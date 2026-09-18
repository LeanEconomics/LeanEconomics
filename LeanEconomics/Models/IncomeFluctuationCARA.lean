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

open Set Filter Topology BoundedContinuousFunction MeasureTheory

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

/-- **The Euler INEQUALITY in endogenous-gridpoint form**, for CARA: consumption never exceeds
the value the grid assigns to the saving chosen. This holds AT the borrowing limit, where the
equality fails, and it is what carries concavity across the kink. -/
theorem cara_egmMap_ge {α : ℝ} (hα : 0 < α) (hβ : 0 < (P.discount : ℝ))
    (hu : P.u = caraUtility α) {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hAmax : A < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A) :
    P.consumptionFnOf (P.toExtended.bellman v) z a ≤ P.caraEgmMap v α z A := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hK : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hS : (0 : ℝ) < ∑ z' : Z, P.transitionMatrix z z'
      * Real.exp (-α * P.consumptionFnOf v z' A) :=
    sum_exp_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) α _
  have hd : HasDerivAt P.u (Real.exp (-α * P.consumptionFnOf (P.toExtended.bellman v) z a))
      (P.consumptionFnOf (P.toExtended.bellman v) z a) := by
    rw [hu]; exact hasDerivAt_caraUtility (ne_of_gt hα) _
  have hd' : ∀ z' : Z, HasDerivAt P.u (Real.exp (-α * P.consumptionFnOf v z' A))
      (P.consumptionFnOf v z' A) := fun z' => by
    rw [hu]; exact hasDerivAt_caraUtility (ne_of_gt hα) _
  have hE := P.euler_le ha hA hAmax hc hd hc' hd'
  -- take logs
  have hprod : ((P.discount : ℝ) * (1 + P.interest))
      * (∑ z' : Z, P.transitionMatrix z z' * Real.exp (-α * P.consumptionFnOf v z' A))
      ≤ Real.exp (-α * P.consumptionFnOf (P.toExtended.bellman v) z a) := by
    refine le_trans (le_of_eq ?_) hE
    ring
  have hlog := Real.log_le_log (by positivity) hprod
  rw [Real.log_mul (ne_of_gt hK) (ne_of_gt hS), Real.log_exp] at hlog
  simp only [caraEgmMap, softMin]
  have hαne : α ≠ 0 := ne_of_gt hα
  have hαpos : (0 : ℝ) < 1 / α := by positivity
  have h2 := mul_le_mul_of_nonneg_left hlog hαpos.le
  have h3 : (1 / α) * (-α * P.consumptionFnOf (P.toExtended.bellman v) z a)
      = -P.consumptionFnOf (P.toExtended.bellman v) z a := by field_simp
  rw [h3] at h2
  linarith

/-- **Carroll and Kimball for CARA, across the borrowing-limit kink.** The version that does not
assume the choice is interior: where the constraint binds the Euler equation fails, but the
INEQUALITY still holds, and `concaveOn_of_egm_corner` needs only that. -/
theorem concaveOn_consumptionFnOf_bellman_of_cara_corner {α : ℝ} (hα : 0 < α)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = caraUtility α) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z' : Z, ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z' : Z, ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmono : ∀ z' : Z, MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap))
    (hcW : ∀ a ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hslackW : ∀ a ∈ Icc assetFloor assetCap,
      P.policyOf (P.toExtended.bellman v) (a, z) < P.maxSaving (a, z))
    (hslackv : ∀ A ∈ Icc assetFloor assetCap, ∀ z' : Z,
      P.policyOf v (A, z') < P.maxSaving (A, z')) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_of_egm_corner (z := z)
    (g := fun a => P.policyOf (P.toExtended.bellman v) (a, z)) (C := P.caraEgmMap v α z)
    (P.concaveOn_caraEgmMap hα z hconc)
    (strictMonoOn_add_egm (P.monotoneOn_caraEgmMap hα z hmono))
    (fun a _ => P.feasible_subset_region (P.policyOf_mem _ (a, z))) (fun a ha => ?_)
    (fun a ha => ?_) fun a ha hfloor => ?_
  · have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
      simp only [resources, max_eq_right ha.1]
    simp only [consumptionFnOf, consumption, hres]; ring
  · exact P.cara_egmMap_ge hα hβ hu ha rfl (hslackW a ha) (hcW a ha)
      fun z' => hpos z' _ (P.feasible_subset_region (P.policyOf_mem _ (a, z)))
  · exact P.cara_egmMap_consumptionFnOf hα hβ hu ha rfl hfloor (hslackW a ha) (hcW a ha)
      (hslackv _ (P.feasible_subset_region (P.policyOf_mem _ (a, z))))
      fun z' => hpos z' _ (P.feasible_subset_region (P.policyOf_mem _ (a, z)))

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

/-! ### The assembly, beyond CRRA

The induction step is not the whole theorem: the iteration also needs consumption positive and
the asset cap slack at every stage, and in the CRRA development both come from CRRA-specific
bounds. For CARA they come from the two marginal bounds of `Models.CARA` — one near zero, one
over the whole consumption range — and two inequalities. -/

/-- **Carroll and Kimball along the iteration, for CARA.** -/
theorem concaveOn_consumptionFnOf_iterates_of_cara {α : ℝ} (hα : 0 < α)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = caraUtility α)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hslack : ∀ n : ℕ, ∀ a ∈ Icc assetFloor assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < P.maxSaving (a, z)) :
    ∀ n : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z) := by
  have hslices : ∀ n : ℕ, ConcaveSlices assetFloor assetCap
      ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact P.concaveSlices_bellman ih
  intro n
  induction n with
  | zero => exact P.concaveOn_consumptionFnOf_zero
  | succ k ih =>
    intro z
    have hnext : ∀ a ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf
        (P.toExtended.bellman ((P.toExtended.bellman)^[k] (0 : (ℝ × Z) →ᵇ ℝ))) z a := by
      intro a ha
      have := hpos (k + 1) z a ha
      rwa [Function.iterate_succ_apply'] at this
    have hnextslack : ∀ a ∈ Icc assetFloor assetCap, P.policyOf
        (P.toExtended.bellman ((P.toExtended.bellman)^[k] (0 : (ℝ × Z) →ᵇ ℝ))) (a, z)
          < P.maxSaving (a, z) := by
      intro a ha
      have := hslack (k + 1) a ha z
      rwa [Function.iterate_succ_apply'] at this
    rw [Function.iterate_succ_apply']
    exact P.concaveOn_consumptionFnOf_bellman_of_cara_corner hα hβ hu z
      (fun z' A hA => hpos k z' A hA) ih
      (fun z' x hx y hy hxy => P.consumptionFnOf_mono (hslices k) hx hy hxy)
      hnext hnextslack (fun A hA z' => hslack k A hA z')

/-- **Carroll and Kimball for CARA, from two inequalities.** The consumption function is
concave.

The first inequality says the marginal value of consumption near zero beats the discounted slope
of the continuation, which is what keeps consumption positive when marginal utility at zero is
FINITE; the second says the cap sits above the saving the marginal bound allows. Neither is
about preferences — they are the two artefacts of the capped, floored formulation. -/
theorem concaveOn_consumptionFn_of_cara {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hβ : 0 < (P.discount : ℝ)) (hb : P.Bounded) (hu : P.u = caraUtility α)
    (hfloor : (P.discount : ℝ) * P.oscSlopeConst P.oscSpread < Real.exp (-α * δ))
    (hcap : assetFloor + 4 * (P.discount : ℝ)
        * (max |P.toExtended.rewardMin| |P.toExtended.rewardMax| / (1 - P.discount))
        / Real.exp (-α * P.maxConsumption) < assetCap)
    (z : Z) : ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) := by
  have hslices : ∀ n : ℕ, ConcaveSlices assetFloor assetCap
      ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact P.concaveSlices_bellman ih
  have hM : MarginalBoundOn P.dom P.u (Real.exp (-α * δ)) := by
    rw [hb, hu]
    exact marginalBoundOn_caraUtility hα hδ
  -- positivity, from the marginal bound near zero
  have hpos : ∀ n : ℕ, ∀ z' : Z, ∀ a ∈ Icc assetFloor assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z' a :=
    fun n z' a ha => P.consumptionFnOf_pos_of_marginal hM P.oscSpread_nonneg (hslices n)
      (P.oscOn_iterate n) hfloor z' ha
  -- the cap, from the marginal bound over the whole range
  have hmpos : (0 : ℝ) < Real.exp (-α * P.maxConsumption) := Real.exp_pos _
  have hslack : ∀ n : ℕ, ∀ a ∈ Icc assetFloor assetCap, ∀ z' : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z') < P.maxSaving (a, z') := by
    intro n a ha z'
    refine P.policyOf_lt_maxSaving_of_pos (hpos n z' a ha) ?_
    have hbound := P.policyOf_le_of_marginal_bound (hslices n) hmpos ?_ ha z'
    · have hn := P.norm_iterate_le n
      have h4 : (0 : ℝ) ≤ 4 * (P.discount : ℝ) := by positivity
      have hstep := mul_le_mul_of_nonneg_left hn h4
      have hdiv : 4 * (P.discount : ℝ) * ‖(P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)‖
            / Real.exp (-α * P.maxConsumption)
          ≤ 4 * (P.discount : ℝ)
            * (max |P.toExtended.rewardMin| |P.toExtended.rewardMax| / (1 - P.discount))
            / Real.exp (-α * P.maxConsumption) := by
        rw [div_le_div_iff_of_pos_right hmpos]
        linarith
      linarith
    · intro c d hd hdc hcmax
      rw [hu]
      exact cara_marginal_bound hα hdc hcmax
  exact P.concaveOn_consumptionFn_of_iterates
    (P.concaveOn_consumptionFnOf_iterates_of_cara hα hβ hu hpos hslack) z

/-- **The corner condition for CARA**, from the generic Lipschitz bound and CARA's own marginal
bound. The CRRA and shifted-CRRA versions are `crra_policy_eq_zero_of_resources` and
`hara_policy_eq_zero_of_primitives`; nothing in the argument was ever CRRA-specific. -/
theorem cara_policy_eq_zero_of_resources {α L : ℝ} (hα : 0 < α) (hu : P.u = caraUtility α)
    (hL : 0 ≤ L) (hbig : (P.slopeBoundU + P.discount * L) * (1 + P.interest) ≤ L)
    {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap)
    (hlt : (P.discount : ℝ) * L < Real.exp (-α * (P.resources s - assetFloor))) :
    P.policy s = assetFloor :=
  P.policy_eq_zero_of_corner_at (P.valueFunction_lipschitz hL hbig) hs
    (fun c d _ hdc hc => by rw [hu]; exact cara_marginal_bound hα hdc hc) hlt

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

/-! ### A CARA economy whose consumption function is concave, unconditionally

`caraWitness` shows a capped CARA model exists. This one is calibrated so that both inequalities
of `concaveOn_consumptionFn_of_cara` hold, which makes it the first non-CRRA economy in the
development with a concave consumption function and nothing assumed.

The calibration is deliberately slack: income at least `3/2` keeps the consumption floor well
away from zero, where CARA's finite marginal utility is weakest, and `β = 1/1000` keeps the
saving bound far below the cap. Both inequalities hold by two orders of magnitude. -/

theorem exp_neg_three_halves_le : Real.exp (-(3 / 2 : ℝ)) ≤ 1 / 4 := by
  have hhalf : (3 : ℝ) / 2 ≤ Real.exp (1 / 2) := by
    have := Real.add_one_le_exp (1 / 2 : ℝ)
    linarith
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hsplit : Real.exp ((3 : ℝ) / 2) = Real.exp 1 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]; norm_num
  have hbig : (4 : ℝ) ≤ Real.exp ((3 : ℝ) / 2) := by
    rw [hsplit]; nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  linarith

theorem inv_three_le_exp_neg_one : (1 : ℝ) / 3 ≤ Real.exp (-1) := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  linarith

theorem inv_twentyone_le_exp_neg_three : (1 : ℝ) / 21 ≤ Real.exp (-3) := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have hsplit : Real.exp (3 : ℝ) = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h21 : Real.exp (3 : ℝ) ≤ 21 := by rw [hsplit]; nlinarith
  rw [show (-3 : ℝ) = -(3 : ℝ) from rfl, Real.exp_neg,
    le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  linarith

/-- **A calibrated CARA economy.** -/
noncomputable def caraCal : IncomeFluctuation (Fin 2) 0 1 where
  income z := if z = 0 then 3 / 2 else 2
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 1000
  u := caraUtility 1
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
  continuousOn_u_dom := (continuous_caraUtility one_ne_zero).continuousOn
  monotoneOn_u_dom := monotoneOn_caraUtility one_pos _
  strictConcaveOn_u_dom := (strictConcaveOn_caraUtility one_pos).subset (subset_univ _)
    (convex_Ici 0)
  continuousOn_extendDom :=
    continuousOn_extendDom_Ici (continuous_caraUtility one_ne_zero).continuousOn

@[simp] theorem caraCal_u : caraCal.u = caraUtility 1 := rfl
@[simp] theorem caraCal_discount : (caraCal.discount : ℝ) = 1 / 1000 := rfl
@[simp] theorem caraCal_interest : caraCal.interest = 0 := rfl
@[simp] theorem caraCal_minConsumption : caraCal.minConsumption = 3 / 2 := by
  norm_num [caraCal]

theorem caraCal_bounded : caraCal.Bounded := rfl

theorem caraCal_maxConsumption : caraCal.maxConsumption = 3 := by
  simp only [IncomeFluctuation.maxConsumption]
  norm_num [caraCal]

/-- The oscillation is small, because utility is bounded and the household is impatient. -/
theorem caraCal_oscSpread_le : caraCal.oscSpread ≤ 1 / 3 := by
  have hu3 : caraCal.u caraCal.maxConsumption = -Real.exp (-3) := by
    rw [caraCal_maxConsumption, caraCal_u]
    simp only [caraUtility]
    norm_num
  have hu32 : caraCal.u caraCal.minConsumption = -Real.exp (-(3 / 2)) := by
    rw [caraCal_minConsumption, caraCal_u]
    simp only [caraUtility]
    norm_num
  have hlow : (0 : ℝ) < Real.exp (-3) := Real.exp_pos _
  have hhigh := exp_neg_three_halves_le
  simp only [IncomeFluctuation.oscSpread, hu3, hu32, caraCal_discount]
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  linarith

theorem caraCal_floor_cond :
    (caraCal.discount : ℝ) * caraCal.oscSlopeConst caraCal.oscSpread < Real.exp (-1 * 1) := by
  have hosc := caraCal_oscSpread_le
  have hosc0 := caraCal.oscSpread_nonneg
  have hexp : (1 : ℝ) / 3 ≤ Real.exp (-1 * 1) := by
    rw [show (-1 : ℝ) * 1 = -1 from by ring]
    exact inv_three_le_exp_neg_one
  simp only [IncomeFluctuation.oscSlopeConst, caraCal_minConsumption, caraCal_discount]
  nlinarith [hosc, hosc0, hexp]

theorem caraCal_cap_cond :
    (0 : ℝ) + 4 * (caraCal.discount : ℝ)
        * (max |caraCal.toExtended.rewardMin| |caraCal.toExtended.rewardMax|
            / (1 - caraCal.discount))
        / Real.exp (-1 * caraCal.maxConsumption) < 1 := by
  have hmin : |caraCal.toExtended.rewardMin| ≤ 1 / 4 := by
    have : caraCal.toExtended.rewardMin = -Real.exp (-(3 / 2)) := by
      change caraCal.u caraCal.minConsumption = _
      rw [caraCal_minConsumption, caraCal_u]
      simp only [caraUtility]
      norm_num
    rw [this, abs_neg, abs_of_pos (Real.exp_pos _)]
    exact exp_neg_three_halves_le
  have hmax : |caraCal.toExtended.rewardMax| ≤ 1 / 4 := by
    have : caraCal.toExtended.rewardMax = -Real.exp (-3) := by
      change caraCal.u caraCal.maxConsumption = _
      rw [caraCal_maxConsumption, caraCal_u]
      simp only [caraUtility]
      norm_num
    rw [this, abs_neg, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-3 : ℝ) ≤ Real.exp (-(3 / 2) : ℝ) := Real.exp_le_exp.mpr (by norm_num)
    linarith [exp_neg_three_halves_le]
  have hm : (1 : ℝ) / 21 ≤ Real.exp (-1 * caraCal.maxConsumption) := by
    rw [caraCal_maxConsumption, show (-1 : ℝ) * 3 = -3 from by ring]
    exact inv_twentyone_le_exp_neg_three
  have hmpos : (0 : ℝ) < Real.exp (-1 * caraCal.maxConsumption) := Real.exp_pos _
  have hmaxle : max |caraCal.toExtended.rewardMin| |caraCal.toExtended.rewardMax| ≤ 1 / 4 :=
    max_le hmin hmax
  have hmax0 : (0 : ℝ) ≤ max |caraCal.toExtended.rewardMin| |caraCal.toExtended.rewardMax| :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  rw [zero_add, div_lt_one hmpos]
  have hstep : 4 * ((1 : ℝ) / 1000)
      * (max |caraCal.toExtended.rewardMin| |caraCal.toExtended.rewardMax| / (1 - 1 / 1000))
      ≤ 4 * (1 / 1000) * ((1 / 4) / (999 / 1000)) := by
    have : max |caraCal.toExtended.rewardMin| |caraCal.toExtended.rewardMax| / (1 - 1 / 1000)
        ≤ (1 / 4) / (999 / 1000 : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      linarith
    nlinarith [this]
  simp only [caraCal_discount] at hstep ⊢
  nlinarith [hstep, hm, hmpos]

/-- **Carroll and Kimball at a CARA calibration, with nothing assumed.** The first non-CRRA
economy in the development whose consumption function is concave outright. -/
theorem caraCal_concaveOn_consumptionFn (z : Fin 2) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (caraCal.consumptionFn z) :=
  caraCal.concaveOn_consumptionFn_of_cara (α := 1) (δ := 1) one_pos one_pos
    (by rw [caraCal_discount]; norm_num) caraCal_bounded rfl
    caraCal_floor_cond caraCal_cap_cond z

/-! ### What CARA can and cannot have

`caraCal` has Carroll--Kimball unconditionally, so it is a legitimate household. It is NOT a
`Calibrated` instance, and there are two independent reasons, both worth stating rather than
reporting.

**Light's Theorem 1 is unavailable.** The class carries `gamma_le_one` because rate monotonicity
needs relative risk aversion at most one. CARA's relative risk aversion is `α c`, so the
condition is `α · maxConsumption ≤ 1` — a restriction on the CALIBRATION, not on the functional
form. `caraCal` has `α = 1` and consumption at least `3/2`, so it fails
(`caraWitness_not_relativeRiskAversionLeOne`, which is a statement about `caraUtility 1` and so
covers this economy too).

**And it holds no capital anyway.** At `β = 1/1000` the household is so impatient that the corner
condition holds at EVERY asset level in the region: `β L ≤ 1/1000` against a marginal utility of
at least `1/21` even at the richest state. So it saves nothing, and capital supply is exactly
zero — the same conclusion as the riskless CRRA economy, reached for the opposite reason.

Those two are not independent accidents. The gain test that buys a positive floor needs
`exp(α(y₀ + Rh - y₁ + h)) < βπR/2`; with `α y₁ ≤ 1` forced by Light's condition, the left side
cannot fall below `e⁻¹`, so `βπR > 2/e`. A CARA economy with both Light's theorem and positive
capital would therefore have to be PATIENT — `βR` close to one — which is exactly where the
oscillation `1/(1-β)` blows the positivity and cap-slack conditions. That squeeze, not the
utility function, is what keeps CARA out. -/

/-- The secant slope of `caraCal`'s utility over `[3/4, 3/2]` is at most `2/3`, because
`exp(-3/4)` is the square root of `exp(-3/2) ≤ 1/4`. -/
theorem caraCal_slopeBoundU_le : caraCal.slopeBoundU ≤ 2 / 3 := by
  have hsq : Real.exp (-(3 / 4 : ℝ)) * Real.exp (-(3 / 4 : ℝ)) = Real.exp (-(3 / 2 : ℝ)) := by
    rw [← Real.exp_add]; norm_num
  have hpos : (0 : ℝ) < Real.exp (-(3 / 4 : ℝ)) := Real.exp_pos _
  have hhalf : Real.exp (-(3 / 4 : ℝ)) ≤ 1 / 2 := by
    nlinarith [hsq, exp_neg_three_halves_le, hpos]
  have hlow : (0 : ℝ) < Real.exp (-(3 / 2 : ℝ)) := Real.exp_pos _
  simp only [IncomeFluctuation.slopeBoundU, caraCal_minConsumption, caraCal_u, slopeBound,
    caraUtility]
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  have h1 : -Real.exp (-1 * (3 / 2 : ℝ)) / 1 = -Real.exp (-(3 / 2 : ℝ)) := by norm_num
  have h2 : -Real.exp (-1 * (3 / 2 / 2 : ℝ)) / 1 = -Real.exp (-(3 / 4 : ℝ)) := by norm_num
  rw [h1, h2]
  linarith [hhalf, hlow]

/-- **The `caraCal` household never saves.** At `β = 1/1000` the corner condition holds at every
asset level: `β L ≤ 1/1000` against a marginal utility of at least `1/21`. -/
theorem caraCal_policy_eq_zero {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 2) :
    caraCal.policy (a, z) = 0 := by
  have hres : caraCal.resources (a, z) ≤ 3 := by
    have hinc : caraCal.income z ≤ 2 := caraCal.le_maxIncome z
    simp only [IncomeFluctuation.resources, max_eq_right ha.1,
      show caraCal.interest = 0 from rfl]
    linarith [ha.2]
  refine caraCal.cara_policy_eq_zero_of_resources (α := 1) (L := 1) one_pos rfl (by norm_num)
    ?_ ha ?_
  · simp only [show caraCal.interest = 0 from rfl, caraCal_discount]
    linarith [caraCal_slopeBoundU_le]
  · have hge : Real.exp (-3 : ℝ) ≤ Real.exp (-1 * (caraCal.resources (a, z) - 0)) :=
      Real.exp_le_exp.mpr (by linarith [hres])
    have h21 := inv_twentyone_le_exp_neg_three
    rw [caraCal_discount]
    linarith [hge, h21]

/-- **Capital supply at `caraCal` is exactly zero.** -/
theorem caraCal_aggregateCapital_eq_zero {μ : ProbabilityMeasure caraCal.State}
    (hμ : caraCal.IsStationary μ) : caraCal.aggregateCapital μ = 0 := by
  rw [caraCal.aggregateCapital_eq_integral_policy hμ]
  have hz : ∀ s : caraCal.State, caraCal.policyCoord s = 0 := by
    intro s
    have hmem : ((s.1 : ℝ)) ∈ Icc (0 : ℝ) 1 := s.1.2
    simp only [IncomeFluctuation.policyCoord_apply, IncomeFluctuation.incl]
    exact caraCal_policy_eq_zero hmem s.2
  simp only [hz, integral_zero]

end LeanEconomics
