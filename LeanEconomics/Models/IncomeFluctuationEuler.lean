/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationEnvelope
import LeanEconomics.Models.IncomeFluctuationCarrollKimball
import LeanEconomics.Models.CRRA

/-!
# The envelope condition along the iteration, and the Euler equation

`IncomeFluctuationEnvelope` proves Clausen and Strub's envelope theorem at the FIXED POINT.
Carroll and Kimball's induction runs along the ITERATES `Tⁿ 0`, and needs it there. Nothing in
the lazy-agent argument used the fixed point: freezing a feasible saving and varying current
assets gives a differentiable lower bound on `bellman v` exactly as it does on the value
function, and concavity supplies the upper half of the sandwich. So the generalisation is the
same proof with `valueFunction` replaced by `bellman v` and `policy` by `policyOf v`.

With the envelope available at every stage the first-order condition can be read off, and that
is the hypothesis `hEuler` of `concaveOn_consumptionFnOf_bellman_of_euler`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### The envelope condition for an iterate -/

/-- **The envelope condition for `bellman v`.** The marginal value of assets is the gross
interest rate times the marginal utility of the consumption the household actually chooses.
Clausen and Strub's sandwich, run one step of the iteration at a time rather than at the fixed
point. -/
theorem hasDerivAt_bellman {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a du : ℝ}
    (ha : assetFloor < a) (hacap : a < assetCap)
    (hconc : ConcaveOn ℝ (Icc assetFloor assetCap) fun x => (P.toExtended.bellman v) (x, z))
    (hint : P.policyOf v (a, z) < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf v z a)
    (hu : HasDerivAt P.u du (P.consumptionFnOf v z a)) :
    HasDerivAt (fun x => (P.toExtended.bellman v) (x, z)) ((1 + P.interest) * du) a := by
  set a' := P.policyOf v (a, z) with ha'
  have hamem : ((a, z) : ℝ × Z).1 ∈ Icc assetFloor assetCap := ⟨ha.le, hacap.le⟩
  have ha'0 : assetFloor ≤ a' := (P.policyOf_mem v (a, z)).1
  have hba : ∀ x : ℝ, P.toExtended.bellmanFn v (x, z) = (P.toExtended.bellman v) (x, z) :=
    fun x => by rw [← P.toExtended.bellman_apply]
  -- the frozen saving stays feasible, and consumption stays positive, near `a`
  have hcms : ContinuousAt (fun x => P.maxSaving (x, z)) a :=
    (P.continuous_maxSaving.comp (continuous_id.prodMk continuous_const)).continuousAt
  have hccon : ContinuousAt (fun x => P.consumption (x, z) a') a :=
    ((P.continuous_resources.comp (continuous_id.prodMk continuous_const)).sub
      continuous_const).continuousAt
  have hev : {x : ℝ | assetFloor < x ∧ x < assetCap ∧ a' < P.maxSaving (x, z)
      ∧ 0 < P.consumption (x, z) a'} ∈ 𝓝 a := by
    have h1 : ∀ᶠ x in 𝓝 a, assetFloor < x := lt_mem_nhds ha
    have h2 : ∀ᶠ x in 𝓝 a, x < assetCap := gt_mem_nhds hacap
    have h3 : ∀ᶠ x in 𝓝 a, a' < P.maxSaving (x, z) := hcms.eventually_const_lt hint
    have h4 : ∀ᶠ x in 𝓝 a, 0 < P.consumption (x, z) a' := hccon.eventually_const_lt hc
    filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4 using ⟨hx1, hx2, hx3, hx4⟩
  obtain ⟨l, r, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  have hIsub : Ioo l r ⊆ Icc assetFloor assetCap := fun x hx =>
    ⟨(hsub hx).1.le, (hsub hx).2.1.le⟩
  have hlow : ∀ x ∈ Ioo l r, P.lazyValue v z a' x ≤ (P.toExtended.bellman v) (x, z) := by
    intro x hx
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hsub hx
    have hfe : a' ∈ P.toExtended.feasible (x, z) := ⟨ha'0, hx3.le⟩
    have := P.lazyValue_le v z ⟨hx1.le, hx2.le⟩ hfe hx4
    rwa [hba x] at this
  have htouch : P.lazyValue v z a' a = (P.toExtended.bellman v) (a, z) := by
    have hfe : a' ∈ P.toExtended.feasible (a, z) := P.policyOf_mem v (a, z)
    have := P.lazyValue_eq v z hamem hfe hc (P.policyOf_optimal v (a, z))
    rwa [hba a] at this
  refine (hconc.subset hIsub (convex_Ioo l r)).hasDerivAt_of_lowerBound hmem
    (Ioo_mem_nhds hmem.1 hmem.2)
    ⟨(l + a) / 2, ⟨by linarith [hmem.1, hmem.2], by linarith [hmem.1, hmem.2]⟩,
      by linarith [hmem.1, hmem.2]⟩
    ⟨(a + r) / 2, ⟨by linarith [hmem.1, hmem.2], by linarith [hmem.1, hmem.2]⟩,
      by linarith [hmem.1, hmem.2]⟩
    hlow htouch (P.hasDerivAt_lazyValue v z a' ha hu)

/-! ### The first-order condition

With the envelope available at the saving actually chosen, the objective is differentiable in
the saving, the choice is a local maximum, and the derivative vanishes. That is the Euler
equation: the marginal utility of consuming now equals the discounted, interest-augmented
expected marginal utility of consuming next period. -/

/-- **The Euler equation along the iteration.** Every hypothesis is an interiority or
differentiability condition at the single state `(a, z)` and at the saving it chooses; nothing
is assumed globally. -/
theorem euler_of_interior {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A du : ℝ} {du' : Z → ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hA0 : assetFloor < A) (hAcap : A < assetCap) (hAmax : A < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hu : HasDerivAt P.u du (P.consumptionFnOf (P.toExtended.bellman v) z a))
    (hconc : ∀ z' : Z, ConcaveOn ℝ (Icc assetFloor assetCap)
      fun x => (P.toExtended.bellman v) (x, z'))
    (hint' : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z'))
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A)
    (hu' : ∀ z' : Z, HasDerivAt P.u (du' z') (P.consumptionFnOf v z' A)) :
    du = (P.discount : ℝ) * ((1 + P.interest) * ∑ z', P.transitionMatrix z z' * du' z') := by
  subst hA
  set W := P.toExtended.bellman v with hWdef
  set A := P.policyOf W (a, z) with hAdef
  have hcA : P.consumptionFnOf W z a = P.resources (a, z) - A := rfl
  -- the continuation is differentiable in the saving, by the envelope one step on
  have hWderiv : ∀ z' : Z, HasDerivAt (fun x => W (x, z')) ((1 + P.interest) * du' z') A :=
    fun z' => P.hasDerivAt_bellman hA0 hAcap (hconc z') (hint' z') (hc' z') (hu' z')
  have hsum : HasDerivAt (fun x => ∑ z' : Z, P.transitionMatrix z z' * W (x, z'))
      (∑ z' : Z, P.transitionMatrix z z' * ((1 + P.interest) * du' z')) A :=
    HasDerivAt.fun_sum fun z' _ => (hWderiv z').const_mul _
  -- and so is the reward
  have hres : HasDerivAt (fun x : ℝ => P.resources (a, z) - x) (-1) A := by
    simpa using (hasDerivAt_id A).const_sub (P.resources (a, z))
  have hrew : HasDerivAt (fun x => P.u (P.resources (a, z) - x)) (du * (-1)) A :=
    HasDerivAt.comp A (hcA ▸ hu) hres
  have hΦ : HasDerivAt (fun x => P.lazyValue W z x a)
      (du * (-1) + (P.discount : ℝ)
        * ∑ z' : Z, P.transitionMatrix z z' * ((1 + P.interest) * du' z')) A :=
    hrew.add (hsum.const_mul (P.discount : ℝ))
  -- the chosen saving is a local maximum of the objective
  have hlm : IsLocalMax (fun x => P.lazyValue W z x a) A := by
    have hcont : ContinuousAt (fun x : ℝ => P.resources (a, z) - x) A :=
      (continuous_const.sub continuous_id).continuousAt
    have h1 : ∀ᶠ x in 𝓝 A, assetFloor < x := lt_mem_nhds hA0
    have h2 : ∀ᶠ x in 𝓝 A, x < P.maxSaving (a, z) := gt_mem_nhds hAmax
    have hcpos : (0 : ℝ) < P.resources (a, z) - A := by rw [← hcA]; exact hc
    have h3 : ∀ᶠ x in 𝓝 A, 0 < P.resources (a, z) - x := hcont.eventually_const_lt hcpos
    have hAopt : P.lazyValue W z A a = P.toExtended.bellmanFn W (a, z) :=
      P.lazyValue_eq W z ha (P.policyOf_mem W (a, z)) hc (P.policyOf_optimal W (a, z))
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [hAopt]
    exact P.lazyValue_le W z ha ⟨hx1.le, hx2.le⟩ hx3
  -- so the derivative vanishes, which is the Euler equation
  have hzero := hlm.hasDerivAt_eq_zero hΦ
  have hfac : ∑ z' : Z, P.transitionMatrix z z' * ((1 + P.interest) * du' z')
      = (1 + P.interest) * ∑ z' : Z, P.transitionMatrix z z' * du' z' := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z' _ => by ring
  rw [hfac] at hzero
  linarith

/-! ### CRRA: the Euler equation in endogenous-gridpoint form

With `u' c = c ^ (-γ)` the Euler equation says that consumption is a positive multiple of the
weighted power mean, exponent `-γ`, of next period's consumptions — which is exactly `egmMap`,
and exactly what `concaveOn_consumptionFnOf_bellman_of_euler` asks for. -/

theorem egm_of_euler {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A)
    (heuler : P.consumptionFnOf (P.toExtended.bellman v) z a ^ (-γ)
      = (P.discount : ℝ) * ((1 + P.interest)
        * ∑ z' : Z, P.transitionMatrix z z' * P.consumptionFnOf v z' A ^ (-γ))) :
    P.consumptionFnOf (P.toExtended.bellman v) z a = P.egmMap v γ z A := by
  have hγn : γ ≠ 0 := ne_of_gt hγ0
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hK : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hS : (0 : ℝ) < ∑ z' : Z, P.transitionMatrix z z' * P.consumptionFnOf v z' A ^ (-γ) :=
    sum_rpow_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hc'
  have hprod : P.consumptionFnOf (P.toExtended.bellman v) z a ^ (-γ)
      = ((P.discount : ℝ) * (1 + P.interest))
        * ∑ z' : Z, P.transitionMatrix z z' * P.consumptionFnOf v z' A ^ (-γ) := by
    rw [heuler]; ring
  have hexp : (-γ) * (-(1 / γ)) = 1 := by field_simp
  have hinv : (P.consumptionFnOf (P.toExtended.bellman v) z a ^ (-γ)) ^ (-(1 / γ))
      = P.consumptionFnOf (P.toExtended.bellman v) z a := by
    rw [← Real.rpow_mul hc.le, hexp, Real.rpow_one]
  rw [← hinv, hprod, Real.mul_rpow hK.le hS.le]
  simp only [egmMap, powerMean]
  congr 1
  rw [show -(1 / γ) = 1 / (-γ) by field_simp]

/-- **The hypothesis `hEuler` of `concaveOn_consumptionFnOf_bellman_of_euler`, discharged.**
Everything that remains is interiority: the saving chosen must be strictly inside the asset
region and strictly below the feasible maximum, this period and next. -/
theorem egmMap_consumptionFnOf {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hu : P.u = crraUtility γ) {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hA0 : assetFloor < A) (hAcap : A < assetCap) (hAmax : A < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hconc : ∀ z' : Z, ConcaveOn ℝ (Icc assetFloor assetCap)
      fun x => (P.toExtended.bellman v) (x, z'))
    (hint' : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z'))
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A) :
    P.consumptionFnOf (P.toExtended.bellman v) z a = P.egmMap v γ z A := by
  have hd : HasDerivAt P.u (P.consumptionFnOf (P.toExtended.bellman v) z a ^ (-γ))
      (P.consumptionFnOf (P.toExtended.bellman v) z a) := by
    rw [hu]; exact hasDerivAt_crraUtility γ hc
  have hd' : ∀ z' : Z, HasDerivAt P.u (P.consumptionFnOf v z' A ^ (-γ))
      (P.consumptionFnOf v z' A) := fun z' => by
    rw [hu]; exact hasDerivAt_crraUtility γ (hc' z')
  exact P.egm_of_euler hγ0 hβ hc hc'
    (P.euler_of_interior ha hA hA0 hAcap hAmax hc hd hconc hint' hc' hd')

/-! ### Carroll and Kimball's induction step, with the Euler equation discharged -/

/-- **The interiority the first-order condition needs.** At `(a, z)` the household saves
strictly inside the asset region and strictly below its feasible maximum, and does so again next
period in every income state. This is exactly what fails at the borrowing limit, where
`policy_eq_zero_of_corner_at` shows the constraint binds. -/
def EulerInterior (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (a : ℝ) : Prop :=
  assetFloor < P.policyOf (P.toExtended.bellman v) (a, z)
    ∧ P.policyOf (P.toExtended.bellman v) (a, z) < assetCap
    ∧ P.policyOf (P.toExtended.bellman v) (a, z) < P.maxSaving (a, z)
    ∧ ∀ z' : Z, P.policyOf v (P.policyOf (P.toExtended.bellman v) (a, z), z')
        < P.maxSaving (P.policyOf (P.toExtended.bellman v) (a, z), z')

/-- **Carroll and Kimball (1996), the induction step for CRRA, with no Euler hypothesis.**

`concaveOn_consumptionFnOf_bellman_of_euler` assumed the first-order condition; here it is
proved, from the Clausen–Strub envelope run along the iteration. What is assumed instead is
interiority, which is a property of the state rather than of the model, and the reason the
statement is not yet unconditional. -/
theorem concaveOn_consumptionFnOf_bellman_of_interior {γ : ℝ} (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z' : Z, ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconcv : ∀ z' : Z, ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmonov : ∀ z' : Z, MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap))
    (hconcW : ∀ z' : Z, ConcaveOn ℝ (Icc assetFloor assetCap)
      fun x => (P.toExtended.bellman v) (x, z'))
    (hcW : ∀ a ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hin : ∀ a ∈ Icc assetFloor assetCap, P.EulerInterior v z a) :
    ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_consumptionFnOf_bellman_of_euler hγ0 hpos hconcv hmonov z fun a ha => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hin a ha
  exact P.egmMap_consumptionFnOf hγ0 hβ hu ha rfl h1 h2 h3 (hcW a ha) hconcW h4
    fun z' => hpos z' _ (P.feasible_subset_region (P.policyOf_mem _ (a, z)))

end IncomeFluctuation

end LeanEconomics
