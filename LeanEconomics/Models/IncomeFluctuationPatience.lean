/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationIterate
import LeanEconomics.Equilibrium.ComparativeStatics

/-!
# A more patient household saves more

Light's Theorem 1 compares two interest rates. This file runs the same argument for the DISCOUNT
FACTOR, and the comparison is strictly easier — easy enough that the restriction Light needs
disappears.

## Why patience is easier than the rate

Raising `r` moves the budget set: cash on hand rises, the saving cap moves, and the two problems
have to be aligned by the rescaling `t = R₁/R₂` of `IncomeFluctuationRateStep` before they can
be compared. That rescaling is what forces `mul_marginal_le_of_scale` into the proof, and with
it the requirement that relative risk aversion be at most one.

Raising `β` moves NOTHING in the budget set: the feasible savings, the consumption map and the
reward are identical (`MorePatientThan.feasible_eq`, `MorePatientThan.reward_eq`). Only the
weight on the continuation differs. So the derivative of the difference is

  `R (β₂ u'(c₂(a)) - β₁ u'(c₁(a)))`,

and single crossing alone signs it: the more patient household saves more, hence consumes less,
hence has the higher marginal utility, and it multiplies the larger discount factor. No scaling,
no relative risk aversion, no Carroll–Kimball.

## What it needs instead

The same envelope (`hasDerivAt_bellman`) and the same interiority and positivity. Marginal
utility must be non-negative and decreasing, which every concave increasing utility has. That is
all.
-/

open scoped NNReal
open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} {P Q : IncomeFluctuation Z 0 assetCap}

/-- **Increasing differences of the DISCOUNTED continuations.** The patience analogue of
`ContIncreasingDifferences`: what matters when the discount factors differ is `β · cont`, not
`cont`. -/
def DiscIncDiff (P Q : IncomeFluctuation Z 0 assetCap) (v w : (ℝ × Z) →ᵇ ℝ) : Prop :=
  ∀ (z : Z) (x y : ℝ), x ∈ Icc (0 : ℝ) assetCap → y ∈ Icc (0 : ℝ) assetCap → x ≤ y →
    (P.discount : ℝ) * (P.contOf v z y - P.contOf v z x)
      ≤ (Q.discount : ℝ) * (Q.contOf w z y - Q.contOf w z x)

/-- It suffices to have it slice by slice, weighted by the discount factors. -/
theorem discIncDiff_of_slices (h : P.MorePatientThan Q) {v w : (ℝ × Z) →ᵇ ℝ}
    (hs : ∀ (z : Z) (x y : ℝ), x ∈ Icc (0 : ℝ) assetCap → y ∈ Icc (0 : ℝ) assetCap → x ≤ y →
      (P.discount : ℝ) * (v (y, z) - v (x, z)) ≤ (Q.discount : ℝ) * (w (y, z) - w (x, z))) :
    DiscIncDiff P Q v w := by
  intro z x y hx hy hxy
  simp only [contOf, ← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum]
  refine Finset.sum_le_sum fun z' _ => ?_
  rw [show Q.transitionMatrix z z' = P.transitionMatrix z z' from (h.same_transition z z').symm]
  have hstep := hs z' x y hx hy hxy
  nlinarith [P.transitionMatrix_nonneg z z', hstep]

/-- **Single crossing in patience.** Two households facing the same budget set, whose discounted
continuations have increasing differences, are ordered in saving. The exchange argument of
`policy_le_of_cont_increasingDifferences` with the discount factors carried along. -/
theorem policyOf_le_of_discIncDiff (h : P.MorePatientThan Q) {v w : (ℝ × Z) →ᵇ ℝ}
    (hw : ConcaveSlices (0 : ℝ) assetCap w) (hid : DiscIncDiff P Q v w)
    {a : ℝ} {z : Z} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.policyOf v (a, z) ≤ Q.policyOf w (a, z) := by
  by_contra hcon
  rw [not_le] at hcon
  set bP : ℝ := P.policyOf v (a, z) with hbP
  set bQ : ℝ := Q.policyOf w (a, z) with hbQ
  have hfeq : P.toExtended.feasible (a, z) = Q.toExtended.feasible (a, z) := h.feasible_eq _
  have hcons : ∀ x : ℝ, P.consumption (a, z) x = Q.consumption (a, z) x := fun x => by
    simp only [consumption, resources, h.same_income, h.same_interest]
  have hbPm : bP ∈ P.toExtended.feasible (a, z) := P.policyOf_mem v (a, z)
  have hbQm : bQ ∈ Q.toExtended.feasible (a, z) := Q.policyOf_mem w (a, z)
  have hbPQ : bP ∈ Q.toExtended.feasible (a, z) := hfeq ▸ hbPm
  have hbQP : bQ ∈ P.toExtended.feasible (a, z) := hfeq ▸ hbQm
  have hcP : P.consumption (a, z) bP ∈ P.dom := P.consumption_policyOf_mem_dom v ha
  have hcQ : Q.consumption (a, z) bQ ∈ Q.dom := Q.consumption_policyOf_mem_dom w ha
  have hcPQ : Q.consumption (a, z) bP ∈ Q.dom := by rw [← hcons, ← h.same_dom]; exact hcP
  have hcQP : P.consumption (a, z) bQ ∈ P.dom := by rw [hcons, h.same_dom]; exact hcQ
  have hoptP := P.objROf_le_of_mem v ha hbQP hcQP
  have hoptQ := Q.objROf_le_of_mem w ha hbPQ hcPQ
  have hidd := hid z bQ bP (Q.feasible_subset_region hbQm) (P.feasible_subset_region hbPm)
    hcon.le
  simp only [objROf, hcons, h.same_u, ← hbP, ← hbQ] at hoptP hoptQ
  have hQeq : Q.objROf w (a, z) bP = Q.objROf w (a, z) bQ := by
    simp only [objROf]
    nlinarith [hoptP, hoptQ, hidd]
  have hbell : Q.toExtended.objectiveE w (a, z) bP
      = ((Q.toExtended.bellmanFn w (a, z) : ℝ) : EReal) := by
    rw [Q.objectiveE_eq_coe_of w ha hbPQ hcPQ, hQeq, ← Q.objectiveE_eq_coe_of w ha hbQm hcQ]
    exact Q.policyOf_optimal w (a, z)
  exact absurd (Q.optimal_action_unique_of_concaveSlices hw ha hbPQ hbQm hbell
    (Q.policyOf_optimal w (a, z))) (by intro heq; rw [heq] at hcon; exact lt_irrefl _ hcon)

/-- Consumption is correspondingly ordered the other way: the more patient consume less. -/
theorem consumptionFnOf_le_of_discIncDiff (h : P.MorePatientThan Q) {v w : (ℝ × Z) →ᵇ ℝ}
    (hw : ConcaveSlices (0 : ℝ) assetCap w) (hid : DiscIncDiff P Q v w)
    {a : ℝ} {z : Z} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    Q.consumptionFnOf w z a ≤ P.consumptionFnOf v z a := by
  have hres : Q.resources (a, z) = P.resources (a, z) := by
    simp only [resources, h.same_income, h.same_interest]
  simp only [consumptionFnOf, consumption, hres]
  linarith [P.policyOf_le_of_discIncDiff h hw hid (z := z) ha]

/-! ### The derivative step

The difference to be signed is `β₂ (T₂ w)(a) - β₁ (T₁ v)(a)`, and the envelope makes its
derivative `R (β₂ u'(c_w(a)) - β₁ u'(c_v(a)))`. Single crossing puts `c_w(a) ≤ c_v(a)`, so
`u'(c_v(a)) ≤ u'(c_w(a))`, and `β₁ ≤ β₂` with marginal utility non-negative finishes it. -/

/-- Increasing differences of the discounted VALUE functions, slice by slice: the property the
induction carries. -/
def DiscIncDiffSlices (P Q : IncomeFluctuation Z 0 assetCap) (v w : (ℝ × Z) →ᵇ ℝ) : Prop :=
  ∀ (z : Z) (x y : ℝ), x ∈ Icc (0 : ℝ) assetCap → y ∈ Icc (0 : ℝ) assetCap → x ≤ y →
    (P.discount : ℝ) * (v (y, z) - v (x, z)) ≤ (Q.discount : ℝ) * (w (y, z) - w (x, z))

theorem discIncDiffSlices_zero (P Q : IncomeFluctuation Z 0 assetCap) :
    DiscIncDiffSlices P Q 0 0 := by
  intro z x y _ _ _
  simp

/-- **The monotone difference.** -/
theorem monotoneOn_bellman_sub_patience (h : P.MorePatientThan Q)
    {v w : (ℝ × Z) →ᵇ ℝ} {z : Z} {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdunn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ du y)
    (hwc : ConcaveSlices (0 : ℝ) assetCap w) (hid : DiscIncDiff P Q v w)
    (hbv : ConcaveOn ℝ (Icc (0 : ℝ) assetCap) fun x => (P.toExtended.bellman v) (x, z))
    (hbw : ConcaveOn ℝ (Icc (0 : ℝ) assetCap) fun x => (Q.toExtended.bellman w) (x, z))
    (hintv : ∀ x ∈ Icc (0 : ℝ) assetCap, P.policyOf v (x, z) < P.maxSaving (x, z))
    (hintw : ∀ x ∈ Icc (0 : ℝ) assetCap, Q.policyOf w (x, z) < Q.maxSaving (x, z))
    (hposv : ∀ x ∈ Icc (0 : ℝ) assetCap, 0 < P.consumptionFnOf v z x)
    (hposw : ∀ x ∈ Icc (0 : ℝ) assetCap, 0 < Q.consumptionFnOf w z x) :
    MonotoneOn (fun a => (Q.discount : ℝ) * (Q.toExtended.bellman w) (a, z)
      - (P.discount : ℝ) * (P.toExtended.bellman v) (a, z)) (Icc (0 : ℝ) assetCap) := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hRQ : (1 : ℝ) + Q.interest = 1 + P.interest := by rw [h.same_interest]
  have hβP : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have key : ∀ a ∈ Ioo (0 : ℝ) assetCap, ∃ D : ℝ, 0 ≤ D ∧
      HasDerivAt (fun x => (Q.discount : ℝ) * (Q.toExtended.bellman w) (x, z)
        - (P.discount : ℝ) * (P.toExtended.bellman v) (x, z)) D a := by
    intro a ha
    have hamem : a ∈ Icc (0 : ℝ) assetCap := ⟨ha.1.le, ha.2.le⟩
    have hdv : HasDerivAt (fun x => (P.toExtended.bellman v) (x, z))
        ((1 + P.interest) * du (P.consumptionFnOf v z a)) a :=
      P.hasDerivAt_bellman ha.1 ha.2 hbv (hintv a hamem) (hposv a hamem)
        (hderiv _ (hposv a hamem))
    have hdw : HasDerivAt (fun x => (Q.toExtended.bellman w) (x, z))
        ((1 + Q.interest) * du (Q.consumptionFnOf w z a)) a :=
      Q.hasDerivAt_bellman ha.1 ha.2 hbw (hintw a hamem) (hposw a hamem)
        (by rw [← h.same_u]; exact hderiv _ (hposw a hamem))
    refine ⟨_, ?_, (hdw.const_mul (Q.discount : ℝ)).sub (hdv.const_mul (P.discount : ℝ))⟩
    -- single crossing, then the two factors
    have hcross : Q.consumptionFnOf w z a ≤ P.consumptionFnOf v z a :=
      consumptionFnOf_le_of_discIncDiff h hwc hid hamem
    have hdu := hanti (mem_Ioi.mpr (hposw a hamem)) (mem_Ioi.mpr (hposv a hamem)) hcross
    have hdu0 : 0 ≤ du (Q.consumptionFnOf w z a) := hdunn _ (mem_Ioi.mpr (hposw a hamem))
    rw [hRQ]
    have h1 : (P.discount : ℝ) * ((1 + P.interest) * du (P.consumptionFnOf v z a))
        ≤ (P.discount : ℝ) * ((1 + P.interest) * du (Q.consumptionFnOf w z a)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdu hR.le) hβP
    have h2 : (P.discount : ℝ) * ((1 + P.interest) * du (Q.consumptionFnOf w z a))
        ≤ (Q.discount : ℝ) * ((1 + P.interest) * du (Q.consumptionFnOf w z a)) :=
      mul_le_mul_of_nonneg_right h.discount_le (mul_nonneg hR.le hdu0)
    linarith
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · refine ContinuousOn.sub ?_ ?_
    · exact (continuous_const.mul ((Q.toExtended.bellman w).continuous.comp
        (continuous_id.prodMk continuous_const))).continuousOn
    · exact (continuous_const.mul ((P.toExtended.bellman v).continuous.comp
        (continuous_id.prodMk continuous_const))).continuousOn
  · rw [interior_Icc]
    intro x hx
    obtain ⟨D, _, hD⟩ := key x hx
    exact hD.differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    obtain ⟨D, hD0, hD⟩ := key x hx
    rw [hD.deriv]
    exact hD0

/-- **The step**: increasing differences survive the two Bellman operators. -/
theorem discIncDiffSlices_bellman (h : P.MorePatientThan Q) {v w : (ℝ × Z) →ᵇ ℝ} {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdunn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ du y)
    (hvc : ConcaveSlices (0 : ℝ) assetCap v) (hwc : ConcaveSlices (0 : ℝ) assetCap w)
    (hpcP : P.PositiveConsumptionAll) (hpcQ : Q.PositiveConsumptionAll)
    (hslackv : ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, P.policyOf v (x, z) < assetCap)
    (hslackw : ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, Q.policyOf w (x, z) < assetCap)
    (hid : DiscIncDiffSlices P Q v w) :
    DiscIncDiffSlices P Q (P.toExtended.bellman v) (Q.toExtended.bellman w) := by
  intro z x y hx hy hxy
  have hmono := monotoneOn_bellman_sub_patience h hderiv hanti hdunn hwc
    (discIncDiff_of_slices h hid) (P.concaveSlices_bellman hvc z) (Q.concaveSlices_bellman hwc z)
    (fun b hb => P.policyOf_lt_maxSaving hpcP hvc hb (hslackv b hb z))
    (fun b hb => Q.policyOf_lt_maxSaving hpcQ hwc hb (hslackw b hb z))
    (fun b hb => hpcP v hvc z b hb) (fun b hb => hpcQ w hwc z b hb)
  have hkey := hmono hx hy hxy
  simp only at hkey
  linarith

/-! ### The induction, the limit, and the conclusion -/

/-- **A more patient household saves more**, at every asset level and every income state. No
restriction on relative risk aversion: the budget set does not move with `β`. -/
theorem policy_le_of_morePatient (h : P.MorePatientThan Q) {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdunn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ du y)
    (hpcP : P.PositiveConsumptionAll) (hpcQ : Q.PositiveConsumptionAll)
    (hslackP : ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (x, z) < assetCap)
    (hslackQ : ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      Q.policyOf ((Q.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (x, z) < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.policy (a, z) ≤ Q.policy (a, z) := by
  have hslices : ∀ (R : IncomeFluctuation Z 0 assetCap) (n : ℕ),
      ConcaveSlices (0 : ℝ) assetCap ((R.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro R n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact R.concaveSlices_bellman ih
  -- the induction
  have hstep : ∀ n : ℕ, DiscIncDiffSlices P Q
      ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ))
      ((Q.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact discIncDiffSlices_zero P Q
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact discIncDiffSlices_bellman h hderiv hanti hdunn (hslices P k) (hslices Q k)
        hpcP hpcQ (fun b hb z' => hslackP k b hb z') (fun b hb z' => hslackQ k b hb z') ih
  -- and the limit
  have hpt : ∀ (R : IncomeFluctuation Z 0 assetCap) (p : ℝ × Z),
      Tendsto (fun n => ((R.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) p) atTop
        (𝓝 (R.toExtended.valueFunction p)) := fun R p =>
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (R.toExtended.tendsto_iterate_valueFunction 0)).tendsto_at p
  have hlim : DiscIncDiffSlices P Q P.toExtended.valueFunction Q.toExtended.valueFunction := by
    intro z' x y hx hy hxy
    refine le_of_tendsto_of_tendsto
      (((hpt P (y, z')).sub (hpt P (x, z'))).const_mul (P.discount : ℝ))
      (((hpt Q (y, z')).sub (hpt Q (x, z'))).const_mul (Q.discount : ℝ))
      (Eventually.of_forall fun n => hstep n z' x y hx hy hxy)
  exact P.policyOf_le_of_discIncDiff h Q.concaveSlices_valueFunction
    (discIncDiff_of_slices h hlim) ha

/-- **A more patient household saves more, for CRRA**, at every `γ > 0`. Note what is NOT
assumed: `γ ≤ 1`. Light's rate theorem needs relative risk aversion at most one because the
budget set moves with the rate; the patience comparison has no such requirement. -/
theorem policy_le_of_morePatient_crra {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (h : P.MorePatientThan Q)
    (hpcP : P.PositiveConsumptionAll) (hpcQ : Q.PositiveConsumptionAll)
    (hslackP : ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (x, z) < assetCap)
    (hslackQ : ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      Q.policyOf ((Q.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (x, z) < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.policy (a, z) ≤ Q.policy (a, z) :=
  policy_le_of_morePatient h (du := fun c => c ^ (-γ))
    (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility γ hc)
    (fun _ hx _ _ hxy => Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
    (fun y hy => Real.rpow_nonneg (le_of_lt hy) _) hpcP hpcQ hslackP hslackQ ha z

/-! ### The equilibrium rate

Uniqueness is what makes this statement possible: `r*` is a number attached to an economy only
because the market clears once. Given that, the comparison is immediate — the more patient
population's supply schedule lies above, and demand is strictly decreasing. -/

/-- **A more patient population faces a lower equilibrium interest rate.** -/
theorem equilibriumRate_le_of_policy_le {A δ rlo rhi : ℝ} (hA : A ≠ 0) (hδ : 0 < rlo + δ)
    (Pf Qf : ℝ → IncomeFluctuation Z 0 assetCap)
    (hprobP : ∀ r r' : ℝ, ∀ z z' : Z,
      (Pf r).transitionMatrix z z' = (Pf r').transitionMatrix z z')
    (hprobPQ : ∀ r : ℝ, ∀ z z' : Z, (Pf r).transitionMatrix z z' = (Qf r).transitionMatrix z z')
    (hmonoP : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (Pf r).policy s ≤ (Pf r').policy s)
    (hpol : ∀ r ∈ Icc rlo rhi, ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap →
      (Pf r).policy s ≤ (Qf r).policy s)
    (μ₀ : ProbabilityMeasure P.State) (ν ρ : ℝ → ProbabilityMeasure P.State)
    (hconvP : ∀ r ∈ Icc rlo rhi, Tendsto (fun m => (Pf r).pushProb^[m] μ₀) atTop (𝓝 (ν r)))
    (hconvQ : ∀ r ∈ Icc rlo rhi, Tendsto (fun m => (Qf r).pushProb^[m] μ₀) atTop (𝓝 (ρ r)))
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (he₁ : P.aggregateCapital (ν r₁) = capitalDemand A δ r₁)
    (he₂ : P.aggregateCapital (ρ r₂) = capitalDemand A δ r₂) : r₂ ≤ r₁ :=
  equilibriumRate_le_of_supply_le hA hδ
    (P.monotoneOn_capitalSupply_of_policy_mono Pf hprobP hmonoP μ₀ ν hconvP)
    (fun r hr => P.capitalSupply_le_of_policy_le Pf Qf hprobPQ hpol μ₀ ν ρ hconvP hconvQ hr)
    h₁ h₂ he₁ he₂

end IncomeFluctuation

end LeanEconomics
