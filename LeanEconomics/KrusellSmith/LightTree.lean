/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CarrollKimballIterate
import LeanEconomics.KrusellSmith.SavingMonotoneReduction
import LeanEconomics.Analysis.DifferentiableSandwich
import LeanEconomics.Analysis.RelativeRiskAversion

/-!
# Light's step on the tree: higher returns, steeper values

Milestone MR4c of `MINIMAL_STATE_PLAN.md`: increasing differences of value functions across
higher return paths (`ValueIncreasingDifferences`), the remaining input of `savingMonotone_of`.

* `hasDerivAt_bellman_tree`, **the envelope equality one Bellman step from `w`**: the marginal
  value of assets is the return times marginal utility of the consumption chosen. Clausen and
  Strub's lazy agent: freeze the saving and vary assets for a differentiable lower bound, and
  `ConcaveOn.hasDerivAt_of_lowerBound` (`Analysis/DifferentiableSandwich`, used as it stands)
  supplies the upper half from concavity.
* `policyOf_le_policyOf`, **Topkis against continuations**: at the same label, with at least as
  much cash and a continuation with increasing differences, saving is at least as high.

* `incDiff_bellman`, **Light's step on the tree**: one Bellman step carries increasing
  differences of the continuation along a higher return path (same wages) to increasing
  differences of the values. With the envelope, `D = V' − V` has derivative `R' u'(c') − R u'(c)`.
  At the rescaled asset level `t a`, `t = R/R'`, cash is the same, so the steeper continuation
  gives lower consumption, `c'(t a) ≤ c(a)`; then `mul_marginal_le_of_scale`
  (`Analysis/RelativeRiskAversion`, used as it stands: concave consumption from MR4b, relative
  risk aversion at most one) gives `t u'(c'(t a)) ≤ u'(c'(a))`.
* `incDiff_iterate`, `incDiff_valueFunction`: along every pair of iterates, then in the limit.
* **`valueIncreasingDifferences_of`** and **`exists_consistentSelection_of_complementarity`**:
  for a wage independent of capital, a return nondecreasing in capital, CRRA with γ ≤ 1,
  positive returns, and the floor and cap slack along the iterates (explicit hypotheses, to be
  discharged by calibration), **a recursive equilibrium on the minimal state exists without any
  uniqueness assumption**.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (U : M.SmoothUtility) (z₀ : Z) (K : List Z → ℝ × ℝ)

/-- **The envelope equality, one Bellman step from `w`.** At an interior asset level where
consumption is above the floor, the value `T w` is differentiable in assets with derivative the
return times marginal utility of the consumption chosen. -/
theorem hasDerivAt_bellman_tree {w : M.State →ᵇ ℝ} (hw : M.ConcaveSlices w) {a : ℝ}
    (ha : 0 < a) (hacap : a < M.assetCap) (l : Label Z E)
    (hsl : M.consFloor < M.consumptionOf z₀ K w (M.stateAt a l)) :
    HasDerivAt (fun x => (M.household z₀ K).bellman w (M.stateAt x l))
      (M.returnAt z₀ K l.node * U.du (M.consumptionOf z₀ K w (M.stateAt a l))) a := by
  set R := M.returnAt z₀ K l.node
  set W := M.wageAt z₀ K l.node * M.efficiency l.idio
  set p := M.policyOf z₀ K w (M.stateAt a l) with hp
  set c := M.consumptionOf z₀ K w (M.stateAt a l) with hc
  have hpm := M.policyOf_mem z₀ K w (M.stateAt a l)
  have hpI : p ∈ Icc 0 M.assetCap := M.mem_Icc_of_mem_feasible z₀ K hpm
  have haI : a ∈ Icc 0 M.assetCap := ⟨ha.le, hacap.le⟩
  have hcash : ∀ x ∈ Icc 0 M.assetCap, M.cash z₀ K (M.stateAt x l) = R * x + W :=
    fun x hx => M.cash_stateAt z₀ K hx l
  have hca : c = R * a + W - p := by rw [hc, consumptionOf, hcash a haI]
  -- the lazy lower bound: freeze the saving `p`
  set L : ℝ → ℝ := fun x => M.utility (R * x + W - p) + M.discount * M.contOf z₀ w (M.stateAt a l) p
    with hL
  have hev : {x : ℝ | 0 < x ∧ x < M.assetCap ∧ M.consFloor < R * x + W - p} ∈ 𝓝 a := by
    have h1 : ∀ᶠ x in 𝓝 a, 0 < x := lt_mem_nhds ha
    have h2 : ∀ᶠ x in 𝓝 a, x < M.assetCap := gt_mem_nhds hacap
    have hcont : Continuous fun x : ℝ => R * x + W - p :=
      ((continuous_const.mul continuous_id).add continuous_const).sub continuous_const
    have h3 : ∀ᶠ x in 𝓝 a, M.consFloor < R * x + W - p :=
      hcont.continuousAt.eventually_const_lt (by
        change M.consFloor < R * a + W - p
        rw [← hca]
        exact hsl)
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 using ⟨hx1, hx2, hx3⟩
  obtain ⟨l', r', hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  have hIsub : Ioo l' r' ⊆ Icc 0 M.assetCap := fun x hx => ⟨(hsub hx).1.le, (hsub hx).2.1.le⟩
  have hlow : ∀ x ∈ Ioo l' r', L x ≤ (M.household z₀ K).bellman w (M.stateAt x l) := by
    intro x hx
    obtain ⟨hx1, hx2, hx3⟩ := hsub hx
    have hxI : x ∈ Icc 0 M.assetCap := ⟨hx1.le, hx2.le⟩
    have hfe : p ∈ (M.household z₀ K).feasible (M.stateAt x l) :=
      ⟨hpI.1, le_min hpI.2 (by rw [hcash x hxI]; linarith)⟩
    have := M.le_bellman_contOf z₀ K w hfe
    rw [hcash x hxI, M.contOf_label z₀ w x a l] at this
    exact this
  have htouch : L a = (M.household z₀ K).bellman w (M.stateAt a l) := by
    rw [M.bellman_eq_contOf z₀ K w (M.stateAt a l), hL]
    simp only
    rw [← hca]
  have hLd : HasDerivAt L (R * U.du c) a := by
    have hinner : HasDerivAt (fun x => R * x + W - p) R a := by
      simpa using (((hasDerivAt_id a).const_mul R).add_const W).sub_const p
    have hu : HasDerivAt M.utility (U.du c) (R * a + W - p) := by
      rw [← hca]; exact U.hasDerivAt c hsl
    exact ((hu.comp a hinner).add_const (M.discount * M.contOf z₀ w (M.stateAt a l) p)).congr_deriv
      (mul_comm _ _)
  have hconc : ConcaveOn ℝ (Ioo l' r') fun x => (M.household z₀ K).bellman w (M.stateAt x l) :=
    (M.concaveSlices_bellman z₀ K hw l).subset hIsub (convex_Ioo l' r')
  exact hconc.hasDerivAt_of_lowerBound hmem (Ioo_mem_nhds hmem.1 hmem.2)
    ⟨(l' + a) / 2, ⟨by linarith [hmem.1, hmem.2], by linarith [hmem.1, hmem.2]⟩,
      by linarith [hmem.1, hmem.2]⟩
    ⟨(a + r') / 2, ⟨by linarith [hmem.1, hmem.2], by linarith [hmem.1, hmem.2]⟩,
      by linarith [hmem.1, hmem.2]⟩
    hlow htouch hLd

/-- **Topkis against continuations.** Two price paths from the same root, two continuations, two
states at the same label: with at least as much cash, and a continuation whose values at every
child have increasing differences over the other's, saving is at least as high. -/
theorem policyOf_le_policyOf {K K' : List Z → ℝ × ℝ} {v v' : M.State →ᵇ ℝ}
    (hv : M.ConcaveSlices v) {s s' : M.State} (hl : s.2 = s'.2)
    (hcash : M.cash z₀ K s ≤ M.cash z₀ K' s')
    (hid : ∀ (l : Label Z E) (x y : ℝ), x ∈ Icc 0 M.assetCap → y ∈ Icc 0 M.assetCap → x ≤ y →
      v (M.stateAt y l) - v (M.stateAt x l) ≤ v' (M.stateAt y l) - v' (M.stateAt x l)) :
    M.policyOf z₀ K v s ≤ M.policyOf z₀ K' v' s' := by
  set p := M.policyOf z₀ K v s
  set p' := M.policyOf z₀ K' v' s'
  set x := M.cash z₀ K s
  set x' := M.cash z₀ K' s'
  by_contra hlt
  rw [not_le] at hlt
  have hp := M.policyOf_mem z₀ K v s
  have hp' := M.policyOf_mem z₀ K' v' s'
  have hpx : p ≤ x - M.consFloor := hp.2.trans (min_le_right _ _)
  have hf' : p' ∈ (M.household z₀ K).feasible s := ⟨hp'.1, hlt.le.trans hp.2⟩
  have hf : p ∈ (M.household z₀ K').feasible s' :=
    ⟨hp.1, le_min (hp.2.trans (min_le_left _ _)) (by
      change p ≤ x' - M.consFloor
      linarith)⟩
  have h2 := M.le_bellman_contOf z₀ K' v' hf
  have v1 := M.bellman_eq_contOf z₀ K v s
  have v2 := M.bellman_eq_contOf z₀ K' v' s'
  -- the continuations at the two states share their children
  have hcid : M.contOf z₀ v s p - M.contOf z₀ v s p'
      ≤ M.contOf z₀ v' s' p - M.contOf z₀ v' s' p' := by
    simp only [contOf, hl]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun ze _ => ?_
    have hpr := M.shockProb_nonneg' z₀ ze (s', p)
    have hsp : ∀ a : ℝ, M.shockProb z₀ ze (s, a) = M.shockProb z₀ ze (s', p) := by
      intro a
      simp only [shockProb, ContinuousMap.coe_mk, hl]
    rw [hsp p, hsp p', M.shockProb_eq z₀ ze s' p' p, ← mul_sub, ← mul_sub]
    exact mul_le_mul_of_nonneg_left (hid _ p' p (M.mem_Icc_of_mem_feasible z₀ K' hp')
      (M.mem_Icc_of_mem_feasible z₀ K hp) hlt.le) hpr
  have hβ := mul_le_mul_of_nonneg_left hcid M.discount_pos.le
  rw [mul_sub, mul_sub] at hβ
  have hcf : M.consFloor ≤ x - p := by linarith
  have hu := concave_increment_le M.strictConcaveOn_utility.concaveOn
    (x := x - p) (y := x' - p) (d := p - p') (by linarith) (by linarith) (mem_Ici.2 hcf)
    (mem_Ici.2 (by linarith))
  have e1 : x' - p + (p - p') = x' - p' := by ring
  have e2 : x - p + (p - p') = x - p' := by ring
  rw [e1, e2] at hu
  have hcx : M.consumptionOf z₀ K v s = x - p := rfl
  have hcx' : M.consumptionOf z₀ K' v' s' = x' - p' := rfl
  rw [hcx] at v1
  rw [hcx'] at v2
  have htie : M.utility (x - p') + M.discount * M.contOf z₀ v s p'
      = (M.household z₀ K).bellman v s := by
    have h1 := M.le_bellman_contOf z₀ K v hf'
    linarith
  exact absurd (M.eq_policyOf_of_objective z₀ K hv hf' htie) hlt.ne

/-- Increasing differences of one continuation over another, at every label. -/
def IncDiff (v v' : M.State →ᵇ ℝ) : Prop :=
  ∀ (l : Label Z E) (x y : ℝ), x ∈ Icc 0 M.assetCap → y ∈ Icc 0 M.assetCap → x ≤ y →
    v (M.stateAt y l) - v (M.stateAt x l) ≤ v' (M.stateAt y l) - v' (M.stateAt x l)

theorem continuous_stateAt (l : Label Z E) : Continuous fun x : ℝ => M.stateAt x l :=
  continuous_projIcc.prodMk continuous_const

/-- CRRA with relative risk aversion at most one: `y ↦ y · y^{-γ} = y^{1-γ}` is nondecreasing. -/
theorem monotoneOn_mul_rpow_neg {γ : ℝ} (hγ1 : γ ≤ 1) :
    MonotoneOn (fun y : ℝ => y * y ^ (-γ)) (Ioi 0) := by
  have key : ∀ y : ℝ, 0 < y → y * y ^ (-γ) = y ^ (1 - γ) := fun y hy => by
    rw [Real.rpow_sub hy, Real.rpow_one, Real.rpow_neg hy.le, div_eq_mul_inv]
  intro a ha b hb hab
  simp only
  rw [key a ha, key b hb]
  exact Real.rpow_le_rpow ha.le hab (by linarith)

/-- **Light's step on the tree.** One Bellman step carries increasing differences of the
continuation along a higher return path (same wages) to increasing differences of the values:
the marginal value of assets `R u'(c)` is higher, because at the rescaled asset level with the
same cash the steeper continuation lowers consumption, and `mul_marginal_le_of_scale`
(concave consumption, relative risk aversion at most one) handles the rescaling. -/
theorem incDiff_bellman {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) {K K' : List Z → ℝ × ℝ}
    (hR : ∀ h, 0 < M.returnAt z₀ K h) (hRle : ∀ h, M.returnAt z₀ K h ≤ M.returnAt z₀ K' h)
    (hW : ∀ h, M.wageAt z₀ K h = M.wageAt z₀ K' h) {v v' : M.State →ᵇ ℝ}
    (hv : M.ConcaveSlices v) (hv' : M.ConcaveSlices v') (hsl : M.SlackOf z₀ K v)
    (hsl' : M.SlackOf z₀ K' v')
    (hcc' : ∀ l : Label Z E,
      ConcaveOn ℝ (Icc 0 M.assetCap) fun A => M.consumptionOf z₀ K' v' (M.stateAt A l))
    (hid : M.IncDiff v v') :
    M.IncDiff ((M.household z₀ K).bellman v) ((M.household z₀ K').bellman v') := by
  intro l x y hx hy hxy
  set D : ℝ → ℝ := fun a => (M.household z₀ K').bellman v' (M.stateAt a l)
    - (M.household z₀ K).bellman v (M.stateAt a l) with hD
  suffices hmono : MonotoneOn D (Icc 0 M.assetCap) by
    have := hmono hx hy hxy
    simp only [hD] at this
    linarith
  have hderiv : ∀ a ∈ Ioo 0 M.assetCap, HasDerivAt D
      (M.returnAt z₀ K' l.node * U.du (M.consumptionOf z₀ K' v' (M.stateAt a l))
        - M.returnAt z₀ K l.node * U.du (M.consumptionOf z₀ K v (M.stateAt a l))) a :=
    fun a ha => (M.hasDerivAt_bellman_tree U z₀ K' hv' ha.1 ha.2 l (hsl' _)).sub
      (M.hasDerivAt_bellman_tree U z₀ K hv ha.1 ha.2 l (hsl _))
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · exact ((((M.household z₀ K').bellman v').continuous.comp (M.continuous_stateAt l)).sub
      (((M.household z₀ K).bellman v).continuous.comp (M.continuous_stateAt l))).continuousOn
  · rw [interior_Icc]
    exact fun a ha => (hderiv a ha).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro a ha
    rw [(hderiv a ha).deriv, sub_nonneg]
    -- the rescaled asset level with the same cash
    set R := M.returnAt z₀ K l.node
    set R' := M.returnAt z₀ K' l.node
    have hRpos := hR l.node
    have hR'pos : 0 < R' := hRpos.trans_le (hRle l.node)
    set t := R / R' with ht
    have ht0 : 0 < t := div_pos hRpos hR'pos
    have ht1 : t ≤ 1 := (div_le_one hR'pos).2 (hRle l.node)
    have haI : a ∈ Icc 0 M.assetCap := ⟨ha.1.le, ha.2.le⟩
    have htaI : t * a ∈ Icc 0 M.assetCap :=
      ⟨mul_nonneg ht0.le ha.1.le, by nlinarith [ha.1, ha.2]⟩
    have hRta : R' * (t * a) = R * a := by
      rw [ht]
      field_simp
    have hcash : M.cash z₀ K (M.stateAt a l) = M.cash z₀ K' (M.stateAt (t * a) l) := by
      rw [M.cash_stateAt z₀ K haI, M.cash_stateAt z₀ K' htaI, hW l.node]
      change R * a + _ = R' * (t * a) + _
      rw [hRta]
    have hp := M.policyOf_le_policyOf z₀ hv (s := M.stateAt a l) (s' := M.stateAt (t * a) l) rfl
      hcash.le hid
    set c := M.consumptionOf z₀ K v (M.stateAt a l)
    set c't := M.consumptionOf z₀ K' v' (M.stateAt (t * a) l)
    set c' := M.consumptionOf z₀ K' v' (M.stateAt a l)
    have hcc : c't ≤ c := by
      change M.cash z₀ K' (M.stateAt (t * a) l) - _ ≤ M.cash z₀ K (M.stateAt a l) - _
      rw [hcash]
      linarith
    have hc0 : 0 < c't := M.consFloor_nonneg.trans_lt (hsl' _)
    rw [hdu c (hsl _), hdu c' (hsl' _)]
    have h1 : c ^ (-γ) ≤ c't ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos hc0 hcc (by linarith)
    have hzero : M.consFloor < M.consumptionOf z₀ K' v' (M.stateAt 0 l) := hsl' _
    have h2 := mul_marginal_le_of_scale (c := fun A => M.consumptionOf z₀ K' v' (M.stateAt A l))
      (du := fun y => y ^ (-γ)) (s := Icc 0 M.assetCap) (hcc' l) ⟨le_rfl, M.assetCap_pos.le⟩
      (M.consFloor_nonneg.trans_lt hzero)
      (fun x hx y hy hxy => M.consumptionOf_mono z₀ K' hv' hx hy hxy l)
      (monotoneOn_mul_rpow_neg hγ1) (fun y hy => Real.rpow_nonneg (le_of_lt hy) _)
      ht0 ht1 ha.1 htaI (by rw [one_mul]; exact haI)
    simp only [one_mul] at h2
    have hRt : R = R' * t := by rw [ht]; field_simp
    calc R * c ^ (-γ) ≤ R * c't ^ (-γ) := mul_le_mul_of_nonneg_left h1 hRpos.le
      _ = R' * (t * c't ^ (-γ)) := by rw [hRt]; ring
      _ ≤ R' * c' ^ (-γ) := mul_le_mul_of_nonneg_left h2 hR'pos.le

/-- **Increasing differences along every pair of iterates.** -/
theorem incDiff_iterate {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) {K K' : List Z → ℝ × ℝ}
    (hR : ∀ h, 0 < M.returnAt z₀ K h) (hR' : ∀ h, 0 < M.returnAt z₀ K' h)
    (hRle : ∀ h, M.returnAt z₀ K h ≤ M.returnAt z₀ K' h)
    (hW : ∀ h, M.wageAt z₀ K h = M.wageAt z₀ K' h)
    (hsl : ∀ n : ℕ, M.SlackOf z₀ K (((M.household z₀ K).bellman)^[n] 0))
    (hsl' : ∀ n : ℕ, M.SlackOf z₀ K' (((M.household z₀ K').bellman)^[n] 0))
    (hcap' : ∀ (n : ℕ) (s : M.State),
      M.policyOf z₀ K' (((M.household z₀ K').bellman)^[n] 0) s < M.assetCap) :
    ∀ n : ℕ, M.IncDiff (((M.household z₀ K).bellman)^[n] 0)
      (((M.household z₀ K').bellman)^[n] 0)
  | 0 => fun l x y _ _ _ => by simp
  | n + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact M.incDiff_bellman U z₀ hγ0 hγ1 hdu hR hRle hW (M.concaveSlices_iterate z₀ K n)
      (M.concaveSlices_iterate z₀ K' n) (hsl n) (hsl' n)
      (M.concaveOn_consumptionOf_iterate U z₀ K' hγ0 hdu hR' hsl' hcap' n)
      (incDiff_iterate hγ0 hγ1 hdu hR hR' hRle hW hsl hsl' hcap' n)

/-- **Increasing differences of the value functions**, the limit of the iterates. -/
theorem incDiff_valueFunction {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) {K K' : List Z → ℝ × ℝ}
    (hR : ∀ h, 0 < M.returnAt z₀ K h) (hR' : ∀ h, 0 < M.returnAt z₀ K' h)
    (hRle : ∀ h, M.returnAt z₀ K h ≤ M.returnAt z₀ K' h)
    (hW : ∀ h, M.wageAt z₀ K h = M.wageAt z₀ K' h)
    (hsl : ∀ n : ℕ, M.SlackOf z₀ K (((M.household z₀ K).bellman)^[n] 0))
    (hsl' : ∀ n : ℕ, M.SlackOf z₀ K' (((M.household z₀ K').bellman)^[n] 0))
    (hcap' : ∀ (n : ℕ) (s : M.State),
      M.policyOf z₀ K' (((M.household z₀ K').bellman)^[n] 0) s < M.assetCap) :
    M.IncDiff (M.household z₀ K).valueFunction (M.household z₀ K').valueFunction := by
  intro l x y hx hy hxy
  have h1 := (M.household z₀ K).tendsto_iterate_valueFunction 0
  have h2 := (M.household z₀ K').tendsto_iterate_valueFunction 0
  have hev : ∀ (V : ℕ → M.State →ᵇ ℝ) (V₀ : M.State →ᵇ ℝ), Tendsto V atTop (𝓝 V₀) →
      Tendsto (fun n => V n (M.stateAt y l) - V n (M.stateAt x l)) atTop
        (𝓝 (V₀ (M.stateAt y l) - V₀ (M.stateAt x l))) := fun V V₀ hV =>
    (((continuous_eval_const _).tendsto V₀).comp hV).sub
      (((continuous_eval_const _).tendsto V₀).comp hV)
  exact le_of_tendsto_of_tendsto' (hev _ _ h1) (hev _ _ h2) fun n =>
    M.incDiff_iterate U z₀ hγ0 hγ1 hdu hR hR' hRle hW hsl hsl' hcap' n l x y hx hy hxy

/-- **`ValueIncreasingDifferences` for complementarity economies**: a wage independent of capital,
a return nondecreasing in capital, CRRA with relative risk aversion at most one, positive
returns, and the consumption floor and asset cap slack along the Bellman iterates of every price
path. -/
theorem valueIncreasingDifferences_of {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) (hw : M.WageIndependent)
    (hRm : M.ReturnMonotone)
    (hRpos : ∀ (z : Z) (m₀ : E → ℝ) (K : List Z → ℝ) (h : List Z),
      0 < M.returnAt z (M.pricePath z m₀ K) h)
    (hsl : ∀ (z : Z) (m₀ : E → ℝ) (K : List Z → ℝ) (n : ℕ),
      M.SlackOf z (M.pricePath z m₀ K) (((M.household z (M.pricePath z m₀ K)).bellman)^[n] 0))
    (hcap : ∀ (z : Z) (m₀ : E → ℝ) (K : List Z → ℝ) (n : ℕ) (s : M.State),
      M.policyOf z (M.pricePath z m₀ K)
        (((M.household z (M.pricePath z m₀ K)).bellman)^[n] 0) s < M.assetCap) :
    M.ValueIncreasingDifferences := by
  intro z m₀ K K' hKK' l x y hx hy hxy
  refine M.incDiff_valueFunction U z hγ0 hγ1 hdu (hRpos z m₀ K) (hRpos z m₀ K') (fun h => ?_)
    (fun h => ?_) (hsl z m₀ K) (hsl z m₀ K') (hcap z m₀ K') l x y hx hy hxy
  · exact hRm _ _ _ _ (hKK' h)
  · exact hw _ _ _ _

/-- **A recursive equilibrium on the minimal state without uniqueness, for complementarity
economies.** If the wage does not depend on aggregate capital, the return is nondecreasing in
it, utility is CRRA with relative risk aversion at most one, returns are positive, and the
consumption floor and the asset cap are slack along the Bellman iterates, then the greatest
sequential equilibrium is a consistent selection: a recursive equilibrium on `(z, μ)` exists,
with no uniqueness assumption (`ConsistentSelection.isRecursive`). -/
theorem exists_consistentSelection_of_complementarity {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) (hw : M.WageIndependent)
    (hRm : M.ReturnMonotone)
    (hRpos : ∀ (z : Z) (m₀ : E → ℝ) (K : List Z → ℝ) (h : List Z),
      0 < M.returnAt z (M.pricePath z m₀ K) h)
    (hsl : ∀ (z : Z) (m₀ : E → ℝ) (K : List Z → ℝ) (n : ℕ),
      M.SlackOf z (M.pricePath z m₀ K) (((M.household z (M.pricePath z m₀ K)).bellman)^[n] 0))
    (hcap : ∀ (z : Z) (m₀ : E → ℝ) (K : List Z → ℝ) (n : ℕ) (s : M.State),
      M.policyOf z (M.pricePath z m₀ K)
        (((M.household z (M.pricePath z m₀ K)).bellman)^[n] 0) s < M.assetCap) :
    Nonempty M.ConsistentSelection :=
  ⟨SavingMonotone.consistentSelection (savingMonotone_of hw hRm
    (valueIncreasingDifferences_of U hγ0 hγ1 hdu hw hRm hRpos hsl hcap))⟩

end KSModel

end KrusellSmith

end LeanEconomics
