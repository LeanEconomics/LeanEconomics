/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.LightTree
import LeanEconomics.KrusellSmith.SavingMonotoneReduction
import LeanEconomics.KrusellSmith.Sensitivity
import LeanEconomics.KrusellSmith.CobbDouglasCapital

/-!
# Higher future wages lower saving

Step (a) of milestone B2 (`EXISTENCE_EXTENSIONS_PLAN.md`): with Cobb–Douglas prices, higher
expected future capital means lower future returns and higher future wages, and both should lower
saving today. The return channel is Light's step read with the two paths swapped
(`incDiff_bellman`, γ ≤ 1). This file proves the **wage channel**, for every smooth utility.

* `consumptionOf_le_consumptionOf`: at the same label, with at least as much cash and a flatter
  continuation, consumption is at least as high (deviate by the consumption gap at both states;
  concavity and the flatter continuation chain the four increments; strict concavity rules out the
  tie).
* `incDiff_bellman_wage`: along a path with the same returns and higher wages, one Bellman step
  carries a flatter continuation to a flatter value: by the envelope the marginal value is
  `R u'(c)`, and consumption is higher.
* `incDiff_valueFunction_wage`: the value functions, as the limit of the iterates.
* **`policy_le_of_wages`**: with the same returns, higher wages along the path and no more cash
  today, every household saves (weakly) less.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (U : M.SmoothUtility) (z₀ : Z)

/-- **More cash and a flatter continuation give more consumption.** -/
theorem consumptionOf_le_consumptionOf {K K' : List Z → ℝ × ℝ} {v v' : M.State →ᵇ ℝ}
    (hv : M.ConcaveSlices v) {s s' : M.State} (hl : s.2 = s'.2)
    (hcash : M.cash z₀ K s ≤ M.cash z₀ K' s') (hid : M.IncDiff v' v) :
    M.consumptionOf z₀ K v s ≤ M.consumptionOf z₀ K' v' s' := by
  set p := M.policyOf z₀ K v s
  set p' := M.policyOf z₀ K' v' s'
  set x := M.cash z₀ K s
  set x' := M.cash z₀ K' s'
  change x - p ≤ x' - p'
  by_contra hlt
  rw [not_le] at hlt
  set δ := (x - p) - (x' - p') with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hp := M.policyOf_mem z₀ K v s
  have hp' := M.policyOf_mem z₀ K' v' s'
  have hpI := M.mem_Icc_of_mem_feasible z₀ K hp
  have hpI' := M.mem_Icc_of_mem_feasible z₀ K' hp'
  have hpx : p ≤ x - M.consFloor := hp.2.trans (min_le_right _ _)
  have hpx' : p' ≤ x' - M.consFloor := hp'.2.trans (min_le_right _ _)
  -- each deviates by the consumption gap
  have hf : p + δ ∈ (M.household z₀ K).feasible s :=
    ⟨by linarith [hp.1], le_min (by rw [hδ]; linarith [hpI'.2]) (by
      change p + δ ≤ x - M.consFloor
      rw [hδ]; linarith)⟩
  have hf' : p' - δ ∈ (M.household z₀ K').feasible s' :=
    ⟨by rw [hδ]; linarith [hp.1], le_min (by linarith [hpI'.2]) (by
      change p' - δ ≤ x' - M.consFloor
      rw [hδ]; linarith)⟩
  have hfI := M.mem_Icc_of_mem_feasible z₀ K hf
  have hfI' := M.mem_Icc_of_mem_feasible z₀ K' hf'
  have h1 := M.le_bellman_contOf z₀ K v hf
  have h2 := M.le_bellman_contOf z₀ K' v' hf'
  have v1 := M.bellman_eq_contOf z₀ K v s
  have v2 := M.bellman_eq_contOf z₀ K' v' s'
  have hc1 : M.consumptionOf z₀ K v s = x - p := rfl
  have hc2 : M.consumptionOf z₀ K' v' s' = x' - p' := rfl
  rw [hc1] at v1
  rw [hc2] at v2
  have e1 : x - (p + δ) = x' - p' := by rw [hδ]; ring
  have e2 : x' - (p' - δ) = x - p := by rw [hδ]; ring
  rw [e1] at h1
  rw [e2] at h2
  -- concavity: the increment at `p` is at least the one at `p' − δ ≥ p`
  have hle : p ≤ p' - δ := by rw [hδ]; linarith
  have hconc := concave_increment_le (M.concaveOn_contOf z₀ hv s) (x := p) (y := p' - δ) (d := δ)
    hle hδ0.le hpI (by rw [sub_add_cancel]; exact hpI')
  rw [sub_add_cancel] at hconc
  -- the flatter continuation, at the shared children
  have hflat : M.contOf z₀ v' s' p' - M.contOf z₀ v' s' (p' - δ)
      ≤ M.contOf z₀ v s p' - M.contOf z₀ v s (p' - δ) := by
    simp only [contOf, hl]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun ze _ => ?_
    have hpr := M.shockProb_nonneg' z₀ ze (s', p')
    have hsp : ∀ a : ℝ, M.shockProb z₀ ze (s, a) = M.shockProb z₀ ze (s', p') := by
      intro a
      simp only [shockProb, ContinuousMap.coe_mk, hl]
    have hsp' : M.shockProb z₀ ze (s', p' - δ) = M.shockProb z₀ ze (s', p') :=
      M.shockProb_eq z₀ ze s' (p' - δ) p'
    rw [hsp p', hsp (p' - δ), hsp', ← mul_sub, ← mul_sub]
    exact mul_le_mul_of_nonneg_left (hid _ (p' - δ) p' hfI' hpI' (by linarith)) hpr
  have hβ1 := mul_le_mul_of_nonneg_left hflat M.discount_pos.le
  have hβ2 := mul_le_mul_of_nonneg_left hconc M.discount_pos.le
  rw [mul_sub, mul_sub] at hβ1 hβ2
  -- the deviation at `s` ties with the optimum
  have htie : M.utility (x - (p + δ)) + M.discount * M.contOf z₀ v s (p + δ)
      = (M.household z₀ K).bellman v s := by
    rw [e1]
    linarith
  have := M.eq_policyOf_of_objective z₀ K hv hf htie
  change p + δ = p at this
  linarith

include U in
/-- **The wage step**: with the same returns and higher wages along the path, one Bellman step
carries a flatter continuation to a flatter value. -/
theorem incDiff_bellman_wage {K K' : List Z → ℝ × ℝ}
    (hR : ∀ h, M.returnAt z₀ K h = M.returnAt z₀ K' h)
    (hW : ∀ h, M.wageAt z₀ K h ≤ M.wageAt z₀ K' h) {v v' : M.State →ᵇ ℝ}
    (hv : M.ConcaveSlices v) (hv' : M.ConcaveSlices v') (hsl : M.SlackOf z₀ K v)
    (hsl' : M.SlackOf z₀ K' v') (hid : M.IncDiff v' v) :
    M.IncDiff ((M.household z₀ K').bellman v') ((M.household z₀ K).bellman v) := by
  intro l x y hx hy hxy
  set D : ℝ → ℝ := fun a => (M.household z₀ K).bellman v (M.stateAt a l)
    - (M.household z₀ K').bellman v' (M.stateAt a l) with hD
  suffices hmono : MonotoneOn D (Icc 0 M.assetCap) by
    have := hmono hx hy hxy
    simp only [hD] at this
    linarith
  have hderiv : ∀ a ∈ Ioo 0 M.assetCap, HasDerivAt D
      (M.returnAt z₀ K l.node * U.du (M.consumptionOf z₀ K v (M.stateAt a l))
        - M.returnAt z₀ K' l.node * U.du (M.consumptionOf z₀ K' v' (M.stateAt a l))) a :=
    fun a ha => (M.hasDerivAt_bellman_tree U z₀ K hv ha.1 ha.2 l (hsl _)).sub
      (M.hasDerivAt_bellman_tree U z₀ K' hv' ha.1 ha.2 l (hsl' _))
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · exact ((((M.household z₀ K).bellman v).continuous.comp (M.continuous_stateAt l)).sub
      (((M.household z₀ K').bellman v').continuous.comp (M.continuous_stateAt l))).continuousOn
  · rw [interior_Icc]
    exact fun a ha => (hderiv a ha).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro a ha
    rw [(hderiv a ha).deriv, sub_nonneg, ← hR l.node]
    have haI : a ∈ Icc 0 M.assetCap := ⟨ha.1.le, ha.2.le⟩
    have hcash : M.cash z₀ K (M.stateAt a l) ≤ M.cash z₀ K' (M.stateAt a l) := by
      rw [M.cash_stateAt z₀ K haI, M.cash_stateAt z₀ K' haI, hR l.node]
      have := mul_le_mul_of_nonneg_right (hW l.node) (M.efficiency_nonneg l.idio)
      linarith
    have hc := M.consumptionOf_le_consumptionOf z₀ hv (s := M.stateAt a l)
      (s' := M.stateAt a l) rfl hcash hid
    exact mul_le_mul_of_nonneg_left (U.du_anti (hsl _) hc) (M.returnAt_nonneg z₀ K l.node)

include U in
/-- **A flatter value along every pair of iterates.** -/
theorem incDiff_iterate_wage {K K' : List Z → ℝ × ℝ}
    (hR : ∀ h, M.returnAt z₀ K h = M.returnAt z₀ K' h)
    (hW : ∀ h, M.wageAt z₀ K h ≤ M.wageAt z₀ K' h)
    (hsl : ∀ n : ℕ, M.SlackOf z₀ K (((M.household z₀ K).bellman)^[n] 0))
    (hsl' : ∀ n : ℕ, M.SlackOf z₀ K' (((M.household z₀ K').bellman)^[n] 0)) :
    ∀ n : ℕ, M.IncDiff (((M.household z₀ K').bellman)^[n] 0)
      (((M.household z₀ K).bellman)^[n] 0)
  | 0 => fun l x y _ _ _ => by simp
  | n + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact M.incDiff_bellman_wage U z₀ hR hW (M.concaveSlices_iterate z₀ K n)
      (M.concaveSlices_iterate z₀ K' n) (hsl n) (hsl' n)
      (incDiff_iterate_wage hR hW hsl hsl' n)

include U in
/-- **A flatter value function under higher wages**, the limit of the iterates. -/
theorem incDiff_valueFunction_wage {K K' : List Z → ℝ × ℝ}
    (hR : ∀ h, M.returnAt z₀ K h = M.returnAt z₀ K' h)
    (hW : ∀ h, M.wageAt z₀ K h ≤ M.wageAt z₀ K' h)
    (hsl : ∀ n : ℕ, M.SlackOf z₀ K (((M.household z₀ K).bellman)^[n] 0))
    (hsl' : ∀ n : ℕ, M.SlackOf z₀ K' (((M.household z₀ K').bellman)^[n] 0)) :
    M.IncDiff (M.household z₀ K').valueFunction (M.household z₀ K).valueFunction := by
  intro l x y hx hy hxy
  have h1 := (M.household z₀ K').tendsto_iterate_valueFunction 0
  have h2 := (M.household z₀ K).tendsto_iterate_valueFunction 0
  have hev : ∀ (V : ℕ → M.State →ᵇ ℝ) (V₀ : M.State →ᵇ ℝ), Tendsto V atTop (𝓝 V₀) →
      Tendsto (fun n => V n (M.stateAt y l) - V n (M.stateAt x l)) atTop
        (𝓝 (V₀ (M.stateAt y l) - V₀ (M.stateAt x l))) := fun V V₀ hV =>
    (((continuous_eval_const _).tendsto V₀).comp hV).sub
      (((continuous_eval_const _).tendsto V₀).comp hV)
  exact le_of_tendsto_of_tendsto' (hev _ _ h1) (hev _ _ h2) fun n =>
    M.incDiff_iterate_wage U z₀ hR hW hsl hsl' n l x y hx hy hxy

include U in
/-- **Higher future wages lower saving**: with the same returns along the path, higher wages, and
no more cash today, every household saves weakly less. -/
theorem policy_le_of_wages {K K' : List Z → ℝ × ℝ}
    (hR : ∀ h, M.returnAt z₀ K h = M.returnAt z₀ K' h)
    (hW : ∀ h, M.wageAt z₀ K h ≤ M.wageAt z₀ K' h)
    (hsl : ∀ n : ℕ, M.SlackOf z₀ K (((M.household z₀ K).bellman)^[n] 0))
    (hsl' : ∀ n : ℕ, M.SlackOf z₀ K' (((M.household z₀ K').bellman)^[n] 0))
    (s : M.State) (hcash : M.cash z₀ K' s ≤ M.cash z₀ K s) :
    M.policy z₀ K' s ≤ M.policy z₀ K s :=
  M.policy_le_policy z₀ s hcash (M.cont_increasingDifferences z₀ s
    (M.incDiff_valueFunction_wage U z₀ hR hW hsl hsl'))

/-! ### Lower returns and higher wages together (Cobb–Douglas) -/

include U in
/-- **The Cobb–Douglas step**: along a path with lower returns and higher wages, for CRRA with
relative risk aversion at most one and no borrowing, one Bellman step carries a flatter
continuation to a flatter value. At the rescaled asset level `t a`, `t = R'/R`, the high-return
household has no more cash than the low-return one at `a`, and a steeper continuation, so it
consumes less; the rescaling is `mul_marginal_le_of_scale` (concave consumption, γ ≤ 1). -/
theorem incDiff_bellman_cd {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) {K K' : List Z → ℝ × ℝ}
    (hR' : ∀ h, 0 < M.returnAt z₀ K' h) (hRle : ∀ h, M.returnAt z₀ K' h ≤ M.returnAt z₀ K h)
    (hW : ∀ h, M.wageAt z₀ K h ≤ M.wageAt z₀ K' h) (hb : M.borrowLimit = 0)
    {v v' : M.State →ᵇ ℝ} (hv : M.ConcaveSlices v) (hv' : M.ConcaveSlices v')
    (hsl : M.SlackOf z₀ K v) (hsl' : M.SlackOf z₀ K' v')
    (hcc : ∀ l : Label Z E,
      ConcaveOn ℝ (Icc 0 M.assetCap) fun A => M.consumptionOf z₀ K v (M.stateAt A l))
    (hid : M.IncDiff v' v) :
    M.IncDiff ((M.household z₀ K').bellman v') ((M.household z₀ K).bellman v) := by
  intro l x y hx hy hxy
  set D : ℝ → ℝ := fun a => (M.household z₀ K).bellman v (M.stateAt a l)
    - (M.household z₀ K').bellman v' (M.stateAt a l) with hD
  suffices hmono : MonotoneOn D (Icc 0 M.assetCap) by
    have := hmono hx hy hxy
    simp only [hD] at this
    linarith
  have hderiv : ∀ a ∈ Ioo 0 M.assetCap, HasDerivAt D
      (M.returnAt z₀ K l.node * U.du (M.consumptionOf z₀ K v (M.stateAt a l))
        - M.returnAt z₀ K' l.node * U.du (M.consumptionOf z₀ K' v' (M.stateAt a l))) a :=
    fun a ha => (M.hasDerivAt_bellman_tree U z₀ K hv ha.1 ha.2 l (hsl _)).sub
      (M.hasDerivAt_bellman_tree U z₀ K' hv' ha.1 ha.2 l (hsl' _))
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · exact ((((M.household z₀ K).bellman v).continuous.comp (M.continuous_stateAt l)).sub
      (((M.household z₀ K').bellman v').continuous.comp (M.continuous_stateAt l))).continuousOn
  · rw [interior_Icc]
    exact fun a ha => (hderiv a ha).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro a ha
    rw [(hderiv a ha).deriv, sub_nonneg]
    set R := M.returnAt z₀ K l.node
    set R' := M.returnAt z₀ K' l.node
    have hR'pos := hR' l.node
    have hRpos : 0 < R := hR'pos.trans_le (hRle l.node)
    set t := R' / R with ht
    have ht0 : 0 < t := div_pos hR'pos hRpos
    have ht1 : t ≤ 1 := (div_le_one hRpos).2 (hRle l.node)
    have haI : a ∈ Icc 0 M.assetCap := ⟨ha.1.le, ha.2.le⟩
    have htaI : t * a ∈ Icc 0 M.assetCap :=
      ⟨mul_nonneg ht0.le ha.1.le, by nlinarith [ha.1, ha.2]⟩
    have hRta : R * (t * a) = R' * a := by
      rw [ht]
      field_simp
    have hcash : M.cash z₀ K (M.stateAt (t * a) l) ≤ M.cash z₀ K' (M.stateAt a l) := by
      rw [M.cash_stateAt z₀ K htaI, M.cash_stateAt z₀ K' haI, hb, mul_zero, mul_zero]
      change R * (t * a) + _ - 0 ≤ R' * a + _ - 0
      rw [hRta]
      have := mul_le_mul_of_nonneg_right (hW l.node) (M.efficiency_nonneg l.idio)
      linarith
    have hct := M.consumptionOf_le_consumptionOf z₀ hv (s := M.stateAt (t * a) l)
      (s' := M.stateAt a l) rfl hcash hid
    set c := M.consumptionOf z₀ K v (M.stateAt a l)
    set ct := M.consumptionOf z₀ K v (M.stateAt (t * a) l)
    set c' := M.consumptionOf z₀ K' v' (M.stateAt a l)
    have hc0 : 0 < ct := M.consFloor_nonneg.trans_lt (hsl _)
    rw [hdu c (hsl _), hdu c' (hsl' _)]
    have h1 : c' ^ (-γ) ≤ ct ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos hc0 hct (by linarith)
    have hzero : M.consFloor < M.consumptionOf z₀ K v (M.stateAt 0 l) := hsl _
    have h2 := mul_marginal_le_of_scale (c := fun A => M.consumptionOf z₀ K v (M.stateAt A l))
      (du := fun y => y ^ (-γ)) (s := Icc 0 M.assetCap) (hcc l) ⟨le_rfl, M.assetCap_pos.le⟩
      (M.consFloor_nonneg.trans_lt hzero)
      (fun x hx y hy hxy => M.consumptionOf_mono z₀ K hv hx hy hxy l)
      (monotoneOn_mul_rpow_neg hγ1) (fun y hy => Real.rpow_nonneg (le_of_lt hy) _)
      ht0 ht1 ha.1 htaI (by rw [one_mul]; exact haI)
    simp only [one_mul] at h2
    have hRt : R' = R * t := by rw [ht]; field_simp
    calc R' * c' ^ (-γ) ≤ R' * ct ^ (-γ) := mul_le_mul_of_nonneg_left h1 hR'pos.le
      _ = R * (t * ct ^ (-γ)) := by rw [hRt]; ring
      _ ≤ R * c ^ (-γ) := mul_le_mul_of_nonneg_left h2 hRpos.le

include U in
/-- **A flatter value along every pair of iterates**, lower returns and higher wages. -/
theorem incDiff_iterate_cd {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) {K K' : List Z → ℝ × ℝ}
    (hR' : ∀ h, 0 < M.returnAt z₀ K' h) (hRle : ∀ h, M.returnAt z₀ K' h ≤ M.returnAt z₀ K h)
    (hW : ∀ h, M.wageAt z₀ K h ≤ M.wageAt z₀ K' h) (hb : M.borrowLimit = 0)
    (hsl : ∀ n : ℕ, M.SlackOf z₀ K (((M.household z₀ K).bellman)^[n] 0))
    (hsl' : ∀ n : ℕ, M.SlackOf z₀ K' (((M.household z₀ K').bellman)^[n] 0))
    (hcap : ∀ (n : ℕ) (s : M.State),
      M.policyOf z₀ K (((M.household z₀ K).bellman)^[n] 0) s < M.assetCap) :
    ∀ n : ℕ, M.IncDiff (((M.household z₀ K').bellman)^[n] 0)
      (((M.household z₀ K).bellman)^[n] 0)
  | 0 => fun l x y _ _ _ => by simp
  | n + 1 => by
    have hR : ∀ h, 0 < M.returnAt z₀ K h := fun h => (hR' h).trans_le (hRle h)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact M.incDiff_bellman_cd U z₀ hγ0 hγ1 hdu hR' hRle hW hb (M.concaveSlices_iterate z₀ K n)
      (M.concaveSlices_iterate z₀ K' n) (hsl n) (hsl' n)
      (M.concaveOn_consumptionOf_iterate U z₀ K hγ0 hdu hR hsl hcap n)
      (incDiff_iterate_cd hγ0 hγ1 hdu hR' hRle hW hb hsl hsl' hcap n)

include U in
/-- **Higher expected capital lowers saving (household level, Cobb–Douglas directions)**: along a
path with lower returns and higher wages, for CRRA with γ ≤ 1 and no borrowing, a household with
no more cash today saves weakly less. -/
theorem policy_le_of_cd {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) {K K' : List Z → ℝ × ℝ}
    (hR' : ∀ h, 0 < M.returnAt z₀ K' h) (hRle : ∀ h, M.returnAt z₀ K' h ≤ M.returnAt z₀ K h)
    (hW : ∀ h, M.wageAt z₀ K h ≤ M.wageAt z₀ K' h) (hb : M.borrowLimit = 0)
    (hsl : ∀ n : ℕ, M.SlackOf z₀ K (((M.household z₀ K).bellman)^[n] 0))
    (hsl' : ∀ n : ℕ, M.SlackOf z₀ K' (((M.household z₀ K').bellman)^[n] 0))
    (hcap : ∀ (n : ℕ) (s : M.State),
      M.policyOf z₀ K (((M.household z₀ K).bellman)^[n] 0) s < M.assetCap)
    (s : M.State) (hcash : M.cash z₀ K' s ≤ M.cash z₀ K s) :
    M.policy z₀ K' s ≤ M.policy z₀ K s := by
  have hV : M.IncDiff (M.household z₀ K').valueFunction (M.household z₀ K).valueFunction := by
    intro l x y hx hy hxy
    have h1 := (M.household z₀ K').tendsto_iterate_valueFunction 0
    have h2 := (M.household z₀ K).tendsto_iterate_valueFunction 0
    have hev : ∀ (V : ℕ → M.State →ᵇ ℝ) (V₀ : M.State →ᵇ ℝ), Tendsto V atTop (𝓝 V₀) →
        Tendsto (fun n => V n (M.stateAt y l) - V n (M.stateAt x l)) atTop
          (𝓝 (V₀ (M.stateAt y l) - V₀ (M.stateAt x l))) := fun V V₀ hV =>
      (((continuous_eval_const _).tendsto V₀).comp hV).sub
        (((continuous_eval_const _).tendsto V₀).comp hV)
    exact le_of_tendsto_of_tendsto' (hev _ _ h1) (hev _ _ h2) fun n =>
      M.incDiff_iterate_cd U z₀ hγ0 hγ1 hdu hR' hRle hW hb hsl hsl' hcap n l x y hx hy hxy
  exact M.policy_le_policy z₀ s hcash (M.cont_increasingDifferences z₀ s hV)

end KSModel

/-! ### Cobb–Douglas prices move the right way -/

namespace CobbDouglas

variable (T : CobbDouglas Z)

theorem clampCap_mono {K K' : ℝ} (h : K ≤ K') : T.clampCap K ≤ T.clampCap K' :=
  max_le_max le_rfl (min_le_min le_rfl h)

/-- **The return falls with capital.** -/
theorem grossReturn_anti (z : Z) {K K' : ℝ} (h : K ≤ K') (L : ℝ) :
    T.grossReturn z K' L ≤ T.grossReturn z K L := by
  have h1 : T.clampCap K' ^ (T.share - 1) ≤ T.clampCap K ^ (T.share - 1) :=
    Real.rpow_le_rpow_of_nonpos (T.clampCap_pos K) (T.clampCap_mono h)
      (by linarith [T.share_lt_one])
  have h2 : 0 ≤ T.share * T.tfp z := mul_nonneg T.share_pos.le (T.tfp_pos z).le
  have h3 : 0 ≤ T.clampLab L ^ (1 - T.share) := Real.rpow_nonneg (T.clampLab_pos L).le _
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) h3
  simp only [grossReturn]
  linarith

/-- **The wage rises with capital.** -/
theorem wage_mono (z : Z) {K K' : ℝ} (h : K ≤ K') (L : ℝ) :
    T.wage z K L ≤ T.wage z K' L := by
  have h1 : T.clampCap K ^ T.share ≤ T.clampCap K' ^ T.share :=
    Real.rpow_le_rpow (T.clampCap_pos K).le (T.clampCap_mono h) T.share_pos.le
  have h2 : 0 ≤ (1 - T.share) * T.tfp z :=
    mul_nonneg (by linarith [T.share_lt_one]) (T.tfp_pos z).le
  have h3 : 0 ≤ T.clampLab L ^ (-T.share) := Real.rpow_nonneg (T.clampLab_pos L).le _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) h3

end CobbDouglas

/-! ### The CRRA, Cobb–Douglas household -/

variable (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)

/-- **Step (a) of B2 for CRRA, Cobb–Douglas with γ ≤ 1**: if the expected capital path is higher at
every node (labour unchanged), every household with no more cash today saves weakly less —
lower future returns and higher future wages both lower saving. Floor and cap slackness along the
Bellman iterates are explicit hypotheses. -/
theorem crra_policy_le_of_capital (hγ1 : γ ≤ 1) (z₀ : Z) {K K' : List Z → ℝ × ℝ}
    (hK : ∀ h, (K h).1 ≤ (K' h).1) (hL : ∀ h, (K h).2 = (K' h).2)
    (hsl : ∀ n : ℕ, (crraModel V T hγ).SlackOf z₀ K
      ((((crraModel V T hγ).household z₀ K).bellman)^[n] 0))
    (hsl' : ∀ n : ℕ, (crraModel V T hγ).SlackOf z₀ K'
      ((((crraModel V T hγ).household z₀ K').bellman)^[n] 0))
    (hcap : ∀ (n : ℕ) (s : (crraModel V T hγ).State),
      (crraModel V T hγ).policyOf z₀ K ((((crraModel V T hγ).household z₀ K).bellman)^[n] 0) s
        < (crraModel V T hγ).assetCap)
    (s : (crraModel V T hγ).State)
    (hcash : (crraModel V T hγ).cash z₀ K' s ≤ (crraModel V T hγ).cash z₀ K s) :
    (crraModel V T hγ).policy z₀ K' s ≤ (crraModel V T hγ).policy z₀ K s := by
  refine KSModel.policy_le_of_cd (crraSmoothUtility V T hγ) z₀ hγ hγ1 (fun _ _ => rfl)
    (fun h => T.grossReturn_pos _ _ _) (fun h => ?_) (fun h => ?_) rfl hsl hsl' hcap s hcash
  · change T.grossReturn (shockAt z₀ h) (K' h).1 (K' h).2
      ≤ T.grossReturn (shockAt z₀ h) (K h).1 (K h).2
    rw [← hL h]
    exact T.grossReturn_anti _ (hK h) _
  · change T.wage (shockAt z₀ h) (K h).1 (K h).2 ≤ T.wage (shockAt z₀ h) (K' h).1 (K' h).2
    rw [← hL h]
    exact T.wage_mono _ (hK h) _

end KrusellSmith

end LeanEconomics
