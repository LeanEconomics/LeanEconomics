/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Aggregates

/-!
# The CRRA Euler bound on consumption

Milestone C2 of `CLAMP_PLAN.md`, after Cao (2020, Lemmas 7 and 9). With CRRA marginal utility
`u'(c) = c^{-γ}`, a household that saves below the asset cap consumes at most
`(β π R')^{-1/γ}` times its expected consumption at the child with the same aggregate shock,
where `π` bounds the probability that the aggregate shock repeats and `R'` is the gross return
there (`consumption_le_child`):

* the Euler inequality `u'(c) ≥ β E[R' u'(c')]` (`euler_ge`);
* drop every child except the one with the same aggregate shock;
* Jensen for the convex `c ↦ c^{-γ}` (`convexOn_rpow_neg`): `E[c'^{-γ}] ≥ (E c')^{-γ}`;
* invert: `c^{-γ} ≥ A m^{-γ}` gives `c ≤ A^{-1/γ} m`.

A household at the asset cap consumes at most its cash on hand, at most `R a + w ē` with
`a ≤ assetCap`. Weighting that by `a' / assetCap`, which is one at the cap, gives a bound valid
for **every** household (`consumption_le`):

    c ≤ (β π R')^{-1/γ} E[c'] + (a' / assetCap) (R · assetCap + w ē).
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

/-- **`c ↦ c^{-γ}` is convex on `(0, ∞)`** for `γ > 0`. -/
theorem convexOn_rpow_neg {γ : ℝ} (hγ : 0 < γ) : ConvexOn ℝ (Ioi 0) fun x : ℝ => x ^ (-γ) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
    (fun x hx => (Real.continuousAt_rpow_const x (-γ) (Or.inl (ne_of_gt hx))).continuousWithinAt)
    ?_ ?_
  · rw [interior_Ioi]
    exact fun x hx =>
      (Real.hasDerivAt_rpow_const (p := -γ) (Or.inl (ne_of_gt hx))).differentiableAt
        |>.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx y hy hxy
    have hx0 : (0 : ℝ) < x := hx
    have hy0 : (0 : ℝ) < y := hy
    rw [(Real.hasDerivAt_rpow_const (p := -γ) (Or.inl hx0.ne')).deriv,
      (Real.hasDerivAt_rpow_const (p := -γ) (Or.inl hy0.ne')).deriv]
    exact mul_le_mul_of_nonpos_left (Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith))
      (by linarith)

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (U : M.SmoothUtility) (z₀ : Z) (K : List Z → ℝ × ℝ) {γ : ℝ}

/-- **The CRRA Euler bound.** A household saving below the asset cap, with CRRA marginal utility
above the floor, consumes at most `(β π R')^{-1/γ}` times its expected consumption at the child
`z :: h` with the same aggregate shock `z`, where `π ≤ aggProb z z` and `R'` is the gross return
there. -/
theorem consumption_le_child (hγ : 0 < γ)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) (hsl : M.Slack z₀ K) (s : M.State)
    (hcap : M.policy z₀ K s < M.assetCap) {π : ℝ} (hπ : 0 < π)
    (hπle : π ≤ M.aggProb (shockAt z₀ s.2.node) (shockAt z₀ s.2.node))
    (hR : 0 < M.returnAt z₀ K (shockAt z₀ s.2.node :: s.2.node)) :
    M.consumption z₀ K s
      ≤ (M.discount * π * M.returnAt z₀ K (shockAt z₀ s.2.node :: s.2.node)) ^ (-1 / γ)
        * ∑ e', M.idioProb (shockAt z₀ s.2.node) (shockAt z₀ s.2.node) s.2.idio e'
          * M.consumption z₀ K
              (M.stateAt (M.policy z₀ K s) ⟨e', shockAt z₀ s.2.node :: s.2.node⟩) := by
  set zs := shockAt z₀ s.2.node with hzs
  set p := M.policy z₀ K s with hp
  set R := M.returnAt z₀ K (zs :: s.2.node) with hRdef
  set q : E → ℝ := fun e' => M.idioProb zs zs s.2.idio e' with hq
  set cc : E → ℝ := fun e' => M.consumption z₀ K (M.stateAt p ⟨e', zs :: s.2.node⟩) with hcc
  set c := M.consumption z₀ K s with hc
  have hc0 : 0 < c := M.consFloor_nonneg.trans_lt (hsl s)
  have hcc0 : ∀ e', 0 < cc e' := fun e' => M.consFloor_nonneg.trans_lt (hsl _)
  have hq0 : ∀ e', 0 ≤ q e' := fun e' => M.idioProb_nonneg _ _ _ _
  have hq1 : ∑ e', q e' = 1 := M.idioProb_sum _ _ _
  have hβ := M.discount_pos
  -- the Euler inequality
  have h1 := euler_ge U z₀ K hsl s hcap
  -- only the child with the same aggregate shock
  have h2 : π * R * ∑ e', q e' * cc e' ^ (-γ) ≤ M.eulerRhs U z₀ K s p := by
    have hterm : ∀ ze : Z × E, 0 ≤ M.shockProb z₀ ze (s, p) * M.returnAt z₀ K (ze.1 :: s.2.node)
        * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)) := by
      intro ze
      rw [hdu _ (hsl _)]
      exact mul_nonneg (mul_nonneg (M.shockProb_nonneg' z₀ ze _) (M.grossReturn_nonneg _ _ _))
        (Real.rpow_nonneg (M.consFloor_nonneg.trans (hsl _).le) _)
    simp only [eulerRhs]
    rw [Fintype.sum_prod_type]
    refine le_trans ?_ (Finset.single_le_sum (f := fun z => ∑ e', M.shockProb z₀ (z, e') (s, p)
      * M.returnAt z₀ K (z :: s.2.node)
      * U.du (M.consumption z₀ K (M.stateAt p ⟨e', z :: s.2.node⟩)))
      (fun z _ => Finset.sum_nonneg fun e' _ => hterm (z, e')) (Finset.mem_univ zs))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e' _ => ?_
    rw [hdu _ (hsl _)]
    change π * R * (q e' * cc e' ^ (-γ))
      ≤ M.aggProb zs zs * q e' * R * cc e' ^ (-γ)
    have hR0 := hR.le
    have hw : 0 ≤ q e' * R * cc e' ^ (-γ) :=
      mul_nonneg (mul_nonneg (hq0 e') hR0) (Real.rpow_nonneg (hcc0 e').le _)
    nlinarith [mul_le_mul_of_nonneg_right hπle hw]
  -- Jensen
  set m := ∑ e', q e' * cc e' with hm
  have hm0 : 0 < m := by
    obtain ⟨e₁, he₁⟩ : ∃ e, 0 < q e := by
      by_contra hne
      simp only [not_exists, not_lt] at hne
      have : ∑ e', q e' ≤ 0 := Finset.sum_nonpos fun e _ => hne e
      linarith
    calc 0 < q e₁ * cc e₁ := mul_pos he₁ (hcc0 e₁)
      _ ≤ m := Finset.single_le_sum (f := fun e => q e * cc e)
          (fun e _ => mul_nonneg (hq0 e) (hcc0 e).le) (Finset.mem_univ e₁)
  have h3 : m ^ (-γ) ≤ ∑ e', q e' * cc e' ^ (-γ) := by
    have := (convexOn_rpow_neg hγ).map_sum_le (t := Finset.univ) (w := q) (p := cc)
      (fun e _ => hq0 e) hq1 (fun e _ => hcc0 e)
    simpa only [smul_eq_mul] using this
  -- combine: `A m^{-γ} ≤ c^{-γ}`
  set A := M.discount * π * R with hA
  have hA0 : 0 < A := mul_pos (mul_pos hβ hπ) hR
  have h4 : A * m ^ (-γ) ≤ c ^ (-γ) := by
    rw [← hdu c (hsl s)]
    have h5 : M.discount * (π * R * ∑ e', q e' * cc e' ^ (-γ)) ≤ U.du c :=
      (mul_le_mul_of_nonneg_left h2 hβ.le).trans h1
    have h6 : A * m ^ (-γ) ≤ M.discount * (π * R * ∑ e', q e' * cc e' ^ (-γ)) := by
      rw [hA, show M.discount * π * R * m ^ (-γ) = M.discount * (π * R * m ^ (-γ)) by ring]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h3 (mul_nonneg hπ.le hR.le)) hβ.le
    linarith
  -- invert
  have hpos : 0 < A * m ^ (-γ) := mul_pos hA0 (Real.rpow_pos_of_pos hm0 _)
  have h7 := Real.rpow_le_rpow_of_nonpos hpos h4 (show -1 / γ ≤ 0 by
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hγ.le)
  have hexp : -γ * (-1 / γ) = 1 := by field_simp
  rw [← Real.rpow_mul hc0.le, hexp, Real.rpow_one, Real.mul_rpow hA0.le
    (Real.rpow_nonneg hm0.le _), ← Real.rpow_mul hm0.le, hexp, Real.rpow_one] at h7
  exact h7

/-- **The consumption bound for every household.** With `ē` bounding efficiency, every
household, at the asset cap or not, consumes at most
`(β π R')^{-1/γ} E[c'] + (a' / assetCap) (R · assetCap + w ē)`. -/
theorem consumption_le (hγ : 0 < γ)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) (hsl : M.Slack z₀ K) (s : M.State)
    {π : ℝ} (hπ : 0 < π) (hπle : π ≤ M.aggProb (shockAt z₀ s.2.node) (shockAt z₀ s.2.node))
    (hR : 0 < M.returnAt z₀ K (shockAt z₀ s.2.node :: s.2.node)) {ē : ℝ}
    (hē : ∀ e, M.efficiency e ≤ ē) :
    M.consumption z₀ K s
      ≤ (M.discount * π * M.returnAt z₀ K (shockAt z₀ s.2.node :: s.2.node)) ^ (-1 / γ)
          * ∑ e', M.idioProb (shockAt z₀ s.2.node) (shockAt z₀ s.2.node) s.2.idio e'
            * M.consumption z₀ K
                (M.stateAt (M.policy z₀ K s) ⟨e', shockAt z₀ s.2.node :: s.2.node⟩)
        + M.policy z₀ K s / M.assetCap
          * (M.returnAt z₀ K s.2.node * M.assetCap + M.wageAt z₀ K s.2.node * ē) := by
  have hpI := M.policy_mem_Icc z₀ K s
  have hcap0 := M.assetCap_pos
  have hRh : 0 ≤ M.returnAt z₀ K s.2.node := M.grossReturn_nonneg _ _ _
  have hwh : 0 ≤ M.wageAt z₀ K s.2.node := M.wage_nonneg _ _ _
  have hē0 : 0 ≤ ē := (M.efficiency_nonneg s.2.idio).trans (hē _)
  have hsec : 0 ≤ M.policy z₀ K s / M.assetCap
      * (M.returnAt z₀ K s.2.node * M.assetCap + M.wageAt z₀ K s.2.node * ē) :=
    mul_nonneg (div_nonneg hpI.1 hcap0.le) (add_nonneg (mul_nonneg hRh hcap0.le)
      (mul_nonneg hwh hē0))
  have hfirst : 0 ≤ (M.discount * π * M.returnAt z₀ K (shockAt z₀ s.2.node :: s.2.node)) ^ (-1 / γ)
      * ∑ e', M.idioProb (shockAt z₀ s.2.node) (shockAt z₀ s.2.node) s.2.idio e'
        * M.consumption z₀ K
            (M.stateAt (M.policy z₀ K s) ⟨e', shockAt z₀ s.2.node :: s.2.node⟩) :=
    mul_nonneg (Real.rpow_nonneg (mul_nonneg (mul_nonneg M.discount_pos.le hπ.le) hR.le) _)
      (Finset.sum_nonneg fun e' _ => mul_nonneg (M.idioProb_nonneg _ _ _ _)
        (M.consFloor_nonneg.trans (hsl _).le))
  rcases hpI.2.lt_or_eq with hlt | heq
  · have := consumption_le_child U z₀ K hγ hdu hsl s hlt hπ hπle hR
    linarith
  · -- at the cap: consumption is at most cash on hand
    have hcash : M.consumption z₀ K s
        ≤ M.returnAt z₀ K s.2.node * M.assetCap + M.wageAt z₀ K s.2.node * ē := by
      have ha := s.1.2
      have h1 : M.consumption z₀ K s ≤ M.cash z₀ K s := by
        simp only [consumption]
        linarith [hpI.1]
      refine h1.trans ?_
      have h2 := mul_le_mul_of_nonneg_left ha.2 hRh
      have h3 := mul_le_mul_of_nonneg_left (hē s.2.idio) hwh
      have h4 := mul_nonneg hRh M.borrowLimit_nonneg
      simp only [cash]
      linarith
    have hone : M.policy z₀ K s / M.assetCap
        * (M.returnAt z₀ K s.2.node * M.assetCap + M.wageAt z₀ K s.2.node * ē)
        = M.returnAt z₀ K s.2.node * M.assetCap + M.wageAt z₀ K s.2.node * ē := by
      rw [heq, div_self hcap0.ne', one_mul]
    linarith

end KSModel

end KrusellSmith

end LeanEconomics
