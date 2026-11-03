/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# There is no C¹ retraction of the closed ball onto its boundary sphere

Foundation for the Brouwer fixed-point theorem of SLP §17.3 (Theorem 17.3, p. 517), which the
book quotes without proof. Mathlib has no Brouwer theorem; this module proves the analytic core of
the argument of Milnor in the form given by C. A. Rogers, *A less strange version of Milnor's proof
of Brouwer's fixed-point theorem*, Amer. Math. Monthly 87 (1980).

`E` is a finite-dimensional real normed space and `B` its closed unit ball.

* `exists_polynomial_det_id_add_smul`: `s ↦ det (id + s • A)` is a polynomial of degree at most
  `dim E`.
* `integral_eq_of_polynomial_of_eq_on_Ioc`: if `φ x s` is a polynomial in `s` of bounded degree
  and `∫ φ x s dμ(x) = c` for all `s ∈ (0, δ]`, then `∫ φ x r dμ(x) = c` for every `r`
  (Lagrange interpolation).
* `no_C1_retraction` (Rogers' lemma): there is no map `g`, C¹ on an open neighbourhood of `B`,
  with `‖g x‖ = 1` on `B` and `g x = x` on the unit sphere.

Proof of `no_C1_retraction`. Put `f_t x = x + t (g x − x)` and `V(t) = ∫_{B°} det D f_t`.
For small `t > 0`, `f_t` is injective on the open ball `B°` (since `g − id` is Lipschitz there),
`det D f_t > 0`, and `f_t(B°) = B°`: the image lies in `B°`, is open (inverse function theorem),
and is relatively closed in `B°` because `f_t` fixes the sphere. By the change of variables formula
`V(t) = vol(B°)`. `V` is a polynomial, so `V(1) = vol(B°) > 0`; but `D f_1 = D g` is singular on
`B°` (otherwise `g` would map a neighbourhood onto a neighbourhood of a point of the sphere), so
`V(1) = 0`.
-/

namespace LeanEconomics.FixedPoint

open Polynomial MeasureTheory Metric Set Filter Topology Module

/-- For a continuous linear endomorphism `A` of a finite-dimensional real normed space `E`, the
function `s ↦ det (id + s • A)` is a polynomial of degree at most `dim E`. -/
theorem exists_polynomial_det_id_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →L[ℝ] E) :
    ∃ p : ℝ[X], p.natDegree ≤ finrank ℝ E ∧
      ∀ s : ℝ, p.eval s = (ContinuousLinearMap.id ℝ E + s • A).det := by
  let b := Module.finBasis ℝ E
  let M := LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)
  refine ⟨Matrix.det ((X : ℝ[X]) • M.map C +
    (1 : Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ).map C), ?_, fun s => ?_⟩
  · simpa using natDegree_det_X_add_C_le M 1
  · rw [← coe_evalRingHom, RingHom.map_det, ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [M, hij] <;> ring

/-- Lagrange interpolation under the integral. Let `φ x s` be, for every `x`, a polynomial in `s`
of degree at most `N`, integrable in `x` for every `s`. If `∫ φ x s dμ(x) = c` for all
`s ∈ (0, δ]`, then `∫ φ x r dμ(x) = c` for every `r`. -/
theorem integral_eq_of_polynomial_of_eq_on_Ioc {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {φ : X → ℝ → ℝ} {N : ℕ} (hpoly : ∀ x, ∃ p : ℝ[X], p.natDegree ≤ N ∧ ∀ s, p.eval s = φ x s)
    (hint : ∀ s, Integrable (fun x => φ x s) μ) {δ c : ℝ} (hδ : 0 < δ)
    (hc : ∀ s ∈ Ioc 0 δ, ∫ x, φ x s ∂μ = c) (r : ℝ) : ∫ x, φ x r ∂μ = c := by
  let v : ℕ → ℝ := fun j => δ / (j + 1)
  let S : Finset ℕ := Finset.range (N + 1)
  have hinj : Set.InjOn v S := by
    intro i _ j _ h
    have hi : (0 : ℝ) < i + 1 := by positivity
    have hj : (0 : ℝ) < j + 1 := by positivity
    simp only [v] at h
    rw [div_eq_div_iff hi.ne' hj.ne'] at h
    have : (j : ℝ) + 1 = i + 1 := mul_left_cancel₀ hδ.ne' h
    exact_mod_cast (by linarith : (i : ℝ) = j)
  have hv : ∀ j, v j ∈ Ioc 0 δ := by
    intro j
    have hj : (1 : ℝ) ≤ j + 1 := by have := j.cast_nonneg (α := ℝ); linarith
    exact ⟨by positivity, div_le_self hδ.le hj⟩
  have key : ∀ x, φ x r = ∑ j ∈ S, φ x (v j) * (Lagrange.basis S v j).eval r := by
    intro x
    obtain ⟨p, hpN, hp⟩ := hpoly x
    have hdeg : p.degree < S.card := by
      refine (degree_le_natDegree).trans_lt ?_
      simp only [S, Finset.card_range]
      exact_mod_cast Nat.lt_succ_of_le hpN
    rw [← hp r]
    conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
    simp [Lagrange.interpolate_apply, eval_finsetSum, hp]
  calc ∫ x, φ x r ∂μ = ∫ x, ∑ j ∈ S, φ x (v j) * (Lagrange.basis S v j).eval r ∂μ := by
        simp_rw [← key]
    _ = ∑ j ∈ S, (∫ x, φ x (v j) ∂μ) * (Lagrange.basis S v j).eval r := by
        rw [integral_finsetSum _ fun j _ => (hint (v j)).mul_const _]
        exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
    _ = c * (∑ j ∈ S, Lagrange.basis S v j).eval r := by
        simp [hc _ (hv _), eval_finsetSum, Finset.mul_sum]
    _ = c := by
        rw [Lagrange.sum_basis hinj ⟨0, by simp [S]⟩]
        simp

/-- A linear map `id + s • A` with `s ‖A‖ < 1` is injective, hence (in finite dimensions) has
nonzero determinant and full range. -/
theorem isUnit_id_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {A : E →L[ℝ] E} {s : ℝ} (hs : 0 ≤ s) (hA : s * ‖A‖ < 1) :
    IsUnit ((ContinuousLinearMap.id ℝ E + s • A : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hv' : v = -(s • A v) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa using hv
  have h1 : ‖v‖ ≤ s * ‖A‖ * ‖v‖ := by
    calc ‖v‖ = ‖-(s • A v)‖ := by rw [← hv']
      _ = s * ‖A v‖ := by rw [norm_neg, norm_smul, Real.norm_of_nonneg hs]
      _ ≤ s * (‖A‖ * ‖v‖) := mul_le_mul_of_nonneg_left (A.le_opNorm v) hs
      _ = s * ‖A‖ * ‖v‖ := by ring
  have h2 : ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v]
  exact norm_le_zero_iff.1 h2

/-- **Rogers' lemma** (no C¹ retraction of the ball onto the sphere). Let `E` be a
finite-dimensional real normed space. There is no map `g : E → E` that is C¹ on an open set
`U ⊇ closedBall 0 1`, takes values of norm `1` on the closed unit ball, and fixes every point of
the unit sphere. -/
theorem no_C1_retraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → E} {U : Set E} (hU : IsOpen U)
    (hBU : closedBall (0 : E) 1 ⊆ U) (hg : ContDiffOn ℝ 1 g U)
    (hsph : ∀ x ∈ closedBall (0 : E) 1, ‖g x‖ = 1) (hid : ∀ x : E, ‖x‖ = 1 → g x = x) :
    False := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar
  set B := closedBall (0 : E) 1 with hB
  set Bo := ball (0 : E) 1 with hBo
  have hBoB : Bo ⊆ B := ball_subset_closedBall
  set g' := fderiv ℝ g
  have hstrict : ∀ x ∈ U, HasStrictFDerivAt g (g' x) x := fun x hx =>
    (hg.contDiffAt (hU.mem_nhds hx)).hasStrictFDerivAt one_ne_zero
  have hg'c : ContinuousOn g' U := hg.continuousOn_fderiv_of_isOpen hU le_rfl
  set A : E → E →L[ℝ] E := fun x => g' x - ContinuousLinearMap.id ℝ E with hAdef
  have hAc : ContinuousOn A U := hg'c.sub continuousOn_const
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn (hAc.mono hBU)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 (mem_closedBall_self zero_le_one))
  -- `g − id` is `L`-Lipschitz on the open ball
  have hlip : ∀ x ∈ Bo, ∀ y ∈ Bo, ‖(g y - y) - (g x - x)‖ ≤ L * ‖y - x‖ := by
    intro x hx y hy
    refine (convex_ball (0 : E) 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z => g z - z) (f' := A) (fun z hz => ?_) (fun z hz => hL z (hBoB hz)) hx hy
    exact ((hstrict z (hBU (hBoB hz))).hasFDerivAt.sub (hasFDerivAt_id z)).hasFDerivWithinAt
  have hgc : ContinuousOn g B := hg.continuousOn.mono hBU
  set δ : ℝ := 1 / (L + 2) with hδ
  have hδ0 : 0 < δ := by positivity
  -- the volume integral of the Jacobian of `x ↦ x + t (g x − x)`
  have hc : ∀ t ∈ Ioc 0 δ, ∫ x in Bo, (ContinuousLinearMap.id ℝ E + t • A x).det ∂μ
      = μ.real Bo := by
    rintro t ⟨ht0, htδ⟩
    have htL : t * L < 1 := by
      calc t * L ≤ δ * L := mul_le_mul_of_nonneg_right htδ hL0
        _ < 1 := by rw [hδ, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]; linarith
    have ht1 : t < 1 := by
      calc t ≤ δ := htδ
        _ < 1 := by rw [hδ, div_lt_one (by linarith)]; linarith
    set F : E → E := fun x => x + t • (g x - x) with hFdef
    have hF' : ∀ x ∈ U, HasStrictFDerivAt F (ContinuousLinearMap.id ℝ E + t • A x) x :=
      fun x hx => (hasStrictFDerivAt_id x).add
        (((hstrict x hx).sub (hasStrictFDerivAt_id x)).const_smul t)
    have hunit : ∀ x ∈ B, ∀ s ∈ Icc 0 t,
        IsUnit ((ContinuousLinearMap.id ℝ E + s • A x : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
      rintro x hx s ⟨hs0, hst⟩
      refine isUnit_id_add_smul hs0 ?_
      calc s * ‖A x‖ ≤ t * L := mul_le_mul hst (hL x hx) (norm_nonneg _) ht0.le
        _ < 1 := htL
    have hdetpos : ∀ x ∈ B, 0 < (ContinuousLinearMap.id ℝ E + t • A x).det := by
      intro x hx
      by_contra hneg
      rw [not_lt] at hneg
      set φ : ℝ → ℝ := fun s => (ContinuousLinearMap.id ℝ E + s • A x).det
      have hφc : ContinuousOn φ (Icc 0 t) :=
        (ContinuousLinearMap.continuous_det.comp
          (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
      have hφ0 : φ 0 = 1 := by
        simp only [φ, zero_smul, add_zero, ContinuousLinearMap.det, ContinuousLinearMap.coe_id]
        exact LinearMap.det_id
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht0.le hφc
        ⟨hneg, by rw [hφ0]; exact zero_le_one⟩
      exact ((LinearMap.isUnit_iff_isUnit_det _).1 (hunit x hx s hs)).ne_zero hs0
    have hFB : ∀ x ∈ Bo, F x ∈ Bo := by
      intro x hx
      rw [hBo, mem_ball_zero_iff] at hx ⊢
      have hFx : F x = (1 - t) • x + t • g x := by
        simp only [hFdef, smul_sub, sub_smul, one_smul]
        abel
      rw [hFx]
      calc ‖(1 - t) • x + t • g x‖ ≤ ‖(1 - t) • x‖ + ‖t • g x‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * ‖g x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
            Real.norm_of_nonneg ht0.le]
        _ < 1 := by
          rw [hsph x (hBoB (mem_ball_zero_iff.2 hx))]
          nlinarith
    have hFS : ∀ x ∈ B, x ∉ Bo → F x = x := by
      intro x hx hxo
      have hx1 : ‖x‖ = 1 := le_antisymm (mem_closedBall_zero_iff.1 hx)
        (not_lt.1 fun h => hxo (mem_ball_zero_iff.2 h))
      simp [hFdef, hid x hx1]
    have hFcont : ContinuousOn F B := continuousOn_id.add (continuousOn_const.smul (hgc.sub
      continuousOn_id))
    have hopen : IsOpen (F '' Bo) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨x, hx, rfl⟩
      have hsurj : (ContinuousLinearMap.id ℝ E + t • A x).range = ⊤ :=
        (LinearMap.isUnit_iff_range_eq_top _).1 (hunit x (hBoB hx) t ⟨ht0.le, le_rfl⟩)
      rw [← (hF' x (hBU (hBoB hx))).map_nhds_eq_of_surj hsurj]
      exact image_mem_map (isOpen_ball.mem_nhds hx)
    have hcpt : IsCompact (F '' B) := (isCompact_closedBall (0 : E) 1).image_of_continuousOn hFcont
    have himage : F '' Bo = Bo := by
      refine Subset.antisymm (image_subset_iff.2 hFB) ?_
      refine (convex_ball (0 : E) 1).isPreconnected.subset_left_of_subset_union hopen
        hcpt.isClosed.isOpen_compl
        (Set.disjoint_compl_right_iff_subset.2 (image_mono hBoB)) ?_ ?_
      · intro y hy
        by_cases h : y ∈ F '' B
        · left
          obtain ⟨x, hxB, rfl⟩ := h
          by_cases hxo : x ∈ Bo
          · exact ⟨x, hxo, rfl⟩
          · rw [hFS x hxB hxo] at hy
            exact absurd hy hxo
        · exact Or.inr h
      · exact ⟨F 0, hFB 0 (mem_ball_self one_pos), 0, mem_ball_self one_pos, rfl⟩
    have hinjF : InjOn F Bo := by
      intro x hx y hy hxy
      have h1 := hlip y hy x hx
      have h2 : x - y = t • ((g y - y) - (g x - x)) := by
        simp only [hFdef] at hxy
        rw [smul_sub]
        linear_combination (norm := module) hxy
      have h3 : ‖x - y‖ ≤ t * L * ‖x - y‖ := by
        calc ‖x - y‖ = t * ‖(g y - y) - (g x - x)‖ := by
              rw [h2, norm_smul, Real.norm_of_nonneg ht0.le]
          _ ≤ t * (L * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact h1) ht0.le
          _ = t * L * ‖x - y‖ := by ring
      have h4 : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h4)
    have hcov := integral_image_eq_integral_abs_det_fderiv_smul μ measurableSet_ball
      (fun x hx => (hF' x (hBU (hBoB hx))).hasFDerivAt.hasFDerivWithinAt) hinjF
      (fun _ => (1 : ℝ))
    rw [himage] at hcov
    simp only [smul_eq_mul, mul_one, setIntegral_const, smul_eq_mul, mul_one] at hcov
    rw [hcov]
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    exact (abs_of_pos (hdetpos x (hBoB hx))).symm
  have hint : ∀ s : ℝ,
      Integrable (fun x => (ContinuousLinearMap.id ℝ E + s • A x).det) (μ.restrict Bo) := by
    intro s
    refine IntegrableOn.mono_set ?_ hBoB
    exact (ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.add ((hAc.mono hBU).const_smul s))).integrableOn_compact
      (isCompact_closedBall 0 1)
  have h1 := integral_eq_of_polynomial_of_eq_on_Ioc (μ := μ.restrict Bo)
    (fun x => exists_polynomial_det_id_add_smul (A x)) hint hδ0 hc 1
  have hzero : ∀ x ∈ Bo, (ContinuousLinearMap.id ℝ E + (1 : ℝ) • A x).det = 0 := by
    intro x hx
    have hxU : x ∈ U := hBU (hBoB hx)
    have hA1 : ContinuousLinearMap.id ℝ E + (1 : ℝ) • A x = g' x := by
      simp [hAdef]
    rw [hA1]
    by_contra hdet
    have hsurj : (g' x).range = ⊤ :=
      (LinearMap.isUnit_iff_range_eq_top _).1
        ((LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet))
    have hmap := (hstrict x hxU).map_nhds_eq_of_surj hsurj
    have hmem : sphere (0 : E) 1 ∈ 𝓝 (g x) := by
      rw [← hmap, mem_map]
      refine mem_of_superset (isOpen_ball.mem_nhds hx) fun y hy => ?_
      simp [hsph y (hBoB hy)]
    obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hmem
    have hgx : ‖g x‖ = 1 := hsph x (hBoB hx)
    have hy : g x + (r / 2) • g x ∈ ball (g x) r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hgx, mul_one,
        Real.norm_of_nonneg (by positivity)]
      linarith
    have hy1 := hrs hy
    rw [mem_sphere_zero_iff_norm] at hy1
    have : ‖g x + (r / 2) • g x‖ = 1 + r / 2 := by
      rw [← one_smul ℝ (g x), smul_smul, mul_one, ← add_smul, norm_smul, hgx, mul_one,
        Real.norm_of_nonneg (by positivity)]
    linarith
  rw [setIntegral_congr_fun measurableSet_ball hzero, integral_zero] at h1
  have hpos : 0 < μ.real Bo :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  linarith

end LeanEconomics.FixedPoint
