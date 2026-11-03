/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.FixedPoint.BrouwerBall

/-!
# The Brouwer fixed-point theorem

SLP §17.3, Theorem 17.3 (p. 517), quoted in the book without proof: a continuous self-map of a
nonempty, closed, bounded, convex subset of a finite-dimensional normed space has a fixed point.
The ball case is `brouwer_closedBall`; this module reduces the general case to it.

* `exists_lipschitz_retraction`: a nonempty complete convex subset `K` of a real inner product
  space is a 1-Lipschitz retract of the whole space (nearest-point projection).
* `brouwer_inner`: Brouwer for compact convex `K` in a finite-dimensional real inner product space
  (extend `f` by `f ∘ P_K` and rescale `K` into the unit ball).
* `brouwer`: Brouwer for a nonempty compact convex `K` in any finite-dimensional
  real normed space (transport to Euclidean space along `toEuclidean`).
* `brouwer_subtype`: the same for a continuous self-map `f : K → K` of the subtype.
* `theorem_17_3` (**Theorem 17.3**, p. 517): the book's form, for `F` nonempty, closed, bounded
  and convex (compact by Heine–Borel in finite dimensions) and `T : F → F` continuous.
-/

namespace LeanEconomics.FixedPoint

open Metric Set Filter Topology Module
open scoped RealInnerProductSpace

/-- **Nearest-point retraction.** A nonempty complete convex subset `K` of a real inner product
space is a retract of the whole space by a 1-Lipschitz (in particular continuous) map. -/
theorem exists_lipschitz_retraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (hne : K.Nonempty) (hcpl : IsComplete K) (hconv : Convex ℝ K) :
    ∃ P : E → E, LipschitzWith 1 P ∧ (∀ x, P x ∈ K) ∧ ∀ x ∈ K, P x = x := by
  choose P hPK hPmin using exists_norm_eq_iInf_of_complete_convex hne hcpl hconv
  have hvar : ∀ x, ∀ w ∈ K, ⟪x - P x, w - P x⟫ ≤ 0 := fun x =>
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hPK x)).1 (hPmin x)
  refine ⟨P, LipschitzWith.of_dist_le_mul fun x y => ?_, hPK, fun x hx => ?_⟩
  · rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have h1 := hvar x (P y) (hPK y)
    have h2 := hvar y (P x) (hPK x)
    have h3 : ‖P x - P y‖ ^ 2 ≤ ⟪x - y, P x - P y⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      have e1 : ⟪x - P x, P y - P x⟫ = ⟪x - y, P y - P x⟫ + ⟪y - P y, P y - P x⟫ +
          ⟪P y - P x, P y - P x⟫ := by
        rw [← inner_add_left, ← inner_add_left]
        congr 1
        abel
      have e2 : ⟪y - P y, P x - P y⟫ = -⟪y - P y, P y - P x⟫ := by
        rw [← inner_neg_right, neg_sub]
      have e3 : ⟪x - y, P x - P y⟫ = -⟪x - y, P y - P x⟫ := by
        rw [← inner_neg_right, neg_sub]
      have e4 : ⟪P x - P y, P x - P y⟫ = ⟪P y - P x, P y - P x⟫ := by
        rw [← inner_neg_neg, neg_sub]
      linarith
    have h4 : ⟪x - y, P x - P y⟫ ≤ ‖x - y‖ * ‖P x - P y‖ := real_inner_le_norm _ _
    nlinarith [norm_nonneg (P x - P y), norm_nonneg (x - y)]
  · have h := hvar x x hx
    rw [real_inner_self_eq_norm_sq] at h
    have : ‖x - P x‖ = 0 := by nlinarith [norm_nonneg (x - P x)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

/-- **Brouwer fixed-point theorem in a finite-dimensional real inner product space.** A map
continuous on a nonempty compact convex set `K` and mapping `K` into itself has a fixed point
in `K`. -/
theorem brouwer_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) {f : E → E} (hf : ContinuousOn f K) (hmaps : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  obtain ⟨P, hPlip, hPK, hPid⟩ := exists_lipschitz_retraction hne hK.isComplete hconv
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall 0
  set R := max R0 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR0' : 0 < R := by linarith
  have hKR : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx =>
    (mem_closedBall_zero_iff.1 (hR0 hx)).trans (le_max_left _ _)
  set h : E → E := fun y => R⁻¹ • f (P (R • y)) with hhdef
  have hcont : ContinuousOn h (closedBall 0 1) := by
    refine continuousOn_const.smul (hf.comp ?_ fun y _ => hPK _)
    exact (hPlip.continuous.comp (continuous_const.smul continuous_id)).continuousOn
  have hmapsB : MapsTo h (closedBall 0 1) (closedBall 0 1) := by
    intro y _
    rw [mem_closedBall_zero_iff, hhdef, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_le_iff₀ hR0', mul_one]
    exact hKR _ (hmaps (hPK _))
  obtain ⟨y, -, hy⟩ := brouwer_closedBall hcont hmapsB
  have hfx : f (P (R • y)) = R • y := by
    have h1 := congrArg (fun z => R • z) hy
    simp only [hhdef, smul_smul, mul_inv_cancel₀ hR0'.ne', one_smul] at h1
    exact h1
  have hxK : R • y ∈ K := hfx ▸ hmaps (hPK _)
  refine ⟨R • y, hxK, ?_⟩
  calc f (R • y) = f (P (R • y)) := by rw [hPid _ hxK]
    _ = R • y := hfx

/-- **Brouwer fixed-point theorem.** Let `K` be a nonempty compact convex
subset of a finite-dimensional real normed space `E`, and `f` a map continuous on `K` with
`f(K) ⊆ K`. Then `f` has a fixed point in `K`. -/
theorem brouwer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) {f : E → E}
    (hf : ContinuousOn f K) (hmaps : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  set e := (toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))) with he
  set K' := e '' K with hK'
  set f' := fun y => e (f (e.symm y)) with hf'
  have hmapsK' : MapsTo e.symm K' K := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  have hK'c : IsCompact K' := hK.image e.continuous
  have hK'conv : Convex ℝ K' := by
    simpa [hK'] using hconv.linear_image e.toLinearEquiv.toLinearMap
  have hf'c : ContinuousOn f' K' :=
    e.continuous.comp_continuousOn (hf.comp e.symm.continuous.continuousOn hmapsK')
  have hf'm : MapsTo f' K' K' := fun y hy => ⟨_, hmaps (hmapsK' hy), rfl⟩
  obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := brouwer_inner hK'c hK'conv (hne.image e) hf'c hf'm
  refine ⟨x, hx, e.injective ?_⟩
  simpa [hf'] using hy

/-- **Brouwer fixed-point theorem, subtype form.** A continuous self-map of a nonempty compact
convex subset `K` of a finite-dimensional real normed space has a fixed point. -/
theorem brouwer_subtype {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) {f : K → K} (hf : Continuous f) : ∃ x : K, f x = x := by
  classical
  set F : E → E := fun x => if h : x ∈ K then (f ⟨x, h⟩ : E) else x with hFdef
  have hFK : ∀ x : K, F x = f x := fun x => by simp [hFdef, x.2]
  have hFc : ContinuousOn F K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : K.domRestrict F = fun x : K => (f x : E) := funext hFK
    rw [this]
    exact continuous_subtype_val.comp hf
  have hFm : MapsTo F K K := fun x hx => by
    rw [hFK ⟨x, hx⟩]
    exact (f _).2
  obtain ⟨x, hx, hFx⟩ := brouwer hK hconv hne hFc hFm
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [← hFK ⟨x, hx⟩]
  exact hFx

/-- **Theorem 17.3 (Brouwer fixed-point theorem)**, p. 517. Let `F` be a nonempty, closed,
bounded, convex subset of a finite-dimensional real normed space. Every continuous `T : F → F`
has a fixed point. -/
theorem theorem_17_3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Set E} (hne : F.Nonempty) (hcl : IsClosed F)
    (hbdd : Bornology.IsBounded F) (hconv : Convex ℝ F) {T : F → F} (hT : Continuous T) :
    ∃ f : F, T f = f :=
  brouwer_subtype (Metric.isCompact_of_isClosed_isBounded hcl hbdd) hconv hne hT

end LeanEconomics.FixedPoint
