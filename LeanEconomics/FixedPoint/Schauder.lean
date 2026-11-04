/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.FixedPoint.Brouwer

/-!
# The Schauder fixed-point theorem

SLP §17.4 (Theorem 17.4, p. 520) quotes a version of Schauder's theorem for spaces of bounded
continuous functions without proof. This module proves the general theorem for real normed
spaces, from the Brouwer theorem `brouwer`; the book's form is `theorem_17_4` in
`FixedPointArguments.SchauderBoundedContinuous`.

* `exists_approx_fixed_point`: a continuous self-map `f` of a compact convex set `K` has
  `ε`-approximate fixed points for every `ε > 0`. Take a finite `ε`-net `{y_i} ⊆ K`, the Schauder
  projection `P x = Σ μ_i(x) y_i / Σ μ_i(x)` with `μ_i(x) = max(0, ε − ‖x − y_i‖)` (continuous on
  `K`, into `conv{y_i}`, with `‖P x − x‖ ≤ ε`), and a Brouwer fixed point of `P ∘ f` on the compact
  convex set `conv{y_i}` inside the finite-dimensional span of the `y_i`.
* `schauder`: a continuous self-map of a nonempty compact convex subset of a real normed space has
  a fixed point (approximate fixed points plus compactness).
* `schauder_subtype`: the same for `f : K → K`.
* `schauder_closed`: in a real Banach space, a map `T` continuous on a nonempty closed convex set
  `F`, with `T(F) ⊆ F` and `T(F)` relatively compact, has a fixed point (apply `schauder` to the
  closed convex hull of `T(F)`, compact by Mazur's theorem `TotallyBounded.convexHull`).
* `schauder_closed_subtype`: the same for `T : F → F`.
-/

namespace LeanEconomics.FixedPoint

open Metric Set Filter Topology Module

/-- **Approximate fixed points.** A map `f` continuous on a compact convex set `K` of a real
normed space, with `f(K) ⊆ K`, has for every `ε > 0` a point `x ∈ K` with `‖f x − x‖ ≤ ε`. -/
theorem exists_approx_fixed_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) {f : E → E}
    (hf : ContinuousOn f K) (hmaps : MapsTo f K K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ K, ‖f x - x‖ ≤ ε := by
  classical
  obtain ⟨t, htK, htfin, hcov⟩ := finite_approx_of_totallyBounded hK.totallyBounded ε hε
  set s : Finset E := htfin.toFinset with hs
  have hsK : (s : Set E) ⊆ K := by simpa [hs] using htK
  have hcov' : ∀ x ∈ K, ∃ y ∈ s, ‖x - y‖ < ε := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov hx)
    exact ⟨y, by simpa [hs] using hy, by rwa [mem_ball, dist_eq_norm] at hxy⟩
  -- the Schauder projection
  set μ : E → E → ℝ := fun y x => max 0 (ε - ‖x - y‖) with hμ
  have hμ0 : ∀ y x, 0 ≤ μ y x := fun y x => le_max_left _ _
  have hμc : ∀ y, Continuous (μ y) := fun y =>
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
  set P : E → E := fun x => (∑ y ∈ s, μ y x)⁻¹ • ∑ y ∈ s, μ y x • y with hP
  have hsum : ∀ x ∈ K, 0 < ∑ y ∈ s, μ y x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcov' x hx
    refine Finset.sum_pos' (fun z _ => hμ0 z x) ⟨y, hy, ?_⟩
    exact lt_max_of_lt_right (by linarith)
  have hPc : ContinuousOn P K := by
    refine ContinuousOn.smul ?_ ?_
    · exact (continuous_finsetSum _ fun y _ => hμc y).continuousOn.inv₀
        fun x hx => (hsum x hx).ne'
    · exact (continuous_finsetSum _ fun y _ => (hμc y).smul continuous_const).continuousOn
  set C : Set E := convexHull ℝ (s : Set E) with hC
  have hPC : ∀ x ∈ K, P x ∈ C := fun x hx =>
    s.centerMass_mem_convexHull (fun y _ => hμ0 y x) (hsum x hx) fun y hy => hy
  have hPclose : ∀ x ∈ K, ‖P x - x‖ ≤ ε := by
    intro x hx
    have hS := hsum x hx
    have hPx : P x - x = (∑ y ∈ s, μ y x)⁻¹ • ∑ y ∈ s, μ y x • (y - x) := by
      simp only [hP, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
      rw [smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
    rw [hPx, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hS.le), inv_mul_le_iff₀ hS]
    calc ‖∑ y ∈ s, μ y x • (y - x)‖ ≤ ∑ y ∈ s, μ y x * ε := by
          refine norm_sum_le_of_le _ fun y _ => ?_
          rw [norm_smul, Real.norm_of_nonneg (hμ0 y x)]
          by_cases hxy : ‖x - y‖ ≤ ε
          · rw [norm_sub_rev]
            exact mul_le_mul_of_nonneg_left hxy (hμ0 y x)
          · have : μ y x = 0 := max_eq_left (by linarith)
            simp [this]
      _ = (∑ y ∈ s, μ y x) * ε := by rw [Finset.sum_mul]
  -- Brouwer inside the span of the net
  set V : Submodule ℝ E := Submodule.span ℝ (s : Set E) with hV
  have hCV : C ⊆ V := convexHull_min Submodule.subset_span V.convex
  have hPV : ∀ x, P x ∈ V := fun x =>
    V.smul_mem _ (V.sum_mem fun y hy => V.smul_mem _ (Submodule.subset_span hy))
  set C' : Set V := (Subtype.val : V → E) ⁻¹' C with hC'
  have hC'img : (Subtype.val : V → E) '' C' = C := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨⟨x, hCV hx⟩, hx, rfl⟩
  have hCK : C ⊆ K := convexHull_min hsK hconv
  have hC'c : IsCompact C' := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, hC'img]
    exact s.finite_toSet.isCompact_convexHull ℝ
  have hC'conv : Convex ℝ C' :=
    Convex.linear_preimage (𝕜 := ℝ) (convex_convexHull ℝ (s : Set E)) V.subtype
  have hsne : (s : Set E).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, -⟩ := hcov' x hx
    exact ⟨y, hy⟩
  have hC'ne : C'.Nonempty := by
    obtain ⟨y, hy⟩ := hsne
    exact ⟨⟨y, Submodule.subset_span hy⟩, subset_convexHull ℝ _ hy⟩
  set h : V → V := fun v => ⟨P (f v), hPV _⟩ with hh
  have hhc : ContinuousOn h C' := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine hPc.comp (hf.comp continuous_subtype_val.continuousOn fun v hv => hCK hv) ?_
    exact fun v hv => hmaps (hCK hv)
  have hhm : MapsTo h C' C' := fun v hv => hPC _ (hmaps (hCK hv))
  obtain ⟨v, hvC, hv⟩ := brouwer hC'c hC'conv hC'ne hhc hhm
  have hvK : (v : E) ∈ K := hCK hvC
  refine ⟨v, hvK, ?_⟩
  have hPv : P (f v) = v := congrArg Subtype.val hv
  calc ‖f v - v‖ = ‖P (f v) - f v‖ := by rw [hPv, norm_sub_rev]
    _ ≤ ε := hPclose _ (hmaps hvK)

/-- **Schauder fixed-point theorem.** A map continuous on a nonempty compact convex subset `K`
of a real normed space and mapping `K` into itself has a fixed point in `K`. -/
theorem schauder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) {f : E → E}
    (hf : ContinuousOn f K) (hmaps : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  by_contra hcon
  have hne' : ∀ x ∈ K, f x ≠ x := fun x hx h => hcon ⟨x, hx, h⟩
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne ((hf.sub continuousOn_id).norm)
  have hδ : 0 < ‖f x0 - x0‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne' x0 hx0))
  obtain ⟨x, hx, hxε⟩ := exists_approx_fixed_point hK hconv hne hf hmaps (half_pos hδ)
  have : ‖f x0 - x0‖ ≤ ‖f x - x‖ := hmin hx
  linarith

/-- **Schauder fixed-point theorem, subtype form.** A continuous self-map of a nonempty compact
convex subset `K` of a real normed space has a fixed point. -/
theorem schauder_subtype {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) {f : K → K} (hf : Continuous f) :
    ∃ x : K, f x = x := by
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
  obtain ⟨x, hx, hFx⟩ := schauder hK hconv hne hFc hFm
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [← hFK ⟨x, hx⟩]
  exact hFx

/-- **Schauder fixed-point theorem, closed convex form.** In a real Banach space, let `F` be
nonempty, closed and convex, and `T` continuous on `F` with `T(F) ⊆ F` and `T(F)` relatively
compact. Then `T` has a fixed point in `F`. -/
theorem schauder_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Set E} (hcl : IsClosed F) (hconv : Convex ℝ F) (hne : F.Nonempty) {T : E → E}
    (hT : ContinuousOn T F) (hmaps : MapsTo T F F) (hcpt : IsCompact (closure (T '' F))) :
    ∃ x ∈ F, T x = x := by
  set K := closure (convexHull ℝ (T '' F)) with hKdef
  have hTB : TotallyBounded (T '' F) := hcpt.totallyBounded.subset subset_closure
  have hKc : IsCompact K := hTB.convexHull.closure.isCompact_of_isClosed isClosed_closure
  have hKF : K ⊆ F := closure_minimal (convexHull_min (image_subset_iff.2 hmaps) hconv) hcl
  have hKconv : Convex ℝ K := (convex_convexHull ℝ _).closure
  have hKne : K.Nonempty := ((hne.image T).convexHull).closure
  have hKm : MapsTo T K K := fun x hx =>
    subset_closure (subset_convexHull ℝ _ (mem_image_of_mem T (hKF hx)))
  obtain ⟨x, hx, hTx⟩ := schauder hKc hKconv hKne (hT.mono hKF) hKm
  exact ⟨x, hKF hx, hTx⟩

/-- **Schauder fixed-point theorem, closed convex subtype form.** In a real Banach space, a
continuous self-map `T` of a nonempty closed convex set `F` whose range has compact closure has a
fixed point. -/
theorem schauder_closed_subtype {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : Set E} (hcl : IsClosed F) (hconv : Convex ℝ F) (hne : F.Nonempty)
    {T : F → F} (hT : Continuous T) (hcpt : IsCompact (closure (range fun x => (T x : E)))) :
    ∃ x : F, T x = x := by
  classical
  set G : E → E := fun x => if h : x ∈ F then (T ⟨x, h⟩ : E) else x with hGdef
  have hGF : ∀ x : F, G x = T x := fun x => by simp [hGdef, x.2]
  have hGc : ContinuousOn G F := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : F.domRestrict G = fun x : F => (T x : E) := funext hGF
    rw [this]
    exact continuous_subtype_val.comp hT
  have hGm : MapsTo G F F := fun x hx => by
    rw [hGF ⟨x, hx⟩]
    exact (T _).2
  have himg : G '' F = range fun x => (T x : E) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hGF ⟨x, hx⟩).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, hGF x⟩
  obtain ⟨x, hx, hGx⟩ := schauder_closed hcl hconv hne hGc hGm (himg ▸ hcpt)
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [← hGF ⟨x, hx⟩]
  exact hGx

end LeanEconomics.FixedPoint
