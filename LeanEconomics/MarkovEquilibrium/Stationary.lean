/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.MarkovEquilibrium.MeanFixedPoint

/-!
# Stationary Markov transitions selected from a correspondence (DGMM Theorem 1.1)

Milestone S3 of `KrusellSmith/STATIONARITY_PLAN.md`. `J` is compact metrizable and
`G : J → Set (P(J))` has closed graph and nonempty convex values (convex under mixtures).

**Theorem** (`exists_stationary`, Duffie–Geanakoplos–Mas-Colell–McLennan 1994, Theorem 1.1).
There are a probability measure `μ` on `J` and a measurable transition `Π : J → P(J)` with
`μ.bind Π = μ` (`μ` is invariant) and `Π s ∈ G s` for `μ`-almost every `s`.

Proof. Take the fixed point `ν` of `MeanFixedPoint.lean`: `ν (Gr G) = 1` and `m₁ ν = E (m₂ ν)`.
Disintegrate `ν = μ ⊗ P` (`Measure.condKernel`; `P(J)` is standard Borel) and set `Π s = E (P s)`.
* Invariance: `∫ Π s dμ = ∫∫ σ dP s dμ = E (m₂ ν) = m₁ ν = μ`.
* Selection: `ν (Gr G) = 1` gives `P s (G s) = 1` for a.e. `s`; and the mean of a measure supported
  on a closed convex set lies in it (`mean_mem`). DGMM argue with countably many separating test
  functions instead; with an exact disintegration the barycentre statement suffices. It is proved
  by Hahn–Banach in `(J →ᵇ ℝ≥0) → ℝ`, where a continuous linear functional is a finite combination
  of coordinates (`LinearMap.mem_span_iff_continuous`), so it commutes with the mean.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction TopologicalSpace ProbabilityTheory
open scoped ENNReal NNReal

namespace LeanEconomics.MarkovEquilibrium

variable {J : Type*} [TopologicalSpace J] [MeasurableSpace J] [BorelSpace J]
  [MetrizableSpace J] [CompactSpace J]

/-- Probability measures on `J` form a compact metrizable, hence completely metrizable, space; with
`borelSpace` it is standard Borel, so measures on `J × P(J)` disintegrate. -/
instance isCompletelyMetrizableSpace : IsCompletelyMetrizableSpace (ProbabilityMeasure J) := by
  let _ := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure J)
  infer_instance

omit [MetrizableSpace J] [CompactSpace J] in
/-- Test values of the mean are means of test values. -/
theorem testValue_mean (η : ProbabilityMeasure (ProbabilityMeasure J)) (f : J →ᵇ ℝ≥0) :
    testValue (mean η) f = ∫ ρ, testValue ρ f ∂(η : Measure (ProbabilityMeasure J)) := by
  unfold testValue
  have hm : Measurable fun ρ : ProbabilityMeasure J => ∫⁻ x, ((f x : ℝ≥0) : ℝ≥0∞) ∂(ρ : Measure J) :=
    (Measure.measurable_lintegral (ENNReal.continuous_coe.comp f.continuous).measurable).comp
      measurable_subtype_coe
  rw [lintegral_mean η (g := fun x => ((f x : ℝ≥0) : ℝ≥0∞))
      (ENNReal.continuous_coe.comp f.continuous).measurable]
  exact (integral_toReal hm.aemeasurable (ae_of_all _ fun ρ => (lintegral_ne_top ρ f).lt_top)).symm

/-- **Barycentres**: the mean of a measure supported on a closed set of probability measures that
is closed under mixtures lies in that set. -/
theorem mean_mem {C : Set (ProbabilityMeasure J)} (hC : IsClosed C)
    (hconv : ∀ ρ ∈ C, ∀ σ ∈ C, ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1), mix t ht ρ σ ∈ C)
    (η : ProbabilityMeasure (ProbabilityMeasure J)) (hη : (η : Measure _) C = 1) : mean η ∈ C := by
  by_contra hm
  have hTc : IsClosed (embed '' C) := (hC.isCompact.image continuous_embed).isClosed
  have hTv : Convex ℝ (embed '' C) := by
    rintro _ ⟨ρ, hρ, rfl⟩ _ ⟨σ, hσ, rfl⟩ a b ha hb hab
    obtain rfl : b = 1 - a := by linarith
    exact ⟨mix a ⟨ha, by linarith⟩ ρ σ, hconv ρ hρ σ hσ a _, embed_mix _ _ _ _⟩
  have hx : embed (mean η) ∉ embed '' C := fun ⟨ρ, hρ, h⟩ => hm (embed_injective h ▸ hρ)
  obtain ⟨φ, u, hφx, hφC⟩ := geometric_hahn_banach_point_closed hTv hTc hx
  -- a continuous linear functional on the product is a finite combination of coordinates
  have hspan : φ.toLinearMap ∈ Submodule.span ℝ
      (range fun f : J →ᵇ ℝ≥0 => (LinearMap.proj f : ((J →ᵇ ℝ≥0) → ℝ) →ₗ[ℝ] ℝ)) :=
    (LinearMap.mem_span_iff_continuous _).2 φ.continuous
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hspan
  have hφ : ∀ x, φ x = ∑ f ∈ c.support, c f * x f := by
    intro x
    have := congrArg (fun L : ((J →ᵇ ℝ≥0) → ℝ) →ₗ[ℝ] ℝ => L x) hc
    simp only [Finsupp.sum] at this
    rw [← ContinuousLinearMap.coe_coe φ, ← this, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  have hint : ∀ f, Integrable (fun ρ : ProbabilityMeasure J => testValue ρ f) (η : Measure _) :=
    fun f => (BoundedContinuousFunction.mkOfCompact
      ⟨fun ρ : ProbabilityMeasure J => testValue ρ f,
        (continuous_apply f).comp continuous_embed⟩).integrable _
  have hmean : φ (embed (mean η)) = ∫ ρ, φ (embed ρ) ∂(η : Measure _) := by
    simp only [hφ]
    change ∑ f ∈ c.support, c f * testValue (mean η) f
      = ∫ ρ, ∑ f ∈ c.support, c f * testValue ρ f ∂(η : Measure _)
    rw [integral_finsetSum _ fun f _ => (hint f).const_mul _]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [integral_const_mul]
    exact congrArg _ (testValue_mean η f)
  have hae : ∀ᵐ ρ ∂(η : Measure _), ρ ∈ C := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff hC.measurableSet).2 hη
  have hge : u ≤ ∫ ρ, φ (embed ρ) ∂(η : Measure _) := by
    have hu : ∫ _ρ, u ∂(η : Measure (ProbabilityMeasure J)) = u := by simp
    rw [← hu]
    refine integral_mono_ae (integrable_const u)
      ((BoundedContinuousFunction.mkOfCompact
        ⟨fun ρ : ProbabilityMeasure J => φ (embed ρ), φ.continuous.comp continuous_embed⟩).integrable
          _) ?_
    filter_upwards [hae] with ρ hρ
    exact (hφC _ ⟨ρ, hρ, rfl⟩).le
  linarith [hmean ▸ hge]

/-- **DGMM Theorem 1.1**: an invariant measure `μ` and a measurable transition `T` selected from
`G` almost everywhere. -/
theorem exists_stationary [Nonempty J] {G : J → Set (ProbabilityMeasure J)}
    (hGr : IsClosed (graphSet G)) (hne : ∀ s, (G s).Nonempty)
    (hconv : ∀ s, ∀ ρ ∈ G s, ∀ σ ∈ G s, ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1), mix t ht ρ σ ∈ G s) :
    ∃ (μ : ProbabilityMeasure J) (T : J → ProbabilityMeasure J), Measurable T ∧
      (μ : Measure J).bind (fun s => (T s : Measure J)) = μ ∧ ∀ᵐ s ∂(μ : Measure J), T s ∈ G s := by
  obtain ⟨ν, hνG, hνfix⟩ := exists_mean_fixedPoint hGr hne
  set ρ : Measure (J × ProbabilityMeasure J) := (ν : Measure (J × ProbabilityMeasure J))
  have : Nonempty (ProbabilityMeasure J) :=
    ⟨⟨Measure.dirac (Classical.arbitrary J), inferInstance⟩⟩
  set κ := ρ.condKernel
  have hdis : ρ.fst ⊗ₘ κ = ρ := ρ.disintegrate κ
  have hfst : ρ.fst = (marginalFst ν : Measure J) := rfl
  set P : J → ProbabilityMeasure (ProbabilityMeasure J) := fun s => ⟨κ s, inferInstance⟩
  have hP : Measurable P := κ.measurable.subtype_mk
  refine ⟨marginalFst ν, fun s => mean (P s), continuous_mean.measurable.comp hP, ?_, ?_⟩
  · -- invariance
    ext A hA
    have hTm : Measurable fun s => ((mean (P s) : ProbabilityMeasure J) : Measure J) :=
      measurable_subtype_coe.comp (continuous_mean.measurable.comp hP)
    rw [Measure.bind_apply hA hTm.aemeasurable]
    have hAm : Measurable fun σ : ProbabilityMeasure J => (σ : Measure J) A :=
      (Measure.measurable_coe hA).comp measurable_subtype_coe
    calc ∫⁻ s, (mean (P s) : Measure J) A ∂(marginalFst ν : Measure J)
        = ∫⁻ s, ∫⁻ σ, (σ : Measure J) A ∂(κ s) ∂ρ.fst := by
          rw [hfst]
          exact lintegral_congr fun s => mean_apply (P s) hA
      _ = ∫⁻ p, (p.2 : Measure J) A ∂ρ := by
          exact (Measure.lintegral_compProd (hAm.comp measurable_snd)).symm.trans
            (by rw [hdis]; rfl)
      _ = ∫⁻ σ, (σ : Measure J) A ∂(marginalSnd ν : Measure (ProbabilityMeasure J)) := by
          change _ = ∫⁻ σ, (σ : Measure J) A ∂(ρ.map Prod.snd)
          rw [lintegral_map hAm measurable_snd]
      _ = (marginalFst ν : Measure J) A := by
          rw [hνfix, mean_apply _ hA]
  · -- selection
    have hsec : ∀ s, (Prod.mk s ⁻¹' graphSet G) = G s := fun s => rfl
    have h0 : ∫⁻ s, κ s (Prod.mk s ⁻¹' (graphSet G)ᶜ) ∂ρ.fst = 0 := by
      rw [← Measure.compProd_apply hGr.measurableSet.compl, hdis]
      exact (prob_compl_eq_zero_iff hGr.measurableSet).2 hνG
    rw [lintegral_eq_zero_iff (κ.measurable_kernel_prodMk_left hGr.measurableSet.compl)] at h0
    rw [← hfst]
    filter_upwards [h0] with s hs
    have hGs : IsClosed (G s) := hGr.preimage (Continuous.prodMk_right s)
    refine mean_mem hGs (hconv s) (P s) ?_
    change κ s (G s) = 1
    rw [← prob_compl_eq_zero_iff hGs.measurableSet, ← hsec, ← preimage_compl]
    exact hs

end LeanEconomics.MarkovEquilibrium
