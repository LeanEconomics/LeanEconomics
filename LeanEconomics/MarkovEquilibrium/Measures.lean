/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Probability measures on a compact metrizable space as a convex set

Milestone S1 of `KrusellSmith/STATIONARITY_PLAN.md`: the measure-theoretic set-up for the
Duffie–Geanakoplos–Mas-Colell–McLennan (1994) theorem on stationary Markov equilibria. Throughout,
`J` is a compact metrizable space with its Borel σ-algebra, and `P(J)` (`ProbabilityMeasure J`)
carries the topology of weak convergence.

* **The embedding** `embed : P(J) → ((J →ᵇ ℝ≥0) → ℝ)`, `ρ ↦ (f ↦ ∫ f dρ)`, into a locally convex
  Hausdorff space (a product of copies of `ℝ`) is a topological embedding (`isEmbedding_embed`),
  carries mixtures to convex combinations (`embed_mix`), and has compact convex range
  (`isCompact_range_embed`, `convex_range_embed`). This is where Fan–Glicksberg will apply.
* **The Borel structure** (`borelSpace`): the Giry σ-algebra Mathlib puts on `P(J)` is the Borel
  σ-algebra of the weak topology. One inclusion: `ρ ↦ ρ U` is lower semicontinuous for open `U`
  (portmanteau), and open sets generate. The other: the weak topology is second countable and
  induced by the Giry-measurable maps `ρ ↦ ∫ f dρ`, so every open set is a countable union of
  finite intersections of their preimages. Hence measures on `P(J)` and on `J × P(J)` behave:
  `P(P(J))` is again compact metrizable.
* **The mean** `mean : P(P(J)) → P(J)`, `∫ f d(mean η) = ∫ (∫ f dρ) dη(ρ)` (`lintegral_mean`), is
  continuous (`continuous_mean`).
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction TopologicalSpace
open scoped ENNReal NNReal

namespace LeanEconomics.MarkovEquilibrium

variable {J : Type*} [TopologicalSpace J] [MeasurableSpace J] [BorelSpace J]

omit [BorelSpace J] in
theorem lintegral_ne_top (ρ : ProbabilityMeasure J) (f : J →ᵇ ℝ≥0) :
    ∫⁻ x, f x ∂(ρ : Measure J) ≠ ∞ :=
  (BoundedContinuousFunction.lintegral_lt_top_of_nnreal (ρ : Measure J) f).ne

/-- The integral of a nonnegative bounded continuous test function. -/
noncomputable def testValue (ρ : ProbabilityMeasure J) (f : J →ᵇ ℝ≥0) : ℝ :=
  (∫⁻ x, f x ∂(ρ : Measure J)).toReal

/-- **The embedding** of probability measures into a product of lines. -/
noncomputable def embed (ρ : ProbabilityMeasure J) : (J →ᵇ ℝ≥0) → ℝ := fun f => testValue ρ f

theorem tendsto_embed_iff {γ : Type*} {F : Filter γ} {ρs : γ → ProbabilityMeasure J}
    {ρ : ProbabilityMeasure J} :
    Tendsto ρs F (𝓝 ρ) ↔ Tendsto (fun i => embed (ρs i)) F (𝓝 (embed ρ)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto, tendsto_pi_nhds]
  refine forall_congr' fun f => ?_
  exact (ENNReal.tendsto_toReal_iff (fun i => lintegral_ne_top _ _) (lintegral_ne_top _ _)).symm

theorem continuous_embed : Continuous (embed : ProbabilityMeasure J → _) :=
  continuous_iff_continuousAt.2 fun _ => tendsto_embed_iff.1 tendsto_id

theorem isInducing_embed : IsInducing (embed : ProbabilityMeasure J → _) := by
  rw [isInducing_iff_nhds]
  intro ρ
  apply le_antisymm
  · exact (continuous_embed.tendsto ρ).le_comap
  · exact (tendsto_embed_iff (ρs := id) (F := comap embed (𝓝 (embed ρ)))).2 tendsto_comap

theorem embed_injective [HasOuterApproxClosed J] :
    Function.Injective (embed : ProbabilityMeasure J → _) := by
  intro ρ σ h
  have : (ρ : Measure J) = (σ : Measure J) :=
    ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun f =>
      (ENNReal.toReal_eq_toReal_iff' (lintegral_ne_top ρ f) (lintegral_ne_top σ f)).1
        (congrFun h f)
  exact Subtype.ext this

/-- **Probability measures embed** in a locally convex Hausdorff space. -/
theorem isEmbedding_embed [HasOuterApproxClosed J] :
    IsEmbedding (embed : ProbabilityMeasure J → _) :=
  ⟨isInducing_embed, embed_injective⟩

/-! ### Mixtures -/

/-- The mixture `t ρ + (1 − t) σ`. -/
noncomputable def mix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ρ σ : ProbabilityMeasure J) :
    ProbabilityMeasure J :=
  ⟨ENNReal.ofReal t • (ρ : Measure J) + ENNReal.ofReal (1 - t) • (σ : Measure J), ⟨by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add ht.1 (sub_nonneg.2 ht.2),
      add_sub_cancel, ENNReal.ofReal_one]⟩⟩

omit [TopologicalSpace J] [BorelSpace J] in
theorem coe_mix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ρ σ : ProbabilityMeasure J) :
    (mix t ht ρ σ : Measure J)
      = ENNReal.ofReal t • (ρ : Measure J) + ENNReal.ofReal (1 - t) • (σ : Measure J) := rfl

omit [BorelSpace J] in
/-- **Mixtures embed as convex combinations.** -/
theorem embed_mix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ρ σ : ProbabilityMeasure J) :
    embed (mix t ht ρ σ) = t • embed ρ + (1 - t) • embed σ := by
  funext f
  simp only [embed, testValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul, coe_mix]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul,
    smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_ne_top ρ f))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_ne_top σ f)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.1,
    ENNReal.toReal_ofReal (sub_nonneg.2 ht.2)]

omit [BorelSpace J] in
theorem convex_range_embed : Convex ℝ (range (embed : ProbabilityMeasure J → _)) := by
  rintro _ ⟨ρ, rfl⟩ _ ⟨σ, rfl⟩ a b ha hb hab
  refine ⟨mix a ⟨ha, by linarith⟩ ρ σ, ?_⟩
  obtain rfl : b = 1 - a := by linarith
  exact embed_mix a ⟨ha, by linarith⟩ ρ σ

theorem isCompact_range_embed [CompactSpace J] [T2Space J] :
    IsCompact (range (embed : ProbabilityMeasure J → _)) :=
  isCompact_range continuous_embed

/-! ### The Borel structure on probability measures -/

theorem measurable_testValue (f : J →ᵇ ℝ≥0) :
    Measurable fun ρ : ProbabilityMeasure J => testValue ρ f :=
  ((Measure.measurable_lintegral (ENNReal.continuous_coe.comp f.continuous).measurable).comp
    measurable_subtype_coe).ennreal_toReal

variable [HasOuterApproxClosed J]

/-- `ρ ↦ ρ U` is lower semicontinuous for open `U` (portmanteau). -/
theorem lowerSemicontinuous_measure_open {U : Set J} (hU : IsOpen U) :
    LowerSemicontinuous fun ρ : ProbabilityMeasure J => (ρ : Measure J) U := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro ρ
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto (μs := id) tendsto_id hU

/-- **The Giry σ-algebra on probability measures is the Borel σ-algebra of the weak topology.** -/
theorem borel_eq [SecondCountableTopology (ProbabilityMeasure J)] :
    borel (ProbabilityMeasure J) = (inferInstance : MeasurableSpace (ProbabilityMeasure J)) := by
  apply le_antisymm
  · -- every open set is a countable union of measurable boxes
    refine MeasurableSpace.generateFrom_le fun U hU => ?_
    obtain ⟨W, hW, rfl⟩ := isInducing_embed.isOpen_iff.1 hU
    have hbox : ∀ ρ : embed ⁻¹' W, ∃ I : Finset (J →ᵇ ℝ≥0), ∃ u : (J →ᵇ ℝ≥0) → Set ℝ,
        (∀ a ∈ I, IsOpen (u a) ∧ embed (ρ : ProbabilityMeasure J) a ∈ u a) ∧
          (I : Set (J →ᵇ ℝ≥0)).pi u ⊆ W :=
      fun ρ => isOpen_pi_iff.1 hW _ ρ.2
    choose I u hu hsub using hbox
    set V : embed ⁻¹' W → Set (ProbabilityMeasure J) :=
      fun ρ => embed ⁻¹' ((I ρ : Set (J →ᵇ ℝ≥0)).pi (u ρ)) with hV
    have hVopen : ∀ ρ, IsOpen (V ρ) := fun ρ =>
      (isOpen_set_pi (I ρ).finite_toSet fun a ha => (hu ρ a ha).1).preimage continuous_embed
    have hUnion : embed ⁻¹' W = ⋃ ρ, V ρ := by
      ext σ
      constructor
      · intro hσ
        exact mem_iUnion.2 ⟨⟨σ, hσ⟩, fun a ha => (hu ⟨σ, hσ⟩ a ha).2⟩
      · intro hσ
        obtain ⟨ρ, hρ⟩ := mem_iUnion.1 hσ
        exact hsub ρ hρ
    have hVmeas : ∀ ρ, MeasurableSet (V ρ) := by
      intro ρ
      have : V ρ = ⋂ a ∈ I ρ, (fun σ : ProbabilityMeasure J => testValue σ a) ⁻¹' (u ρ a) := by
        ext σ
        simp only [hV, mem_preimage, Set.mem_pi, Finset.mem_coe, mem_iInter]
        rfl
      rw [this]
      exact MeasurableSet.biInter (I ρ).countable_toSet fun a ha =>
        measurable_testValue a (hu ρ a ha).1.measurableSet
    obtain ⟨T, hT, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable V hVopen
    rw [hUnion, ← hTeq]
    exact MeasurableSet.biUnion hT fun ρ _ => hVmeas ρ
  · -- the evaluations at open sets are lower semicontinuous, hence Borel measurable
    change MeasurableSpace.comap Subtype.val _ ≤ _
    let _ : MeasurableSpace (ProbabilityMeasure J) := borel _
    have : OpensMeasurableSpace (ProbabilityMeasure J) := ⟨le_rfl⟩
    have : Measurable fun ρ : ProbabilityMeasure J => (ρ : Measure J) :=
      Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
        ((BorelSpace.measurable_eq).trans rfl) isPiSystem_isOpen
        fun U hU => (lowerSemicontinuous_measure_open hU).measurable
    exact this.comap_le

/-- **Probability measures on a compact metrizable space form a Borel space.** -/
instance borelSpace [SecondCountableTopology (ProbabilityMeasure J)] :
    BorelSpace (ProbabilityMeasure J) :=
  ⟨borel_eq.symm⟩

/-! ### The mean of a measure on measures -/

variable [MetrizableSpace J] [CompactSpace J]

/-- Probability measures as measures. -/
def toMeasureFn (ρ : ProbabilityMeasure J) : Measure J := ρ

omit [TopologicalSpace J] [BorelSpace J] [HasOuterApproxClosed J] [MetrizableSpace J]
  [CompactSpace J] in
theorem measurable_toMeasureFn : Measurable (toMeasureFn : ProbabilityMeasure J → Measure J) :=
  measurable_subtype_coe

/-- **The mean** of a probability measure on probability measures:
`∫ f d(mean η) = ∫ (∫ f dρ) dη(ρ)`. -/
noncomputable def mean (η : ProbabilityMeasure (ProbabilityMeasure J)) : ProbabilityMeasure J :=
  ⟨(η : Measure (ProbabilityMeasure J)).bind toMeasureFn, ⟨by
    rw [Measure.bind_apply MeasurableSet.univ measurable_toMeasureFn.aemeasurable]
    change ∫⁻ ρ : ProbabilityMeasure J, (ρ : Measure J) univ ∂(η : Measure _) = 1
    simp only [measure_univ, lintegral_const, one_mul]⟩⟩

omit [TopologicalSpace J] [BorelSpace J] [HasOuterApproxClosed J] [MetrizableSpace J]
  [CompactSpace J] in
theorem lintegral_mean (η : ProbabilityMeasure (ProbabilityMeasure J)) {g : J → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(mean η : Measure J)
      = ∫⁻ ρ, ∫⁻ x, g x ∂(ρ : Measure J) ∂(η : Measure (ProbabilityMeasure J)) := by
  change ∫⁻ x, g x ∂((η : Measure (ProbabilityMeasure J)).bind toMeasureFn) = _
  rw [Measure.lintegral_bind measurable_toMeasureFn.aemeasurable hg.aemeasurable]
  rfl

/-- The integral of a test function, as a bounded continuous function on `P(J)`. -/
noncomputable def integralFn (f : J →ᵇ ℝ≥0) : ProbabilityMeasure J →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun ρ => ρ.toFiniteMeasure.testAgainstNN f,
      (FiniteMeasure.continuous_testAgainstNN_eval f).comp
        (ProbabilityMeasure.toFiniteMeasure_isEmbedding J).continuous⟩

omit [HasOuterApproxClosed J] in
theorem coe_integralFn (f : J →ᵇ ℝ≥0) (ρ : ProbabilityMeasure J) :
    (integralFn f ρ : ℝ≥0∞) = ∫⁻ x, f x ∂(ρ : Measure J) :=
  FiniteMeasure.testAgainstNN_coe_eq

/-- **The mean is continuous.** -/
theorem continuous_mean :
    Continuous (mean : ProbabilityMeasure (ProbabilityMeasure J) → ProbabilityMeasure J) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_lintegral]
  intro f
  have e : (fun η : ProbabilityMeasure (ProbabilityMeasure J) => ∫⁻ x, f x ∂(mean η : Measure J))
      = fun η : ProbabilityMeasure (ProbabilityMeasure J) =>
        ∫⁻ ρ, (integralFn f ρ : ℝ≥0∞) ∂(η : Measure (ProbabilityMeasure J)) := by
    funext η
    rw [lintegral_mean η (g := fun x => ((f x : ℝ≥0) : ℝ≥0∞))
      (ENNReal.continuous_coe.comp f.continuous).measurable]
    simp only [coe_integralFn]
  rw [e]
  exact ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction (integralFn f)

/-- Measures on measures are again a compact space (Prokhorov, with `borelSpace`). -/
instance : CompactSpace (ProbabilityMeasure (ProbabilityMeasure J)) := inferInstance

/-! ### Marginals -/

section Marginals

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  {L : Type*} [TopologicalSpace L] [MeasurableSpace L] [BorelSpace L]

/-- The first marginal. -/
noncomputable def marginalFst (ν : ProbabilityMeasure (K × L)) : ProbabilityMeasure K :=
  ν.map Prod.fst

/-- The second marginal. -/
noncomputable def marginalSnd (ν : ProbabilityMeasure (K × L)) : ProbabilityMeasure L :=
  ν.map Prod.snd

omit [BorelSpace L] in
theorem continuous_marginalFst [OpensMeasurableSpace (K × L)] :
    Continuous (marginalFst : ProbabilityMeasure (K × L) → ProbabilityMeasure K) := by
  unfold marginalFst
  exact ProbabilityMeasure.continuous_map continuous_fst

omit [BorelSpace K] in
theorem continuous_marginalSnd [OpensMeasurableSpace (K × L)] :
    Continuous (marginalSnd : ProbabilityMeasure (K × L) → ProbabilityMeasure L) := by
  unfold marginalSnd
  exact ProbabilityMeasure.continuous_map continuous_snd

end Marginals

end LeanEconomics.MarkovEquilibrium
