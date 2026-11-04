/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.MarkovEquilibrium.Stationary

/-!
# An ergodic stationary transition (DGMM Corollary 1.1)

Milestone S4 of `KrusellSmith/STATIONARITY_PLAN.md`.

**Theorem** (`exists_ergodic`). Under the hypotheses of `exists_stationary`, the invariant measure
`μ` and the transition `T` can be chosen so that `μ` is **ergodic** for `T`: every measurable set
`A` with `T s A = 1` for `μ`-a.e. `s ∈ A` has `μ A = 0` or `μ A = 1`.

Proof. The fixed points `F = {ν : ν (Gr G) = 1, m₁ ν = E (m₂ ν)}` form a nonempty compact set; embed
`P(J × P(J))` in a locally convex space (`Measures.lean`) and take an extreme point `ν` (Krein–Milman,
`IsCompact.extremePoints_nonempty`). Let `μ = m₁ ν`, `T = transition ν`. If `A` is invariant with
`0 < μ A < 1`, so is `Aᶜ` (`ae_compl_of_invariant`), and conditioning `ν` on `A × P(J)` and on
`Aᶜ × P(J)` gives two members of `F` (`cond_mem`, using `∫_A T s B dμ = μ (A ∩ B)`,
`setLIntegral_invariant`) of which `ν` is the proper mixture with weights `μ A`, `μ Aᶜ`. They differ
from `ν`, contradicting extremality. Invariance alone, without the symmetric condition, is enough.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction TopologicalSpace ProbabilityTheory
open scoped ENNReal NNReal

namespace LeanEconomics.MarkovEquilibrium

/-! ### Invariant sets of an invariant measure -/

section Invariant

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {T : X → ProbabilityMeasure X}

/-- If `A` is invariant (`T s A = 1` a.e. on `A`), the chain does not enter `A` from `Aᶜ`. -/
theorem ae_compl_of_invariant (hT : Measurable T)
    (hinv : ∀ B, MeasurableSet B → ∫⁻ s, (T s : Measure X) B ∂μ = μ B) {A : Set X}
    (hA : MeasurableSet A) (hAinv : ∀ᵐ s ∂μ, s ∈ A → (T s : Measure X) A = 1) :
    ∀ᵐ s ∂μ, s ∈ Aᶜ → (T s : Measure X) A = 0 := by
  have hTA : Measurable fun s => (T s : Measure X) A :=
    (Measure.measurable_coe hA).comp (measurable_subtype_coe.comp hT)
  have h1 : ∫⁻ s in A, (T s : Measure X) A ∂μ = μ A := by
    rw [setLIntegral_congr_fun_ae (g := fun _ => 1) hA hAinv, setLIntegral_const, one_mul]
  have h2 := lintegral_add_compl (fun s => (T s : Measure X) A) hA (μ := μ)
  rw [hinv A hA, h1] at h2
  have h3 : ∫⁻ s in Aᶜ, (T s : Measure X) A ∂μ = 0 :=
    (ENNReal.add_right_inj (measure_ne_top μ A)).1 (h2.trans (add_zero _).symm)
  exact (setLIntegral_eq_zero_iff hA.compl hTA).1 h3

/-- The complement of an invariant set is invariant. -/
theorem compl_invariant (hT : Measurable T)
    (hinv : ∀ B, MeasurableSet B → ∫⁻ s, (T s : Measure X) B ∂μ = μ B) {A : Set X}
    (hA : MeasurableSet A) (hAinv : ∀ᵐ s ∂μ, s ∈ A → (T s : Measure X) A = 1) :
    ∀ᵐ s ∂μ, s ∈ Aᶜ → (T s : Measure X) Aᶜ = 1 := by
  filter_upwards [ae_compl_of_invariant hT hinv hA hAinv] with s hs hsA
  rw [prob_compl_eq_one_sub hA, hs hsA, tsub_zero]

/-- On an invariant set the chain stays put: `∫_A T s B dμ = μ (A ∩ B)`. -/
theorem setLIntegral_invariant (hT : Measurable T)
    (hinv : ∀ B, MeasurableSet B → ∫⁻ s, (T s : Measure X) B ∂μ = μ B) {A : Set X}
    (hA : MeasurableSet A) (hAinv : ∀ᵐ s ∂μ, s ∈ A → (T s : Measure X) A = 1) {B : Set X}
    (hB : MeasurableSet B) : ∫⁻ s in A, (T s : Measure X) B ∂μ = μ (A ∩ B) := by
  have hc := ae_compl_of_invariant hT hinv hA hAinv
  have hAc : ∀ᵐ s ∂μ, s ∈ A → (T s : Measure X) B = (T s : Measure X) (A ∩ B) := by
    filter_upwards [hAinv] with s hs hsA
    rw [inter_comm]
    exact (measure_inter_conull ((prob_compl_eq_zero_iff hA).2 (hs hsA))).symm
  have hTAB : Measurable fun s => (T s : Measure X) (A ∩ B) :=
    (Measure.measurable_coe (hA.inter hB)).comp (measurable_subtype_coe.comp hT)
  have e1 : ∫⁻ s in Aᶜ, (T s : Measure X) (A ∩ B) ∂μ = 0 := by
    rw [setLIntegral_eq_zero_iff hA.compl hTAB]
    filter_upwards [hc] with s hs hsA
    exact measure_mono_null inter_subset_left (hs hsA)
  have h2 := lintegral_add_compl (fun s => (T s : Measure X) (A ∩ B)) hA (μ := μ)
  rw [e1, add_zero, hinv _ (hA.inter hB)] at h2
  rw [← h2]
  exact setLIntegral_congr_fun_ae hA hAc

end Invariant

variable {J : Type*} [TopologicalSpace J] [MeasurableSpace J] [BorelSpace J]
  [MetrizableSpace J] [CompactSpace J] [Nonempty J]

/-- The fixed points of DGMM's correspondence, as measures on `J × P(J)`. -/
def fixedPoints (G : J → Set (ProbabilityMeasure J)) :
    Set (ProbabilityMeasure (J × ProbabilityMeasure J)) :=
  {ν | (ν : Measure _) (graphSet G) = 1 ∧ marginalFst ν = mean (marginalSnd ν)}

omit [Nonempty J] in
theorem isClosed_fixedPoints {G : J → Set (ProbabilityMeasure J)} (hGr : IsClosed (graphSet G)) :
    IsClosed (fixedPoints G) :=
  (isClosed_measure_eq_one hGr).inter
    (isClosed_eq continuous_marginalFst (continuous_mean.comp continuous_marginalSnd))

/-- **Conditioning a fixed point on an invariant set** gives a fixed point. -/
theorem cond_mem {G : J → Set (ProbabilityMeasure J)} (hGr : IsClosed (graphSet G))
    {ν : ProbabilityMeasure (J × ProbabilityMeasure J)} (hν : ν ∈ fixedPoints G) {C : Set J} (hC : MeasurableSet C)
    (hC0 : (marginalFst ν : Measure J) C ≠ 0)
    (hCinv : ∀ᵐ s ∂(marginalFst ν : Measure J), s ∈ C → (transition ν s : Measure J) C = 1) :
    ∃ hP : IsProbabilityMeasure ((ν : Measure (J × ProbabilityMeasure J))[|Prod.fst ⁻¹' C]),
      (⟨_, hP⟩ : ProbabilityMeasure (J × ProbabilityMeasure J)) ∈ fixedPoints G := by
  set ρ := (ν : Measure (J × ProbabilityMeasure J))
  have hρC : ρ (Prod.fst ⁻¹' C) = (marginalFst ν : Measure J) C :=
    (Measure.map_apply measurable_fst hC).symm
  have hP : IsProbabilityMeasure (ρ[|Prod.fst ⁻¹' C]) := cond_isProbabilityMeasure (hρC ▸ hC0)
  have hinv : ∀ B, MeasurableSet B →
      ∫⁻ s, (transition ν s : Measure J) B ∂(marginalFst ν : Measure J)
        = (marginalFst ν : Measure J) B := fun B hB => by
    have hTm : Measurable fun s => (transition ν s : Measure J) :=
      measurable_subtype_coe.comp (measurable_transition ν)
    rw [← Measure.bind_apply hB hTm.aemeasurable, bind_transition hν.2]
  refine ⟨hP, ?_, ?_⟩
  · change ρ[|Prod.fst ⁻¹' C] (graphSet G) = 1
    rw [← prob_compl_eq_zero_iff hGr.measurableSet, cond_apply (measurable_fst hC),
      measure_mono_null inter_subset_right ((prob_compl_eq_zero_iff hGr.measurableSet).2 hν.1),
      mul_zero]
  · apply Subtype.ext
    ext B hB
    have hBm : Measurable fun σ : ProbabilityMeasure J => (σ : Measure J) B :=
      (Measure.measurable_coe hB).comp measurable_subtype_coe
    change (ρ[|Prod.fst ⁻¹' C]).map Prod.fst B
      = (mean (marginalSnd (⟨_, hP⟩ : ProbabilityMeasure (J × ProbabilityMeasure J))) : Measure J) B
    rw [Measure.map_apply measurable_fst hB, cond_apply (measurable_fst hC), ← preimage_inter,
      ← Measure.map_apply measurable_fst (hC.inter hB), hρC, mean_apply _ hB]
    change _ = ∫⁻ σ, (σ : Measure J) B ∂((ρ[|Prod.fst ⁻¹' C]).map Prod.snd)
    rw [lintegral_map hBm measurable_snd, ProbabilityTheory.cond, lintegral_smul_measure,
      setLIntegral_transition ν hC hB, hρC,
      setLIntegral_invariant (measurable_transition ν) hinv hC hCinv hB, smul_eq_mul]
    rfl

/-- **DGMM Corollary 1.1**: a stationary transition selected from `G` with an **ergodic** invariant
measure. -/
theorem exists_ergodic {G : J → Set (ProbabilityMeasure J)}
    (hGr : IsClosed (graphSet G)) (hne : ∀ s, (G s).Nonempty)
    (hconv : ∀ s, ∀ ρ ∈ G s, ∀ σ ∈ G s, ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1), mix t ht ρ σ ∈ G s) :
    ∃ (μ : ProbabilityMeasure J) (T : J → ProbabilityMeasure J), Measurable T ∧
      (μ : Measure J).bind (fun s => (T s : Measure J)) = μ ∧
      (∀ᵐ s ∂(μ : Measure J), T s ∈ G s) ∧
      ∀ A, MeasurableSet A → (∀ᵐ s ∂(μ : Measure J), s ∈ A → (T s : Measure J) A = 1) →
        (μ : Measure J) A = 0 ∨ (μ : Measure J) A = 1 := by
  obtain ⟨ν₀, hν₀⟩ := exists_mean_fixedPoint hGr hne
  obtain ⟨x, hx⟩ := ((isClosed_fixedPoints hGr).isCompact.image
    continuous_embed).extremePoints_nonempty ⟨_, ν₀, hν₀, rfl⟩
  rw [mem_extremePoints] at hx
  obtain ⟨⟨ν, hν, rfl⟩, hext⟩ := hx
  refine ⟨marginalFst ν, transition ν, measurable_transition ν, bind_transition hν.2,
    ae_transition_mem hGr hconv hν.1, ?_⟩
  intro A hA hAinv
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, h1⟩ := hcon
  set μ := (marginalFst ν : Measure J) with hμ
  have hinv : ∀ B, MeasurableSet B → ∫⁻ s, (transition ν s : Measure J) B ∂μ = μ B :=
    fun B hB => by
      have hTm : Measurable fun s => (transition ν s : Measure J) :=
        measurable_subtype_coe.comp (measurable_transition ν)
      rw [← Measure.bind_apply hB hTm.aemeasurable, bind_transition hν.2]
  have hc0 : μ Aᶜ ≠ 0 := fun h => h1 ((prob_compl_eq_zero_iff hA).1 h)
  obtain ⟨hP₁, hF₁⟩ := cond_mem hGr hν hA h0 hAinv
  obtain ⟨hP₂, hF₂⟩ := cond_mem hGr hν hA.compl hc0
    (compl_invariant (measurable_transition ν) hinv hA hAinv)
  set ρ := (ν : Measure (J × ProbabilityMeasure J))
  have hAtop : μ A ≠ ∞ := measure_ne_top μ A
  have ht0 : 0 < (μ A).toReal := ENNReal.toReal_pos h0 hAtop
  have ht1 : (μ A).toReal < 1 := by
    have : μ A < 1 := lt_of_le_of_ne prob_le_one h1
    simpa using (ENNReal.toReal_lt_toReal hAtop ENNReal.one_ne_top).2 this
  have ht : (μ A).toReal ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have hρA : ρ (Prod.fst ⁻¹' A) = μ A := (Measure.map_apply measurable_fst hA).symm
  have hρAc : ρ (Prod.fst ⁻¹' A)ᶜ = μ Aᶜ := (Measure.map_apply measurable_fst hA.compl).symm
  have hmix : mix (μ A).toReal ht ⟨_, hP₁⟩ ⟨_, hP₂⟩ = ν := by
    apply Subtype.ext
    ext B hB
    change (ENNReal.ofReal (μ A).toReal • ρ[|Prod.fst ⁻¹' A]
      + ENNReal.ofReal (1 - (μ A).toReal) • ρ[|(Prod.fst ⁻¹' A)ᶜ]) B = ρ B
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal hAtop,
      ← prob_compl_eq_one_sub hA, ← hρA, ← hρAc, ← cond_add_cond_compl_eq (t := B) (measurable_fst hA) ρ]
    ring
  have hseg : embed ν ∈ openSegment ℝ (embed (⟨_, hP₁⟩ : ProbabilityMeasure _))
      (embed (⟨_, hP₂⟩ : ProbabilityMeasure _)) :=
    ⟨(μ A).toReal, 1 - (μ A).toReal, ht0, by linarith, by ring, (embed_mix (μ A).toReal ht _ _).symm.trans (congrArg embed hmix)⟩
  obtain ⟨h₁, -⟩ := hext _ ⟨_, hF₁, rfl⟩ _ ⟨_, hF₂, rfl⟩ hseg
  have heq := congrArg (fun ν' : ProbabilityMeasure (J × ProbabilityMeasure J) =>
    (ν' : Measure (J × ProbabilityMeasure J)) (Prod.fst ⁻¹' A)ᶜ) (embed_injective h₁)
  change ρ[(Prod.fst ⁻¹' A)ᶜ | Prod.fst ⁻¹' A] = ρ (Prod.fst ⁻¹' A)ᶜ at heq
  rw [cond_apply (measurable_fst hA), inter_compl_self, measure_empty, mul_zero, hρAc] at heq
  exact hc0 heq.symm

end LeanEconomics.MarkovEquilibrium
