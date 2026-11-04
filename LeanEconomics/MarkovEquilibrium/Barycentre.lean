/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.MarkovEquilibrium.Ergodic

/-!
# Barycentric hulls and conditionally restricted ergodic transitions (DGMM Proposition 1.3)

Milestone SP1 of `KrusellSmith/SPOTLESS_PLAN.md`. `J` is compact metrizable,
`g : J → Set (P(J))` has closed graph and nonempty values (in the application: the *spotless*
consistent beliefs), and `G ⊇ g` has closed graph and convex values.

* `baryHull g s`: the means `E η` of probability measures `η` on `P(J)` concentrated on `g s`
  (DGMM's `Ĝ`, the closed convex hull of `g s`).
* It has nonempty (`E δ_ρ = ρ`, `mean_dirac`) and convex (`mean_mix`) values, and a **closed
  graph** (`isClosed_graph_baryHull`): `{(s, η) : η (g s) = 1}` is the preimage of
  `{ν : ν (Gr g) = 1}` under `(s, η) ↦ δ_s ⊗ η`, which is continuous (Mathlib's
  `ProbabilityMeasure.continuous_prod`, `continuous_diracProba`); the graph of `baryHull g` is its
  continuous image, compact.
* `baryHull g s ⊆ G s` (`mean_mem`).

**Theorem** (`exists_ergodic_baryHull`). There are an ergodic invariant `μ` and a measurable `T`
with, for `μ`-a.e. `s`, `T s = E η` for some `η` concentrated on `g s`; in particular
`T s ∈ G s`.
-/

open MeasureTheory Topology Filter Set
open scoped ENNReal

namespace LeanEconomics.MarkovEquilibrium

variable {J : Type*} [TopologicalSpace J] [MeasurableSpace J] [BorelSpace J]
  [TopologicalSpace.MetrizableSpace J] [CompactSpace J]

omit [TopologicalSpace J] [BorelSpace J] [TopologicalSpace.MetrizableSpace J] [CompactSpace J] in
/-- The mean of a Dirac mass. -/
theorem mean_dirac (ρ : ProbabilityMeasure J) : mean (diracProba ρ) = ρ := by
  apply Subtype.ext
  ext A hA
  change (mean (diracProba ρ) : Measure J) A = (ρ : Measure J) A
  rw [mean_apply _ hA]
  exact lintegral_dirac' ρ ((Measure.measurable_coe hA).comp measurable_subtype_coe)

/-- **The barycentric hull**: means of probability measures concentrated on `g s`. -/
def baryHull (g : J → Set (ProbabilityMeasure J)) (s : J) : Set (ProbabilityMeasure J) :=
  {ρ | ∃ η : ProbabilityMeasure (ProbabilityMeasure J),
    (η : Measure (ProbabilityMeasure J)) (g s) = 1 ∧ mean η = ρ}

variable {g : J → Set (ProbabilityMeasure J)}

omit [TopologicalSpace.MetrizableSpace J] [CompactSpace J] in
theorem isClosed_section {G : J → Set (ProbabilityMeasure J)} (hG : IsClosed (graphSet G))
    (s : J) : IsClosed (G s) :=
  hG.preimage (Continuous.prodMk_right s)

omit [TopologicalSpace J] [BorelSpace J] [TopologicalSpace.MetrizableSpace J] [CompactSpace J] in
theorem baryHull_nonempty (hne : ∀ s, (g s).Nonempty) (s : J) :
    (baryHull g s).Nonempty := by
  obtain ⟨ρ, hρ⟩ := hne s
  exact ⟨ρ, diracProba ρ, diracProba_toMeasure_apply_of_mem hρ, mean_dirac ρ⟩

omit [TopologicalSpace J] [BorelSpace J] [TopologicalSpace.MetrizableSpace J] [CompactSpace J] in
theorem mix_mem_baryHull (s : J) :
    ∀ ρ ∈ baryHull g s, ∀ σ ∈ baryHull g s, ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      mix t ht ρ σ ∈ baryHull g s := by
  rintro _ ⟨η, hη, rfl⟩ _ ⟨θ, hθ, rfl⟩ t ht
  exact ⟨mix t ht η θ, mix_apply_eq_one t ht hη hθ, mean_mix t ht η θ⟩

/-- **The barycentric hull lies in any closed convex-valued correspondence containing `g`.** -/
theorem baryHull_subset {G : J → Set (ProbabilityMeasure J)} (hG : IsClosed (graphSet G))
    (hconv : ∀ s, ∀ ρ ∈ G s, ∀ σ ∈ G s, ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1), mix t ht ρ σ ∈ G s)
    (hgG : ∀ s, g s ⊆ G s) (s : J) : baryHull g s ⊆ G s := by
  rintro _ ⟨η, hη, rfl⟩
  exact mean_mem (isClosed_section hG s) (hconv s) η (measure_eq_one_mono (hgG s) hη)

/-- `δ_s ⊗ η` charges the graph of `g` exactly as `η` charges `g s`. -/
theorem prod_dirac_graphSet (hg : IsClosed (graphSet g)) (s : J)
    (η : ProbabilityMeasure (ProbabilityMeasure J)) :
    ((diracProba s).prod η : Measure (J × ProbabilityMeasure J)) (graphSet g)
      = (η : Measure (ProbabilityMeasure J)) (g s) := by
  rw [ProbabilityMeasure.toMeasure_prod, Measure.prod_apply hg.measurableSet]
  change ∫⁻ x, (η : Measure (ProbabilityMeasure J)) (Prod.mk x ⁻¹' graphSet g)
      ∂(Measure.dirac s) = _
  rw [lintegral_dirac' s (measurable_measure_prodMk_left hg.measurableSet)]
  rfl

/-- **The barycentric hull has a closed graph.** -/
theorem isClosed_graph_baryHull (hg : IsClosed (graphSet g)) :
    IsClosed (graphSet (baryHull g)) := by
  set K : Set (J × ProbabilityMeasure (ProbabilityMeasure J)) :=
    {p | (p.2 : Measure (ProbabilityMeasure J)) (g p.1) = 1}
  have hK : IsClosed K := by
    have e : K = (fun p : J × ProbabilityMeasure (ProbabilityMeasure J) =>
        (diracProba p.1).prod p.2) ⁻¹'
          {ν : ProbabilityMeasure (J × ProbabilityMeasure J) |
            (ν : Measure _) (graphSet g) = 1} := by
      ext p
      simp only [K, mem_preimage, mem_ofPred_eq, prod_dirac_graphSet hg]
    rw [e]
    exact (isClosed_measure_eq_one hg).preimage (ProbabilityMeasure.continuous_prod.comp
      ((continuous_diracProba.comp continuous_fst).prodMk continuous_snd))
  have e : graphSet (baryHull g)
      = (fun p : J × ProbabilityMeasure (ProbabilityMeasure J) => (p.1, mean p.2)) '' K := by
    ext ⟨s, ρ⟩
    constructor
    · rintro ⟨η, hη, rfl⟩
      exact ⟨(s, η), hη, rfl⟩
    · rintro ⟨⟨s', η⟩, hη, h⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨η, hη, rfl⟩
  rw [e]
  exact (hK.isCompact.image (continuous_fst.prodMk (continuous_mean.comp continuous_snd))).isClosed

/-- **DGMM Proposition 1.3, abstract form**: an ergodic invariant measure for a transition whose
values are, almost everywhere, barycentres of measures concentrated on `g s`, hence in `G s`. -/
theorem exists_ergodic_baryHull [Nonempty J] (hg : IsClosed (graphSet g))
    (hne : ∀ s, (g s).Nonempty) {G : J → Set (ProbabilityMeasure J)} (hG : IsClosed (graphSet G))
    (hconv : ∀ s, ∀ ρ ∈ G s, ∀ σ ∈ G s, ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1), mix t ht ρ σ ∈ G s)
    (hgG : ∀ s, g s ⊆ G s) :
    ∃ (μ : ProbabilityMeasure J) (T : J → ProbabilityMeasure J), Measurable T ∧
      (μ : Measure J).bind (fun s => (T s : Measure J)) = μ ∧
      (∀ᵐ s ∂(μ : Measure J), T s ∈ baryHull g s ∧ T s ∈ G s) ∧
      ∀ A, MeasurableSet A → (∀ᵐ s ∂(μ : Measure J), s ∈ A → (T s : Measure J) A = 1) →
        (μ : Measure J) A = 0 ∨ (μ : Measure J) A = 1 := by
  obtain ⟨μ, T, hT, hinv, hsel, herg⟩ := exists_ergodic (isClosed_graph_baryHull hg)
    (baryHull_nonempty hne) mix_mem_baryHull
  refine ⟨μ, T, hT, hinv, ?_, herg⟩
  filter_upwards [hsel] with s hs
  exact ⟨hs, baryHull_subset hG hconv hgG s hs⟩

end LeanEconomics.MarkovEquilibrium
