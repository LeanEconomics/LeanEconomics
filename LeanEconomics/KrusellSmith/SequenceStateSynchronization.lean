/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.SequenceStateMarkov
import LeanEconomics.KrusellSmith.Synchronization

/-!
# Fading memory of the sequence-state equilibrium

Milestone LS2 of `LEE_MATCHING_PLAN.md`: Lee's synchronization theorem (LS1) applied to the
Krusell–Smith economy.

Under uniqueness of sequential equilibrium, a sequence-state equilibrium moves by the Markov law
of motion of `Recursive.lean` (`eq_lawOfMotion`), so it is a consistent assignment for the maps
`ν ↦ lawOfMotion z ν z'` (`IsSeqStateEquilibrium.consistent`). The metric on distributions is
left open: any injective `ι` into a metric space (`dist (ι μ) (ι ν)`; e.g. the Lévy–Prokhorov
or a Wasserstein distance). `LawContraction ι S c D` is Lee's Definition 7 for the law of
motion, measured through `ι`, on a set `S` of distributions; it is a hypothesis, as in Lee.

Then, for sequence-state equilibria with distributions in `S`:

* `IsSeqStateEquilibrium.dist_le_of_agree`: **fading memory** — two histories agreeing over
  their last `T + 1` shocks carry distributions within `c ^ T * D`, whatever happened before;
* `IsSeqStateEquilibrium.dist_run_le`: **burn-in** — the distribution today is within
  `c ^ T * D` of the one obtained by starting from any distribution in `S`, `T` periods back,
  and running the law of motion along the realized shocks;
* `IsSeqStateEquilibrium.eq_of_contraction`: **uniqueness** of the sequence-state equilibrium;
* `existsUnique_seqStateEquilibrium`: with `S` everything, **exactly one** sequence-state
  equilibrium exists.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

/-- The law of motion as the family of maps of `Synchronization.lean`: today's shock `z`, the
new shock `z'`. -/
noncomputable def lawMap (M : KSModel Z E) (z z' : Z) (ν : ProbabilityMeasure M.AState) :
    ProbabilityMeasure M.AState :=
  M.lawOfMotion z ν z'

/-- Under uniqueness, **a sequence-state equilibrium is consistent for the law of motion**. -/
theorem IsSeqStateEquilibrium.consistent {μ : History Z → ProbabilityMeasure M.AState}
    (hμ : M.IsSeqStateEquilibrium μ) (hU : M.UniqueSequentialEquilibrium) :
    Consistent M.lawMap μ :=
  consistent_iff_cons.2 fun z' ω => hμ.eq_lawOfMotion hU ω z'

variable {X : Type*} [MetricSpace X]

variable (M) in
/-- **Uniform contraction of the law of motion** (Lee, Definition 7), with distances between
distributions measured by `dist (ι μ) (ι ν)`, on the set `S`. -/
structure LawContraction (ι : ProbabilityMeasure M.AState → X)
    (S : Set (ProbabilityMeasure M.AState)) (c D : ℝ) : Prop where
  mapsTo : ∀ z z', MapsTo (M.lawMap z z') S S
  dist_le : ∀ z z', ∀ μ ∈ S, ∀ ν ∈ S,
    dist (ι (M.lawMap z z' μ)) (ι (M.lawMap z z' ν)) ≤ c * dist (ι μ) (ι ν)
  rate_nonneg : 0 ≤ c
  rate_lt_one : c < 1
  diam : ∀ μ ∈ S, ∀ ν ∈ S, dist (ι μ) (ι ν) ≤ D

variable {ι : ProbabilityMeasure M.AState → X} {S : Set (ProbabilityMeasure M.AState)} {c D : ℝ}

/-- The contraction, in the metric `ι` induces on distributions. -/
theorem LawContraction.uniformContraction (hι : Function.Injective ι)
    (h : M.LawContraction ι S c D) :
    letI : MetricSpace (ProbabilityMeasure M.AState) := MetricSpace.induced ι hι inferInstance
    UniformContraction M.lawMap S c D :=
  letI : MetricSpace (ProbabilityMeasure M.AState) := MetricSpace.induced ι hι inferInstance
  ⟨h.mapsTo, h.dist_le, h.rate_nonneg, h.rate_lt_one, h.diam⟩

section Fading

variable {μ : History Z → ProbabilityMeasure M.AState} (hμ : M.IsSeqStateEquilibrium μ)
  (hU : M.UniqueSequentialEquilibrium) (hι : Function.Injective ι)
  (h : M.LawContraction ι S c D) (hS : ∀ ω, μ ω ∈ S)
include hμ hU hι h hS

/-- **Fading memory** (Lee, Theorem 2(ii)): two histories agreeing over the shocks
`ω 0, …, ω T` carry distributions within `c ^ T * D`. -/
theorem IsSeqStateEquilibrium.dist_le_of_agree (T : ℕ) {ω ω' : History Z}
    (hag : ∀ n ≤ T, ω n = ω' n) : dist (ι (μ ω)) (ι (μ ω')) ≤ c ^ T * D := by
  let : MetricSpace (ProbabilityMeasure M.AState) := MetricSpace.induced ι hι inferInstance
  exact (hμ.consistent hU).dist_le_of_agree hS (h.uniformContraction hι) T hag

/-- **Burn-in** (Lee, Theorem 2(i)): the distribution today is within `c ^ T * D` of the one
reached by starting from any `ν ∈ S`, `T` periods back, along the realized shocks. -/
theorem IsSeqStateEquilibrium.dist_run_le (T : ℕ) (ω : History Z) {ν : ProbabilityMeasure M.AState}
    (hν : ν ∈ S) : dist (ι (μ ω)) (ι (run M.lawMap T ω ν)) ≤ c ^ T * D := by
  let : MetricSpace (ProbabilityMeasure M.AState) := MetricSpace.induced ι hι inferInstance
  exact (hμ.consistent hU).dist_run_le hS (h.uniformContraction hι) T ω hν

/-- **Uniqueness of the sequence-state equilibrium** among those with distributions in `S`. -/
theorem IsSeqStateEquilibrium.eq_of_contraction {μ' : History Z → ProbabilityMeasure M.AState}
    (hμ' : M.IsSeqStateEquilibrium μ') (hS' : ∀ ω, μ' ω ∈ S) : μ = μ' := by
  let : MetricSpace (ProbabilityMeasure M.AState) := MetricSpace.induced ι hι inferInstance
  exact (hμ.consistent hU).eq (hμ'.consistent hU) hS hS' (h.uniformContraction hι)

end Fading

variable (M) in
/-- **Exactly one sequence-state equilibrium** when the law of motion contracts on all
distributions. -/
theorem existsUnique_seqStateEquilibrium [Nonempty E] (hU : M.UniqueSequentialEquilibrium)
    (hι : Function.Injective ι) (h : M.LawContraction ι univ c D) :
    ∃! μ : History Z → ProbabilityMeasure M.AState, M.IsSeqStateEquilibrium μ := by
  obtain ⟨μ, hμ⟩ := M.exists_seqStateEquilibrium
  exact ⟨μ, hμ, fun μ' hμ' =>
    (hμ.eq_of_contraction hU hι h (fun _ => mem_univ _) hμ' (fun _ => mem_univ _)).symm⟩

end KSModel

end KrusellSmith

end LeanEconomics
