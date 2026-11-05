/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Continuation
import LeanEconomics.KrusellSmith.SequenceStateMap
import LeanEconomics.FixedPoint.SchauderTychonoff
import LeanEconomics.KrusellSmith.CobbDouglas

/-!
# Existence of a sequence-state equilibrium

Milestone TS3 of `SEQUENCE_STATE_PLAN.md`.

A **sequence-state equilibrium** is an assignment `μ : History Z → P(AState)` of a distribution of
households to every infinite history of aggregate shocks that is a fixed point of the update
(`IsSeqStateEquilibrium`): the distribution at `cons z' ω` is the one households at `ω` move to
after the shock `z'`, saving optimally against the prices the assignment implies on the future
of `ω`. There is no initial distribution: the state is the whole infinite past.

* `exists_seqStateEquilibrium`: **one exists**, for every `KSModel` (with a nonempty set of
  idiosyncratic states), in particular for Cobb–Douglas prices. Schauder–Tychonoff on the compact
  convex image of the assignments in `History Z → ((AState →ᵇ ℝ≥0) → ℝ)` (TS1), with the update
  continuous (TS2).
* `IsSeqStateEquilibrium.nodeDist_eq`: along the tree rooted at any history `ω`, the
  distributions the households generate from `μ ω` are those the assignment gives at the
  extended histories.
* `IsSeqStateEquilibrium.isSequentialEquilibrium`: **at every history `ω`, mean assets of the
  assignment along the future of `ω` is a sequential equilibrium from `(ω 0, μ ω)`**, in the sense
  of `Equilibrium.lean`, with the capital path in `capitalPaths`; and labour at every node is the
  mean efficiency of the households there (`IsSeqStateEquilibrium.labour_eq`).
* `logEconomy_exists_seqStateEquilibrium`: the instance with log utility and clamped
  Cobb–Douglas prices.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **Sequence-state equilibrium**: the assignment is a fixed point of the update. -/
def IsSeqStateEquilibrium (μ : History Z → ProbabilityMeasure M.AState) : Prop :=
  M.seqStep μ = μ

/-- **Existence of a sequence-state equilibrium** in every Krusell–Smith economy. -/
theorem exists_seqStateEquilibrium [Nonempty E] :
    ∃ μ : History Z → ProbabilityMeasure M.AState, M.IsSeqStateEquilibrium μ := by
  have hx : Nonempty M.AState :=
    ⟨(⟨0, le_refl 0, M.assetCap_pos.le⟩, ⟨Classical.arbitrary E⟩)⟩
  have hP : Nonempty (ProbabilityMeasure M.AState) :=
    ⟨⟨Measure.dirac (Classical.arbitrary M.AState), inferInstance⟩⟩
  set e := (isEmbedding_embedAssign (H := History Z) (X := M.AState)).toHomeomorph with he
  obtain ⟨y, hy⟩ := FixedPoint.schauderTychonoff_subtype isCompact_range_embedAssign
    convex_range_embedAssign (range_nonempty _)
    (f := fun y => e (M.seqStep (e.symm y)))
    (e.continuous.comp (M.continuous_seqStep.comp e.symm.continuous))
  refine ⟨e.symm y, ?_⟩
  have := congrArg e.symm hy
  simp only [Homeomorph.symm_apply_apply] at this
  exact this

variable {M}

/-- **Along the tree rooted at a history, the households generate the assignment's
distributions.** -/
theorem IsSeqStateEquilibrium.nodeDist_eq {μ : History Z → ProbabilityMeasure M.AState}
    (hμ : M.IsSeqStateEquilibrium μ) (ω : History Z) :
    ∀ g : List Z, M.nodeDist (ω 0) (μ ω : Measure M.AState) (M.seqPrices μ ω) g
      = (μ (History.prepend g ω) : Measure M.AState)
  | [] => rfl
  | z' :: g => by
    have IH := IsSeqStateEquilibrium.nodeDist_eq hμ ω g
    change M.pushNode (ω 0) (M.seqPrices μ ω) g z'
        (M.nodeDist (ω 0) (μ ω : Measure M.AState) (M.seqPrices μ ω) g) = _
    rw [IH, History.prepend_cons, ← congrArg (fun ν => (ν (History.cons z' (History.prepend g ω))
      : Measure M.AState)) hμ, M.coe_seqStep_cons, History.prepend_zero]
    have hP : M.seqPrices μ (History.prepend g ω) = shiftPath (M.seqPrices μ ω) g := by
      funext g'
      rw [M.seqPrices_prepend, shiftPath_apply]
    rw [hP, M.pushNode_shift (ω 0) (M.seqPrices μ ω) g [] z']
    rfl

/-- The capital path an assignment implies on the future of `ω`. -/
noncomputable def seqCapital (μ : History Z → ProbabilityMeasure M.AState) (ω : History Z) :
    List Z → ℝ :=
  fun g => (M.seqPrices μ ω g).1

/-- In equilibrium, the prices seen at `ω` are those of `Equilibrium.lean` for the capital path
`seqCapital`, from `(ω 0, μ ω)`: labour follows the exogenous recursion from the masses of
`μ ω`. -/
theorem IsSeqStateEquilibrium.pricePath_eq {μ : History Z → ProbabilityMeasure M.AState}
    (hμ : M.IsSeqStateEquilibrium μ) (ω : History Z) :
    M.pricePath (ω 0) (M.initMass (μ ω : Measure M.AState)) (M.seqCapital μ ω)
      = M.seqPrices μ ω := by
  funext g
  refine Prod.ext rfl ?_
  change M.labour (ω 0) (M.initMass (μ ω : Measure M.AState)) g = _
  rw [labour, ← M.initMass_nodeDist (ω 0) (μ ω : Measure M.AState) (M.seqPrices μ ω) g,
    hμ.nodeDist_eq ω g]
  rfl

/-- **At every history, a sequence-state equilibrium is a sequential equilibrium** from today's
shock and distribution, with capital in `capitalPaths`. -/
theorem IsSeqStateEquilibrium.isSequentialEquilibrium
    {μ : History Z → ProbabilityMeasure M.AState} (hμ : M.IsSeqStateEquilibrium μ)
    (ω : History Z) :
    M.seqCapital μ ω ∈ M.capitalPaths (M.initCapital (μ ω : Measure M.AState)) ∧
      M.IsSequentialEquilibrium (ω 0) (μ ω : Measure M.AState) (M.seqCapital μ ω) := by
  have hmc : ∀ g, M.meanCapital (ω 0) (μ ω : Measure M.AState)
      (M.pricePath (ω 0) (M.initMass (μ ω : Measure M.AState)) (M.seqCapital μ ω)) g
        = M.seqCapital μ ω g := by
    intro g
    rw [hμ.pricePath_eq ω, meanCapital, hμ.nodeDist_eq ω g]
    rfl
  refine ⟨⟨rfl, fun g => ?_⟩, fun g => (hmc g).symm⟩
  rw [← hmc g]
  exact M.meanCapital_mem (ω 0) _ _ g

/-- **Labour is consistent**: at every node of the future of every history, labour in the prices
is the mean efficiency of the households there. -/
theorem IsSeqStateEquilibrium.labour_eq {μ : History Z → ProbabilityMeasure M.AState}
    (hμ : M.IsSeqStateEquilibrium μ) (ω : History Z) (g : List Z) :
    (M.seqPrices μ ω g).2
      = ∫ x, M.efficiency x.2.idio ∂(μ (History.prepend g ω) : Measure M.AState) := by
  rw [← hμ.pricePath_eq ω, ← hμ.nodeDist_eq ω g]
  exact M.labour_eq_integral (ω 0) (μ ω : Measure M.AState) _ g

end KSModel

/-- **A sequence-state equilibrium with log utility and Cobb–Douglas production.** -/
theorem logEconomy_exists_seqStateEquilibrium [Nonempty E] (V : KSEnvironment Z E)
    (T : CobbDouglas Z) :
    ∃ μ : History Z → ProbabilityMeasure (logEconomy V T).floored.AState,
      (logEconomy V T).floored.IsSeqStateEquilibrium μ :=
  (logEconomy V T).floored.exists_seqStateEquilibrium

end KrusellSmith

end LeanEconomics
