/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Spotless
import LeanEconomics.KrusellSmith.StationaryEquilibrium
import LeanEconomics.MarkovEquilibrium.Barycentre

/-!
# Existence of a conditionally spotless stationary recursive equilibrium

Milestone SP3 of `SPOTLESS_PLAN.md`: Cao (2020, Definition 6 and Theorem 4), via Duffie,
Geanakoplos, Mas-Colell and McLennan (1994, Proposition 1.3).

**Theorem** (`exists_conditionallySpotlessEquilibrium`). Every Krusell–Smith economy has a
stationary recursive equilibrium with an ergodic distribution (`StationaryRecursiveEquilibrium`,
S6) that is moreover **conditionally spotless**: for almost every state `ξ`, the transition
`T ξ` is the mean `E η` of a probability measure `η` on beliefs that are each **spotless**
(tomorrow's state is a function of tomorrow's shock) and **consistent** with `ξ`
(`spotlessExpectations`).

Sunspots then only choose among spotless, individually consistent continuations: households'
choices today are optimal against each of them, not just against their average. A fully spotless
stationary equilibrium (no randomisation at all) is not claimed; Cao leaves it open.

The proof is `MarkovEquilibrium.exists_ergodic_baryHull` with `g = spotlessExpectations` (closed
graph: `isClosed_graph_expectations` and `isClosed_spotless`; nonempty: the justified beliefs,
`justifiedBelief_mem`, `justifiedBelief_spotless`) and `G = expectations` (closed graph, convex).
-/

open Set MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **Spotless consistent beliefs** at a state. -/
def spotlessExpectations (ξ : ↥M.equilibriumStates) :
    Set (ProbabilityMeasure ↥M.equilibriumStates) :=
  M.expectations ξ ∩ M.spotless

theorem isClosed_graph_spotlessExpectations :
    IsClosed (MarkovEquilibrium.graphSet M.spotlessExpectations) :=
  M.isClosed_graph_expectations.inter (M.isClosed_spotless.preimage continuous_snd)

theorem spotlessExpectations_nonempty (ξ : ↥M.equilibriumStates) :
    (M.spotlessExpectations ξ).Nonempty := by
  obtain ⟨K, hK, hv, ha⟩ := ξ.2
  exact ⟨_, M.justifiedBelief_mem ξ hK hv ha, M.justifiedBelief_spotless _ _ hK⟩

/-- **A conditionally spotless stationary recursive equilibrium** (Cao 2020, Definition 6): a
stationary recursive equilibrium with an ergodic distribution whose transition is, almost
everywhere, a mixture of spotless consistent beliefs. -/
structure ConditionallySpotlessEquilibrium extends M.StationaryRecursiveEquilibrium where
  /-- Sunspots only randomise over spotless, individually consistent continuations. -/
  conditionallySpotless : ∀ᵐ ξ ∂(stationary : Measure ↥M.equilibriumStates),
    ∃ η : ProbabilityMeasure (ProbabilityMeasure ↥M.equilibriumStates),
      (η : Measure (ProbabilityMeasure ↥M.equilibriumStates)) (M.spotlessExpectations ξ) = 1 ∧
        MarkovEquilibrium.mean η = transition ξ

/-- **Existence of a conditionally spotless stationary recursive equilibrium with an ergodic
distribution** in every Krusell–Smith economy (Cao 2020, Theorem 4; DGMM 1994, Proposition 1.3).
-/
theorem exists_conditionallySpotlessEquilibrium [Nonempty Z] [Nonempty E] :
    Nonempty M.ConditionallySpotlessEquilibrium := by
  obtain ⟨γ, T, hT, hinv, hsel, herg⟩ := MarkovEquilibrium.exists_ergodic_baryHull
    M.isClosed_graph_spotlessExpectations M.spotlessExpectations_nonempty
    M.isClosed_graph_expectations M.mix_mem_expectations
    (fun ξ => inter_subset_left)
  exact ⟨⟨⟨T, γ, hT, hinv, hsel.mono fun ξ h => h.2, herg⟩, hsel.mono fun ξ h => h.1⟩⟩

end KSModel

end KrusellSmith

end LeanEconomics
