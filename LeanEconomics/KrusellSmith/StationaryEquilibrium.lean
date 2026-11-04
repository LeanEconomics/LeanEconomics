/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.SelfJustified

/-!
# Existence of a stationary recursive equilibrium with an ergodic distribution

Milestone S6 of `STATIONARITY_PLAN.md`: Cao (2020, Theorem 4), via Duffie, Geanakoplos,
Mas-Colell and McLennan (1994, Theorem 1.1 and Corollary 1.1).

**Theorem** (`exists_stationaryRecursiveEquilibrium`). Every Krusell–Smith economy (`KSModel`) has
a **stationary recursive equilibrium**: a transition `T` on the compact set `J*` of equilibrium
states `(z, μ, v, a)` (shock, distribution of households, their value and saving policy), and a
probability measure `γ` on `J*`, such that

* `T` is measurable and `γ` is **invariant**: `∫ T ξ dγ(ξ) = γ`;
* for `γ`-almost every state `ξ`, the beliefs `T ξ` about tomorrow's state are **consistent with
  `ξ`** (`expectations`): tomorrow's shock follows `π`, tomorrow's distribution is today's pushed
  forward by the policy `a`, and `(v, a)` solve the household's Bellman equation against the
  expected continuation values under `T ξ`;
* `γ` is **ergodic** for `T`: every invariant set has `γ`-measure `0` or `1`.

`T ξ` may randomise over tomorrow's states given tomorrow's shock (a sunspot: DGMM's
"randomisation over continuation equilibria"); the distribution of households tomorrow is
nevertheless pinned down by today's state. Cao's refinement to a conditionally spotless
equilibrium is not attempted.

The proof is `MarkovEquilibrium.exists_ergodic` applied to `J*` (compact metrizable,
`isCompact_equilibriumStates`) and the expectations correspondence (closed graph, convex and
nonempty values: `isClosed_graph_expectations`, `mix_mem_expectations`, `expectations_nonempty`).
The theorem holds for every `KSModel`, in particular the log and CRRA economies of `Inada.lean`.
-/

open Set MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

instance [Nonempty Z] [Nonempty E] : Nonempty ↥M.equilibriumStates :=
  M.equilibriumStates_nonempty.to_subtype

/-- **A stationary recursive equilibrium** with an ergodic distribution of states: a measurable
transition on equilibrium states, selected from the expectations correspondence almost
everywhere, and an invariant ergodic distribution. -/
structure StationaryRecursiveEquilibrium where
  /-- The transition: beliefs about tomorrow's state at each state today. -/
  transition : ↥M.equilibriumStates → ProbabilityMeasure ↥M.equilibriumStates
  /-- The stationary distribution of states. -/
  stationary : ProbabilityMeasure ↥M.equilibriumStates
  measurable_transition : Measurable transition
  /-- The distribution of states is invariant under the transition. -/
  invariant : (stationary : Measure ↥M.equilibriumStates).bind
      (fun ξ => (transition ξ : Measure ↥M.equilibriumStates)) = stationary
  /-- Almost every state's beliefs are consistent with it. -/
  consistent : ∀ᵐ ξ ∂(stationary : Measure ↥M.equilibriumStates),
    transition ξ ∈ M.expectations ξ
  /-- The distribution of states is ergodic. -/
  ergodic : ∀ A : Set ↥M.equilibriumStates, MeasurableSet A →
    (∀ᵐ ξ ∂(stationary : Measure ↥M.equilibriumStates), ξ ∈ A →
      (transition ξ : Measure ↥M.equilibriumStates) A = 1) →
    (stationary : Measure ↥M.equilibriumStates) A = 0 ∨
      (stationary : Measure ↥M.equilibriumStates) A = 1

/-- **Existence of a stationary recursive equilibrium with an ergodic distribution** in every
Krusell–Smith economy (Cao 2020, Theorem 4; DGMM 1994, Corollary 1.1). -/
theorem exists_stationaryRecursiveEquilibrium [Nonempty Z] [Nonempty E] :
    Nonempty M.StationaryRecursiveEquilibrium := by
  obtain ⟨γ, T, hT, hinv, hcons, herg⟩ := MarkovEquilibrium.exists_ergodic
    M.isClosed_graph_expectations M.expectations_nonempty M.mix_mem_expectations
  exact ⟨⟨T, γ, hT, hinv, hcons, herg⟩⟩

end KSModel

end KrusellSmith

end LeanEconomics
