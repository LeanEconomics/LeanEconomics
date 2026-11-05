/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.SequenceStateRecursive
import LeanEconomics.KrusellSmith.Recursive

/-!
# When the sequence-state equilibrium is Markov in today's shock and distribution

Milestone TS5 of `SEQUENCE_STATE_PLAN.md`.

A sequence-state equilibrium (TS3, TS4) has the infinite history `ω` as its aggregate state. It
is **Markov in the minimal state** at a pair of histories with the same shock and the same
distribution if tomorrow's distributions, the prices and the household's value and policy agree
there.

**Local uniqueness suffices** (`IsSeqStateEquilibrium.markov_*`): if the sequential equilibrium
from `(ω 0, μ ω)` is unique (`UniqueFrom`), then every history `ω'` with the same shock and
distribution has the same prices on its future, the same distribution after every new shock, and
the same value and saving policy. Only uniqueness from the states the equilibrium actually
visits is needed, not from every `(z, μ)`.

**Under global uniqueness** (`UniqueSequentialEquilibrium`) every sequence-state equilibrium is
the Markov equilibrium of `Recursive.lean` on the distributions it visits: tomorrow's distribution
is its `lawOfMotion` (`eq_lawOfMotion`), the distributions on the future of `ω` are its
`nodeProb` (`eq_nodeProb`), and saving is its `recursivePolicy`
(`seqPolicy_eq_recursivePolicy`).

Without uniqueness, the infinite history can carry information that `(z, μ)` does not: which of
several continuation equilibria from `(z, μ)` the past expected. The history then selects the
continuation, as in the expanded state spaces of Duffie, Geanakoplos, Mas-Colell and McLennan.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **Uniqueness of the sequential equilibrium from one state** `(z, ν)`. -/
def UniqueFrom (z : Z) (ν : ProbabilityMeasure M.AState) : Prop :=
  ∀ K K' : List Z → ℝ, M.IsSequentialEquilibrium z (ν : Measure M.AState) K →
    M.IsSequentialEquilibrium z (ν : Measure M.AState) K' → K = K'

variable {M}

theorem UniqueSequentialEquilibrium.uniqueFrom (hU : M.UniqueSequentialEquilibrium) (z : Z)
    (ν : ProbabilityMeasure M.AState) : M.UniqueFrom z ν :=
  hU z ν

variable {μ : History Z → ProbabilityMeasure M.AState}

/-! ### Local uniqueness gives Markov-ness -/

section Local

variable (hμ : M.IsSeqStateEquilibrium μ) {ω ω' : History Z} (hz : ω 0 = ω' 0)
  (hd : μ ω = μ ω') (hU : M.UniqueFrom (ω 0) (μ ω))
include hμ hz hd hU

/-- Same shock and distribution, with a unique sequential equilibrium there: **the same prices
on the future**. -/
theorem IsSeqStateEquilibrium.markov_seqPrices : M.seqPrices μ ω = M.seqPrices μ ω' := by
  have h1 := (hμ.isSequentialEquilibrium ω).2
  have h2 := (hμ.isSequentialEquilibrium ω').2
  rw [← hz, ← hd] at h2
  have hK : M.seqCapital μ ω = M.seqCapital μ ω' := hU _ _ h1 h2
  rw [← hμ.pricePath_eq ω, ← hμ.pricePath_eq ω', hK, hz, hd]

/-- **The same distribution after every new shock.** -/
theorem IsSeqStateEquilibrium.markov_cons (z' : Z) :
    μ (History.cons z' ω) = μ (History.cons z' ω') := by
  have hP := hμ.markov_seqPrices hz hd hU
  rw [← congrFun hμ (History.cons z' ω), ← congrFun hμ (History.cons z' ω')]
  apply Subtype.ext
  change M.pushNode (ω 0) (M.seqPrices μ ω) [] z' (μ ω : Measure M.AState)
    = M.pushNode (ω' 0) (M.seqPrices μ ω') [] z' (μ ω' : Measure M.AState)
  rw [hP, hz, hd]

/-- **The same saving policy.** -/
theorem IsSeqStateEquilibrium.markov_seqPolicy : M.seqPolicy μ ω = M.seqPolicy μ ω' := by
  have hP := hμ.markov_seqPrices hz hd hU
  funext a e
  apply Subtype.ext
  change M.policy (ω 0) (M.seqPrices μ ω) (a, ⟨e, []⟩)
    = M.policy (ω' 0) (M.seqPrices μ ω') (a, ⟨e, []⟩)
  rw [hP, hz]

/-- **The same value.** -/
theorem IsSeqStateEquilibrium.markov_seqValue : M.seqValue μ ω = M.seqValue μ ω' := by
  have hP := hμ.markov_seqPrices hz hd hU
  funext a e
  change (M.household (ω 0) (M.seqPrices μ ω)).valueFunction (a, ⟨e, []⟩)
    = (M.household (ω' 0) (M.seqPrices μ ω')).valueFunction (a, ⟨e, []⟩)
  rw [hP, hz]

end Local

/-! ### Global uniqueness: the Markov equilibrium of `Recursive.lean` -/

section Global

variable (hμ : M.IsSeqStateEquilibrium μ) (hU : M.UniqueSequentialEquilibrium)
include hμ hU

/-- Under uniqueness, capital on the future of `ω` is the equilibrium path from `(ω 0, μ ω)`. -/
theorem IsSeqStateEquilibrium.seqCapital_eq_eqPath (ω : History Z) :
    M.seqCapital μ ω = M.eqPath (ω 0) (μ ω) :=
  hU.eq_eqPath (hμ.isSequentialEquilibrium ω).2

/-- **The distributions on the future of `ω` are those of the Markov equilibrium.** -/
theorem IsSeqStateEquilibrium.eq_nodeProb (ω : History Z) (g : List Z) :
    μ (History.prepend g ω) = M.nodeProb (ω 0) (μ ω) g := by
  apply Subtype.ext
  change (μ (History.prepend g ω) : Measure M.AState)
    = M.nodeDist (ω 0) (μ ω : Measure M.AState)
      (M.pricePath (ω 0) (M.initMass (μ ω : Measure M.AState)) (M.eqPath (ω 0) (μ ω))) g
  rw [← hμ.seqCapital_eq_eqPath hU ω, hμ.pricePath_eq ω, hμ.nodeDist_eq ω g]

/-- **Tomorrow's distribution is the Markov law of motion** of today's shock and
distribution. -/
theorem IsSeqStateEquilibrium.eq_lawOfMotion (ω : History Z) (z' : Z) :
    μ (History.cons z' ω) = M.lawOfMotion (ω 0) (μ ω) z' :=
  hμ.eq_nodeProb hU ω [z']

/-- **Saving is the Markov policy** of today's shock and distribution. -/
theorem IsSeqStateEquilibrium.seqPolicy_eq_recursivePolicy (ω : History Z)
    (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    (M.seqPolicy μ ω a e : ℝ) = M.recursivePolicy (ω 0) (μ ω) (a, ⟨e⟩) := by
  rw [recursivePolicy, ← hμ.seqCapital_eq_eqPath hU ω, hμ.pricePath_eq ω]
  rfl

end Global

end KSModel

end KrusellSmith

end LeanEconomics
