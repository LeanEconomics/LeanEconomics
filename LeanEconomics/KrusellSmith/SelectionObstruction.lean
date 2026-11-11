/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ConsistentSelection

/-!
# What a selection of sequential equilibria must satisfy

Route 3 of `CROSS_SECTION_PLAN.md`. A recursive equilibrium on the minimal state `(z, μ)` is a
**consistent** selection of sequential equilibria (`ConsistentSelection.isRecursive`). Selection
theorems produce selections, not consistent ones; this file records what consistency forces.

* **`shiftPath_eq_of_merge`**: if the equilibria selected from two states reach, at nodes with the
  same shock, the same cross-section, their continuations from those nodes coincide. In
  particular a selected equilibrium is Markov on its own tree (`shiftPath_eq_of_node_eq`).
* **`isEmpty_of_conflict`**: so if two states each have a *unique* sequential equilibrium, and
  these reach the same shock and cross-section with different continuations, **no consistent
  selection exists** — no recursive equilibrium on the minimal state, measurable or not.

The second is the form a counterexample would take (as in Kubler–Schmedders for finitely many
agents): the common child state has two equilibria, and each parent's households, expecting one
of them, save so as to reach it. Nothing in the model rules this out once sequential equilibrium
is not unique, which is why the selection route cannot deliver the minimal state in general.
-/

open Set MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

namespace ConsistentSelection

variable (S : M.ConsistentSelection)

/-- **Merging states merge continuations**: if the equilibria selected from `(z₁, μ₁)` and
`(z₂, μ₂)` reach the same shock and cross-section at nodes `h₁`, `h₂`, they continue identically
from there. -/
theorem shiftPath_eq_of_merge {z₁ z₂ : Z} {μ₁ μ₂ : ProbabilityMeasure M.AState} {h₁ h₂ : List Z}
    (hz : shockAt z₁ h₁ = shockAt z₂ h₂) (hμ : S.nodeProb z₁ μ₁ h₁ = S.nodeProb z₂ μ₂ h₂) :
    shiftPath (S.sel z₁ μ₁) h₁ = shiftPath (S.sel z₂ μ₂) h₂ := by
  rw [S.shiftPath_sel z₁ μ₁ h₁, S.shiftPath_sel z₂ μ₂ h₂, hz, hμ]

/-- **A selected equilibrium is Markov on its own tree**: nodes with the same shock and
cross-section have the same continuation. -/
theorem shiftPath_eq_of_node_eq (z : Z) (μ : ProbabilityMeasure M.AState) {h g : List Z}
    (hz : shockAt z h = shockAt z g) (hμ : S.nodeProb z μ h = S.nodeProb z μ g) :
    shiftPath (S.sel z μ) h = shiftPath (S.sel z μ) g :=
  S.shiftPath_eq_of_merge hz hμ

end ConsistentSelection

/-- **A conflict rules out every consistent selection**: two states with unique sequential
equilibria `K₁`, `K₂` that reach the same shock and cross-section at nodes `h₁`, `h₂` but continue
differently from there. -/
theorem isEmpty_consistentSelection_of_conflict {z₁ z₂ : Z}
    {μ₁ μ₂ : ProbabilityMeasure M.AState} {K₁ K₂ : List Z → ℝ} {h₁ h₂ : List Z}
    (hu₁ : ∀ K, M.IsSequentialEquilibrium z₁ (μ₁ : Measure M.AState) K → K = K₁)
    (hu₂ : ∀ K, M.IsSequentialEquilibrium z₂ (μ₂ : Measure M.AState) K → K = K₂)
    (hz : shockAt z₁ h₁ = shockAt z₂ h₂)
    (hμ : M.nodeDist z₁ (μ₁ : Measure M.AState)
        (M.pricePath z₁ (M.initMass (μ₁ : Measure M.AState)) K₁) h₁
      = M.nodeDist z₂ (μ₂ : Measure M.AState)
        (M.pricePath z₂ (M.initMass (μ₂ : Measure M.AState)) K₂) h₂)
    (hne : shiftPath K₁ h₁ ≠ shiftPath K₂ h₂) : IsEmpty M.ConsistentSelection := by
  refine ⟨fun S => hne ?_⟩
  have e1 := hu₁ _ (S.sel_spec z₁ μ₁)
  have e2 := hu₂ _ (S.sel_spec z₂ μ₂)
  have hμ' : S.nodeProb z₁ μ₁ h₁ = S.nodeProb z₂ μ₂ h₂ := by
    refine Subtype.ext ?_
    change M.nodeDist z₁ (μ₁ : Measure M.AState)
        (M.pricePath z₁ (M.initMass (μ₁ : Measure M.AState)) (S.sel z₁ μ₁)) h₁
      = M.nodeDist z₂ (μ₂ : Measure M.AState)
        (M.pricePath z₂ (M.initMass (μ₂ : Measure M.AState)) (S.sel z₂ μ₂)) h₂
    rw [e1, e2]
    exact hμ
  have h := S.shiftPath_eq_of_merge hz hμ'
  rwa [e1, e2] at h

end KSModel

end KrusellSmith

end LeanEconomics
