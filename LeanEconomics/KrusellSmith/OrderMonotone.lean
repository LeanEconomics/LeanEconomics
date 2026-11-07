/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.OrderStructure
import LeanEconomics.KrusellSmith.GreatestEquilibrium

/-!
# The equilibrium law of motion preserves dominance

Milestone OS2 of `ORDER_STRUCTURE_PLAN.md`: hypothesis (Mon) of the chain theorem from
primitives, when savings rise with aggregate capital (`SavingMonotone`, MR3) and sequential
equilibrium is unique.

* **`eqPath_mono`** (Tarski comparative statics): if `ν ≼ ν'`, the equilibrium capital path from
  `ν` lies below the one from `ν'`. Dominance forces equal employment marginals, so labour is the
  same; the path from `ν` is then a post-fixed point of the equilibrium map from `ν'`
  (`meanCapital_le`), hence below its greatest fixed point (`le_greatest_of_post`), which under
  uniqueness is the equilibrium.
* **`lawOfMotion_dominates`**: then every household saves more from `ν'` (`SavingMonotone`), so
  next period's cross-section from `ν'` dominates the one from `ν` (`nodeDist_dominates`).
* **`monOnHistories_of_savingMonotone`**: (Mon) holds for every sequence-state equilibrium;
  **`kSufficient_of_savingMonotone`**: with (Sep), `(z, K)` is a sufficient state.

`SavingMonotone` is proved for complementarity economies (constant wage, return nondecreasing in
capital, RRA ≤ 1; `savingMonotone_of`), and fails for Cobb–Douglas.
-/

open MeasureTheory Set

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (hH : M.SavingMonotone) (hU : M.UniqueSequentialEquilibrium)

include hH hU in
/-- **The equilibrium capital path is isotone in the cross-section.** -/
theorem eqPath_mono (z : Z) {ν ν' : ProbabilityMeasure M.AState}
    (hν : M.AssetDominates ν ν') (h : List Z) : M.eqPath z ν h ≤ M.eqPath z ν' h := by
  have hm : M.initMass (ν : Measure M.AState) = M.initMass (ν' : Measure M.AState) :=
    hν.initMass_eq
  have hspec := M.eqPath_spec z ν
  have hgr : greatest hH z ν' = M.eqPath z ν' := hU.eq_eqPath (greatest_spec hH z ν')
  rw [← hgr]
  refine le_greatest_of_post hH z ν'
    (fun g => M.equilibrium_mem_pi z ν hspec g (mem_univ g)) (fun g => ?_) h
  rw [hspec g, ← hm]
  exact M.meanCapital_le z (fun s => le_rfl) hν g

include hH hU in
/-- **The equilibrium law of motion preserves dominance.** -/
theorem lawOfMotion_dominates (z z' : Z) {ν ν' : ProbabilityMeasure M.AState}
    (hν : M.AssetDominates ν ν') :
    M.AssetDominates (M.lawOfMotion z ν z' : Measure M.AState) (M.lawOfMotion z ν' z') := by
  have hm : M.initMass (ν : Measure M.AState) = M.initMass (ν' : Measure M.AState) :=
    hν.initMass_eq
  have hpol : ∀ s, M.policy z (M.pricePath z (M.initMass (ν : Measure M.AState))
      (M.eqPath z ν)) s
      ≤ M.policy z (M.pricePath z (M.initMass (ν' : Measure M.AState)) (M.eqPath z ν')) s := by
    rw [← hm]
    exact hH z _ _ _ (eqPath_mono hH hU z hν)
  exact M.nodeDist_dominates z hpol hν [z']

include hH hU in
/-- **(Mon)** for every sequence-state equilibrium, when savings rise with aggregate capital. -/
theorem monOnHistories_of_savingMonotone [LinearOrder Z]
    {μ : History Z → ProbabilityMeasure M.AState} (hμ : M.IsSeqStateEquilibrium μ) :
    MonOnHistories μ := by
  intro ω ω' h0 hd z'
  rw [hμ.eq_lawOfMotion hU ω z', hμ.eq_lawOfMotion hU ω' z', ← h0]
  exact lawOfMotion_dominates hH hU (ω 0) z' hd

include hH hU in
/-- **`(z, K)` is a sufficient state** when savings rise with aggregate capital, sequential
equilibrium is unique, and the cross-sections after ordered shocks are ordered (Sep). -/
theorem kSufficient_of_savingMonotone [LinearOrder Z]
    {μ : History Z → ProbabilityMeasure M.AState} (hμ : M.IsSeqStateEquilibrium μ)
    (hSep : SepOnHistories μ) : KSufficient μ :=
  kSufficient_of_chain hμ hU (monOnHistories_of_savingMonotone hH hU hμ) hSep

end KSModel

end KrusellSmith

end LeanEconomics
