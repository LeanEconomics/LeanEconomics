/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CornerVerification

/-!
# The corner candidate is an equilibrium, represented on `(z, K)`

Milestone C3 of `CORNER_PLAN.md`. Suppose the corner conditions hold along the candidate's own
price tree at every history (`CornerConditions`). Then:

* `pushNode_cornerDist`: with the corner policy, one step from `cornerDist y z` after the shock
  `z'` is `cornerDist z z'` — the push depends only on the employment marginal, which is
  `D.m z` (design consistency);
* **`isSeqStateEquilibrium_μc`**: the candidate is a sequence-state equilibrium — a
  Krusell–Smith equilibrium **with idiosyncratic heterogeneity** (households hold `ā` or `0`
  according to last period's employment);
* **`exists_represents_μc`**: it satisfies `KSufficient`, so a recursive equilibrium on `(z, K)`
  represents it.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (D : EmploymentDesign M.idioProb) (saver : E → Prop)
  [DecidablePred saver] (U : M.SmoothUtility)

/-- **The corner conditions along the candidate's price tree** at every history. -/
def CornerConditions : Prop :=
  ∀ ω : History Z, CornerFeas M saver (ω 0) (M.seqPrices (μc D saver) ω) ∧
    CornerEmp saver U (ω 0) (M.seqPrices (μc D saver) ω) ∧
    CornerUnemp saver U (ω 0) (M.seqPrices (μc D saver) ω)

variable {D saver U}

/-- **One step from the candidate is the candidate**, when households follow the corner policy. -/
theorem pushNode_cornerDist (y z z' : Z) (K : List Z → ℝ × ℝ)
    (hpol : ∀ s : M.State, s.2.node = [] → M.policy z K s = cornerPolicy M saver s) :
    M.pushNode z K [] z' (cornerDist D saver y z : Measure M.AState)
      = (cornerDist D saver z z' : Measure M.AState) := by
  have : IsProbabilityMeasure (M.pushNode z K [] z' (cornerDist D saver y z : Measure M.AState)) :=
    M.isProbabilityMeasure_pushNode _ _ _ _ _
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [M.integral_pushNode]
  -- the integrand is a function of the employment state
  set φ : M.AState →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => ∑ e', M.idioProb z z' x.2.idio e' * f (cornerPt M saver (x.2.idio, e')),
      (continuous_of_discreteTopology (f := fun i : Idio E =>
        ∑ e', M.idioProb z z' i.idio e' * f (cornerPt M saver (i.idio, e')))).comp continuous_snd⟩
  have hφ : ∀ x : M.AState, ∑ e', M.nextProb z [] z' e' x * f (M.nextA z K [] e' x) = φ x := by
    intro x
    refine Finset.sum_congr rfl fun e' _ => ?_
    have hn : M.nextA z K [] e' x = cornerPt M saver (x.2.idio, e') := by
      have hp := hpol (x.1, ⟨x.2.idio, []⟩) rfl
      change (M.clampAssets (M.policy z K (x.1, ⟨x.2.idio, []⟩)), (⟨e'⟩ : Idio E)) = _
      rw [hp]
      refine Prod.ext ?_ rfl
      change M.clampAssets (cornerSave M saver x.2.idio : ℝ) = cornerSave M saver x.2.idio
      rw [M.clampAssets_of_mem (cornerSave M saver x.2.idio).2]
    rw [hn]
    rfl
  simp only [hφ]
  rw [integral_cornerDist, integral_cornerDist, Fintype.sum_prod_type, Fintype.sum_prod_type]
  -- regroup by today's employment state
  change ∑ em, ∑ e, D.m y em * M.idioProb y z em e
      * ∑ e', M.idioProb z z' e e' * f (cornerPt M saver (e, e'))
    = ∑ e, ∑ e', D.m z e * M.idioProb z z' e e' * f (cornerPt M saver (e, e'))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_mul, D.consistent y z e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e' _ => ?_
  ring

/-- **The corner candidate is a sequence-state equilibrium.** -/
theorem isSeqStateEquilibrium_μc (hC : CornerConditions D saver U) :
    M.IsSeqStateEquilibrium (μc D saver) := by
  funext ω'
  rw [← History.cons_head_tail ω']
  set ω := History.tail ω'
  set z' := ω' 0
  apply ProbabilityMeasure.toMeasure_injective
  rw [M.coe_seqStep_cons]
  obtain ⟨hF, hE, hU⟩ := hC ω
  exact pushNode_cornerDist (ω 1) (ω 0) z' _
    fun s _ => policy_eq_cornerPolicy hF hE hU s

/-- **The corner equilibrium is represented by a recursive equilibrium on `(z, K)`.** -/
theorem exists_represents_μc (hC : CornerConditions D saver U) :
    ∃ R : M.AggStateRecursiveEquilibrium, R.Represents (μc D saver) :=
  (kSufficient_iff_exists_represents (isSeqStateEquilibrium_μc hC)).1 (kSufficient_μc D saver)

end KSModel

end KrusellSmith

end LeanEconomics
