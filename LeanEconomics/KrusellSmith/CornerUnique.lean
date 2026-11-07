/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CornerStationary
import LeanEconomics.KrusellSmith.ValueState

/-!
# Uniqueness in the corner economy

When households save by the corner policy along **every** price path (the corner conditions
hold uniformly, as in the witness):

* **`uniqueSequentialEquilibrium_of_policy`**: from every initial shock and distribution there is
  exactly one sequential equilibrium — the distribution path, hence the capital path, does not
  depend on prices;
* `pushNode_of_marginal`: one step from any cross-section with employment marginal `D.m z` is
  `cornerDist z z'`;
* **`eq_μc_of_policy`**: under the KS design, the corner candidate is the **only** sequence-state
  equilibrium (every sequence-state equilibrium has the design's marginal,
  `initMass_eq_design`).

**`cornerUnique`**: for the witness economy (log utility, Cobb–Douglas, heterogeneous households)
the sequential equilibrium is unique from every initial state, the sequence-state equilibrium is
unique and equals the corner one, `(z, K)` is sufficient, and the stationary law on `(z, K)` is
unique.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (saver : E → Prop) [DecidablePred saver]

/-- **Uniqueness of sequential equilibrium** when households save by the corner policy along
every price path. -/
theorem uniqueSequentialEquilibrium_of_policy
    (hpol : ∀ (z₀ : Z) (P : List Z → ℝ × ℝ) (s : M.State),
      M.policy z₀ P s = cornerPolicy M saver s) :
    M.UniqueSequentialEquilibrium := by
  intro z μ K K' hK hK'
  have hnd : ∀ (P P' : List Z → ℝ × ℝ) (h : List Z),
      M.nodeDist z (μ : Measure M.AState) P h = M.nodeDist z (μ : Measure M.AState) P' h := by
    intro P P' h
    induction h with
    | nil => rfl
    | cons z' h ih =>
      change M.pushNode z P h z' (M.nodeDist z (μ : Measure M.AState) P h)
        = M.pushNode z P' h z' (M.nodeDist z (μ : Measure M.AState) P' h)
      rw [ih]
      exact M.pushNode_congr rfl (fun e' x => by simp only [nextA, hpol]) z' _
  funext h
  rw [hK h, hK' h]
  unfold meanCapital
  rw [hnd _ (M.pricePath z (M.initMass (μ : Measure M.AState)) K') h]

/-- Integrating a function of the employment state. -/
theorem integral_idioFun (ν : Measure M.AState) [IsProbabilityMeasure ν] (g : E → ℝ) :
    ∫ x, g x.2.idio ∂ν = ∑ e, M.initMass ν e * g e := by
  have hfun : (fun x : M.AState => g x.2.idio) = fun x => ∑ e, g e * M.idioInd e x := by
    funext x
    rw [Finset.sum_eq_single x.2.idio]
    · rw [M.idioInd_of_eq rfl, mul_one]
    · intro e _ he
      rw [M.idioInd_of_ne (fun h => he h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hfun, integral_finsetSum _ fun e _ => ((M.idioInd e).integrable ν).const_mul _]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_const_mul, M.integral_idioInd, mul_comm]
  rfl

/-- **One step from any cross-section with the design marginal is the corner cross-section**,
when households follow the corner policy. -/
theorem pushNode_of_marginal (D : EmploymentDesign M.idioProb) {z z' : Z}
    {K : List Z → ℝ × ℝ}
    (hpol : ∀ s : M.State, s.2.node = [] → M.policy z K s = cornerPolicy M saver s)
    {ν : Measure M.AState} [IsProbabilityMeasure ν] (hν : M.initMass ν = D.m z) :
    M.pushNode z K [] z' ν = (cornerDist D saver z z' : Measure M.AState) := by
  have : IsProbabilityMeasure (M.pushNode z K [] z' ν) := M.isProbabilityMeasure_pushNode _ _ _ _ _
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [M.integral_pushNode]
  have hφ : ∀ x : M.AState, ∑ e', M.nextProb z [] z' e' x * f (M.nextA z K [] e' x)
      = (fun i : E => ∑ e', M.idioProb z z' i e' * f (cornerPt M saver (i, e'))) x.2.idio := by
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
  have hI := integral_idioFun ν
    (fun i : E => ∑ e', M.idioProb z z' i e' * f (cornerPt M saver (i, e')))
  rw [hI, hν, integral_cornerDist, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e' _ => ?_
  change D.m z e * (M.idioProb z z' e e' * f (cornerPt M saver (e, e')))
    = D.m z e * M.idioProb z z' e e' * f (cornerPt M saver (e, e'))
  ring

/-- **The corner candidate is the only sequence-state equilibrium**, under the KS design, when
households save by the corner policy along every price path. -/
theorem eq_μc_of_policy (D : EmploymentDesign M.idioProb)
    (hpol : ∀ (z₀ : Z) (P : List Z → ℝ × ℝ) (s : M.State),
      M.policy z₀ P s = cornerPolicy M saver s)
    {μ : History Z → ProbabilityMeasure M.AState} (hμ : M.IsSeqStateEquilibrium μ) :
    μ = μc D saver := by
  funext ω'
  rw [← History.cons_head_tail ω']
  apply ProbabilityMeasure.toMeasure_injective
  have h := congrArg (fun ν : History Z → ProbabilityMeasure M.AState =>
    (ν (History.cons (ω' 0) (History.tail ω')) : Measure M.AState)) hμ
  rw [← h, M.coe_seqStep_cons]
  exact pushNode_of_marginal saver D (fun s _ => hpol _ _ s)
    (hμ.initMass_eq_design D (History.tail ω'))

end KSModel

namespace CornerWitness

open KSModel

/-- **Uniqueness of sequential equilibrium** in the witness economy, from every initial state. -/
theorem uniqueSequentialEquilibrium_witness : model.UniqueSequentialEquilibrium :=
  uniqueSequentialEquilibrium_of_policy saver policy_witness

/-- **The corner equilibrium is the only sequence-state equilibrium** of the witness economy. -/
theorem eq_μw {μ : History Bool → ProbabilityMeasure model.AState}
    (hμ : model.IsSeqStateEquilibrium μ) : μ = μw :=
  eq_μc_of_policy saver design policy_witness hμ

/-- **The corner economy, complete**: in the log-utility, Cobb–Douglas economy with heterogeneous
households of `CornerWitness.lean`, sequential equilibrium is unique from every initial state;
the sequence-state equilibrium exists, is unique, and is the corner one; `(z, K)` is a sufficient
state and a recursive equilibrium on `(z, K)` represents it; and its law of motion on `(z, K)` has
a unique stationary distribution on the capital sets. -/
theorem cornerUnique :
    model.UniqueSequentialEquilibrium ∧ model.IsSeqStateEquilibrium μw ∧
      (∀ μ, model.IsSeqStateEquilibrium μ → μ = μw) ∧ KSufficient μw ∧
      (∃ R : model.AggStateRecursiveEquilibrium, R.Represents μw) ∧
      IsAggInvariant μw statLaw ∧ statLaw (Kgraph μw) = 1 ∧
      ∀ (Λ : Measure (ShockVal Bool × ℝ)) [IsProbabilityMeasure Λ],
        IsAggInvariant μw Λ → Λ (Kgraph μw) = 1 → Λ = statLaw :=
  ⟨uniqueSequentialEquilibrium_witness, cornerWitness.1, fun _ hμ => eq_μw hμ,
    cornerWitness.2.1, cornerWitness.2.2, cornerStationary.1, cornerStationary.2.1,
    cornerStationary.2.2⟩

end CornerWitness

end KrusellSmith

end LeanEconomics
