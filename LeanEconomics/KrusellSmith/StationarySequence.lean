/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ShockHistory
import LeanEconomics.KrusellSmith.SequenceStateMarkov

/-!
# A stationary sequential equilibrium, as a factor of the shock history

Milestone SS2 of `STATIONARY_SEQUENCE_PLAN.md`. A sequence-state equilibrium `μ` is a function of
the infinite shock history. Draw the history from a law `P` that the extension kernel leaves
invariant (`ShockHistory.lean`); then the aggregate state `(ξ 0, μ ξ)` — today's shock and today's
distribution of households — has the same law every period. No recursive state space and no
sunspot randomisation: the equilibrium inherits stationarity from the shocks.

* `stateOf μ ξ = (ξ 0, μ ξ)`, `stateLaw P μ`: the law of the aggregate state.
* **`stateLaw_tomorrow`** (no uniqueness needed): for a measurable sequence-state equilibrium, the
  law of tomorrow's state `(z', μ (cons z' ξ))`, with `z'` drawn by the aggregate chain, is
  `stateLaw P μ` again.
* `eqKernel`: the equilibrium law of motion on the aggregate state,
  `(z, ν) ↦ Σ_{z'} π z z' δ_{(z', lawOfMotion z ν z')}`.
* **`isInvariant_stateLaw`**: under uniqueness of sequential equilibrium, `stateLaw P μ` is an
  invariant distribution of the equilibrium Markov process; **`ergodic_stateLaw`**: it is ergodic
  when `P` is.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction TopologicalSpace ProbabilityTheory
open scoped ENNReal NNReal

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

omit [Fintype Z] in
theorem ShockPath.toHistory_cons (z : Z) (ξ : ShockPath Z) :
    (ShockPath.cons z ξ).toHistory = History.cons z ξ.toHistory := by
  funext n
  cases n <;> rfl

omit [Fintype Z] in
theorem ShockPath.toHistory_zero (ξ : ShockPath Z) : ξ.toHistory 0 = (ξ 0).val := rfl

namespace KSModel

variable {M : KSModel Z E}

/-- **The aggregate state at a history**: today's shock and today's distribution. -/
def stateOf (μ : History Z → ProbabilityMeasure M.AState) (ξ : ShockPath Z) :
    ShockVal Z × ProbabilityMeasure M.AState :=
  (ξ 0, μ ξ.toHistory)

/-- **The law of the aggregate state** when the history is drawn from `P`. -/
noncomputable def stateLaw (P : Measure (ShockPath Z))
    (μ : History Z → ProbabilityMeasure M.AState) :
    Measure (ShockVal Z × ProbabilityMeasure M.AState) :=
  P.map (stateOf μ)

theorem measurable_stateOf {μ : History Z → ProbabilityMeasure M.AState}
    (hmeas : Measurable fun ξ : ShockPath Z => μ ξ.toHistory) : Measurable (stateOf μ) :=
  (measurable_pi_apply 0).prodMk hmeas

theorem stateOf_cons (μ : History Z → ProbabilityMeasure M.AState) (z' : Z) (ξ : ShockPath Z) :
    stateOf μ (ShockPath.cons z' ξ) = ((⟨z'⟩ : ShockVal Z), μ (History.cons z' ξ.toHistory)) := by
  simp only [stateOf, ShockPath.cons_zero, ShockPath.toHistory_cons]

theorem indicator_preimage_stateOf_cons (μ : History Z → ProbabilityMeasure M.AState)
    (B : Set (ShockVal Z × ProbabilityMeasure M.AState)) (z' : Z) (ξ : ShockPath Z) :
    (stateOf μ ⁻¹' B).indicator (1 : ShockPath Z → ℝ≥0∞) (ShockPath.cons z' ξ)
      = B.indicator 1 ((⟨z'⟩ : ShockVal Z), μ (History.cons z' ξ.toHistory)) := by
  by_cases h : stateOf μ (ShockPath.cons z' ξ) ∈ B
  · rw [Set.indicator_of_mem (show ShockPath.cons z' ξ ∈ stateOf μ ⁻¹' B from h),
      Set.indicator_of_mem (show _ ∈ B by rwa [stateOf_cons] at h)]
    rfl
  · rw [Set.indicator_of_notMem (show ShockPath.cons z' ξ ∉ stateOf μ ⁻¹' B from h),
      Set.indicator_of_notMem (show _ ∉ B by rwa [stateOf_cons] at h)]

/-- **A stationary sequential equilibrium**: if the history is drawn from an invariant law, the
law of tomorrow's aggregate state `(z', μ (cons z' ξ))`, with `z'` drawn by the aggregate chain,
is the law of today's. No uniqueness is needed. -/
theorem stateLaw_tomorrow {μ : History Z → ProbabilityMeasure M.AState}
    (hmeas : Measurable fun ξ : ShockPath Z => μ ξ.toHistory)
    {P : Measure (ShockPath Z)} (hP : ShockPath.IsInvariant M.aggProb P)
    {B : Set (ShockVal Z × ProbabilityMeasure M.AState)} (hB : MeasurableSet B) :
    ∫⁻ ξ, ∑ z', ENNReal.ofReal (M.aggProb (ξ 0).val z')
        * B.indicator 1 ((⟨z'⟩ : ShockVal Z), μ (History.cons z' ξ.toHistory)) ∂P
      = stateLaw P μ B := by
  have hA : MeasurableSet (stateOf μ ⁻¹' B) := measurable_stateOf hmeas hB
  rw [stateLaw, Measure.map_apply (measurable_stateOf hmeas) hB, hP.apply M.aggProb hA]
  refine lintegral_congr fun ξ => ?_
  rw [ShockPath.extMeasure_apply M.aggProb ξ hA]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [indicator_preimage_stateOf_cons]

/-! ### The equilibrium Markov process on the aggregate state -/

variable (hU : M.UniqueSequentialEquilibrium)

variable (M) in
/-- **The equilibrium law of motion on the aggregate state**:
`(z, ν) ↦ Σ_{z'} π z z' δ_{(z', lawOfMotion z ν z')}`. -/
noncomputable def eqKernel (s : ShockVal Z × ProbabilityMeasure M.AState) :
    Measure (ShockVal Z × ProbabilityMeasure M.AState) :=
  ∑ z', ENNReal.ofReal (M.aggProb s.1.val z')
    • Measure.dirac ((⟨z'⟩ : ShockVal Z), M.lawOfMotion s.1.val s.2 z')

theorem eqKernel_apply (s : ShockVal Z × ProbabilityMeasure M.AState)
    {B : Set (ShockVal Z × ProbabilityMeasure M.AState)} (hB : MeasurableSet B) :
    M.eqKernel s B = ∑ z', ENNReal.ofReal (M.aggProb s.1.val z')
      * B.indicator 1 ((⟨z'⟩ : ShockVal Z), M.lawOfMotion s.1.val s.2 z') := by
  simp only [eqKernel, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hB, smul_eq_mul]

include hU in
theorem measurable_eqKernel : Measurable M.eqKernel := by
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have e : (fun s => M.eqKernel s B) = fun s : ShockVal Z × ProbabilityMeasure M.AState =>
      ∑ z', ENNReal.ofReal (M.aggProb s.1.val z')
        * B.indicator 1 ((⟨z'⟩ : ShockVal Z), M.lawOfMotion s.1.val s.2 z') :=
    funext fun s => eqKernel_apply s hB
  rw [e]
  refine measurable_from_prod_countable_right fun v => ?_
  refine Finset.measurable_sum _ fun z' _ => ?_
  change Measurable fun y : ProbabilityMeasure M.AState => ENNReal.ofReal (M.aggProb v.val z')
    * B.indicator 1 ((⟨z'⟩ : ShockVal Z), M.lawOfMotion v.val y z')
  refine Measurable.const_mul ?_ _
  exact (measurable_one.indicator hB).comp
    (measurable_const.prodMk (M.continuous_lawOfMotion hU v.val z').measurable)

include hU in
/-- **The law of the aggregate state is an invariant distribution of the equilibrium Markov
process**, under uniqueness of sequential equilibrium, for every measurable sequence-state
equilibrium and every invariant law of the shock history. -/
theorem isInvariant_stateLaw {μ : History Z → ProbabilityMeasure M.AState}
    (hμ : M.IsSeqStateEquilibrium μ) (hmeas : Measurable fun ξ : ShockPath Z => μ ξ.toHistory)
    {P : Measure (ShockPath Z)} (hP : ShockPath.IsInvariant M.aggProb P) :
    (stateLaw P μ).bind M.eqKernel = stateLaw P μ := by
  ext B hB
  rw [Measure.bind_apply hB (measurable_eqKernel hU).aemeasurable, stateLaw,
    lintegral_map (f := fun s => M.eqKernel s B)
      ((Measure.measurable_coe hB).comp (measurable_eqKernel hU)) (measurable_stateOf hmeas),
    ← stateLaw, ← stateLaw_tomorrow hmeas hP hB]
  refine lintegral_congr fun ξ => ?_
  rw [eqKernel_apply _ hB]
  refine Finset.sum_congr rfl fun z' _ => ?_
  simp only [stateOf]
  rw [hμ.eq_lawOfMotion hU ξ.toHistory z']
  rfl

include hU in
/-- **The invariant distribution is ergodic when the shock law is**: every set the equilibrium
process does not leave has probability `0` or `1`. -/
theorem ergodic_stateLaw {μ : History Z → ProbabilityMeasure M.AState}
    (hμ : M.IsSeqStateEquilibrium μ) (hmeas : Measurable fun ξ : ShockPath Z => μ ξ.toHistory)
    {P : Measure (ShockPath Z)}
    (hPerg : ∀ A, MeasurableSet A → (∀ᵐ ξ ∂P, ξ ∈ A → ShockPath.extMeasure M.aggProb ξ A = 1) →
      P A = 0 ∨ P A = 1)
    {B : Set (ShockVal Z × ProbabilityMeasure M.AState)} (hB : MeasurableSet B)
    (hinv : ∀ᵐ s ∂(stateLaw P μ), s ∈ B → M.eqKernel s B = 1) :
    stateLaw P μ B = 0 ∨ stateLaw P μ B = 1 := by
  have hφ := measurable_stateOf hmeas
  have hA : MeasurableSet (stateOf μ ⁻¹' B) := hφ hB
  rw [stateLaw, Measure.map_apply hφ hB]
  refine hPerg _ hA ?_
  have h := ae_of_ae_map hφ.aemeasurable hinv
  refine h.mono fun ξ hξ hmem => ?_
  rw [ShockPath.extMeasure_apply M.aggProb ξ hA, ← hξ hmem, eqKernel_apply _ hB]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [indicator_preimage_stateOf_cons, hμ.eq_lawOfMotion hU ξ.toHistory z']
  rfl

end KSModel

end KrusellSmith

end LeanEconomics
