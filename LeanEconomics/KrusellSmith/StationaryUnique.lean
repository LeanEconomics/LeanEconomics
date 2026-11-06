/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.SequenceStateContinuity

/-!
# The stationary distribution of the equilibrium is unique

Milestone SS4 of `STATIONARY_SEQUENCE_PLAN.md`. Under the contraction hypotheses of
`HistoryMarginals.lean`, the equilibrium Markov process on the aggregate state
`(z, ν) ↦ (z', lawOfMotion z ν z')` (`eqKernel`) has **at most one invariant distribution**, when
the aggregate chain has a unique stationary distribution.

**Test functions** (`DistLip C F`): `F (v, ν)` is bounded, measurable, and Lipschitz in `ν` for the
norm of the two-part distance, `|F (v, ν) − F (v, ν')| ≤ C (da + ω dm)` whenever
`Dist2 da dm ν ν'`.

**Proof.**
* Invariance: `∫ F dΛ = ∫ Qᵀ F dΛ` (`integral_qIter`), through `lintegral_bind` and the finite form
  of the kernel.
* Burn-in against an equilibrium (`abs_qIter_sub_eIter_le`): `Qᵀ F (v, ν)` is within
  `C r*ᵀ (da + ω dm)` of the same expectation along the sequence-state equilibrium `μ*`,
  `eIter T F ω`, for any history `ω` ending in `v` with `Dist2 da dm ν (μ* ω)`; any two
  distributions are within `(0, 1)`, so the error is at most `C r*ᵀ ω` whatever `ν`. Taking `ω`
  the constant history at `v`, `Qᵀ F (v, ν)` is within `C r*ᵀ ω` of a function of `v` alone.
* The shock marginal of an invariant distribution is `π`-stationary (`marginal_stationary`), hence
  the same for any two.
* So any two invariant distributions integrate every test function to within `2 C r*ᵀ ω`, for
  every `T`: they agree on test functions (`integral_eq_of_isInvariant`), and test functions
  separate measures (`distLipSubalgebra`, `separatesPoints`, Stone–Weierstrass on the Polish
  aggregate state space): **`eq_of_isInvariant`**.

**`minMPC_smallShare_unique_stationary`**: in the small-share CRRA economy, with both shock chains
bounded below, the law of the aggregate state of the unique sequence-state equilibrium is **the
unique** invariant distribution of the equilibrium Markov process, and it is ergodic.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction TopologicalSpace ProbabilityTheory
open scoped ENNReal NNReal

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

instance (M : KSModel Z E) : SecondCountableTopology (ProbabilityMeasure M.AState) := by
  let := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure M.AState)
  infer_instance

instance (M : KSModel Z E) : BorelSpace (ShockVal Z × ProbabilityMeasure M.AState) :=
  Prod.borelSpace

/-- The one-step expectation under the equilibrium kernel. -/
noncomputable def qStep (M : KSModel Z E) (F : ShockVal Z × ProbabilityMeasure M.AState → ℝ)
    (s : ShockVal Z × ProbabilityMeasure M.AState) : ℝ :=
  ∑ z', M.aggProb s.1.val z' * F ((⟨z'⟩ : ShockVal Z), M.lawOfMotion s.1.val s.2 z')

/-- The `T`-step expectation under the equilibrium kernel. -/
noncomputable def qIter (M : KSModel Z E) (F : ShockVal Z × ProbabilityMeasure M.AState → ℝ) :
    ℕ → ShockVal Z × ProbabilityMeasure M.AState → ℝ
  | 0 => F
  | T + 1 => M.qStep (M.qIter F T)

/-- The `T`-step expectation along a sequence-state equilibrium. -/
noncomputable def eIter (M : KSModel Z E) (μ : History Z → ProbabilityMeasure M.AState)
    (F : ShockVal Z × ProbabilityMeasure M.AState → ℝ) : ℕ → History Z → ℝ
  | 0 => fun ω => F ((⟨ω 0⟩ : ShockVal Z), μ ω)
  | T + 1 => fun ω => ∑ z', M.aggProb (ω 0) z' * M.eIter μ F T (History.cons z' ω)

variable (hU : M.UniqueSequentialEquilibrium)

include hU in
theorem measurable_qStep {F : ShockVal Z × ProbabilityMeasure M.AState → ℝ} (hF : Measurable F) :
    Measurable (M.qStep F) := by
  refine measurable_from_prod_countable_right fun v => ?_
  change Measurable fun y : ProbabilityMeasure M.AState =>
    ∑ z', M.aggProb v.val z' * F ((⟨z'⟩ : ShockVal Z), M.lawOfMotion v.val y z')
  refine Finset.measurable_sum _ fun z' _ => Measurable.const_mul ?_ _
  exact hF.comp (measurable_const.prodMk (M.continuous_lawOfMotion hU v.val z').measurable)

theorem abs_qStep_le {F : ShockVal Z × ProbabilityMeasure M.AState → ℝ} {c : ℝ}
    (hF : ∀ s, |F s| ≤ c) (s : ShockVal Z × ProbabilityMeasure M.AState) : |M.qStep F s| ≤ c := by
  calc |M.qStep F s| ≤ ∑ z', M.aggProb s.1.val z' * c := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z' _ => ?_)
        rw [abs_mul, abs_of_nonneg (M.aggProb_nonneg _ _)]
        exact mul_le_mul_of_nonneg_left (hF _) (M.aggProb_nonneg _ _)
    _ = c := by rw [← Finset.sum_mul, M.aggProb_sum, one_mul]

include hU in
theorem measurable_qIter {F : ShockVal Z × ProbabilityMeasure M.AState → ℝ} (hF : Measurable F) :
    ∀ T, Measurable (M.qIter F T)
  | 0 => hF
  | T + 1 => measurable_qStep hU (measurable_qIter hF T)

theorem abs_qIter_le {F : ShockVal Z × ProbabilityMeasure M.AState → ℝ} {c : ℝ}
    (hF : ∀ s, |F s| ≤ c) : ∀ T s, |M.qIter F T s| ≤ c
  | 0 => hF
  | T + 1 => abs_qStep_le (abs_qIter_le hF T)

/-- `Λ` is an **invariant distribution** of the equilibrium Markov process. -/
def IsEqInvariant (Λ : Measure (ShockVal Z × ProbabilityMeasure M.AState)) : Prop :=
  Λ.bind M.eqKernel = Λ

include hU in
/-- **Invariance against bounded measurable functions**: `∫ F dΛ = ∫ Q F dΛ`. -/
theorem IsEqInvariant.integral_qStep {Λ : Measure (ShockVal Z × ProbabilityMeasure M.AState)}
    [IsProbabilityMeasure Λ] (hΛ : M.IsEqInvariant Λ)
    {F : ShockVal Z × ProbabilityMeasure M.AState → ℝ} (hF : Measurable F) {c : ℝ}
    (hc : ∀ s, |F s| ≤ c) : ∫ s, F s ∂Λ = ∫ s, M.qStep F s ∂Λ := by
  set G : ShockVal Z × ProbabilityMeasure M.AState → ℝ := fun s => F s + c
  have hG0 : ∀ s, 0 ≤ G s := fun s => by
    have := (abs_le.1 (hc s)).1
    simp only [G]
    linarith
  have hGm : Measurable G := hF.add measurable_const
  have hQG : ∀ s, M.qStep G s = M.qStep F s + c := by
    intro s
    simp only [qStep, G, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, M.aggProb_sum, one_mul]
  have hQG0 : ∀ s, 0 ≤ M.qStep G s := fun s =>
    Finset.sum_nonneg fun z' _ => mul_nonneg (M.aggProb_nonneg _ _) (hG0 _)
  have hint : ∀ s, ∫⁻ x, ENNReal.ofReal (G x) ∂(M.eqKernel s)
      = ENNReal.ofReal (M.qStep G s) := by
    intro s
    rw [eqKernel, lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, smul_eq_mul]
    rw [qStep, ENNReal.ofReal_sum_of_nonneg fun z' _ => mul_nonneg (M.aggProb_nonneg _ _) (hG0 _)]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [lintegral_dirac' _ hGm.ennreal_ofReal, ENNReal.ofReal_mul (M.aggProb_nonneg _ _)]
  have key : ∫⁻ s, ENNReal.ofReal (G s) ∂Λ = ∫⁻ s, ENNReal.ofReal (M.qStep G s) ∂Λ := by
    conv_lhs => rw [← hΛ]
    rw [Measure.lintegral_bind (measurable_eqKernel hU).aemeasurable
      hGm.ennreal_ofReal.aemeasurable]
    exact lintegral_congr hint
  have hFi : Integrable F Λ :=
    Integrable.of_bound hF.aestronglyMeasurable c (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]; exact hc s)
  have hQFi : Integrable (M.qStep F) Λ :=
    Integrable.of_bound (measurable_qStep hU hF).aestronglyMeasurable c
      (Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact abs_qStep_le hc s)
  have e1 : ∫ s, G s ∂Λ = (∫⁻ s, ENNReal.ofReal (G s) ∂Λ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hG0) hGm.aestronglyMeasurable
  have e2 : ∫ s, M.qStep G s ∂Λ = (∫⁻ s, ENNReal.ofReal (M.qStep G s) ∂Λ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hQG0)
      (measurable_qStep hU hGm).aestronglyMeasurable
  have e3 : ∫ s, G s ∂Λ = ∫ s, F s ∂Λ + c := by
    rw [integral_add hFi (integrable_const c), integral_const, probReal_univ, one_smul]
  have e4 : ∫ s, M.qStep G s ∂Λ = ∫ s, M.qStep F s ∂Λ + c := by
    simp_rw [hQG]
    rw [integral_add hQFi (integrable_const c), integral_const, probReal_univ, one_smul]
  have := e1.trans (key ▸ e2.symm)
  linarith

include hU in
theorem IsEqInvariant.integral_qIter {Λ : Measure (ShockVal Z × ProbabilityMeasure M.AState)}
    [IsProbabilityMeasure Λ] (hΛ : M.IsEqInvariant Λ)
    {F : ShockVal Z × ProbabilityMeasure M.AState → ℝ} (hF : Measurable F) {c : ℝ}
    (hc : ∀ s, |F s| ≤ c) : ∀ T, ∫ s, F s ∂Λ = ∫ s, M.qIter F T s ∂Λ
  | 0 => rfl
  | T + 1 => (hΛ.integral_qIter hF hc T).trans
      (hΛ.integral_qStep hU (measurable_qIter hU hF T) (abs_qIter_le hc T))

/-- The shock marginal of a distribution on the aggregate state. -/
noncomputable def shockMarginal (Λ : Measure (ShockVal Z × ProbabilityMeasure M.AState)) (z : Z) :
    ℝ :=
  Λ.real (Prod.fst ⁻¹' {(⟨z⟩ : ShockVal Z)})

theorem measurableSet_fst_singleton (v : ShockVal Z) :
    MeasurableSet (Prod.fst ⁻¹' {v} : Set (ShockVal Z × ProbabilityMeasure M.AState)) :=
  measurable_fst (MeasurableSpace.measurableSet_top : MeasurableSet {v})

/-- **Integrating a function of today's shock** against its marginal. -/
theorem integral_fst (Λ : Measure (ShockVal Z × ProbabilityMeasure M.AState))
    [IsProbabilityMeasure Λ] (g : ShockVal Z → ℝ) :
    ∫ s, g s.1 ∂Λ = ∑ z, shockMarginal Λ z * g ⟨z⟩ := by
  have e : (fun s : ShockVal Z × ProbabilityMeasure M.AState => g s.1)
      = fun s => ∑ z, g ⟨z⟩ * (Prod.fst ⁻¹' {(⟨z⟩ : ShockVal Z)}).indicator
        (1 : ShockVal Z × ProbabilityMeasure M.AState → ℝ) s := by
    funext s
    rw [Finset.sum_eq_single s.1.val]
    · rw [Set.indicator_of_mem (show s ∈ Prod.fst ⁻¹' {(⟨s.1.val⟩ : ShockVal Z)} from rfl),
        Pi.one_apply, mul_one]
    · intro z _ hz
      rw [Set.indicator_of_notMem (fun h => hz (by
        rw [mem_preimage, mem_singleton_iff] at h; rw [h])), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e, integral_finsetSum _ fun z _ => ?_]
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [integral_const_mul, integral_indicator_one (measurableSet_fst_singleton _), mul_comm]
    rfl
  · exact ((integrable_const (1 : ℝ)).indicator (measurableSet_fst_singleton _)).const_mul _

include hU in
/-- **The shock marginal of an invariant distribution is `π`-stationary.** -/
theorem IsEqInvariant.marginal_stationary
    {Λ : Measure (ShockVal Z × ProbabilityMeasure M.AState)} [IsProbabilityMeasure Λ]
    (hΛ : M.IsEqInvariant Λ) (z' : Z) :
    ∑ z, shockMarginal Λ z * M.aggProb z z' = shockMarginal Λ z' := by
  set F : ShockVal Z × ProbabilityMeasure M.AState → ℝ :=
    (Prod.fst ⁻¹' {(⟨z'⟩ : ShockVal Z)}).indicator 1
  have hFm : Measurable F := measurable_one.indicator (measurableSet_fst_singleton _)
  have hFc : ∀ s, |F s| ≤ 1 := fun s => by
    simp only [F, Set.indicator, Pi.one_apply]
    split_ifs <;> simp
  have h := hΛ.integral_qStep hU hFm hFc
  have hL : ∫ s, F s ∂Λ = shockMarginal Λ z' := by
    rw [integral_indicator_one (measurableSet_fst_singleton _)]
    rfl
  have hQ : M.qStep F = fun s => M.aggProb s.1.val z' := by
    funext s
    rw [qStep, Finset.sum_eq_single z']
    · simp only [F]
      rw [Set.indicator_of_mem (show ((⟨z'⟩ : ShockVal Z), M.lawOfMotion s.1.val s.2 z')
        ∈ Prod.fst ⁻¹' {(⟨z'⟩ : ShockVal Z)} from rfl), Pi.one_apply, mul_one]
    · intro z _ hz
      simp only [F]
      rw [Set.indicator_of_notMem (fun h => hz (by
        rw [mem_preimage, mem_singleton_iff] at h; exact congrArg ShockVal.val h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hQ, integral_fst Λ (fun v => M.aggProb v.val z')] at h
  rw [← h, hL]

/-! ### Test functions -/

namespace SlopeContraction

variable {ε : ℝ} (hminor : ∀ z z' e e', ε ≤ M.idioProb z z' e e') (S : M.SlopeContraction)
  {ℓL : ℝ} (hℓL : 0 ≤ ℓL)
  (hRL : ∀ z k L L', |M.grossReturn z k L - M.grossReturn z k L'| ≤ ℓL * |L - L'|)
  (hwL : ∀ z k L L', |M.wage z k L - M.wage z k L'| ≤ ℓL * |L - L'|)
  (hε : 0 < ε) (hκ : S.κ < 1) (hr : S.rate < 1)

/-- **Test functions**: Lipschitz in the distribution for the norm `da + ω dm` of the two-part
distance. -/
def DistLip (ℓL ε C : ℝ) (F : ShockVal Z × ProbabilityMeasure M.AState → ℝ) : Prop :=
  ∀ (v : ShockVal Z) (ν ν' : ProbabilityMeasure M.AState) (da dm : ℝ), 0 ≤ da → 0 ≤ dm →
    Dist2 da dm (ν : Measure M.AState) ν' →
      |F (v, ν) - F (v, ν')| ≤ C * (da + S.histWeight ℓL ε * dm)

variable {μ : History Z → ProbabilityMeasure M.AState} (hμ : M.IsSeqStateEquilibrium μ)

include hminor hℓL hRL hwL hε hκ hμ in
/-- **Burn-in against the equilibrium**: `Qᵀ F (v, ν)` is within `C r*ᵀ (da + ω dm)` of the
expectation along the equilibrium from any history ending in `v` whose distribution is within
`(da, dm)` of `ν`. -/
theorem abs_qIter_sub_eIter_le [Nonempty E] {C : ℝ} (hC : 0 ≤ C)
    {F : ShockVal Z × ProbabilityMeasure M.AState → ℝ} (hF : S.DistLip ℓL ε C F) :
    ∀ (T : ℕ) (ω : History Z) (ν : ProbabilityMeasure M.AState) (da dm : ℝ), 0 ≤ da → 0 ≤ dm →
      Dist2 da dm (ν : Measure M.AState) (μ ω) →
      |M.qIter F T ((⟨ω 0⟩ : ShockVal Z), ν) - M.eIter μ F T ω|
        ≤ C * (S.histRate ε ^ T * (da + S.histWeight ℓL ε * dm))
  | 0, ω, ν, da, dm, hda, hdm, hd => by
    rw [pow_zero, one_mul]
    exact hF _ ν (μ ω) da dm hda hdm hd
  | T + 1, ω, ν, da, dm, hda, hdm, hd => by
    have hU := S.uniqueSequentialEquilibrium hκ
    have hr0 : 0 ≤ S.histRate ε := (S.rate_nonneg hκ).trans (le_max_left _ _)
    have hterm : ∀ z', |M.qIter F T ((⟨z'⟩ : ShockVal Z), M.lawOfMotion (ω 0) ν z')
        - M.eIter μ F T (History.cons z' ω)|
        ≤ C * (S.histRate ε ^ (T + 1) * (da + S.histWeight ℓL ε * dm)) := by
      intro z'
      have hD := S.dist2_lawOfMotion hminor hℓL hRL hwL hε hκ hda hdm hd (z := ω 0) z'
      have heq : μ (History.cons z' ω) = M.lawOfMotion (ω 0) (μ ω) z' := hμ.eq_lawOfMotion hU ω z'
      rw [← heq] at hD
      have hda' : 0 ≤ S.θ * da + M.assetCap * dm
          + S.B.G₁ * ((S.B.ℓ * da + S.labourGap ℓL * dm) / (1 - S.κ)) :=
        add_nonneg (add_nonneg (mul_nonneg S.θ_nonneg hda) (mul_nonneg M.assetCap_pos.le hdm))
          (mul_nonneg S.B.G₁_nonneg (div_nonneg (add_nonneg (mul_nonneg S.B.ℓ_nonneg hda)
            (mul_nonneg (S.labourGap_nonneg hℓL) hdm)) (sub_pos.2 hκ).le))
      have hdm' := mul_nonneg (mix_nonneg hminor (ω 0)) hdm
      have ih := abs_qIter_sub_eIter_le hC hF T (History.cons z' ω) _ _ _ hda' hdm' hD
      have hstep := S.norm_step hminor hℓL hε hκ hda hdm (ω 0)
      refine ih.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hC
      calc _ ≤ S.histRate ε ^ T * (S.histRate ε * (da + S.histWeight ℓL ε * dm)) :=
            mul_le_mul_of_nonneg_left hstep (pow_nonneg hr0 T)
        _ = _ := by ring
    change |∑ z', M.aggProb (ω 0) z' * M.qIter F T ((⟨z'⟩ : ShockVal Z), M.lawOfMotion (ω 0) ν z')
        - ∑ z', M.aggProb (ω 0) z' * M.eIter μ F T (History.cons z' ω)| ≤ _
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ z', M.aggProb (ω 0) z'
          * (C * (S.histRate ε ^ (T + 1) * (da + S.histWeight ℓL ε * dm))) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z' _ => ?_)
          rw [← mul_sub, abs_mul, abs_of_nonneg (M.aggProb_nonneg _ _)]
          exact mul_le_mul_of_nonneg_left (hterm z') (M.aggProb_nonneg _ _)
      _ = _ := by rw [← Finset.sum_mul, M.aggProb_sum, one_mul]

include hminor hℓL hRL hwL hε hκ hr hμ in
/-- **Two invariant distributions agree on test functions**, when the aggregate chain has a unique
stationary distribution. -/
theorem integral_eq_of_isInvariant [Nonempty E]
    (huniq : ∀ q q' : Z → ℝ, (∀ z, 0 ≤ q z) → ∑ z, q z = 1 →
      (∀ z', ∑ z, q z * M.aggProb z z' = q z') → (∀ z, 0 ≤ q' z) → ∑ z, q' z = 1 →
      (∀ z', ∑ z, q' z * M.aggProb z z' = q' z') → q = q')
    {Λ₁ Λ₂ : Measure (ShockVal Z × ProbabilityMeasure M.AState)} [IsProbabilityMeasure Λ₁]
    [IsProbabilityMeasure Λ₂] (h₁ : M.IsEqInvariant Λ₁) (h₂ : M.IsEqInvariant Λ₂)
    {C c : ℝ} (hC : 0 ≤ C) {F : ShockVal Z × ProbabilityMeasure M.AState → ℝ}
    (hFm : Measurable F) (hFc : ∀ s, |F s| ≤ c) (hF : S.DistLip ℓL ε C F) :
    ∫ s, F s ∂Λ₁ = ∫ s, F s ∂Λ₂ := by
  have hU := S.uniqueSequentialEquilibrium hκ
  set w := S.histWeight ℓL ε
  set r := S.histRate ε
  have hr0 : 0 ≤ r := (S.rate_nonneg hκ).trans (le_max_left _ _)
  have hr1 : r < 1 := S.histRate_lt_one hε hr
  -- the comparator: a function of today's shock
  set g : ℕ → ShockVal Z → ℝ := fun T v => M.eIter μ F T (fun _ => v.val)
  have hclose : ∀ T s, |M.qIter F T s - g T s.1| ≤ C * (r ^ T * w) := by
    intro T s
    have := S.abs_qIter_sub_eIter_le hminor hℓL hRL hwL hε hκ hμ hC hF T (fun _ => s.1.val) s.2
      0 1 le_rfl zero_le_one (dist2_zero_one _ _)
    simpa [g] using this
  have hint : ∀ (Λ : Measure (ShockVal Z × ProbabilityMeasure M.AState)) [IsProbabilityMeasure Λ],
      ∀ T, |∫ s, M.qIter F T s ∂Λ - ∑ z, shockMarginal Λ z * g T ⟨z⟩| ≤ C * (r ^ T * w) := by
    intro Λ _ T
    have hset : ∀ v : ShockVal Z, MeasurableSet (Prod.fst ⁻¹' {v} :
        Set (ShockVal Z × ProbabilityMeasure M.AState)) :=
      fun v => measurable_fst (MeasurableSpace.measurableSet_top : MeasurableSet {v})
    have hg : ∫ s, g T s.1 ∂Λ = ∑ z, shockMarginal Λ z * g T ⟨z⟩ := integral_fst Λ (g T)
    have hgm : Measurable fun s : ShockVal Z × ProbabilityMeasure M.AState => g T s.1 :=
      (measurable_of_countable (fun v : ShockVal Z => g T v)).comp measurable_fst
    have hqi : Integrable (M.qIter F T) Λ :=
      Integrable.of_bound (measurable_qIter hU hFm T).aestronglyMeasurable c
        (Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact abs_qIter_le hFc T s)
    have hgi : Integrable (fun s : ShockVal Z × ProbabilityMeasure M.AState => g T s.1) Λ := by
      refine Integrable.of_bound hgm.aestronglyMeasurable (∑ z, |g T ⟨z⟩|)
        (Eventually.of_forall fun s => ?_)
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun z => |g T ⟨z⟩|) (fun z _ => abs_nonneg _)
        (Finset.mem_univ s.1.val)
    rw [← hg, ← integral_sub hqi hgi]
    have := norm_integral_le_of_norm_le_const (μ := Λ)
      (f := fun s => M.qIter F T s - g T s.1) (Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs]; exact hclose T s)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  -- the shock marginals agree
  have hm : shockMarginal Λ₁ = shockMarginal Λ₂ := by
    have hsum : ∀ (Λ : Measure (ShockVal Z × ProbabilityMeasure M.AState))
        [IsProbabilityMeasure Λ], ∑ z, shockMarginal Λ z = 1 := by
      intro Λ _
      have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset Z) : Set Z)
          fun z => (Prod.fst ⁻¹' {(⟨z⟩ : ShockVal Z)} :
            Set (ShockVal Z × ProbabilityMeasure M.AState)) := by
        intro z _ z' _ hzz'
        refine Set.disjoint_left.2 fun s h h' => hzz' ?_
        rw [mem_preimage, mem_singleton_iff] at h h'
        exact congrArg ShockVal.val (h.symm.trans h')
      have hU' : (⋃ z ∈ (Finset.univ : Finset Z),
          (Prod.fst ⁻¹' {(⟨z⟩ : ShockVal Z)} : Set (ShockVal Z × ProbabilityMeasure M.AState)))
          = univ := by
        ext s
        simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_preimage, mem_singleton_iff,
          mem_univ, iff_true]
        exact ⟨s.1.val, rfl⟩
      have := measureReal_biUnion_finset (μ := Λ) hdisj fun z _ =>
        measurable_fst (MeasurableSpace.measurableSet_top : MeasurableSet {(⟨z⟩ : ShockVal Z)})
      rw [hU', probReal_univ] at this
      exact this.symm
    exact huniq _ _ (fun z => measureReal_nonneg) (hsum Λ₁) (h₁.marginal_stationary hU)
      (fun z => measureReal_nonneg) (hsum Λ₂) (h₂.marginal_stationary hU)
  -- conclude
  have hbound : ∀ T, |∫ s, F s ∂Λ₁ - ∫ s, F s ∂Λ₂| ≤ 2 * (C * (r ^ T * w)) := by
    intro T
    rw [h₁.integral_qIter hU hFm hFc T, h₂.integral_qIter hU hFm hFc T]
    have a := hint Λ₁ T
    have b := hint Λ₂ T
    rw [hm] at a
    calc _ ≤ |∫ s, M.qIter F T s ∂Λ₁ - ∑ z, shockMarginal Λ₂ z * g T ⟨z⟩|
          + |∫ s, M.qIter F T s ∂Λ₂ - ∑ z, shockMarginal Λ₂ z * g T ⟨z⟩| := by
          rw [abs_sub_comm (∫ s, M.qIter F T s ∂Λ₂)]
          exact abs_sub_le _ _ _
      _ ≤ _ := by linarith
  have hlim : Tendsto (fun T : ℕ => 2 * (C * (r ^ T * w))) atTop (𝓝 (2 * (C * (0 * w)))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul tendsto_const_nhds))
  rw [zero_mul, mul_zero, mul_zero] at hlim
  have h0 := ge_of_tendsto' hlim hbound
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-! ### Test functions separate distributions -/

include hκ hε in
theorem one_le_histWeight [Nonempty E] (hℓL : 0 ≤ ℓL) : 1 ≤ S.histWeight ℓL ε := by
  have hJ := S.histJ_nonneg hℓL hκ
  have h1c : 0 < 1 - (1 - Fintype.card E * ε) := by
    have := mix_lt_one (E := E) hε
    linarith
  have : 0 ≤ 2 * S.histJ ℓL / (1 - (1 - Fintype.card E * ε)) := by positivity
  simp only [histWeight]
  linarith

/-- **Bounded continuous test functions**, as a subalgebra. -/
noncomputable def distLipSubalgebra (ℓL ε : ℝ) :
    StarSubalgebra ℝ ((ShockVal Z × ProbabilityMeasure M.AState) →ᵇ ℝ) where
  carrier := {F | ∃ C, 0 ≤ C ∧ S.DistLip ℓL ε C F}
  mul_mem' := by
    rintro F G ⟨C, hC, hF⟩ ⟨C', hC', hG⟩
    refine ⟨‖F‖ * C' + ‖G‖ * C, add_nonneg (mul_nonneg (norm_nonneg _) hC')
      (mul_nonneg (norm_nonneg _) hC), fun v ν ν' da dm hda hdm hd => ?_⟩
    change |F (v, ν) * G (v, ν) - F (v, ν') * G (v, ν')| ≤ _
    have e : F (v, ν) * G (v, ν) - F (v, ν') * G (v, ν')
        = F (v, ν) * (G (v, ν) - G (v, ν')) + G (v, ν') * (F (v, ν) - F (v, ν')) := by ring
    rw [e]
    have h1 : |F (v, ν)| ≤ ‖F‖ := by rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm _
    have h2 : |G (v, ν')| ≤ ‖G‖ := by rw [← Real.norm_eq_abs]; exact G.norm_coe_le_norm _
    calc _ ≤ |F (v, ν)| * |G (v, ν) - G (v, ν')| + |G (v, ν')| * |F (v, ν) - F (v, ν')| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ ‖F‖ * (C' * (da + S.histWeight ℓL ε * dm)) + ‖G‖ * (C * (da + S.histWeight ℓL ε * dm)) :=
          add_le_add (mul_le_mul h1 (hG v ν ν' da dm hda hdm hd) (abs_nonneg _) (norm_nonneg _))
            (mul_le_mul h2 (hF v ν ν' da dm hda hdm hd) (abs_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  add_mem' := by
    rintro F G ⟨C, hC, hF⟩ ⟨C', hC', hG⟩
    refine ⟨C + C', add_nonneg hC hC', fun v ν ν' da dm hda hdm hd => ?_⟩
    change |(F (v, ν) + G (v, ν)) - (F (v, ν') + G (v, ν'))| ≤ _
    have e : (F (v, ν) + G (v, ν)) - (F (v, ν') + G (v, ν'))
        = (F (v, ν) - F (v, ν')) + (G (v, ν) - G (v, ν')) := by ring
    rw [e, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hF v ν ν' da dm hda hdm hd)
      (hG v ν ν' da dm hda hdm hd))
  algebraMap_mem' := by
    intro a
    refine ⟨0, le_rfl, fun v ν ν' da dm _ _ _ => ?_⟩
    change |a - a| ≤ _
    simp
  star_mem' := by
    intro F hF
    have : star F = F := by
      ext x
      simp
    rw [this]
    exact hF

include hκ hε hℓL in
theorem distLipSubalgebra_separatesPoints [Nonempty E] :
    ((S.distLipSubalgebra ℓL ε).map (toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  have mem : ∀ F : (ShockVal Z × ProbabilityMeasure M.AState) →ᵇ ℝ,
      F ∈ S.distLipSubalgebra ℓL ε →
      (F : ShockVal Z × ProbabilityMeasure M.AState → ℝ) ∈
        ((fun g : C(ShockVal Z × ProbabilityMeasure M.AState, ℝ) => (g : _ → ℝ)) ''
          (((S.distLipSubalgebra ℓL ε).map (toContinuousMapStarₐ ℝ)) :
            Set C(ShockVal Z × ProbabilityMeasure M.AState, ℝ))) :=
    fun F hF => ⟨toContinuousMapStarₐ ℝ F, ⟨F, hF, rfl⟩, rfl⟩
  have hw1 := S.one_le_histWeight hε hκ hℓL
  by_cases hv : x.1 = y.1
  · -- different distributions: an asset-Lipschitz test function tells them apart
    have hν : x.2 ≠ y.2 := fun h => hxy (Prod.ext hv h)
    have hne : (x.2 : Measure M.AState) ≠ y.2 := fun h => hν (Subtype.ext h)
    obtain ⟨L, hL, f, hf, hfne⟩ : ∃ L, 0 ≤ L ∧ ∃ f : M.AState →ᵇ ℝ, AssetLip L f ∧
        ∫ a, f a ∂(x.2 : Measure M.AState) ≠ ∫ a, f a ∂(y.2 : Measure M.AState) := by
      by_contra hc
      push Not at hc
      exact hne (eq_of_forall_assetLip fun L hL f hf => hc L hL f hf)
    set F : (ShockVal Z × ProbabilityMeasure M.AState) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfBound
        ⟨fun s => ∫ a, f a ∂(s.2 : Measure M.AState),
          (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp continuous_snd⟩
        (2 * ‖f‖) fun s t => by
          change dist (∫ a, f a ∂(s.2 : Measure M.AState)) (∫ a, f a ∂(t.2 : Measure M.AState)) ≤ _
          rw [Real.dist_eq]
          have hs := norm_integral_le_of_norm_le_const (μ := (s.2 : Measure M.AState))
            (Eventually.of_forall fun a => f.norm_coe_le_norm a)
          have ht := norm_integral_le_of_norm_le_const (μ := (t.2 : Measure M.AState))
            (Eventually.of_forall fun a => f.norm_coe_le_norm a)
          rw [probReal_univ, mul_one, Real.norm_eq_abs] at hs ht
          calc _ ≤ |∫ a, f a ∂(s.2 : Measure M.AState)| + |∫ a, f a ∂(t.2 : Measure M.AState)| :=
                abs_sub _ _
            _ ≤ _ := by linarith
    have hFmem : F ∈ S.distLipSubalgebra ℓL ε := by
      refine ⟨L + 2 * ‖f‖, add_nonneg hL (mul_nonneg zero_le_two (norm_nonneg f)),
        fun v ν ν' da dm hda hdm hd => ?_⟩
      change |∫ a, f a ∂(ν : Measure M.AState) - ∫ a, f a ∂(ν' : Measure M.AState)| ≤ _
      have hosc : ∀ a b, f a - f b ≤ 2 * ‖f‖ := fun a b => by
        have h1 := f.norm_coe_le_norm a
        have h2 := f.norm_coe_le_norm b
        rw [Real.norm_eq_abs] at h1 h2
        linarith [(abs_le.1 h1).2, (abs_le.1 h2).1]
      refine (hd L (2 * ‖f‖) hL f hf hosc).trans ?_
      have hf0 := norm_nonneg f
      have h3 : 2 * ‖f‖ * dm ≤ 2 * ‖f‖ * (S.histWeight ℓL ε * dm) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hdm hw1) (by positivity)
      have h4 : 0 ≤ L * (S.histWeight ℓL ε * dm) :=
        mul_nonneg hL (mul_nonneg (zero_le_one.trans hw1) hdm)
      have h5 : 0 ≤ 2 * ‖f‖ * da := mul_nonneg (by positivity) hda
      have e : (L + 2 * ‖f‖) * (da + S.histWeight ℓL ε * dm)
          = L * da + L * (S.histWeight ℓL ε * dm) + 2 * ‖f‖ * da
            + 2 * ‖f‖ * (S.histWeight ℓL ε * dm) := by ring
      rw [e]
      linarith
    exact ⟨_, mem F hFmem, hfne⟩
  · -- different shocks: the indicator of today's shock
    set F : (ShockVal Z × ProbabilityMeasure M.AState) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfBound
        ⟨(Prod.fst ⁻¹' {x.1}).indicator 1,
          (continuous_of_discreteTopology (f := ({x.1} : Set (ShockVal Z)).indicator
            (1 : ShockVal Z → ℝ))).comp continuous_fst⟩ 1 fun s t => by
          change dist ((Prod.fst ⁻¹' {x.1}).indicator
              (1 : ShockVal Z × ProbabilityMeasure M.AState → ℝ) s)
            ((Prod.fst ⁻¹' {x.1}).indicator
              (1 : ShockVal Z × ProbabilityMeasure M.AState → ℝ) t) ≤ 1
          simp only [Set.indicator, mem_preimage, mem_singleton_iff, Pi.one_apply]
          split_ifs <;> simp
    have hFmem : F ∈ S.distLipSubalgebra ℓL ε := by
      refine ⟨0, le_rfl, fun v ν ν' da dm _ _ _ => ?_⟩
      change |(Prod.fst ⁻¹' {x.1}).indicator
          (1 : ShockVal Z × ProbabilityMeasure M.AState → ℝ) (v, ν)
        - (Prod.fst ⁻¹' {x.1}).indicator
          (1 : ShockVal Z × ProbabilityMeasure M.AState → ℝ) (v, ν')| ≤ _
      have heq : (Prod.fst ⁻¹' {x.1}).indicator
            (1 : ShockVal Z × ProbabilityMeasure M.AState → ℝ) (v, ν)
          = (Prod.fst ⁻¹' {x.1}).indicator
            (1 : ShockVal Z × ProbabilityMeasure M.AState → ℝ) (v, ν') := by
        by_cases hvx : v = x.1
        · rw [Set.indicator_of_mem (show (v, ν) ∈ Prod.fst ⁻¹' {x.1} from hvx),
            Set.indicator_of_mem (show (v, ν') ∈ Prod.fst ⁻¹' {x.1} from hvx)]
          rfl
        · rw [Set.indicator_of_notMem (show (v, ν) ∉ Prod.fst ⁻¹' {x.1} from hvx),
            Set.indicator_of_notMem (show (v, ν') ∉ Prod.fst ⁻¹' {x.1} from hvx)]
      rw [heq, sub_self, abs_zero, zero_mul]
    refine ⟨_, mem F hFmem, ?_⟩
    change (Prod.fst ⁻¹' {x.1}).indicator (1 : ShockVal Z × ProbabilityMeasure M.AState → ℝ) x
      ≠ (Prod.fst ⁻¹' {x.1}).indicator (1 : ShockVal Z × ProbabilityMeasure M.AState → ℝ) y
    rw [Set.indicator_of_mem (show x ∈ Prod.fst ⁻¹' {x.1} from rfl),
      Set.indicator_of_notMem (show y ∉ Prod.fst ⁻¹' {x.1} from fun h => hv (h.symm))]
    exact one_ne_zero

include hminor hℓL hRL hwL hε hκ hr hμ in
/-- **The invariant distribution of the equilibrium Markov process is unique**, when the aggregate
chain has a unique stationary distribution. -/
theorem eq_of_isInvariant [Nonempty E]
    (huniq : ∀ q q' : Z → ℝ, (∀ z, 0 ≤ q z) → ∑ z, q z = 1 →
      (∀ z', ∑ z, q z * M.aggProb z z' = q z') → (∀ z, 0 ≤ q' z) → ∑ z, q' z = 1 →
      (∀ z', ∑ z, q' z * M.aggProb z z' = q' z') → q = q')
    {Λ₁ Λ₂ : Measure (ShockVal Z × ProbabilityMeasure M.AState)} [IsProbabilityMeasure Λ₁]
    [IsProbabilityMeasure Λ₂] (h₁ : M.IsEqInvariant Λ₁) (h₂ : M.IsEqInvariant Λ₂) :
    Λ₁ = Λ₂ := by
  refine ext_of_forall_mem_subalgebra_integral_eq_of_polish
    (S.distLipSubalgebra_separatesPoints hℓL hε hκ) fun F ⟨C, hC, hF⟩ => ?_
  exact S.integral_eq_of_isInvariant hminor hℓL hRL hwL hε hκ hr hμ huniq h₁ h₂ hC
    F.continuous.measurable (fun s => by rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm s) hF

end SlopeContraction

end KSModel

/-! ### The small-share economy -/

variable [Nonempty Z] [Nonempty E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ}
  (hγ : 0 < γ) {ε εZ : ℝ} (hε : 0 < ε) (hminor : ∀ z z' e e', ε ≤ V.idioProb z z' e e')
  (hεZ : 0 < εZ) (hminorZ : ∀ z z', εZ ≤ V.aggProb z z')
include hε hminor hεZ hminorZ

/-- **The unique stationary distribution of the equilibrium**: for CRRA, clamped Cobb–Douglas with
`0 ≤ δ < 1` and `(β (1 − δ))^{1/γ} < 1 − δ`, both shock chains bounded below and small capital
shares, there is a unique sequence-state equilibrium, continuous in the history; the law of its
aggregate state under the (unique, ergodic) stationary law of the shock history is invariant and
ergodic for the equilibrium Markov process, and **every invariant distribution of that process is
this one**. -/
theorem minMPC_smallShare_unique_stationary (hδ1 : T.depreciation < 1)
    (hgap : (V.discount * (1 - T.depreciation)) ^ (1 / γ) < 1 - T.depreciation) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃ μ : History Z → ProbabilityMeasure (crraModel V (T.withShare α h0 hα) hγ).AState,
        (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ ∧
        (∀ μ', (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ' → μ' = μ) ∧
        Continuous (fun ξ : ShockPath Z => μ ξ.toHistory) ∧
        ∃ P : ProbabilityMeasure (ShockPath Z),
          ShockPath.IsInvariant V.aggProb (P : Measure (ShockPath Z)) ∧
          (crraModel V (T.withShare α h0 hα) hγ).IsEqInvariant
            (KSModel.stateLaw (P : Measure (ShockPath Z)) μ) ∧
          (∀ B, MeasurableSet B →
            (∀ᵐ s ∂(KSModel.stateLaw (P : Measure (ShockPath Z)) μ),
              s ∈ B → (crraModel V (T.withShare α h0 hα) hγ).eqKernel s B = 1) →
            KSModel.stateLaw (P : Measure (ShockPath Z)) μ B = 0 ∨
              KSModel.stateLaw (P : Measure (ShockPath Z)) μ B = 1) ∧
          ∀ (Λ : Measure (ShockVal Z × ProbabilityMeasure
              (crraModel V (T.withShare α h0 hα) hγ).AState)) [IsProbabilityMeasure Λ],
            (crraModel V (T.withShare α h0 hα) hγ).IsEqInvariant Λ →
            Λ = KSModel.stateLaw (P : Measure (ShockPath Z)) μ := by
  obtain ⟨α₀, hα₀, h⟩ := minMPC_smallShare V T hγ hδ1 hgap
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, S, hκ, hr⟩ := h α h0 hα
  refine ⟨h1, ?_⟩
  have hminor' : ∀ z z' e e', ε ≤ (crraModel V (T.withShare α h0 h1) hγ).idioProb z z' e e' :=
    hminor
  have hℓL := (T.withShare α h0 h1).labLip_nonneg
  have hRL := (T.withShare α h0 h1).abs_grossReturn_sub_le_lab
  have hwL := (T.withShare α h0 h1).abs_wage_sub_le_lab
  have hU := S.uniqueSequentialEquilibrium hκ
  obtain ⟨μ, hμ⟩ := (crraModel V (T.withShare α h0 h1) hγ).exists_seqStateEquilibrium
  have hc := S.continuous_seqState hminor' hℓL hRL hwL hε hκ hr hμ
  obtain ⟨P, hP, herg⟩ := ShockPath.exists_invariant_ergodic V.aggProb V.aggProb_nonneg
    V.aggProb_sum
  have huniq := ShockPath.stationary_unique_of_minor V.aggProb_sum hεZ hminorZ
  have hinvΛ : (crraModel V (T.withShare α h0 h1) hγ).IsEqInvariant
      (KSModel.stateLaw (P : Measure (ShockPath Z)) μ) :=
    KSModel.isInvariant_stateLaw hU hμ hc.measurable hP
  have : IsProbabilityMeasure (KSModel.stateLaw (P : Measure (ShockPath Z)) μ) :=
    (Measure.isProbabilityMeasure_map_iff
      (KSModel.measurable_stateOf hc.measurable).aemeasurable).2 inferInstance
  refine ⟨μ, hμ, fun μ' hμ' => S.eq_of_rate_lt_one hκ hμ' hr hμ
      (hμ'.initMass_eq_of_minor hμ hε hminor'), hc, P, hP, hinvΛ,
    fun B hB hinv => KSModel.ergodic_stateLaw hU hμ hc.measurable herg hB hinv, ?_⟩
  intro Λ _ hΛ
  exact S.eq_of_isInvariant hminor' hℓL hRL hwL hε hκ hr hμ huniq hΛ hinvΛ

end KrusellSmith

end LeanEconomics
