/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.AggregateStateRecursive

/-!
# The stationary distribution on `(z, K)`

Milestone AK3 of `AGGREGATE_STATE_PLAN.md`. Under `KSufficient`, capital evolves by
`lawK z K z'` on the capital sets (`AggregateState.lean`). Here:

* `lawKm`: `lawK` on the capital sets, `0` off them — **measurable** (continuous on the closed
  capital sets); `aggKernel (z, K) = Σ_{z'} π z z' δ_{(z', lawKm z K z')}`, the Markov kernel of
  `(z, K)`; `Kgraph = {(z, K) : K ∈ Kset z}`, where it lives;
* `capMap (z, ν) = (z, ∫ a dν)`; `aggLaw P μ`, the law of `(z, K)`: the push-forward of the law of
  the aggregate state `stateLaw P μ`; `aggKernel_capMap`: on the ergodic set, one step of
  `(z, K)` is the image of one step of `(z, ν)`;
* **`isInvariant_aggLaw`**: `aggLaw P μ` is invariant for `aggKernel`; **`ergodic_aggLaw`**: it is
  ergodic when the shock law is; `aggLaw_Kgraph`: it lives on `Kgraph`.
* **Uniqueness** (small-share contraction, `SlopeContraction`): `kIter F T (z, K)`, the
  `T`-step expectation, is the expectation along the sequence-state equilibrium from any history
  with shock `z` and capital `K` (`kIter_eq_eIterK`); capital forgets old shocks
  (`abs_capAt_sub_le`, from `dist2_of_agree`), and a bounded continuous test function is uniformly
  continuous on the compact capital sets, so `kIter F T` is within any `η` of a function of today's
  shock alone for `T` large (`abs_eIterK_sub_le`). Shock marginals of invariant laws are
  `π`-stationary; so **two invariant laws living on `Kgraph` agree** on every bounded continuous
  function (`integral_eq_of_isAggInvariant`), hence are equal (`eq_of_isAggInvariant`).
  No Lipschitz test functions and no measurable selection of distributions are needed.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction TopologicalSpace ProbabilityTheory
open scoped ENNReal NNReal

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} {μ : History Z → ProbabilityMeasure M.AState}

/-! ### The Markov kernel of `(z, K)` -/

open Classical in
/-- **The law of motion of capital, made measurable**: `lawK` on the capital sets, `0` off them. -/
noncomputable def lawKm (μ : History Z → ProbabilityMeasure M.AState) (z : Z) (k : ℝ) (z' : Z) :
    ℝ :=
  if k ∈ Kset μ z then lawK μ z k z' else 0

theorem lawKm_of_mem {z : Z} {k : ℝ} (hk : k ∈ Kset μ z) (z' : Z) :
    lawKm μ z k z' = lawK μ z k z' := by
  simp [lawKm, hk]

theorem measurable_lawKm (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) (z z' : Z) :
    Measurable fun k => lawKm μ z k z' := by
  classical
  have e : (fun k => lawKm μ z k z')
      = (Kset μ z).piecewise (fun k => lawK μ z k z') (fun _ => 0) := by
    funext k
    by_cases hk : k ∈ Kset μ z
    · rw [Set.piecewise_eq_of_mem _ _ _ hk, lawKm_of_mem hk]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hk]
      simp [lawKm, hk]
  rw [e]
  exact ContinuousOn.measurable_piecewise (continuousOn_lawK hS hc z z') continuousOn_const
    (isCompact_Kset hc z).isClosed.measurableSet

/-- **The Markov kernel of `(z, K)`.** -/
noncomputable def aggKernel (μ : History Z → ProbabilityMeasure M.AState) (s : ShockVal Z × ℝ) :
    Measure (ShockVal Z × ℝ) :=
  ∑ z', ENNReal.ofReal (M.aggProb s.1.val z')
    • Measure.dirac ((⟨z'⟩ : ShockVal Z), lawKm μ s.1.val s.2 z')

theorem aggKernel_apply (s : ShockVal Z × ℝ) {B : Set (ShockVal Z × ℝ)} (hB : MeasurableSet B) :
    aggKernel μ s B = ∑ z', ENNReal.ofReal (M.aggProb s.1.val z')
      * B.indicator 1 ((⟨z'⟩ : ShockVal Z), lawKm μ s.1.val s.2 z') := by
  simp only [aggKernel, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hB, smul_eq_mul]

theorem measurable_aggKernel (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) : Measurable (aggKernel μ) := by
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have e : (fun s => aggKernel μ s B) = fun s : ShockVal Z × ℝ =>
      ∑ z', ENNReal.ofReal (M.aggProb s.1.val z')
        * B.indicator 1 ((⟨z'⟩ : ShockVal Z), lawKm μ s.1.val s.2 z') :=
    funext fun s => aggKernel_apply s hB
  rw [e]
  refine measurable_from_prod_countable_right fun v => ?_
  refine Finset.measurable_sum _ fun z' _ => ?_
  change Measurable fun y : ℝ => ENNReal.ofReal (M.aggProb v.val z')
    * B.indicator 1 ((⟨z'⟩ : ShockVal Z), lawKm μ v.val y z')
  refine Measurable.const_mul ?_ _
  exact (measurable_one.indicator hB).comp
    (measurable_const.prodMk (measurable_lawKm hS hc v.val z'))

/-- **The graph of the capital sets**, where `(z, K)` lives. -/
def Kgraph (μ : History Z → ProbabilityMeasure M.AState) : Set (ShockVal Z × ℝ) :=
  {s | s.2 ∈ Kset μ s.1.val}

theorem measurableSet_Kgraph (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) :
    MeasurableSet (Kgraph μ) := by
  have e : Kgraph μ = ⋃ z : Z, (Prod.fst ⁻¹' {(⟨z⟩ : ShockVal Z)} ∩ Prod.snd ⁻¹' Kset μ z) := by
    ext s
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    change s.2 ∈ Kset μ s.1.val ↔ _
    constructor
    · intro h
      exact ⟨s.1.val, rfl, h⟩
    · rintro ⟨z, h1, h2⟩
      rw [h1]
      exact h2
  rw [e]
  exact MeasurableSet.iUnion fun z =>
    (measurable_fst (MeasurableSpace.measurableSet_top : MeasurableSet {(⟨z⟩ : ShockVal Z)})).inter
      (measurable_snd (isCompact_Kset hc z).isClosed.measurableSet)

/-! ### The law of `(z, K)` -/

/-- **Capital of the aggregate state**: `(z, ν) ↦ (z, ∫ a dν)`. -/
noncomputable def capMap (s : ShockVal Z × ProbabilityMeasure M.AState) : ShockVal Z × ℝ :=
  (s.1, ∫ x, M.assets x ∂(s.2 : Measure M.AState))

theorem continuous_capMap : Continuous (capMap (M := M)) :=
  continuous_fst.prodMk
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction M.assets).comp
      continuous_snd)

/-- **The law of `(z, K)`** when the history is drawn from `P`. -/
noncomputable def aggLaw (P : Measure (ShockPath Z))
    (μ : History Z → ProbabilityMeasure M.AState) : Measure (ShockVal Z × ℝ) :=
  (stateLaw P μ).map capMap

variable (hμ : M.IsSeqStateEquilibrium μ) (hU : M.UniqueSequentialEquilibrium)

include hμ hU in
/-- On the ergodic set, the next capital of `(z, K)` is the capital of the next distribution. -/
theorem lawKm_capMap (hS : KSufficient μ) {s : ShockVal Z × ProbabilityMeasure M.AState}
    (hs : s ∈ ergSet μ) (z' : Z) :
    capMap ((⟨z'⟩ : ShockVal Z), M.lawOfMotion s.1.val s.2 z')
      = ((⟨z'⟩ : ShockVal Z), lawKm μ (capMap s).1.val (capMap s).2 z') := by
  obtain ⟨ξ, rfl⟩ := hs
  have hk : capAt μ ξ.toHistory ∈ Kset μ (ξ.toHistory 0) := ⟨_, rfl, rfl⟩
  change ((⟨z'⟩ : ShockVal Z),
      ∫ x, M.assets x ∂(M.lawOfMotion (ξ.toHistory 0) (μ ξ.toHistory) z' : Measure M.AState))
    = ((⟨z'⟩ : ShockVal Z), lawKm μ (ξ.toHistory 0) (capAt μ ξ.toHistory) z')
  rw [lawKm_of_mem hk, lawK_eq hS, ← hμ.eq_lawOfMotion hU]
  rfl

include hμ hU in
/-- **One step of `(z, K)` is the image of one step of `(z, ν)`**, on the ergodic set. -/
theorem aggKernel_capMap (hS : KSufficient μ) {s : ShockVal Z × ProbabilityMeasure M.AState}
    (hs : s ∈ ergSet μ) {B : Set (ShockVal Z × ℝ)} (hB : MeasurableSet B) :
    aggKernel μ (capMap s) B = M.eqKernel s (capMap ⁻¹' B) := by
  rw [aggKernel_apply _ hB, eqKernel_apply _ (continuous_capMap.measurable hB)]
  refine Finset.sum_congr rfl fun z' _ => ?_
  congr 1
  rw [← lawKm_capMap hμ hU hS hs z']
  by_cases h : capMap ((⟨z'⟩ : ShockVal Z), M.lawOfMotion s.1.val s.2 z') ∈ B
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show _ ∈ capMap ⁻¹' B from h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show _ ∉ capMap ⁻¹' B from h)]

theorem ae_ergSet (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory)
    (P : Measure (ShockPath Z)) [IsProbabilityMeasure P] :
    ∀ᵐ s ∂(stateLaw P μ), s ∈ ergSet μ := by
  have : IsProbabilityMeasure (stateLaw P μ) :=
    (Measure.isProbabilityMeasure_map_iff (continuous_stateOf hc).measurable.aemeasurable).2
      inferInstance
  exact (prob_compl_eq_zero_iff (isCompact_ergSet hc).isClosed.measurableSet).2
    (stateLaw_ergSet hc P)

include hμ hU in
/-- **The law of `(z, K)` is invariant** for its Markov kernel. -/
theorem isInvariant_aggLaw (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) {P : Measure (ShockPath Z)}
    [IsProbabilityMeasure P] (hP : ShockPath.IsInvariant M.aggProb P) :
    (aggLaw P μ).bind (aggKernel μ) = aggLaw P μ := by
  have hφ : Measurable (capMap (M := M)) := continuous_capMap.measurable
  have hinv := isInvariant_stateLaw hU hμ hc.measurable hP
  ext B hB
  rw [Measure.bind_apply hB (measurable_aggKernel hS hc).aemeasurable, aggLaw,
    lintegral_map (f := fun s => aggKernel μ s B)
      ((Measure.measurable_coe hB).comp (measurable_aggKernel hS hc)) hφ,
    Measure.map_apply hφ hB]
  conv_rhs => rw [← hinv]
  rw [Measure.bind_apply (hφ hB) (measurable_eqKernel hU).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_ergSet hc P] with s hs
  exact aggKernel_capMap hμ hU hS hs hB

include hμ hU in
/-- **The law of `(z, K)` is ergodic** when the shock law is. -/
theorem ergodic_aggLaw (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) {P : Measure (ShockPath Z)}
    [IsProbabilityMeasure P]
    (hPerg : ∀ A, MeasurableSet A → (∀ᵐ ξ ∂P, ξ ∈ A → ShockPath.extMeasure M.aggProb ξ A = 1) →
      P A = 0 ∨ P A = 1)
    {B : Set (ShockVal Z × ℝ)} (hB : MeasurableSet B)
    (hinv : ∀ᵐ s ∂(aggLaw P μ), s ∈ B → aggKernel μ s B = 1) :
    aggLaw P μ B = 0 ∨ aggLaw P μ B = 1 := by
  have hφ : Measurable (capMap (M := M)) := continuous_capMap.measurable
  rw [aggLaw, Measure.map_apply hφ hB]
  refine ergodic_stateLaw hU hμ hc.measurable hPerg (hφ hB) ?_
  have h := ae_of_ae_map hφ.aemeasurable hinv
  filter_upwards [h, ae_ergSet hc P] with s hs hsE hmem
  rw [← aggKernel_capMap hμ hU hS hsE hB]
  exact hs hmem

/-- **The law of `(z, K)` lives on the graph of the capital sets.** -/
theorem aggLaw_Kgraph (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory)
    (P : Measure (ShockPath Z)) [IsProbabilityMeasure P] : aggLaw P μ (Kgraph μ) = 1 := by
  have hφ : Measurable (capMap (M := M)) := continuous_capMap.measurable
  have : IsProbabilityMeasure (stateLaw P μ) :=
    (Measure.isProbabilityMeasure_map_iff (continuous_stateOf hc).measurable.aemeasurable).2
      inferInstance
  rw [aggLaw, Measure.map_apply hφ (measurableSet_Kgraph hc)]
  refine le_antisymm prob_le_one ?_
  rw [← stateLaw_ergSet hc P]
  refine measure_mono ?_
  rintro s ⟨ξ, rfl⟩
  exact ⟨ξ.toHistory, rfl, rfl⟩

/-! ### Expectations on `(z, K)` -/

/-- The one-step expectation of `(z, K)`. -/
noncomputable def kStep (μ : History Z → ProbabilityMeasure M.AState) (F : ShockVal Z × ℝ → ℝ)
    (s : ShockVal Z × ℝ) : ℝ :=
  ∑ z', M.aggProb s.1.val z' * F ((⟨z'⟩ : ShockVal Z), lawKm μ s.1.val s.2 z')

/-- The `T`-step expectation of `(z, K)`. -/
noncomputable def kIter (μ : History Z → ProbabilityMeasure M.AState) (F : ShockVal Z × ℝ → ℝ) :
    ℕ → ShockVal Z × ℝ → ℝ
  | 0 => F
  | T + 1 => kStep μ (kIter μ F T)

/-- The `T`-step expectation of a function of `(z, K)` along the sequence-state equilibrium. -/
noncomputable def eIterK (μ : History Z → ProbabilityMeasure M.AState) (F : ShockVal Z × ℝ → ℝ) :
    ℕ → History Z → ℝ
  | 0 => fun ω => F ((⟨ω 0⟩ : ShockVal Z), capAt μ ω)
  | T + 1 => fun ω => ∑ z', M.aggProb (ω 0) z' * eIterK μ F T (History.cons z' ω)

theorem measurable_kStep (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) {F : ShockVal Z × ℝ → ℝ}
    (hF : Measurable F) : Measurable (kStep μ F) := by
  refine measurable_from_prod_countable_right fun v => ?_
  change Measurable fun y : ℝ =>
    ∑ z', M.aggProb v.val z' * F ((⟨z'⟩ : ShockVal Z), lawKm μ v.val y z')
  refine Finset.measurable_sum _ fun z' _ => Measurable.const_mul ?_ _
  exact hF.comp (measurable_const.prodMk (measurable_lawKm hS hc v.val z'))

theorem measurable_kIter (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) {F : ShockVal Z × ℝ → ℝ}
    (hF : Measurable F) : ∀ T, Measurable (kIter μ F T)
  | 0 => hF
  | T + 1 => measurable_kStep hS hc (measurable_kIter hS hc hF T)

theorem abs_kStep_le {F : ShockVal Z × ℝ → ℝ} {c : ℝ} (hF : ∀ s, |F s| ≤ c)
    (s : ShockVal Z × ℝ) : |kStep μ F s| ≤ c := by
  calc |kStep μ F s| ≤ ∑ z', M.aggProb s.1.val z' * c := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z' _ => ?_)
        rw [abs_mul, abs_of_nonneg (M.aggProb_nonneg _ _)]
        exact mul_le_mul_of_nonneg_left (hF _) (M.aggProb_nonneg _ _)
    _ = c := by rw [← Finset.sum_mul, M.aggProb_sum, one_mul]

theorem abs_kIter_le {F : ShockVal Z × ℝ → ℝ} {c : ℝ} (hF : ∀ s, |F s| ≤ c) :
    ∀ T s, |kIter μ F T s| ≤ c
  | 0 => hF
  | T + 1 => abs_kStep_le (abs_kIter_le hF T)

/-- **Expectations on `(z, K)` are expectations along the equilibrium** from any history with
that shock and capital. -/
theorem kIter_eq_eIterK (hS : KSufficient μ) (F : ShockVal Z × ℝ → ℝ) :
    ∀ T (ω : History Z), kIter μ F T ((⟨ω 0⟩ : ShockVal Z), capAt μ ω) = eIterK μ F T ω
  | 0, _ => rfl
  | T + 1, ω => by
    change ∑ z', M.aggProb (ω 0) z'
        * kIter μ F T ((⟨z'⟩ : ShockVal Z), lawKm μ (ω 0) (capAt μ ω) z')
      = ∑ z', M.aggProb (ω 0) z' * eIterK μ F T (History.cons z' ω)
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [lawKm_of_mem ⟨ω, rfl, rfl⟩, lawK_eq hS, ← kIter_eq_eIterK hS F T (History.cons z' ω)]
    rfl

/-! ### Invariant laws of `(z, K)` -/

/-- `λ` is an **invariant distribution** of `(z, K)`. -/
def IsAggInvariant (μ : History Z → ProbabilityMeasure M.AState) (Λ : Measure (ShockVal Z × ℝ)) :
    Prop :=
  Λ.bind (aggKernel μ) = Λ

/-- **Invariance against bounded measurable functions**: `∫ F dΛ = ∫ Q F dΛ`. -/
theorem IsAggInvariant.integral_kStep (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) {Λ : Measure (ShockVal Z × ℝ)}
    [IsProbabilityMeasure Λ] (hΛ : IsAggInvariant μ Λ) {F : ShockVal Z × ℝ → ℝ}
    (hF : Measurable F) {c : ℝ} (hcF : ∀ s, |F s| ≤ c) :
    ∫ s, F s ∂Λ = ∫ s, kStep μ F s ∂Λ := by
  set G : ShockVal Z × ℝ → ℝ := fun s => F s + c
  have hG0 : ∀ s, 0 ≤ G s := fun s => by
    have := (abs_le.1 (hcF s)).1
    simp only [G]
    linarith
  have hGm : Measurable G := hF.add measurable_const
  have hQG : ∀ s, kStep μ G s = kStep μ F s + c := by
    intro s
    simp only [kStep, G, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, M.aggProb_sum, one_mul]
  have hQG0 : ∀ s, 0 ≤ kStep μ G s := fun s =>
    Finset.sum_nonneg fun z' _ => mul_nonneg (M.aggProb_nonneg _ _) (hG0 _)
  have hint : ∀ s, ∫⁻ x, ENNReal.ofReal (G x) ∂(aggKernel μ s)
      = ENNReal.ofReal (kStep μ G s) := by
    intro s
    rw [aggKernel, lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, smul_eq_mul]
    rw [kStep, ENNReal.ofReal_sum_of_nonneg fun z' _ => mul_nonneg (M.aggProb_nonneg _ _) (hG0 _)]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [lintegral_dirac' _ hGm.ennreal_ofReal, ENNReal.ofReal_mul (M.aggProb_nonneg _ _)]
  have key : ∫⁻ s, ENNReal.ofReal (G s) ∂Λ = ∫⁻ s, ENNReal.ofReal (kStep μ G s) ∂Λ := by
    conv_lhs => rw [← hΛ]
    rw [Measure.lintegral_bind (measurable_aggKernel hS hc).aemeasurable
      hGm.ennreal_ofReal.aemeasurable]
    exact lintegral_congr hint
  have hFi : Integrable F Λ :=
    Integrable.of_bound hF.aestronglyMeasurable c (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]; exact hcF s)
  have hQFi : Integrable (kStep μ F) Λ :=
    Integrable.of_bound (measurable_kStep hS hc hF).aestronglyMeasurable c
      (Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact abs_kStep_le hcF s)
  have e1 : ∫ s, G s ∂Λ = (∫⁻ s, ENNReal.ofReal (G s) ∂Λ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hG0) hGm.aestronglyMeasurable
  have e2 : ∫ s, kStep μ G s ∂Λ = (∫⁻ s, ENNReal.ofReal (kStep μ G s) ∂Λ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hQG0)
      (measurable_kStep hS hc hGm).aestronglyMeasurable
  have e3 : ∫ s, G s ∂Λ = ∫ s, F s ∂Λ + c := by
    rw [integral_add hFi (integrable_const c), integral_const, probReal_univ, one_smul]
  have e4 : ∫ s, kStep μ G s ∂Λ = ∫ s, kStep μ F s ∂Λ + c := by
    simp_rw [hQG]
    rw [integral_add hQFi (integrable_const c), integral_const, probReal_univ, one_smul]
  have := e1.trans (key ▸ e2.symm)
  linarith

theorem IsAggInvariant.integral_kIter (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) {Λ : Measure (ShockVal Z × ℝ)}
    [IsProbabilityMeasure Λ] (hΛ : IsAggInvariant μ Λ) {F : ShockVal Z × ℝ → ℝ}
    (hF : Measurable F) {c : ℝ} (hcF : ∀ s, |F s| ≤ c) :
    ∀ T, ∫ s, F s ∂Λ = ∫ s, kIter μ F T s ∂Λ
  | 0 => rfl
  | T + 1 => (hΛ.integral_kIter hS hc hF hcF T).trans
      (hΛ.integral_kStep hS hc (measurable_kIter hS hc hF T) (abs_kIter_le hcF T))

/-- The shock marginal of a law of `(z, K)`. -/
noncomputable def aggMarginal (Λ : Measure (ShockVal Z × ℝ)) (z : Z) : ℝ :=
  Λ.real (Prod.fst ⁻¹' {(⟨z⟩ : ShockVal Z)})

omit [Fintype Z] in
theorem measurableSet_fst_singleton' (v : ShockVal Z) :
    MeasurableSet (Prod.fst ⁻¹' {v} : Set (ShockVal Z × ℝ)) :=
  measurable_fst (MeasurableSpace.measurableSet_top : MeasurableSet {v})

omit [Fintype E] in
/-- Integrating a function of today's shock against the marginal. -/
theorem integral_fst' (Λ : Measure (ShockVal Z × ℝ)) [IsProbabilityMeasure Λ]
    (g : ShockVal Z → ℝ) : ∫ s, g s.1 ∂Λ = ∑ z, aggMarginal Λ z * g ⟨z⟩ := by
  have e : (fun s : ShockVal Z × ℝ => g s.1)
      = fun s => ∑ z, g ⟨z⟩ * (Prod.fst ⁻¹' {(⟨z⟩ : ShockVal Z)}).indicator
        (1 : ShockVal Z × ℝ → ℝ) s := by
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
    rw [integral_const_mul, integral_indicator_one (measurableSet_fst_singleton' _), mul_comm]
    rfl
  · exact ((integrable_const (1 : ℝ)).indicator (measurableSet_fst_singleton' _)).const_mul _

omit [Fintype E] in
theorem sum_aggMarginal (Λ : Measure (ShockVal Z × ℝ)) [IsProbabilityMeasure Λ] :
    ∑ z, aggMarginal Λ z = 1 := by
  have h := integral_fst' Λ (fun _ => (1 : ℝ))
  simp only [mul_one, integral_const, probReal_univ, one_smul] at h
  exact h.symm

/-- **The shock marginal of an invariant law of `(z, K)` is `π`-stationary.** -/
theorem IsAggInvariant.marginal_stationary (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) {Λ : Measure (ShockVal Z × ℝ)}
    [IsProbabilityMeasure Λ] (hΛ : IsAggInvariant μ Λ) (z' : Z) :
    ∑ z, aggMarginal Λ z * M.aggProb z z' = aggMarginal Λ z' := by
  set F : ShockVal Z × ℝ → ℝ := (Prod.fst ⁻¹' {(⟨z'⟩ : ShockVal Z)}).indicator 1
  have hFm : Measurable F := measurable_one.indicator (measurableSet_fst_singleton' _)
  have hFc : ∀ s, |F s| ≤ 1 := fun s => by
    simp only [F, Set.indicator, Pi.one_apply]
    split_ifs <;> simp
  have h := hΛ.integral_kStep hS hc hFm hFc
  have hL : ∫ s, F s ∂Λ = aggMarginal Λ z' := by
    rw [integral_indicator_one (measurableSet_fst_singleton' _)]
    rfl
  have hQ : kStep μ F = fun s => M.aggProb s.1.val z' := by
    funext s
    rw [kStep, Finset.sum_eq_single z']
    · simp only [F]
      rw [Set.indicator_of_mem (show ((⟨z'⟩ : ShockVal Z), lawKm μ s.1.val s.2 z')
        ∈ Prod.fst ⁻¹' {(⟨z'⟩ : ShockVal Z)} from rfl), Pi.one_apply, mul_one]
    · intro z _ hz
      simp only [F]
      rw [Set.indicator_of_notMem (fun h => hz (by
        rw [mem_preimage, mem_singleton_iff] at h; exact congrArg ShockVal.val h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hQ, integral_fst' Λ (fun v => M.aggProb v.val z')] at h
  rw [← h, hL]

/-! ### Uniqueness for small capital shares -/

namespace SlopeContraction

variable {ε : ℝ} (hminor : ∀ z z' e e', ε ≤ M.idioProb z z' e e') (S : M.SlopeContraction)
  {ℓL : ℝ} (hℓL : 0 ≤ ℓL)
  (hRL : ∀ z k L L', |M.grossReturn z k L - M.grossReturn z k L'| ≤ ℓL * |L - L'|)
  (hwL : ∀ z k L L', |M.wage z k L - M.wage z k L'| ≤ ℓL * |L - L'|)
  (hε : 0 < ε) (hκ : S.κ < 1) (hr : S.rate < 1)

include hminor hℓL hRL hwL hε hκ hμ in
/-- **Capital forgets old shocks**: histories agreeing over their last `m + 1` shocks have
capital within `(1 + ā) r*ᵐ ω`. -/
theorem abs_capAt_sub_le [Nonempty E] (m : ℕ) (ω ω' : History Z) (hag : ∀ n ≤ m, ω n = ω' n) :
    |capAt μ ω - capAt μ ω'|
      ≤ (1 + M.assetCap) * (S.histRate ε ^ m * S.histWeight ℓL ε) := by
  obtain ⟨da, dm, hda, hdm, hN, hD⟩ :=
    S.dist2_of_agree hminor hℓL hRL hwL hε hκ hμ m ω ω' hag
  have hw1 := S.one_le_histWeight hε hκ hℓL
  have hcap := hD.capital
  have hA := M.assetCap_pos.le
  change |∫ x, M.assets x ∂(μ ω : Measure M.AState)
    - ∫ x, M.assets x ∂(μ ω' : Measure M.AState)| ≤ _
  refine hcap.trans ?_
  have h1 : M.assetCap * dm ≤ M.assetCap * (S.histWeight ℓL ε * dm) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hdm hw1) hA
  have h2 : 0 ≤ S.histWeight ℓL ε * dm := mul_nonneg (zero_le_one.trans hw1) hdm
  calc da + M.assetCap * dm ≤ (1 + M.assetCap) * (da + S.histWeight ℓL ε * dm) := by
        nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (by linarith)

include hminor hℓL hRL hwL hε hκ hμ in
/-- **Expectations along the equilibrium forget the start**, for a test function uniformly
continuous on the capital sets. -/
theorem abs_eIterK_sub_le [Nonempty E] {F : ShockVal Z × ℝ → ℝ} {η δ : ℝ}
    (hunif : ∀ (z : Z) (k k' : ℝ), k ∈ Kset μ z → k' ∈ Kset μ z → |k - k'| < δ →
      |F ((⟨z⟩ : ShockVal Z), k) - F ((⟨z⟩ : ShockVal Z), k')| ≤ η) :
    ∀ (j m : ℕ) (ω ω' : History Z), (∀ n ≤ m, ω n = ω' n) →
      (1 + M.assetCap) * (S.histRate ε ^ (m + j) * S.histWeight ℓL ε) < δ →
      |eIterK μ F j ω - eIterK μ F j ω'| ≤ η
  | 0, m, ω, ω', hag, hδ => by
    have h0 := hag 0 (Nat.zero_le _)
    change |F ((⟨ω 0⟩ : ShockVal Z), capAt μ ω) - F ((⟨ω' 0⟩ : ShockVal Z), capAt μ ω')| ≤ η
    rw [← h0]
    refine hunif _ _ _ ⟨ω, rfl, rfl⟩ ⟨ω', h0.symm, rfl⟩ ?_
    exact (S.abs_capAt_sub_le hμ hminor hℓL hRL hwL hε hκ m ω ω' hag).trans_lt
      (by simpa using hδ)
  | j + 1, m, ω, ω', hag, hδ => by
    have h0 := hag 0 (Nat.zero_le _)
    change |∑ z', M.aggProb (ω 0) z' * eIterK μ F j (History.cons z' ω)
      - ∑ z', M.aggProb (ω' 0) z' * eIterK μ F j (History.cons z' ω')| ≤ η
    rw [← h0, ← Finset.sum_sub_distrib]
    have hterm : ∀ z', |eIterK μ F j (History.cons z' ω) - eIterK μ F j (History.cons z' ω')|
        ≤ η := by
      intro z'
      refine abs_eIterK_sub_le hunif j (m + 1) _ _ (fun n hn => ?_) ?_
      · cases n with
        | zero => rfl
        | succ n => exact hag n (by omega)
      · rw [show m + 1 + j = m + (j + 1) by omega]
        exact hδ
    calc _ ≤ ∑ z', M.aggProb (ω 0) z' * η := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z' _ => ?_)
          rw [← mul_sub, abs_mul, abs_of_nonneg (M.aggProb_nonneg _ _)]
          exact mul_le_mul_of_nonneg_left (hterm z') (M.aggProb_nonneg _ _)
      _ = η := by rw [← Finset.sum_mul, M.aggProb_sum, one_mul]

include hminor hℓL hRL hwL hε hκ hr hμ in
/-- **Two invariant laws of `(z, K)` living on the capital sets agree on bounded continuous
functions**, when the aggregate chain has a unique stationary distribution. -/
theorem integral_eq_of_isAggInvariant [Nonempty Z] [Nonempty E] (hS : KSufficient μ)
    (huniq : ∀ q q' : Z → ℝ, (∀ z, 0 ≤ q z) → ∑ z, q z = 1 →
      (∀ z', ∑ z, q z * M.aggProb z z' = q z') → (∀ z, 0 ≤ q' z) → ∑ z, q' z = 1 →
      (∀ z', ∑ z, q' z * M.aggProb z z' = q' z') → q = q')
    {Λ₁ Λ₂ : Measure (ShockVal Z × ℝ)} [IsProbabilityMeasure Λ₁] [IsProbabilityMeasure Λ₂]
    (h₁ : IsAggInvariant μ Λ₁) (h₂ : IsAggInvariant μ Λ₂) (hK₁ : Λ₁ (Kgraph μ) = 1)
    (hK₂ : Λ₂ (Kgraph μ) = 1) (F : (ShockVal Z × ℝ) →ᵇ ℝ) :
    ∫ s, F s ∂Λ₁ = ∫ s, F s ∂Λ₂ := by
  have hc := S.continuous_seqState hminor hℓL hRL hwL hε hκ hr hμ
  have hFm : Measurable F := F.continuous.measurable
  have hFc : ∀ s, |F s| ≤ ‖F‖ := fun s => by rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm s
  set w := S.histWeight ℓL ε
  set r := S.histRate ε
  have hw1 : 1 ≤ w := S.one_le_histWeight hε hκ hℓL
  have hr0 : 0 ≤ r := (S.rate_nonneg hκ).trans (le_max_left _ _)
  have hr1 : r < 1 := S.histRate_lt_one hε hr
  -- the shock marginals agree
  have hm : aggMarginal Λ₁ = aggMarginal Λ₂ :=
    huniq _ _ (fun z => measureReal_nonneg) (sum_aggMarginal Λ₁) (h₁.marginal_stationary hS hc)
      (fun z => measureReal_nonneg) (sum_aggMarginal Λ₂) (h₂.marginal_stationary hS hc)
  -- for every `η > 0` the integrals are within `2 η`
  have hbound : ∀ η > 0, |∫ s, F s ∂Λ₁ - ∫ s, F s ∂Λ₂| ≤ 2 * η := by
    intro η hη
    -- uniform continuity on the capital sets
    have hδv : ∀ z : Z, ∃ δ > 0, ∀ k ∈ Kset μ z, ∀ k' ∈ Kset μ z, dist k k' < δ →
        dist (F ((⟨z⟩ : ShockVal Z), k)) (F ((⟨z⟩ : ShockVal Z), k')) < η := by
      intro z
      have hcont : Continuous fun k : ℝ => F ((⟨z⟩ : ShockVal Z), k) :=
        F.continuous.comp (continuous_const.prodMk continuous_id)
      have hu := (isCompact_Kset hc z).uniformContinuousOn_of_continuous hcont.continuousOn
      exact Metric.uniformContinuousOn_iff.1 hu η hη
    choose δv hδv0 hδv using hδv
    set δ := Finset.univ.inf' Finset.univ_nonempty δv
    have hδ0 : 0 < δ := (Finset.lt_inf'_iff _).2 fun z _ => hδv0 z
    have hunif : ∀ (z : Z) (k k' : ℝ), k ∈ Kset μ z → k' ∈ Kset μ z → |k - k'| < δ →
        |F ((⟨z⟩ : ShockVal Z), k) - F ((⟨z⟩ : ShockVal Z), k')| ≤ η := by
      intro z k k' hk hk' hkk
      have := hδv z k hk k' hk'
        (by rw [Real.dist_eq]; exact hkk.trans_le (Finset.inf'_le _ (Finset.mem_univ z)))
      rw [Real.dist_eq] at this
      exact this.le
    -- a horizon with the fading-memory error below `δ`
    have hpos : 0 < (1 + M.assetCap) * w := by
      have := M.assetCap_pos
      positivity
    obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one (div_pos hδ0 hpos) hr1
    have hTδ : (1 + M.assetCap) * (r ^ (0 + T) * w) < δ := by
      rw [zero_add]
      have := (lt_div_iff₀ hpos).1 hT
      linarith
    -- the comparator: a function of today's shock
    set g : ShockVal Z → ℝ := fun v => eIterK μ F T (fun _ => v.val)
    have hclose : ∀ s ∈ Kgraph μ, |kIter μ F T s - g s.1| ≤ η := by
      rintro ⟨⟨z⟩, k⟩ hs
      obtain ⟨ω, rfl, rfl⟩ := hs
      rw [kIter_eq_eIterK hS]
      refine S.abs_eIterK_sub_le hμ hminor hℓL hRL hwL hε hκ hunif T 0 ω (fun _ => ω 0)
        (fun n hn => ?_) hTδ
      rw [Nat.le_zero.1 hn]
    have hint : ∀ (Λ : Measure (ShockVal Z × ℝ)) [IsProbabilityMeasure Λ], Λ (Kgraph μ) = 1 →
        |∫ s, kIter μ F T s ∂Λ - ∑ z, aggMarginal Λ z * g ⟨z⟩| ≤ η := by
      intro Λ _ hK
      have hae : ∀ᵐ s ∂Λ, s ∈ Kgraph μ :=
        (prob_compl_eq_zero_iff (measurableSet_Kgraph hc)).2 hK
      have hg : ∫ s, g s.1 ∂Λ = ∑ z, aggMarginal Λ z * g ⟨z⟩ := integral_fst' Λ g
      have hgm : Measurable fun s : ShockVal Z × ℝ => g s.1 :=
        (measurable_of_countable (fun v : ShockVal Z => g v)).comp measurable_fst
      have hqi : Integrable (kIter μ F T) Λ :=
        Integrable.of_bound (measurable_kIter hS hc hFm T).aestronglyMeasurable ‖F‖
          (Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact abs_kIter_le hFc T s)
      have hgi : Integrable (fun s : ShockVal Z × ℝ => g s.1) Λ := by
        refine Integrable.of_bound hgm.aestronglyMeasurable (∑ z, |g ⟨z⟩|)
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs]
        exact Finset.single_le_sum (f := fun z => |g ⟨z⟩|) (fun z _ => abs_nonneg _)
          (Finset.mem_univ s.1.val)
      rw [← hg, ← integral_sub hqi hgi]
      have := norm_integral_le_of_norm_le_const (μ := Λ)
        (f := fun s => kIter μ F T s - g s.1) (hae.mono fun s hs => by
          rw [Real.norm_eq_abs]; exact hclose s hs)
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    rw [h₁.integral_kIter hS hc hFm hFc T, h₂.integral_kIter hS hc hFm hFc T]
    have a := hint Λ₁ hK₁
    have b := hint Λ₂ hK₂
    rw [hm] at a
    calc _ ≤ |∫ s, kIter μ F T s ∂Λ₁ - ∑ z, aggMarginal Λ₂ z * g ⟨z⟩|
          + |∫ s, kIter μ F T s ∂Λ₂ - ∑ z, aggMarginal Λ₂ z * g ⟨z⟩| := by
          rw [abs_sub_comm (∫ s, kIter μ F T s ∂Λ₂)]
          exact abs_sub_le _ _ _
      _ ≤ _ := by linarith
  by_contra hne
  have hd : 0 < |∫ s, F s ∂Λ₁ - ∫ s, F s ∂Λ₂| := abs_pos.2 (sub_ne_zero.2 hne)
  have := hbound (|∫ s, F s ∂Λ₁ - ∫ s, F s ∂Λ₂| / 4) (by positivity)
  linarith

include hminor hℓL hRL hwL hε hκ hr hμ in
/-- **The invariant law of `(z, K)` on the capital sets is unique**, when the aggregate chain has
a unique stationary distribution. -/
theorem eq_of_isAggInvariant [Nonempty Z] [Nonempty E] (hS : KSufficient μ)
    (huniq : ∀ q q' : Z → ℝ, (∀ z, 0 ≤ q z) → ∑ z, q z = 1 →
      (∀ z', ∑ z, q z * M.aggProb z z' = q z') → (∀ z, 0 ≤ q' z) → ∑ z, q' z = 1 →
      (∀ z', ∑ z, q' z * M.aggProb z z' = q' z') → q = q')
    {Λ₁ Λ₂ : Measure (ShockVal Z × ℝ)} [IsProbabilityMeasure Λ₁] [IsProbabilityMeasure Λ₂]
    (h₁ : IsAggInvariant μ Λ₁) (h₂ : IsAggInvariant μ Λ₂) (hK₁ : Λ₁ (Kgraph μ) = 1)
    (hK₂ : Λ₂ (Kgraph μ) = 1) : Λ₁ = Λ₂ :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun F =>
    S.integral_eq_of_isAggInvariant hμ hminor hℓL hRL hwL hε hκ hr hS huniq h₁ h₂ hK₁ hK₂ F

include hminor hℓL hRL hwL hε hκ hr hμ in
/-- **The stationary distribution on `(z, K)`**: under `KSufficient`, the law of `(z, K)` is
invariant, lives on the capital sets, is ergodic when the shock law is, and is the only
invariant law on the capital sets. -/
theorem stationary_aggLaw [Nonempty Z] [Nonempty E] (hS : KSufficient μ)
    (huniq : ∀ q q' : Z → ℝ, (∀ z, 0 ≤ q z) → ∑ z, q z = 1 →
      (∀ z', ∑ z, q z * M.aggProb z z' = q z') → (∀ z, 0 ≤ q' z) → ∑ z, q' z = 1 →
      (∀ z', ∑ z, q' z * M.aggProb z z' = q' z') → q = q')
    {P : Measure (ShockPath Z)} [IsProbabilityMeasure P] (hP : ShockPath.IsInvariant M.aggProb P)
    (hPerg : ∀ A, MeasurableSet A → (∀ᵐ ξ ∂P, ξ ∈ A → ShockPath.extMeasure M.aggProb ξ A = 1) →
      P A = 0 ∨ P A = 1) :
    IsAggInvariant μ (aggLaw P μ) ∧ aggLaw P μ (Kgraph μ) = 1 ∧
      (∀ B, MeasurableSet B → (∀ᵐ s ∂(aggLaw P μ), s ∈ B → aggKernel μ s B = 1) →
        aggLaw P μ B = 0 ∨ aggLaw P μ B = 1) ∧
      ∀ (Λ : Measure (ShockVal Z × ℝ)) [IsProbabilityMeasure Λ], IsAggInvariant μ Λ →
        Λ (Kgraph μ) = 1 → Λ = aggLaw P μ := by
  have hc := S.continuous_seqState hminor hℓL hRL hwL hε hκ hr hμ
  have hU := S.uniqueSequentialEquilibrium hκ
  have hφ : Measurable (capMap (M := M)) := continuous_capMap.measurable
  have : IsProbabilityMeasure (stateLaw P μ) :=
    (Measure.isProbabilityMeasure_map_iff (continuous_stateOf hc).measurable.aemeasurable).2
      inferInstance
  have : IsProbabilityMeasure (aggLaw P μ) :=
    (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).2 inferInstance
  have hinv := isInvariant_aggLaw hμ hU hS hc hP
  have hK := aggLaw_Kgraph hc P
  refine ⟨hinv, hK, fun B hB h => ergodic_aggLaw hμ hU hS hc hPerg hB h, fun Λ _ hΛ hΛK => ?_⟩
  exact S.eq_of_isAggInvariant hμ hminor hℓL hRL hwL hε hκ hr hS huniq hΛ hinv hΛK hK

end SlopeContraction

end KSModel

end KrusellSmith

end LeanEconomics
