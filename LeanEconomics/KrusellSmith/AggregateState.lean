/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.StationaryUnique

/-!
# Aggregate shock and aggregate capital as the aggregate state

Milestones AK0–AK1 of `AGGREGATE_STATE_PLAN.md`. For a sequence-state equilibrium `μ` that is
continuous in the history (the small-share class, `continuous_seqState`):

* **AK0** the ergodic set `ergSet μ = {(ξ 0, μ ξ)}` of aggregate states is compact
  (`isCompact_ergSet`), carries the whole law of the aggregate state (`stateLaw_ergSet`), and is
  closed under the equilibrium law of motion (`lawOfMotion_mem_ergSet`, under uniqueness).
* **AK1** households need only prices, i.e. the tree `seqPrices μ ω` of future capital and labour.
  **`KSufficient μ`**: two histories with the same shock and the same capital have the same price
  tree. Then
  * `aggTree μ z k` (the price tree from any history with shock `z` and capital `k`) is well
    defined on the capital set `Kset μ z` (`aggTree_eq`), which is compact (`isCompact_Kset`);
  * the **law of motion of capital** `lawK μ z k z'` and labour `labourK μ z k` on `(z, K)`
    generate the whole tree (`aggTree_eq_stateAlong`), and `lawK` maps `Kset μ z` into
    `Kset μ z'`;
  * all of them are **continuous** on `Kset μ z` (`continuousOn_aggTree`, `continuousOn_lawK`,
    `continuousOn_labourK`): capital is a quotient map from the compact set of histories with
    shock `z`, so no injectivity is needed;
  * `KInjective` (capital injective on distributions with the same shock) implies `KSufficient`
    under uniqueness of sequential equilibrium (`KInjective.kSufficient`).
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction TopologicalSpace ProbabilityTheory
open scoped ENNReal NNReal

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace ShockPath

/-- A history as a shock path. -/
def ofHistory (ω : History Z) : ShockPath Z := fun n => ⟨ω n⟩

omit [Fintype Z] in
@[simp] theorem toHistory_ofHistory (ω : History Z) : (ofHistory ω).toHistory = ω := rfl

/-- **Prepending finite future shocks** (newest first) to a shock path. -/
def prepend : List Z → ShockPath Z → ShockPath Z
  | [], ξ => ξ
  | z :: g, ξ => cons z (prepend g ξ)

omit [Fintype Z] in
theorem toHistory_prepend (g : List Z) (ξ : ShockPath Z) :
    (prepend g ξ).toHistory = History.prepend g ξ.toHistory := by
  induction g with
  | nil => rfl
  | cons z g ih =>
    change (cons z (prepend g ξ)).toHistory = _
    rw [toHistory_cons, ih]
    rfl

omit [Fintype Z] in
theorem continuous_prepend (g : List Z) : Continuous (prepend g : ShockPath Z → ShockPath Z) := by
  induction g with
  | nil => exact continuous_id
  | cons z g ih => exact (continuous_cons z).comp ih

omit [Fintype Z] in
/-- The histories with today's shock `z` form a closed set. -/
theorem isClosed_fibre (z : Z) : IsClosed {ξ : ShockPath Z | (ξ 0).val = z} := by
  change IsClosed ((fun ξ : ShockPath Z => ξ 0) ⁻¹' {s : ShockVal Z | s.val = z})
  exact (isClosed_discrete _).preimage (continuous_apply 0)

end ShockPath

namespace KSModel

variable {M : KSModel Z E} {μ : History Z → ProbabilityMeasure M.AState}

/-- **The price tree is continuous in the history** when the equilibrium is. -/
theorem continuous_seqPrices_history (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory)
    (g : List Z) : Continuous fun ξ : ShockPath Z => M.seqPrices μ ξ.toHistory g := by
  have hg : Continuous fun ξ : ShockPath Z => μ (History.prepend g ξ.toHistory) :=
    (hc.comp (ShockPath.continuous_prepend g)).congr fun ξ => by
      simp only [Function.comp_apply, ShockPath.toHistory_prepend]
  change Continuous fun ξ : ShockPath Z =>
    ((∫ x, M.assets x ∂(μ (History.prepend g ξ.toHistory) : Measure M.AState)),
      ∑ e, M.initMass (μ (History.prepend g ξ.toHistory) : Measure M.AState) e * M.efficiency e)
  refine Continuous.prodMk ?_ ?_
  · exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction M.assets).comp hg
  · refine continuous_finsetSum _ fun e _ => ?_
    exact (((continuous_apply e).comp M.continuous_initMass).comp hg).mul continuous_const

/-! ### AK0: the ergodic set -/

/-- **The ergodic set**: the aggregate states `(ξ 0, μ ξ)` the equilibrium visits. -/
def ergSet (μ : History Z → ProbabilityMeasure M.AState) :
    Set (ShockVal Z × ProbabilityMeasure M.AState) :=
  range (stateOf μ)

theorem continuous_stateOf (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) :
    Continuous (stateOf μ) :=
  (continuous_apply 0).prodMk hc

theorem isCompact_ergSet (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) :
    IsCompact (ergSet μ) :=
  isCompact_range (continuous_stateOf hc)

/-- **The law of the aggregate state lives on the ergodic set.** -/
theorem stateLaw_ergSet (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory)
    (P : Measure (ShockPath Z)) [IsProbabilityMeasure P] : stateLaw P μ (ergSet μ) = 1 := by
  rw [stateLaw, Measure.map_apply (continuous_stateOf hc).measurable
    (isCompact_ergSet hc).isClosed.measurableSet, ergSet, preimage_range, measure_univ]

theorem stateOf_cons_mem_ergSet (z' : Z) (ξ : ShockPath Z) :
    ((⟨z'⟩ : ShockVal Z), μ (History.cons z' ξ.toHistory)) ∈ ergSet μ :=
  ⟨ShockPath.cons z' ξ, stateOf_cons μ z' ξ⟩

/-- **The ergodic set is closed under the equilibrium law of motion** (under uniqueness). -/
theorem lawOfMotion_mem_ergSet (hμ : M.IsSeqStateEquilibrium μ)
    (hU : M.UniqueSequentialEquilibrium) {s : ShockVal Z × ProbabilityMeasure M.AState}
    (hs : s ∈ ergSet μ) (z' : Z) :
    ((⟨z'⟩ : ShockVal Z), M.lawOfMotion s.1.val s.2 z') ∈ ergSet μ := by
  obtain ⟨ξ, rfl⟩ := hs
  refine ⟨ShockPath.cons z' ξ, ?_⟩
  rw [stateOf_cons, hμ.eq_lawOfMotion hU]
  rfl

/-! ### AK1: the price tree on `(z, K)` -/

/-- **Capital at a history.** -/
noncomputable def capAt (μ : History Z → ProbabilityMeasure M.AState) (ω : History Z) : ℝ :=
  (M.seqPrices μ ω []).1

/-- **`(z, K)` is a sufficient aggregate state**: two histories with the same shock and the same
capital have the same future capital and labour at every node. -/
def KSufficient (μ : History Z → ProbabilityMeasure M.AState) : Prop :=
  ∀ ω ω' : History Z, ω 0 = ω' 0 → capAt μ ω = capAt μ ω' →
    M.seqPrices μ ω = M.seqPrices μ ω'

/-- **Capital determines the distribution** among histories with the same shock. -/
def KInjective (μ : History Z → ProbabilityMeasure M.AState) : Prop :=
  ∀ ω ω' : History Z, ω 0 = ω' 0 → capAt μ ω = capAt μ ω' → μ ω = μ ω'

/-- Under uniqueness, `KInjective` implies `KSufficient`. -/
theorem KInjective.kSufficient (hμ : M.IsSeqStateEquilibrium μ)
    (hU : M.UniqueSequentialEquilibrium) (hI : KInjective μ) : KSufficient μ := by
  intro ω ω' h0 hk
  funext g
  have h1 := hμ.eq_nodeProb hU ω g
  have h2 := hμ.eq_nodeProb hU ω' g
  rw [h0, hI ω ω' h0 hk] at h1
  simp only [seqPrices, h1, h2]

/-- **The capital set at shock `z`.** -/
def Kset (μ : History Z → ProbabilityMeasure M.AState) (z : Z) : Set ℝ :=
  {k | ∃ ω : History Z, ω 0 = z ∧ capAt μ ω = k}

theorem Kset_eq_image (z : Z) :
    Kset μ z = (fun ξ : ShockPath Z => capAt μ ξ.toHistory) '' {ξ | (ξ 0).val = z} := by
  ext k
  constructor
  · rintro ⟨ω, h0, rfl⟩
    exact ⟨ShockPath.ofHistory ω, h0, rfl⟩
  · rintro ⟨ξ, h0, rfl⟩
    exact ⟨ξ.toHistory, h0, rfl⟩

theorem isCompact_Kset (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) (z : Z) :
    IsCompact (Kset μ z) := by
  rw [Kset_eq_image]
  exact (ShockPath.isClosed_fibre z).isCompact.image (continuous_seqPrices_history hc []).fst

open Classical in
/-- **The price tree at `(z, k)`**: that of any history with shock `z` and capital `k`. -/
noncomputable def aggTree (μ : History Z → ProbabilityMeasure M.AState) (z : Z) (k : ℝ) :
    List Z → ℝ × ℝ :=
  if h : ∃ ω : History Z, ω 0 = z ∧ capAt μ ω = k then M.seqPrices μ (Classical.choose h)
  else fun _ => 0

/-- **The price tree is a function of `(z, K)`** under `KSufficient`. -/
theorem aggTree_eq (hS : KSufficient μ) (ω : History Z) :
    aggTree μ (ω 0) (capAt μ ω) = M.seqPrices μ ω := by
  have h : ∃ ω' : History Z, ω' 0 = ω 0 ∧ capAt μ ω' = capAt μ ω := ⟨ω, rfl, rfl⟩
  rw [aggTree, dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨h0, hk⟩ := Classical.choose_spec h
  exact hS _ _ h0 hk

theorem aggTree_nil_fst (hS : KSufficient μ) {z : Z} {k : ℝ} (hk : k ∈ Kset μ z) :
    (aggTree μ z k []).1 = k := by
  obtain ⟨ω, rfl, rfl⟩ := hk
  rw [aggTree_eq hS]
  rfl

/-- **The law of motion of capital on `(z, K)`**: capital after the shock `z'`. -/
noncomputable def lawK (μ : History Z → ProbabilityMeasure M.AState) (z : Z) (k : ℝ) (z' : Z) :
    ℝ :=
  (aggTree μ z k [z']).1

/-- **Labour as a function of `(z, K)`.** -/
noncomputable def labourK (μ : History Z → ProbabilityMeasure M.AState) (z : Z) (k : ℝ) :
    ℝ :=
  (aggTree μ z k []).2

theorem lawK_eq (hS : KSufficient μ) (ω : History Z) (z' : Z) :
    lawK μ (ω 0) (capAt μ ω) z' = capAt μ (History.cons z' ω) := by
  rw [lawK, aggTree_eq hS]
  rfl

theorem labourK_eq (hS : KSufficient μ) (ω : History Z) :
    labourK μ (ω 0) (capAt μ ω) = (M.seqPrices μ ω []).2 := by
  rw [labourK, aggTree_eq hS]

theorem lawK_mem (hS : KSufficient μ) {z : Z} {k : ℝ} (hk : k ∈ Kset μ z) (z' : Z) :
    lawK μ z k z' ∈ Kset μ z' := by
  obtain ⟨ω, rfl, rfl⟩ := hk
  exact ⟨History.cons z' ω, rfl, (lawK_eq hS ω z').symm⟩

/-- **The tree after one shock is the tree at the new `(z', K')`.** -/
theorem aggTree_shift (hS : KSufficient μ) {z : Z} {k : ℝ} (hk : k ∈ Kset μ z) (z' : Z)
    (g : List Z) : aggTree μ z' (lawK μ z k z') g = aggTree μ z k (g ++ [z']) := by
  obtain ⟨ω, rfl, rfl⟩ := hk
  have h := aggTree_eq hS (History.cons z' ω)
  rw [History.cons_zero] at h
  rw [lawK_eq hS, h, aggTree_eq hS ω]
  exact M.seqPrices_prepend μ ω [z'] g

/-- **The aggregate state along a node** `g` (newest first) of the tree from `(z, k)`. -/
noncomputable def stateAlong (μ : History Z → ProbabilityMeasure M.AState) (z : Z) (k : ℝ) :
    List Z → Z × ℝ
  | [] => (z, k)
  | z' :: g => (z', lawK μ (stateAlong μ z k g).1 (stateAlong μ z k g).2 z')

theorem stateAlong_mem_and_aggTree (hS : KSufficient μ) {z : Z} {k : ℝ} (hk : k ∈ Kset μ z)
    (g : List Z) :
    (stateAlong μ z k g).2 ∈ Kset μ (stateAlong μ z k g).1 ∧
      ∀ g', aggTree μ z k (g' ++ g)
        = aggTree μ (stateAlong μ z k g).1 (stateAlong μ z k g).2 g' := by
  induction g with
  | nil => exact ⟨hk, fun g' => by rw [List.append_nil]; rfl⟩
  | cons z' g ih =>
    refine ⟨lawK_mem hS ih.1 z', fun g' => ?_⟩
    have happ : g' ++ z' :: g = (g' ++ [z']) ++ g := by simp
    rw [happ, ih.2 (g' ++ [z']), ← aggTree_shift hS ih.1 z' g']
    rfl

/-- **`lawK` and `labourK` generate the whole price tree**: capital at the node `g` is the
`lawK`-iterate along `g`, and labour there is `labourK` at the iterate. -/
theorem aggTree_eq_stateAlong (hS : KSufficient μ) {z : Z} {k : ℝ} (hk : k ∈ Kset μ z)
    (g : List Z) :
    aggTree μ z k g = ((stateAlong μ z k g).2,
      labourK μ (stateAlong μ z k g).1 (stateAlong μ z k g).2) := by
  obtain ⟨hmem, htree⟩ := stateAlong_mem_and_aggTree hS hk g
  have h := htree []
  rw [List.nil_append] at h
  rw [h]
  exact Prod.ext (aggTree_nil_fst hS hmem) rfl

/-- **The price tree on `(z, K)` is continuous in capital** on the capital set: capital is a
quotient map from the compact set of histories with shock `z`. -/
theorem continuousOn_aggTree (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) (z : Z) (g : List Z) :
    ContinuousOn (fun k => aggTree μ z k g) (Kset μ z) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let F := {ξ : ShockPath Z | (ξ 0).val = z}
  have : CompactSpace F := isCompact_iff_compactSpace.1 (ShockPath.isClosed_fibre z).isCompact
  let q : F → Kset μ z := fun ξ =>
    ⟨capAt μ (ξ : ShockPath Z).toHistory, ⟨(ξ : ShockPath Z).toHistory, ξ.2, rfl⟩⟩
  have hq : Continuous q :=
    ((continuous_seqPrices_history hc []).fst.comp continuous_subtype_val).subtype_mk _
  have hsurj : Function.Surjective q := by
    rintro ⟨k, ω, h0, rfl⟩
    exact ⟨⟨ShockPath.ofHistory ω, h0⟩, rfl⟩
  have hQ := hq.isClosedMap.isQuotientMap hq hsurj
  rw [hQ.continuous_iff]
  refine ((continuous_seqPrices_history hc g).comp continuous_subtype_val).congr fun ξ => ?_
  have h := aggTree_eq hS (ξ : ShockPath Z).toHistory
  rw [show (ξ : ShockPath Z).toHistory 0 = z from ξ.2] at h
  simp only [Function.comp_apply, Set.domRestrict_apply, q]
  rw [h]

theorem continuousOn_lawK (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) (z z' : Z) :
    ContinuousOn (fun k => lawK μ z k z') (Kset μ z) :=
  continuous_fst.comp_continuousOn (continuousOn_aggTree hS hc z [z'])

theorem continuousOn_labourK (hS : KSufficient μ)
    (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory) (z : Z) :
    ContinuousOn (fun k => labourK μ z k) (Kset μ z) :=
  continuous_snd.comp_continuousOn (continuousOn_aggTree hS hc z [])

end KSModel

end KrusellSmith

end LeanEconomics
