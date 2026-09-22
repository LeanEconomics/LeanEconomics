/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.Equilibrium
import LeanEconomics.Models.IncomeFluctuationAugmented

/-!
# Capital supply is continuous in the interest rate

The last input the life-cycle equilibrium needs. In the infinite horizon this was a substantial
development, because the stationary distribution itself had to be shown to move continuously with
the rate. Here there is no stationary distribution: capital supply is a finite composition of
finitely many policies, so all that is needed is that each policy moves continuously with the
rate, and then that continuity composes.

## The route

`IncomeFluctuationAugmented` put the interest rate into the state, so that Berge's theorem
delivers continuity in assets and the rate jointly rather than continuity in a parameter. That
file used the device at the fixed point. Everything it needs holds for an arbitrary continuation
(`objectiveE_aug_eq`, `feasible_aug_eq`), so the same device works stage by stage, and here it is
easier: the slice of the augmented Bellman iterate is the iterate of the sliced programme
(`sliceAt_augStageValue`) by a plain induction, with no fixed point to identify.

From there: the augmented argmax at a stage is a singleton because the sliced one is
(`argmax_aug_stage_eq_singleton`, from Carroll--Kimball concavity of the iterates), so the
augmented stage policy is continuous in assets and the rate jointly
(`continuousOn_augStagePolicy`) and agrees with the sliced stage policy
(`augStagePolicy_eq`). The cohort recursion of `Equilibrium` is then run in the augmented state
(`augCohortAssets`), where it is a composition of continuous maps, and reading it at a rate in
range gives capital supply (`augCohortAssets_eq`). The conclusion is
`continuousOn_olgSupply`, and with it existence by the intermediate value theorem
(`exists_olgEquilibrium`).
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap) {rlo rhi r : ℝ}

/-! ### A singleton argmax at any concave continuation -/

/-- **The optimal action against a concave continuation is unique**, so the argmax is the
policy. This is `argmax_eq_singleton` with the value function replaced by any continuation whose
slices are concave, which is what the life-cycle iterates provide. -/
theorem argmax_eq_singleton_of_concaveSlices {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices 0 assetCap v) {t : ℝ × Z} (ht : t.1 ∈ Icc (0 : ℝ) assetCap) :
    argmax (P.toExtended.objectiveE v) P.toExtended.feasible t = {P.policyOf v t} := by
  ext a
  simp only [argmax, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ha, hmax⟩
    refine P.optimal_action_unique_of_concaveSlices hv ht ha (P.policyOf_mem v t) ?_
      (P.policyOf_optimal v t)
    refine le_antisymm (P.toExtended.le_bellmanFn _ ha) ?_
    rw [← P.policyOf_optimal v t]
    exact isMaxOn_iff.mp hmax _ (P.policyOf_mem v t)
  · rintro rfl
    refine ⟨P.policyOf_mem v t, isMaxOn_iff.mpr fun b hb => ?_⟩
    rw [P.policyOf_optimal v t]
    exact P.toExtended.le_bellmanFn _ hb

/-! ### The slice commutes with the Bellman operator -/

/-- **One step of the augmented programme, sliced, is one step of the sliced programme.** The
feasible sets and the objectives agree on the slice, for any continuation. -/
theorem sliceAt_bellman (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (hr : r ∈ Icc rlo rhi)
    (hrr : P.RateOK r) (W : P.AugState →ᵇ ℝ) :
    P.sliceAt ((P.toAugmented hrlo hle).bellman W) r
      = (P.withRate r hrr).toExtended.bellman (P.sliceAt W r) := by
  refine BoundedContinuousFunction.ext fun t => ?_
  rw [sliceAt_apply, (P.toAugmented hrlo hle).bellman_apply,
    (P.withRate r hrr).toExtended.bellman_apply]
  simp only [ExtendedStochasticProgram.bellmanFn, ExtendedStochasticProgram.maxE, maxValueE]
  rw [P.feasible_aug_eq hrlo hle hr hrr t]
  exact congrArg EReal.toReal
    (congrArg sSup (Set.image_congr fun a _ => (P.objectiveE_aug_eq hrlo hle hr hrr W t a).symm))

theorem sliceAt_zero (r : ℝ) : P.sliceAt (0 : P.AugState →ᵇ ℝ) r = 0 := by
  refine BoundedContinuousFunction.ext fun t => ?_
  simp [sliceAt_apply]

/-! ### The augmented stage value and policy -/

/-- The continuation value with `k` periods still to come, in the augmented state. -/
noncomputable def augStageValue (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (k : ℕ) :
    P.AugState →ᵇ ℝ :=
  ((P.toAugmented hrlo hle).bellman)^[k] (0 : P.AugState →ᵇ ℝ)

/-- **The slice of the augmented iterate is the iterate at that rate.** -/
theorem sliceAt_augStageValue (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (hr : r ∈ Icc rlo rhi)
    (hrr : P.RateOK r) (k : ℕ) :
    P.sliceAt (P.augStageValue hrlo hle k) r = (P.withRate r hrr).stageValue k := by
  induction k with
  | zero => exact P.sliceAt_zero r
  | succ k ih =>
    rw [augStageValue, Function.iterate_succ_apply', ← augStageValue,
      P.sliceAt_bellman hrlo hle hr hrr, ih, stageValue_succ]

/-- The saving of a household with `k` periods still to come, in the augmented state. -/
noncomputable def augStagePolicy (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (k : ℕ)
    (x : P.AugState) : ℝ :=
  Classical.choose ((P.toAugmented hrlo hle).exists_optimal_action (P.augStageValue hrlo hle k) x)

theorem augStagePolicy_mem (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (k : ℕ) (x : P.AugState) :
    P.augStagePolicy hrlo hle k x ∈ (P.toAugmented hrlo hle).feasible x :=
  (Classical.choose_spec ((P.toAugmented hrlo hle).exists_optimal_action
    (P.augStageValue hrlo hle k) x)).1

theorem augStagePolicy_optimal (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (k : ℕ) (x : P.AugState) :
    (P.toAugmented hrlo hle).objectiveE (P.augStageValue hrlo hle k) x
        (P.augStagePolicy hrlo hle k x)
      = (((P.toAugmented hrlo hle).bellmanFn (P.augStageValue hrlo hle k) x : ℝ) : EReal) :=
  (Classical.choose_spec ((P.toAugmented hrlo hle).exists_optimal_action
    (P.augStageValue hrlo hle k) x)).2

theorem augStagePolicy_mem_argmax (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (k : ℕ)
    (x : P.AugState) :
    P.augStagePolicy hrlo hle k x ∈ argmax ((P.toAugmented hrlo hle).objectiveE
      (P.augStageValue hrlo hle k)) (P.toAugmented hrlo hle).feasible x := by
  refine ⟨P.augStagePolicy_mem hrlo hle k x, isMaxOn_iff.mpr fun b hb => ?_⟩
  rw [P.augStagePolicy_optimal hrlo hle k x]
  exact (P.toAugmented hrlo hle).le_bellmanFn _ hb

/-- **The augmented argmax at a stage is the sliced stage policy.** -/
theorem argmax_aug_stage_eq_singleton (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi)
    (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) (k : ℕ) {t : ℝ × Z}
    (ht : t.1 ∈ Icc (0 : ℝ) assetCap) :
    argmax ((P.toAugmented hrlo hle).objectiveE (P.augStageValue hrlo hle k))
        (P.toAugmented hrlo hle).feasible ((t.1, r), t.2)
      = {(P.withRate r hrr).stagePolicy k t} := by
  rw [show (P.withRate r hrr).stagePolicy k t
      = (P.withRate r hrr).policyOf ((P.withRate r hrr).stageValue k) t from rfl,
    ← (P.withRate r hrr).argmax_eq_singleton_of_concaveSlices
      ((P.withRate r hrr).concaveSlices_stageValue k) ht]
  have hobj : ∀ a, (P.withRate r hrr).toExtended.objectiveE
        ((P.withRate r hrr).stageValue k) t a
      = (P.toAugmented hrlo hle).objectiveE (P.augStageValue hrlo hle k) ((t.1, r), t.2) a := by
    intro a
    rw [← P.sliceAt_augStageValue hrlo hle hr hrr k]
    exact P.objectiveE_aug_eq hrlo hle hr hrr _ t a
  have heq : (P.toAugmented hrlo hle).objectiveE (P.augStageValue hrlo hle k) ((t.1, r), t.2)
      = (P.withRate r hrr).toExtended.objectiveE ((P.withRate r hrr).stageValue k) t :=
    (funext hobj).symm
  have hfe := P.feasible_aug_eq hrlo hle hr hrr t
  simp only [argmax, heq, ← hfe]

theorem augStagePolicy_eq (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (hr : r ∈ Icc rlo rhi)
    (hrr : P.RateOK r) (k : ℕ) {t : ℝ × Z} (ht : t.1 ∈ Icc (0 : ℝ) assetCap) :
    P.augStagePolicy hrlo hle k ((t.1, r), t.2) = (P.withRate r hrr).stagePolicy k t := by
  have hmem := P.augStagePolicy_mem_argmax hrlo hle k ((t.1, r), t.2)
  rw [P.argmax_aug_stage_eq_singleton hrlo hle hr hrr k ht] at hmem
  exact hmem

/-- **The stage policy is continuous in assets and the interest rate, jointly.** -/
theorem continuousOn_augStagePolicy (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (k : ℕ) :
    ContinuousOn (P.augStagePolicy hrlo hle k)
      {x : P.AugState | x.1.1 ∈ Icc (0 : ℝ) assetCap ∧ x.1.2 ∈ Icc rlo rhi} := by
  refine continuousOn_of_upperHemicontinuous_singleton
    ((P.toAugmented hrlo hle).upperHemicontinuous_argmax (P.augStageValue hrlo hle k))
    fun x hx => ?_
  have hrr : P.RateOK x.1.2 := rateOK_of_floor_zero (by have := hx.2.1; linarith)
  have h := P.argmax_aug_stage_eq_singleton hrlo hle hx.2 hrr k (t := (x.1.1, x.2)) hx.1
  rw [h, P.augStagePolicy_eq hrlo hle hx.2 hrr k (t := (x.1.1, x.2)) hx.1]

/-- The augmented saving stays in the asset region. -/
theorem augStagePolicy_mem_region (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (k : ℕ)
    (x : P.AugState) : P.augStagePolicy hrlo hle k x ∈ Icc (0 : ℝ) assetCap := by
  have h := P.augStagePolicy_mem hrlo hle k x
  change P.augStagePolicy hrlo hle k x ∈ Icc 0 (P.augMaxSaving rlo rhi x) at h
  exact ⟨h.1, h.2.trans (max_le P.assetCap_nonneg (min_le_left _ _))⟩

/-! ### The cohort recursion in the augmented state -/

/-- The expectation of `h` next period, in the augmented state: the rate is carried forward
untouched. -/
noncomputable def augStageStep (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (k : ℕ)
    (h : P.AugState → ℝ) : P.AugState → ℝ :=
  fun x => ∑ z', P.transitionMatrix x.2 z' * h ((P.augStagePolicy hrlo hle k x, x.1.2), z')

/-- The assets a household holds over the rest of its life, in the augmented state. -/
noncomputable def augCohortAssets (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) :
    ℕ → (P.AugState → ℝ)
  | 0 => fun x => x.1.1
  | k + 1 => fun x => x.1.1 + P.augStageStep hrlo hle (k + 1) (augCohortAssets hrlo hle k) x

/-- **Read at a rate in range, the augmented recursion is capital supply at that rate.** -/
theorem augCohortAssets_eq (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (hr : r ∈ Icc rlo rhi)
    (hrr : P.RateOK r) (k : ℕ) {t : ℝ × Z} (ht : t.1 ∈ Icc (0 : ℝ) assetCap) :
    P.augCohortAssets hrlo hle k ((t.1, r), t.2) = (P.withRate r hrr).cohortAssets k t := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [augCohortAssets, cohortAssets_succ]
    refine congrArg (fun y => t.1 + y) ?_
    simp only [augStageStep, stageStep]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [P.augStagePolicy_eq hrlo hle hr hrr (k + 1) ht]
    exact congrArg _ (ih (t := ((P.withRate r hrr).stagePolicy (k + 1) t, z'))
      ((P.withRate r hrr).stagePolicy_mem_region (k + 1) t))

theorem continuousOn_augCohortAssets (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (k : ℕ) :
    ContinuousOn (P.augCohortAssets hrlo hle k)
      {x : P.AugState | x.1.1 ∈ Icc (0 : ℝ) assetCap ∧ x.1.2 ∈ Icc rlo rhi} := by
  induction k with
  | zero => exact (continuous_fst.comp continuous_fst).continuousOn
  | succ k ih =>
    refine ((continuous_fst.comp continuous_fst).continuousOn).add ?_
    refine continuousOn_finsetSum _ fun z' _ => ?_
    refine ContinuousOn.mul
      (((continuous_of_discreteTopology (f := fun w => P.transitionMatrix w z')).comp
        continuous_snd).continuousOn) ?_
    refine ih.comp ?_ ?_
    · exact ((P.continuousOn_augStagePolicy hrlo hle (k + 1)).prodMk
        ((continuous_snd.comp continuous_fst).continuousOn)).prodMk continuousOn_const
    · intro x hx
      exact ⟨P.augStagePolicy_mem_region hrlo hle (k + 1) x, hx.2⟩

/-! ### Capital supply -/

/-- **Capital supply is continuous in the interest rate.** -/
theorem continuousOn_olgSupply (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (K : ℕ) (ν : Z → ℝ) :
    ContinuousOn (fun r => (∑ z, ν z * P.augCohortAssets hrlo hle K ((0, r), z)) / (K + 1))
      (Icc rlo rhi) := by
  refine ContinuousOn.div_const ?_ _
  refine continuousOn_finsetSum _ fun z _ => ?_
  refine continuousOn_const.mul ?_
  refine (P.continuousOn_augCohortAssets hrlo hle K).comp ?_ ?_
  · exact ((continuousOn_const).prodMk continuousOn_id).prodMk continuousOn_const
  · intro r hr
    exact ⟨⟨le_rfl, P.assetCap_nonneg⟩, hr⟩

/-- Capital supply, read at a rate in range, is the life-cycle aggregate of that economy. -/
theorem olgSupply_eq (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (hr : r ∈ Icc rlo rhi)
    (hrr : P.RateOK r) (K : ℕ) (ν : Z → ℝ) :
    (∑ z, ν z * P.augCohortAssets hrlo hle K ((0, r), z)) / (K + 1)
      = (P.withRate r hrr).olgCapital K ν := by
  simp only [olgCapital]
  refine congrArg (fun y => y / ((K : ℝ) + 1)) (Finset.sum_congr rfl fun z _ => ?_)
  exact congrArg _ (P.augCohortAssets_eq hrlo hle hr hrr K (t := (0, z))
    ⟨le_rfl, P.assetCap_nonneg⟩)

/-- **A stationary life-cycle equilibrium exists**: capital supply is continuous, so if it lies
below demand at the bottom of the interval and above it at the top, the two meet. -/
theorem exists_olgEquilibrium (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (K : ℕ) (ν : Z → ℝ)
    {D : ℝ → ℝ} (hD : ContinuousOn D (Icc rlo rhi))
    (hlo : (∑ z, ν z * P.augCohortAssets hrlo hle K ((0, rlo), z)) / (K + 1) ≤ D rlo)
    (hhi : D rhi ≤ (∑ z, ν z * P.augCohortAssets hrlo hle K ((0, rhi), z)) / (K + 1)) :
    ∃ r ∈ Icc rlo rhi,
      (∑ z, ν z * P.augCohortAssets hrlo hle K ((0, r), z)) / (K + 1) = D r := by
  set S : ℝ → ℝ := fun r => (∑ z, ν z * P.augCohortAssets hrlo hle K ((0, r), z)) / (K + 1)
    with hS
  have hcont : ContinuousOn (fun r => S r - D r) (Icc rlo rhi) :=
    (P.continuousOn_olgSupply hrlo hle K ν).sub hD
  have h0 : (S rlo - D rlo) ≤ 0 := by rw [hS]; linarith [hlo]
  have h1 : 0 ≤ (S rhi - D rhi) := by rw [hS]; linarith [hhi]
  obtain ⟨r, hr, hzero⟩ :=
    intermediate_value_Icc hle hcont (by exact ⟨h0, h1⟩ : (0 : ℝ) ∈ Icc (S rlo - D rlo)
      (S rhi - D rhi))
  exact ⟨r, hr, by linarith [hzero]⟩

end IncomeFluctuation

end LeanEconomics
