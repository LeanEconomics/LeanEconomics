/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationRate
import LeanEconomics.Distribution.Stationary

/-!
# The interest rate as a state variable

Comparative statics in the interest rate can be done by a parametric argument -- prove the
value function continuous in the parameter, then the policy, then the distribution -- or by
putting the rate INTO the state and letting the existing machinery do the work. This file
takes the second route.

The rate never changes, so the operator is block diagonal in it: the transition carries the
rate forward untouched. The `r`-slice of the augmented value function is therefore a fixed
point of the `r`-programme's own Bellman operator, hence equal to its value function; and
Berge, already proved in this library, gives continuity of the augmented policy in the whole
state, which includes the rate.

Two design points.

The rate coordinate is CLAMPED to `[rlo, rhi]`. Without it the reward has no bound above,
since maximum consumption grows with the rate. This is the same clamp-and-prove-inactive
device the model already uses for consumption, and `clampRate_eq` is the "inactive" half.

The clamp inside the reward is STATE-DEPENDENT rather than a constant, even though a constant
would also bound it. That is what makes the slice at a rate in range *equal* to the
`r`-programme rather than merely close to it: every piece of data matches on the nose, so the
two Bellman operators are literally the same and uniqueness of the fixed point finishes. With
a constant clamp the two would differ off the region and the slice lemma would need the
region bridge instead of an equality.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

/-- The rate, clamped to the interval under consideration. -/
noncomputable def clampRate (rlo rhi r : ℝ) : ℝ := min rhi (max rlo r)

theorem continuous_clampRate (rlo rhi : ℝ) : Continuous (clampRate rlo rhi) :=
  continuous_const.min (continuous_const.max continuous_id)

theorem clampRate_mem {rlo rhi : ℝ} (hle : rlo ≤ rhi) (r : ℝ) :
    clampRate rlo rhi r ∈ Icc rlo rhi :=
  ⟨le_min hle (le_max_left _ _), min_le_left _ _⟩

/-- On the interval, the clamp is inactive. -/
theorem clampRate_eq {rlo rhi r : ℝ} (hr : r ∈ Icc rlo rhi) : clampRate rlo rhi r = r := by
  rw [clampRate, max_eq_right hr.1, min_eq_right hr.2]

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z assetCap) (rlo rhi : ℝ)

/-- The augmented state: assets, the interest rate, and the income state. -/
abbrev AugState (_P : IncomeFluctuation Z assetCap) : Type _ := (ℝ × ℝ) × Z

noncomputable def augResources (s : P.AugState) : ℝ :=
  P.income s.2 + (1 + clampRate rlo rhi s.1.2) * max 0 s.1.1

noncomputable def augMaxConsumption (s : P.AugState) : ℝ :=
  P.maxIncome + (1 + clampRate rlo rhi s.1.2) * assetCap

noncomputable def augMaxSaving (s : P.AugState) : ℝ :=
  max 0 (min assetCap (P.augResources rlo rhi s))

noncomputable def augRewardFn (p : P.AugState × ℝ) : EReal :=
  extendBot P.u (min (P.augMaxConsumption rlo rhi p.1) (P.augResources rlo rhi p.1 - p.2))

variable {rlo rhi}

theorem one_add_clampRate_pos (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (r : ℝ) :
    0 < 1 + clampRate rlo rhi r := by
  have := (clampRate_mem hle r).1
  linarith

theorem minIncome_le_augResources (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (s : P.AugState) :
    P.minIncome ≤ P.augResources rlo rhi s := by
  have h1 : 0 ≤ (1 + clampRate rlo rhi s.1.2) * max 0 s.1.1 :=
    mul_nonneg (one_add_clampRate_pos hrlo hle _).le (le_max_left _ _)
  have := P.minIncome_le s.2
  simp only [augResources]; linarith

theorem augResources_pos (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (s : P.AugState) :
    0 < P.augResources rlo rhi s :=
  lt_of_lt_of_le P.minIncome_pos (P.minIncome_le_augResources hrlo hle s)

theorem minIncome_le_augMaxConsumption (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (s : P.AugState) :
    P.minIncome ≤ P.augMaxConsumption rlo rhi s := by
  have h1 : 0 ≤ (1 + clampRate rlo rhi s.1.2) * assetCap :=
    mul_nonneg (one_add_clampRate_pos hrlo hle _).le P.assetCap_nonneg
  simp only [augMaxConsumption]; linarith [P.minIncome_le_maxIncome]

theorem augMaxConsumption_pos (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (s : P.AugState) :
    0 < P.augMaxConsumption rlo rhi s :=
  lt_of_lt_of_le P.minIncome_pos (P.minIncome_le_augMaxConsumption hrlo hle s)

/-- The rate clamp is what bounds the reward above. -/
theorem augMaxConsumption_le (hle : rlo ≤ rhi) (s : P.AugState) :
    P.augMaxConsumption rlo rhi s ≤ P.maxIncome + (1 + rhi) * assetCap := by
  have h1 : clampRate rlo rhi s.1.2 ≤ rhi := (clampRate_mem hle _).2
  have h2 := P.assetCap_nonneg
  simp only [augMaxConsumption]
  nlinarith

variable (rlo rhi)

theorem continuous_augResources : Continuous (P.augResources rlo rhi) :=
  (continuous_of_discreteTopology.comp continuous_snd).add
    (((continuous_const.add
      ((continuous_clampRate rlo rhi).comp (continuous_snd.comp continuous_fst)))).mul
      (continuous_const.max (continuous_fst.comp continuous_fst)))

theorem continuous_augMaxConsumption : Continuous (P.augMaxConsumption rlo rhi) :=
  continuous_const.add
    (((continuous_const.add
      ((continuous_clampRate rlo rhi).comp (continuous_snd.comp continuous_fst)))).mul
      continuous_const)

theorem continuous_augMaxSaving : Continuous (P.augMaxSaving rlo rhi) :=
  continuous_const.max (continuous_const.min (P.continuous_augResources rlo rhi))

theorem continuous_augRewardFn : Continuous (P.augRewardFn rlo rhi) := by
  refine (continuous_extendBot P.continuousOn_u P.tendsto_atBot_u).comp ?_
  exact ((P.continuous_augMaxConsumption rlo rhi).comp continuous_fst).min
    (((P.continuous_augResources rlo rhi).comp continuous_fst).sub continuous_snd)

variable {rlo rhi}

/-- **The augmented programme**: the interest rate carried along as a state that never
changes. -/
noncomputable def toAugmented (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) :
    ExtendedStochasticProgram P.AugState ℝ Z where
  feasible s := Icc 0 (P.augMaxSaving rlo rhi s)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible :=
    upperHemicontinuous_Icc continuous_const (P.continuous_augMaxSaving rlo rhi)
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const (P.continuous_augMaxSaving rlo rhi)
      fun _ => le_max_left _ _
  reward := ⟨P.augRewardFn rlo rhi, P.continuous_augRewardFn rlo rhi⟩
  rewardMax := P.u (P.maxIncome + (1 + rhi) * assetCap)
  reward_le := by
    intro s a _
    simp only [ContinuousMap.coe_mk, augRewardFn]
    rcases le_or_gt (min (P.augMaxConsumption rlo rhi s) (P.augResources rlo rhi s - a)) 0
      with h | h
    · rw [extendBot_of_nonpos h]; exact bot_le
    · rw [extendBot_of_pos h, EReal.coe_le_coe_iff]
      refine P.monotoneOn_u h ?_ (le_trans (min_le_left _ _) (P.augMaxConsumption_le hle s))
      exact lt_of_lt_of_le (P.augMaxConsumption_pos hrlo hle s) (P.augMaxConsumption_le hle s)
  select := ⟨fun _ => 0, continuous_const⟩
  select_mem := fun _ => ⟨le_rfl, le_max_left _ _⟩
  rewardMin := P.u P.minIncome
  le_reward_select := by
    intro s
    simp only [ContinuousMap.coe_mk, augRewardFn]
    have h : P.minIncome
        ≤ min (P.augMaxConsumption rlo rhi s) (P.augResources rlo rhi s - 0) := by
      refine le_min (P.minIncome_le_augMaxConsumption hrlo hle s) ?_
      rw [sub_zero]; exact P.minIncome_le_augResources hrlo hle s
    rw [extendBot_of_pos (lt_of_lt_of_le P.minIncome_pos h), EReal.coe_le_coe_iff]
    exact P.monotoneOn_u P.minIncome_pos (lt_of_lt_of_le P.minIncome_pos h) h
  transition z' := ⟨fun p => ((p.2, p.1.1.2), z'),
    (continuous_snd.prodMk ((continuous_snd.comp continuous_fst).comp continuous_fst)).prodMk
      continuous_const⟩
  prob z' := ⟨fun p => P.transitionMatrix p.1.2 z',
    (continuous_of_discreteTopology (f := fun z => P.transitionMatrix z z')).comp
      (continuous_snd.comp continuous_fst)⟩
  prob_nonneg _ _ := P.transitionMatrix_nonneg _ _
  prob_sum p := P.transitionMatrix_sum _
  discount := P.discount
  discount_lt_one := P.discount_lt_one

/-! ### The slice

At a rate inside the interval the clamp is inactive, so every piece of the augmented
programme's data agrees on the nose with the `r`-programme's. The two Bellman operators are
then literally equal on the slice, and uniqueness of the fixed point does the rest. -/

variable {r : ℝ}

theorem augResources_slice (hr : r ∈ Icc rlo rhi) (hrr : 0 < 1 + r) (t : ℝ × Z) :
    P.augResources rlo rhi ((t.1, r), t.2) = (P.withRate r hrr).resources t := by
  simp only [augResources, resources, clampRate_eq hr]
  rfl

theorem augMaxConsumption_slice (hr : r ∈ Icc rlo rhi) (hrr : 0 < 1 + r) (t : ℝ × Z) :
    P.augMaxConsumption rlo rhi ((t.1, r), t.2) = (P.withRate r hrr).maxConsumption := by
  simp only [augMaxConsumption, maxConsumption, clampRate_eq hr]
  rfl

theorem augMaxSaving_slice (hr : r ∈ Icc rlo rhi) (hrr : 0 < 1 + r) (t : ℝ × Z) :
    P.augMaxSaving rlo rhi ((t.1, r), t.2) = (P.withRate r hrr).maxSaving t := by
  simp only [augMaxSaving, maxSaving, P.augResources_slice hr hrr t]

/-- The slice of a bounded continuous function on the augmented state. -/
noncomputable def sliceAt (w : P.AugState →ᵇ ℝ) (r : ℝ) : (ℝ × Z) →ᵇ ℝ :=
  w.compContinuous ⟨fun t => ((t.1, r), t.2),
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd⟩

@[simp]
theorem sliceAt_apply (w : P.AugState →ᵇ ℝ) (r : ℝ) (t : ℝ × Z) :
    P.sliceAt w r t = w ((t.1, r), t.2) := rfl

/-- The feasible sets agree on the slice. -/
theorem feasible_aug_eq (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (hr : r ∈ Icc rlo rhi)
    (hrr : 0 < 1 + r) (t : ℝ × Z) :
    (P.withRate r hrr).toExtended.feasible t
      = (P.toAugmented hrlo hle).feasible ((t.1, r), t.2) := by
  change Icc 0 ((P.withRate r hrr).maxSaving t) = Icc 0 (P.augMaxSaving rlo rhi ((t.1, r), t.2))
  rw [P.augMaxSaving_slice hr hrr t]

/-- The objectives agree on the slice, for ANY continuation value. -/
theorem objectiveE_aug_eq (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (hr : r ∈ Icc rlo rhi)
    (hrr : 0 < 1 + r) (W : P.AugState →ᵇ ℝ) (t : ℝ × Z) (a : ℝ) :
    (P.withRate r hrr).toExtended.objectiveE (P.sliceAt W r) t a
      = (P.toAugmented hrlo hle).objectiveE W ((t.1, r), t.2) a := by
  have hrew : (P.withRate r hrr).toExtended.reward (t, a)
      = (P.toAugmented hrlo hle).reward (((t.1, r), t.2), a) := by
    change extendBot P.u (min ((P.withRate r hrr).maxConsumption)
          ((P.withRate r hrr).resources t - a))
      = extendBot P.u (min (P.augMaxConsumption rlo rhi ((t.1, r), t.2))
          (P.augResources rlo rhi ((t.1, r), t.2) - a))
    rw [P.augMaxConsumption_slice hr hrr t, P.augResources_slice hr hrr t]
  have hexp : (P.withRate r hrr).toExtended.expect (P.sliceAt W r) (t, a)
      = (P.toAugmented hrlo hle).expect W (((t.1, r), t.2), a) := by
    simp only [ExtendedStochasticProgram.expect]
    rfl
  simp only [ExtendedStochasticProgram.objectiveE, hrew, hexp]
  rfl

/-- **The slice of the augmented value function is the value function at that rate.** -/
theorem sliceAt_valueFunction (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (hr : r ∈ Icc rlo rhi)
    (hrr : 0 < 1 + r) :
    P.sliceAt (P.toAugmented hrlo hle).valueFunction r
      = (P.withRate r hrr).toExtended.valueFunction := by
  set W := (P.toAugmented hrlo hle).valueFunction with hW
  set w := P.sliceAt W r with hw
  -- the two programmes have the same feasible set and the same objective on the slice
  have hfeas := P.feasible_aug_eq hrlo hle hr hrr
  have hobj := fun (t : ℝ × Z) (a : ℝ) => P.objectiveE_aug_eq hrlo hle hr hrr W t a
  -- so `w` is a fixed point of the `r`-operator
  refine ((P.withRate r hrr).toExtended.eq_valueFunction ?_).symm ▸ rfl
  refine BoundedContinuousFunction.ext fun t => ?_
  have hfix : W ((t.1, r), t.2)
      = (P.toAugmented hrlo hle).bellmanFn W ((t.1, r), t.2) := by
    rw [hW, ← (P.toAugmented hrlo hle).bellman_apply,
      (P.toAugmented hrlo hle).bellman_valueFunction]
  change (P.withRate r hrr).toExtended.bellmanFn w t = w t
  rw [hw, sliceAt_apply, hfix]
  simp only [ExtendedStochasticProgram.bellmanFn, ExtendedStochasticProgram.maxE, maxValueE]
  rw [hfeas t]
  exact congrArg EReal.toReal (congrArg sSup (Set.image_congr fun a _ => hobj t a))

/-! ### The transfer

Uniqueness of the maximiser is IMPORTED from the slice rather than reproved: since the two
objectives and the two feasible sets coincide, the augmented argmax at `((a, r), z)` is the
`r`-programme's argmax at `(a, z)`, which is already known to be a singleton. So the whole
concavity and strict-concavity chain is reused rather than redone for the augmented state,
which is the reason this route was worth taking. -/

noncomputable def augPolicy (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (x : P.AugState) : ℝ :=
  Classical.choose ((P.toAugmented hrlo hle).exists_optimal_action
    (P.toAugmented hrlo hle).valueFunction x)

theorem augPolicy_mem (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (x : P.AugState) :
    P.augPolicy hrlo hle x ∈ (P.toAugmented hrlo hle).feasible x :=
  (Classical.choose_spec ((P.toAugmented hrlo hle).exists_optimal_action
    (P.toAugmented hrlo hle).valueFunction x)).1

theorem augPolicy_optimal (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (x : P.AugState) :
    (P.toAugmented hrlo hle).objectiveE (P.toAugmented hrlo hle).valueFunction x
        (P.augPolicy hrlo hle x)
      = (((P.toAugmented hrlo hle).bellmanFn (P.toAugmented hrlo hle).valueFunction x : ℝ) :
        EReal) :=
  (Classical.choose_spec ((P.toAugmented hrlo hle).exists_optimal_action
    (P.toAugmented hrlo hle).valueFunction x)).2

theorem augPolicy_mem_argmax (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (x : P.AugState) :
    P.augPolicy hrlo hle x ∈ argmax ((P.toAugmented hrlo hle).objectiveE
      (P.toAugmented hrlo hle).valueFunction) (P.toAugmented hrlo hle).feasible x := by
  refine ⟨P.augPolicy_mem hrlo hle x, isMaxOn_iff.mpr fun b hb => ?_⟩
  rw [P.augPolicy_optimal hrlo hle x]
  exact (P.toAugmented hrlo hle).le_bellmanFn _ hb

/-- **The augmented argmax is the sliced programme's policy.** -/
theorem argmax_aug_eq_singleton (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (hr : r ∈ Icc rlo rhi)
    (hrr : 0 < 1 + r) {t : ℝ × Z} (ht : t.1 ∈ Icc 0 assetCap) :
    argmax ((P.toAugmented hrlo hle).objectiveE (P.toAugmented hrlo hle).valueFunction)
        (P.toAugmented hrlo hle).feasible ((t.1, r), t.2)
      = {(P.withRate r hrr).policy t} := by
  rw [← (P.withRate r hrr).argmax_eq_singleton ht]
  have hobj : ∀ a, (P.withRate r hrr).toExtended.objectiveE
        (P.withRate r hrr).toExtended.valueFunction t a
      = (P.toAugmented hrlo hle).objectiveE (P.toAugmented hrlo hle).valueFunction
        ((t.1, r), t.2) a := by
    intro a
    rw [← P.sliceAt_valueFunction hrlo hle hr hrr]
    exact P.objectiveE_aug_eq hrlo hle hr hrr _ t a
  have heq : (P.toAugmented hrlo hle).objectiveE (P.toAugmented hrlo hle).valueFunction
        ((t.1, r), t.2)
      = (P.withRate r hrr).toExtended.objectiveE
        (P.withRate r hrr).toExtended.valueFunction t := (funext hobj).symm
  have hfe := P.feasible_aug_eq hrlo hle hr hrr t
  simp only [argmax, heq, ← hfe]

theorem augPolicy_eq (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (hr : r ∈ Icc rlo rhi)
    (hrr : 0 < 1 + r) {t : ℝ × Z} (ht : t.1 ∈ Icc 0 assetCap) :
    P.augPolicy hrlo hle ((t.1, r), t.2) = (P.withRate r hrr).policy t := by
  have hmem := P.augPolicy_mem_argmax hrlo hle ((t.1, r), t.2)
  rw [P.argmax_aug_eq_singleton hrlo hle hr hrr ht] at hmem
  exact hmem

/-- **The policy is continuous in the state AND the interest rate, jointly.** -/
theorem continuousOn_augPolicy (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) :
    ContinuousOn (P.augPolicy hrlo hle)
      {x : P.AugState | x.1.1 ∈ Icc 0 assetCap ∧ x.1.2 ∈ Icc rlo rhi} := by
  refine continuousOn_of_upperHemicontinuous_singleton
    ((P.toAugmented hrlo hle).upperHemicontinuous_argmax
      (P.toAugmented hrlo hle).valueFunction) fun x hx => ?_
  have hrr : 0 < 1 + x.1.2 := by have := hx.2.1; linarith
  have h := P.argmax_aug_eq_singleton hrlo hle hx.2 hrr (t := (x.1.1, x.2)) hx.1
  rw [h, P.augPolicy_eq hrlo hle hx.2 hrr (t := (x.1.1, x.2)) hx.1]

/-! ### Uniform convergence of the policy

Joint continuity plus compactness gives uniform continuity, and that is what resolves the
pointwise-versus-uniform difficulty recorded with `abs_markovFn_sub_le`: a parametric
argument would have produced continuity in `r` for each fixed state and then owed an
equicontinuity argument to make it uniform. Here uniformity is free, because a continuous
function on a compact set is uniformly continuous.

As with the continuation value, `Z` carries no metric, so `(ℝ × ℝ) × Z` is not a metric space
and the modulus is taken in `(assets, rate)` for each income state, then combined over the
finitely many states. -/

set_option linter.unusedFintypeInType false in
/-- **The policy converges uniformly as the interest rate moves.** -/
theorem exists_policy_modulus (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ (z : Z), ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi,
      |r - r'| < η →
      |P.augPolicy hrlo hle ((a, r), z) - P.augPolicy hrlo hle ((a, r'), z)| < ε := by
  classical
  have hslice : ∀ z : Z, ∃ η > 0, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ r ∈ Icc rlo rhi,
      ∀ r' ∈ Icc rlo rhi, |r - r'| < η →
      |P.augPolicy hrlo hle ((a, r), z) - P.augPolicy hrlo hle ((a, r'), z)| < ε := by
    intro z
    set K : Set (ℝ × ℝ) := Icc 0 assetCap ×ˢ Icc rlo rhi with hK
    have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
    have hmaps : MapsTo (fun p : ℝ × ℝ => ((p, z) : P.AugState)) K
        {x : P.AugState | x.1.1 ∈ Icc 0 assetCap ∧ x.1.2 ∈ Icc rlo rhi} :=
      fun p hp => ⟨hp.1, hp.2⟩
    have hcont : ContinuousOn (fun p : ℝ × ℝ => P.augPolicy hrlo hle (p, z)) K :=
      (P.continuousOn_augPolicy hrlo hle).comp
        (continuous_id.prodMk continuous_const).continuousOn hmaps
    have huc := hKc.uniformContinuousOn_of_continuous hcont
    obtain ⟨η, hη, hspec⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
    refine ⟨η, hη, fun a ha r hr r' hr' hd => ?_⟩
    have hmem : ((a, r) : ℝ × ℝ) ∈ K := ⟨ha, hr⟩
    have hmem' : ((a, r') : ℝ × ℝ) ∈ K := ⟨ha, hr'⟩
    have hdist : dist ((a, r) : ℝ × ℝ) ((a, r') : ℝ × ℝ) < η := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      simpa using hd
    have := hspec _ hmem _ hmem' hdist
    rwa [Real.dist_eq] at this
  choose η hη hspec using hslice
  have hne : (Finset.univ : Finset Z).Nonempty := ⟨Classical.ofNonempty, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne η, (Finset.lt_inf'_iff _).2 fun z _ => hη z, ?_⟩
  exact fun z a ha r hr r' hr' hd =>
    hspec z a ha r hr r' hr' (lt_of_lt_of_le hd (Finset.inf'_le _ (Finset.mem_univ z)))

/-- The same, stated for the policies of the sliced programmes. -/
theorem exists_policy_modulus_withRate (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η > 0, ∀ (z : Z), ∀ a ∈ Icc (0 : ℝ) assetCap,
      ∀ (r : ℝ) (_hr : r ∈ Icc rlo rhi) (hrr : 0 < 1 + r),
      ∀ (r' : ℝ) (_hr' : r' ∈ Icc rlo rhi) (hrr' : 0 < 1 + r'),
      |r - r'| < η →
      |(P.withRate r hrr).policy (a, z) - (P.withRate r' hrr').policy (a, z)| < ε := by
  obtain ⟨η, hη, hspec⟩ := P.exists_policy_modulus hrlo hle hε
  refine ⟨η, hη, fun z a ha r _hr hrr r' _hr' hrr' hd => ?_⟩
  rw [← P.augPolicy_eq hrlo hle _hr hrr (t := (a, z)) ha,
    ← P.augPolicy_eq hrlo hle _hr' hrr' (t := (a, z)) ha]
  exact hspec z a ha r _hr r' _hr' hd

/-! ### The Markov operator converges uniformly

Feeding the policy modulus through `abs_markovFn_sub_le`. The two successor states differ
only in their asset coordinate -- the income state is the same draw -- so a modulus for the
test function in that coordinate is all that is needed. -/

set_option linter.unusedFintypeInType false in
/-- A modulus for a test function in the asset coordinate, uniform over income states. -/
theorem exists_modulus_state (h : P.State →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ (z' : Z) (x y : ↥(Icc (0 : ℝ) assetCap)), |(x : ℝ) - (y : ℝ)| < η →
      |h (x, z') - h (y, z')| ≤ ε := by
  classical
  have : CompactSpace ↥(Icc (0 : ℝ) assetCap) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hslice : ∀ z' : Z, ∃ η > 0, ∀ x y : ↥(Icc (0 : ℝ) assetCap),
      |(x : ℝ) - (y : ℝ)| < η → |h (x, z') - h (y, z')| ≤ ε := by
    intro z'
    have hcont : Continuous fun x : ↥(Icc (0 : ℝ) assetCap) => h (x, z') :=
      h.continuous.comp (continuous_id.prodMk continuous_const)
    have huc : UniformContinuous fun x : ↥(Icc (0 : ℝ) assetCap) => h (x, z') :=
      CompactSpace.uniformContinuous_of_continuous hcont
    obtain ⟨η, hη, hspec⟩ := Metric.uniformContinuous_iff.mp huc ε hε
    refine ⟨η, hη, fun x y hxy => ?_⟩
    have hd : dist x y < η := by rw [Subtype.dist_eq, Real.dist_eq]; exact hxy
    have := hspec hd
    rw [Real.dist_eq] at this
    exact this.le
  choose η hη hspec using hslice
  have hne : (Finset.univ : Finset Z).Nonempty := ⟨Classical.ofNonempty, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne η, (Finset.lt_inf'_iff _).2 fun z' _ => hη z', ?_⟩
  exact fun z' x y hxy =>
    hspec z' x y (lt_of_lt_of_le hxy (Finset.inf'_le _ (Finset.mem_univ z')))

/-- **The Markov operator converges uniformly as the interest rate moves.** This is the
statement the distribution's closed-graph argument consumes. -/
theorem exists_markovFn_modulus (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (h : P.State →ᵇ ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ (r : ℝ) (_hr : r ∈ Icc rlo rhi) (hrr : 0 < 1 + r)
      (r' : ℝ) (_hr' : r' ∈ Icc rlo rhi) (hrr' : 0 < 1 + r'),
      |r - r'| < η → ∀ s : P.State,
        |(P.withRate r hrr).markovFn h s - (P.withRate r' hrr').markovFn h s| ≤ ε := by
  obtain ⟨ηh, hηh, hh⟩ := P.exists_modulus_state h hε
  obtain ⟨η, hη, hpol⟩ := P.exists_policy_modulus_withRate hrlo hle hηh
  refine ⟨η, hη, fun r hr hrr r' hr' hrr' hd s => ?_⟩
  refine abs_markovFn_sub_le (A := P.withRate r hrr) (B := P.withRate r' hrr') rfl h
    (fun s z' => ?_) s
  -- the successor states differ only in the asset coordinate
  have hmem : ((s.1 : ℝ)) ∈ Icc (0 : ℝ) assetCap := s.1.2
  have hgap := hpol s.2 (s.1 : ℝ) hmem r hr hrr r' hr' hrr' hd
  exact hh z' _ _ hgap

/-! ### The closed-graph estimate

A distribution stationary for a NEARBY rate is almost stationary for the reference rate, with
an error controlled uniformly. This is the estimate the closed-graph argument runs on: the
error term below involves only the two fixed bounded continuous functions `markovOp h` and
`h`, so it survives passage to a weak limit, and uniqueness of the stationary distribution
then pins the limit down. -/

variable [MeasurableSpace Z] [BorelSpace Z]

theorem exists_almost_stationary_modulus (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi)
    {r₀ : ℝ} (hr₀ : r₀ ∈ Icc rlo rhi) (hrr₀ : 0 < 1 + r₀) (h : P.State →ᵇ ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ (r : ℝ) (_hr : r ∈ Icc rlo rhi) (hrr : 0 < 1 + r), |r - r₀| < η →
      ∀ ν : ProbabilityMeasure P.State, (P.withRate r hrr).IsStationary ν →
        |∫ s, (P.withRate r₀ hrr₀).markovOp h s ∂(ν : Measure P.State)
          - ∫ s, h s ∂(ν : Measure P.State)| ≤ ε := by
  obtain ⟨η, hη, hmod⟩ := P.exists_markovFn_modulus hrlo hle h hε
  refine ⟨η, hη, fun r hr hrr hd ν hstat => ?_⟩
  set A := P.withRate r₀ hrr₀ with hA
  set B := P.withRate r hrr with hB
  -- stationarity at the nearby rate
  have hpush : B.push (ν : Measure P.State) = (ν : Measure P.State) :=
    congrArg (fun x : ProbabilityMeasure P.State => (x : Measure P.State)) hstat
  have hstat' : ∫ s, h s ∂(ν : Measure P.State)
      = ∫ s, B.markovOp h s ∂(ν : Measure P.State) := by
    have hp := B.integral_push (ν : Measure P.State) h
    rwa [hpush] at hp
  rw [hstat']
  -- the two operators are uniformly close
  have hptwise : ∀ s : P.State, |A.markovOp h s - B.markovOp h s| ≤ ε := fun s => by
    have hthis := hmod r₀ hr₀ hrr₀ r hr hrr (by rw [abs_sub_comm]; exact hd) s
    rw [IncomeFluctuation.markovOp_apply, IncomeFluctuation.markovOp_apply]
    exact hthis
  have hnorm : ‖A.markovOp h - B.markovOp h‖ ≤ ε :=
    (BoundedContinuousFunction.norm_le hε.le).mpr fun s => by
      rw [Real.norm_eq_abs]
      simpa only [BoundedContinuousFunction.coe_sub, Pi.sub_apply] using hptwise s
  -- so the integrals are close
  have hsub : ∫ s, (A.markovOp h - B.markovOp h) s ∂(ν : Measure P.State)
      = ∫ s, A.markovOp h s ∂(ν : Measure P.State)
        - ∫ s, B.markovOp h s ∂(ν : Measure P.State) := by
    simpa only [BoundedContinuousFunction.coe_sub, Pi.sub_apply] using
      integral_sub ((A.markovOp h).integrable _) ((B.markovOp h).integrable _)
  rw [← hsub]
  exact le_trans (A.abs_integral_le _ _) hnorm

end IncomeFluctuation

end LeanEconomics
