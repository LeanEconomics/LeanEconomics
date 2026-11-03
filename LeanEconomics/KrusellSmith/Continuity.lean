/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Household
import LeanEconomics.DynamicProgramming.Weighted
import LeanEconomics.DynamicProgramming.Parametric
import Mathlib.Basic.Real.Pointwise
import Mathlib.Data.Set.Finite.List
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The household's value moves continuously with the path of capital

The fixed-point argument for sequential equilibrium needs the household's response to depend
continuously on the path `K` of aggregate capital, in the **product topology** on paths: a path
is close to another when it is close at finitely many nodes. In the supremum norm on value
functions this fails, since paths close at finitely many nodes can be far apart deep in the
tree. Discounting is what rescues it, and this module makes that precise.

**Depth weights.** Fix `ρ` with `β < ρ < 1` and weigh a state at depth `t` (a node with `t`
shocks drawn) by `w = ρ^{-t}`. The household's problem is then a
`LeanEconomics.WeightedDynamicProgram` (`weightedHousehold`): tomorrow is one level deeper, so
the drift condition holds with modulus `β/ρ < 1`. Its conjugated Bellman operator carries the
unweighted one at the depth-scaled function `ρ^t V` to `ρ^t (T V)` (`weighted_bellman_scale`),
so its fixed point is the depth-scaled value function (`normalisedValue_eq_scale`), and the two
problems have the same value (`weightedHousehold_valueFunction`).

**Continuity** (`continuousAt_normalisedValue`). By `continuousAt_fixedPoint` it is enough that
the conjugated operator, applied to the fixed point at `K₀`, moves continuously with `K` in the
supremum norm. Below depth `T` every value is at most `ρ^T C` whatever the path, so those states
contribute less than `ε`. Above depth `T` there are finitely many nodes, at each of which the
operator depends on the path only through capital at that node, continuously by Berge's maximum
theorem and uniformly over assets by compactness.
-/

open Set Filter Topology BoundedContinuousFunction Metric
open scoped NNReal Pointwise

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z) (m₀ : E → ℝ)

/-- The depth of a state: the number of shocks drawn at its node. -/
def depth (s : M.State) : ℕ := s.2.node.length

theorem continuous_pow_depth (ρ : ℝ) : Continuous fun s : M.State => ρ ^ M.depth s :=
  (continuous_of_discreteTopology (f := fun l : Label Z E => ρ ^ l.node.length)).comp
    continuous_snd

/-- Scaling by depth: `ρ^t v` at a state of depth `t`. For `0 ≤ ρ ≤ 1` it is bounded by `v`. -/
noncomputable def scale {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (v : M.State →ᵇ ℝ) : M.State →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun s => ρ ^ M.depth s * v s)
    ((M.continuous_pow_depth ρ).mul v.continuous) ‖v‖ fun s => by
      rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hρ0 _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hρ0 hρ1) |>.trans
        (v.norm_coe_le_norm s)

@[simp] theorem scale_apply {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (v : M.State →ᵇ ℝ)
    (s : M.State) : M.scale hρ0 hρ1 v s = ρ ^ M.depth s * v s := rfl

variable (K : List Z → ℝ) {ρ : ℝ} (hρ : M.discount < ρ) (hρ1 : ρ < 1)
include hρ

theorem rho_pos : 0 < ρ := M.discount_pos.trans hρ

/-- The reward divided by the depth weight `ρ^{-t}`. -/
noncomputable def rewardOverWeight : (M.State × ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => (M.household z₀ m₀ K).reward p * ρ ^ M.depth p.1)
    ((M.household z₀ m₀ K).reward.continuous.mul
      ((M.continuous_pow_depth ρ).comp continuous_fst))
    ‖(M.household z₀ m₀ K).reward‖ fun p => by
      rw [norm_mul, Real.norm_of_nonneg (pow_nonneg (M.rho_pos hρ).le _)]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (M.rho_pos hρ).le hρ1.le)
        |>.trans' (mul_le_mul_of_nonneg_right ((M.household z₀ m₀ K).reward.norm_coe_le_norm p)
          (pow_nonneg (M.rho_pos hρ).le _))

omit hρ in
theorem depth_transition (ze : Z × E) (p : M.State × ℝ) :
    M.depth ((M.household z₀ m₀ K).transition ze p) = M.depth p.1 + 1 := rfl

/-- **The household's problem with depth weights** `w = ρ^{-t}`: the drift condition holds with
modulus `β/ρ`, because tomorrow is one level deeper. -/
noncomputable def weightedHousehold : WeightedDynamicProgram M.State ℝ (Z × E) where
  feasible := (M.household z₀ m₀ K).feasible
  isCompact_feasible := (M.household z₀ m₀ K).isCompact_feasible
  feasible_nonempty := (M.household z₀ m₀ K).feasible_nonempty
  upperHemicontinuous_feasible := (M.household z₀ m₀ K).upperHemicontinuous_feasible
  lowerHemicontinuous_feasible := (M.household z₀ m₀ K).lowerHemicontinuous_feasible
  w := ⟨fun s => ρ⁻¹ ^ M.depth s, M.continuous_pow_depth ρ⁻¹⟩
  one_le_w s := one_le_pow₀ (one_le_inv₀ (M.rho_pos hρ) |>.2 hρ1.le)
  rewardOverWeight := M.rewardOverWeight z₀ m₀ K hρ hρ1
  transition := (M.household z₀ m₀ K).transition
  prob := (M.household z₀ m₀ K).prob
  prob_nonneg := (M.household z₀ m₀ K).prob_nonneg
  discount := (M.household z₀ m₀ K).discount
  modulus := ⟨M.discount / ρ, div_nonneg M.discount_pos.le (M.rho_pos hρ).le⟩
  modulus_lt_one := by
    change M.discount / ρ < 1
    rw [div_lt_one (M.rho_pos hρ)]
    exact hρ
  drift s a _ := by
    change M.discount * ∑ ze, (M.household z₀ m₀ K).prob ze (s, a)
        * ρ⁻¹ ^ M.depth ((M.household z₀ m₀ K).transition ze (s, a))
      ≤ M.discount / ρ * ρ⁻¹ ^ M.depth s
    simp only [M.depth_transition, pow_succ, ← mul_assoc, ← Finset.sum_mul,
      (M.household z₀ m₀ K).prob_sum, one_mul]
    rw [div_eq_mul_inv]
    linarith [le_refl (M.discount * ρ⁻¹ ^ M.depth s * ρ⁻¹)]

/-- **The weighted operator at a depth-scaled function is the depth-scaled unweighted
operator.** At depth `t` the weighted objective is `ρ^t` times the unweighted one, because the
continuation sits one level deeper and its weight cancels against `ρ^{t+1}`. -/
theorem weighted_bellman_scale (v : M.State →ᵇ ℝ) :
    (M.weightedHousehold z₀ m₀ K hρ hρ1).bellman (M.scale (M.rho_pos hρ).le hρ1.le v)
      = M.scale (M.rho_pos hρ).le hρ1.le ((M.household z₀ m₀ K).bellman v) := by
  ext s
  have hρ0 := M.rho_pos hρ
  have hobj : ∀ a, (M.weightedHousehold z₀ m₀ K hρ hρ1).objective
      (M.scale hρ0.le hρ1.le v) s a
      = ρ ^ M.depth s * (M.household z₀ m₀ K).objective v s a := by
    intro a
    simp only [WeightedDynamicProgram.objective, WeightedDynamicProgram.expectation,
      StochasticDynamicProgram.objective, StochasticDynamicProgram.expectation]
    change (M.household z₀ m₀ K).reward (s, a) * ρ ^ M.depth s
        + (M.discount * ∑ ze, (M.household z₀ m₀ K).prob ze (s, a)
            * ρ⁻¹ ^ M.depth ((M.household z₀ m₀ K).transition ze (s, a))
            * (ρ ^ M.depth ((M.household z₀ m₀ K).transition ze (s, a))
              * v ((M.household z₀ m₀ K).transition ze (s, a)))) / ρ⁻¹ ^ M.depth s
      = ρ ^ M.depth s * ((M.household z₀ m₀ K).reward (s, a)
          + M.discount * ∑ ze, (M.household z₀ m₀ K).prob ze (s, a)
            * v ((M.household z₀ m₀ K).transition ze (s, a)))
    have hcancel : ∀ ze, (M.household z₀ m₀ K).prob ze (s, a)
        * ρ⁻¹ ^ M.depth ((M.household z₀ m₀ K).transition ze (s, a))
        * (ρ ^ M.depth ((M.household z₀ m₀ K).transition ze (s, a))
          * v ((M.household z₀ m₀ K).transition ze (s, a)))
        = (M.household z₀ m₀ K).prob ze (s, a) * v ((M.household z₀ m₀ K).transition ze (s, a))
        := by
      intro ze
      rw [inv_pow]
      field_simp
    rw [Finset.sum_congr rfl fun ze _ => hcancel ze]
    simp only [inv_pow, div_inv_eq_mul]
    ring
  simp only [WeightedDynamicProgram.bellman_apply, StochasticDynamicProgram.bellman_apply,
    scale_apply, maxValue]
  have himg : (M.weightedHousehold z₀ m₀ K hρ hρ1).objective (M.scale hρ0.le hρ1.le v) s ''
        (M.weightedHousehold z₀ m₀ K hρ hρ1).feasible s
      = ρ ^ M.depth s • ((M.household z₀ m₀ K).objective v s ''
          (M.household z₀ m₀ K).feasible s) := by
    rw [← Set.image_smul, Set.image_image]
    exact Set.image_congr fun a _ => by rw [hobj, smul_eq_mul]
  rw [himg, Real.sSup_smul_of_nonneg (pow_nonneg hρ0.le _), smul_eq_mul]

/-- The fixed point of the weighted operator is the depth-scaled value function. -/
theorem normalisedValue_eq_scale :
    (M.weightedHousehold z₀ m₀ K hρ hρ1).normalisedValue
      = M.scale (M.rho_pos hρ).le hρ1.le (M.household z₀ m₀ K).valueFunction := by
  symm
  refine (M.weightedHousehold z₀ m₀ K hρ hρ1).eq_normalisedValue ?_
  rw [M.weighted_bellman_scale z₀ m₀ K hρ hρ1, (M.household z₀ m₀ K).bellman_valueFunction]

/-- The weighted and unweighted problems have the same value function. -/
theorem weightedHousehold_valueFunction (s : M.State) :
    (M.weightedHousehold z₀ m₀ K hρ hρ1).valueFunction s
      = (M.household z₀ m₀ K).valueFunction s := by
  have hρ0 := M.rho_pos hρ
  simp only [WeightedDynamicProgram.valueFunction, M.normalisedValue_eq_scale z₀ m₀ K hρ hρ1,
    scale_apply]
  change ρ ^ M.depth s * _ * ρ⁻¹ ^ M.depth s = _
  rw [inv_pow, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hρ0.ne'), one_mul]

omit hρ

/-! ### One node at a time -/

/-- Cash on hand at node `h` in idiosyncratic state `e`, as a function of assets and of capital
`k` at that node. -/
noncomputable def nodeCash (e : E) (h : List Z) (x : ↥(Icc (0 : ℝ) M.assetCap) × ℝ) : ℝ :=
  M.grossReturn (shockAt z₀ h) x.2 (M.labour z₀ m₀ h) * x.1
    + M.wage (shockAt z₀ h) x.2 (M.labour z₀ m₀ h) * M.efficiency e

/-- The feasible savings at node `h`, as a function of assets and of capital at that node. -/
def nodeFeasible (e : E) (h : List Z) (x : ↥(Icc (0 : ℝ) M.assetCap) × ℝ) : Set ℝ :=
  Icc 0 (min M.assetCap (M.nodeCash z₀ m₀ e h x))

/-- The household's objective at node `h` with continuation value `v`, as a function of assets
and of capital at that node. -/
noncomputable def nodeObjective (v : M.State →ᵇ ℝ) (e : E) (h : List Z)
    (x : ↥(Icc (0 : ℝ) M.assetCap) × ℝ) (a' : ℝ) : ℝ :=
  M.utility (max 0 (min M.maxCash (M.nodeCash z₀ m₀ e h x - a')))
    + M.discount * ∑ ze : Z × E, M.aggProb (shockAt z₀ h) ze.1
        * M.idioProb (shockAt z₀ h) ze.1 e ze.2 * v (M.clampAssets a', ⟨ze.2, ze.1 :: h⟩)

/-- **At a node, the Bellman operator depends on the path only through capital at that node.** -/
theorem bellman_eq_nodeMax (v : M.State →ᵇ ℝ) (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E)
    (h : List Z) :
    (M.household z₀ m₀ K).bellman v (a, ⟨e, h⟩)
      = maxValue (M.nodeObjective z₀ m₀ v e h) (M.nodeFeasible z₀ m₀ e h) (a, K h) := rfl

theorem continuous_nodeCash (e : E) (h : List Z) : Continuous (M.nodeCash z₀ m₀ e h) := by
  have hR : Continuous fun x : ↥(Icc (0 : ℝ) M.assetCap) × ℝ =>
      M.grossReturn (shockAt z₀ h) x.2 (M.labour z₀ m₀ h) :=
    (M.continuous_grossReturn _).comp (continuous_snd.prodMk continuous_const)
  have hw : Continuous fun x : ↥(Icc (0 : ℝ) M.assetCap) × ℝ =>
      M.wage (shockAt z₀ h) x.2 (M.labour z₀ m₀ h) :=
    (M.continuous_wage _).comp (continuous_snd.prodMk continuous_const)
  exact (hR.mul (continuous_subtype_val.comp continuous_fst)).add (hw.mul continuous_const)

theorem nodeCash_nonneg (e : E) (h : List Z) (x : ↥(Icc (0 : ℝ) M.assetCap) × ℝ) :
    0 ≤ M.nodeCash z₀ m₀ e h x :=
  add_nonneg (mul_nonneg (M.grossReturn_nonneg _ _ _) x.1.2.1)
    (mul_nonneg (M.wage_nonneg _ _ _) (M.efficiency_nonneg _))

theorem continuous_nodeObjective (v : M.State →ᵇ ℝ) (e : E) (h : List Z) :
    Continuous ↿(M.nodeObjective z₀ m₀ v e h) := by
  have hc : Continuous fun q : (↥(Icc (0 : ℝ) M.assetCap) × ℝ) × ℝ =>
      max 0 (min M.maxCash (M.nodeCash z₀ m₀ e h q.1 - q.2)) :=
    continuous_const.max (continuous_const.min
      (((M.continuous_nodeCash z₀ m₀ e h).comp continuous_fst).sub continuous_snd))
  have hu : Continuous fun q : (↥(Icc (0 : ℝ) M.assetCap) × ℝ) × ℝ =>
      M.utility (max 0 (min M.maxCash (M.nodeCash z₀ m₀ e h q.1 - q.2))) :=
    (M.continuousOn_utility.mono Icc_subset_Ici_self).comp_continuous hc fun q =>
      ⟨le_max_left _ _, max_le_max le_rfl (min_le_left _ _)⟩
  refine hu.add (continuous_const.mul (continuous_finsetSum _ fun ze _ => ?_))
  exact continuous_const.mul (v.continuous.comp
    ((continuous_projIcc.comp continuous_snd).prodMk continuous_const))

theorem continuous_nodeMax (v : M.State →ᵇ ℝ) (e : E) (h : List Z) :
    Continuous (maxValue (M.nodeObjective z₀ m₀ v e h) (M.nodeFeasible z₀ m₀ e h)) := by
  have hg : Continuous fun x => min M.assetCap (M.nodeCash z₀ m₀ e h x) :=
    continuous_const.min (M.continuous_nodeCash z₀ m₀ e h)
  have hg0 : ∀ x, (0 : ℝ) ≤ min M.assetCap (M.nodeCash z₀ m₀ e h x) := fun x =>
    le_min M.assetCap_pos.le (M.nodeCash_nonneg z₀ m₀ e h x)
  exact continuous_maxValue (M.continuous_nodeObjective z₀ m₀ v e h)
    (fun x => nonempty_Icc.2 (hg0 x)) (fun _ => isCompact_Icc)
    (upperHemicontinuous_Icc continuous_const hg) (lowerHemicontinuous_Icc continuous_const hg hg0)

/-- **Uniformly over assets**, the node-level maximum moves little when capital at the node moves
little: assets range over a compact interval. -/
theorem eventually_nodeMax (v : M.State →ᵇ ℝ) (e : E) (h : List Z) (k₀ : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ k in 𝓝 k₀, ∀ a : ↥(Icc (0 : ℝ) M.assetCap),
      dist (maxValue (M.nodeObjective z₀ m₀ v e h) (M.nodeFeasible z₀ m₀ e h) (a, k))
        (maxValue (M.nodeObjective z₀ m₀ v e h) (M.nodeFeasible z₀ m₀ e h) (a, k₀)) < ε := by
  set f : ℝ → ↥(Icc (0 : ℝ) M.assetCap) → ℝ := fun k a =>
    maxValue (M.nodeObjective z₀ m₀ v e h) (M.nodeFeasible z₀ m₀ e h) (a, k) with hf
  have hfc : ContinuousOn (Function.uncurry f) (univ ×ˢ univ) :=
    ((M.continuous_nodeMax z₀ m₀ v e h).comp continuous_swap).continuousOn
  obtain ⟨w, hw, hwf⟩ := isCompact_univ.mem_uniformity_of_prod hfc (mem_univ k₀)
    (dist_mem_uniformity hε)
  rw [nhdsWithin_univ] at hw
  filter_upwards [hw] with k hk a
  exact hwf k hk a (mem_univ a)

include hρ

/-- **The conjugated operator at the fixed point for `K₀` moves continuously with the path**, in
the supremum norm and the product topology. -/
theorem continuousAt_weighted_bellman (K₀ : List Z → ℝ) :
    ContinuousAt (fun K => (M.weightedHousehold z₀ m₀ K hρ hρ1).bellman
      ((M.weightedHousehold z₀ m₀ K₀ hρ hρ1).normalisedValue)) K₀ := by
  have hρ0 := M.rho_pos hρ
  set V₀ := (M.household z₀ m₀ K₀).valueFunction with hV₀
  rw [M.normalisedValue_eq_scale z₀ m₀ K₀ hρ hρ1]
  simp only [M.weighted_bellman_scale z₀ m₀ _ hρ hρ1]
  -- a bound on the unweighted operator that does not depend on the path
  set Rb := M.exists_bound_utility.choose with hRbdef
  have hRb := M.exists_bound_utility.choose_spec
  have hRb0 : 0 ≤ Rb := (norm_nonneg _).trans (hRb 0 ⟨le_rfl, le_max_left _ _⟩)
  set C := Rb + M.discount * ‖V₀‖ with hC
  have hC0 : 0 ≤ C := add_nonneg hRb0 (mul_nonneg M.discount_pos.le (norm_nonneg _))
  have hbound : ∀ K s, |(M.household z₀ m₀ K).bellman V₀ s| ≤ C := by
    intro K s
    have h1 := (M.household z₀ m₀ K).abs_bellmanFn_le V₀ s
    have h2 : ‖(M.household z₀ m₀ K).reward‖ ≤ Rb :=
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le (M.continuous_rewardFn z₀ m₀ K) hRb0
        fun p => hRb _ (M.clampedConsumption_mem z₀ m₀ K p)
    change |(M.household z₀ m₀ K).bellmanFn V₀ s| ≤ _
    refine h1.trans ?_
    change ‖(M.household z₀ m₀ K).reward‖ + M.discount * ‖V₀‖ ≤ Rb + M.discount * ‖V₀‖
    linarith
  rw [Metric.continuousAt_iff']
  intro ε hε
  -- below depth `T` the values are too small to matter
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (4 * (C + 1)) by positivity) hρ1
  -- above depth `T` there are finitely many nodes
  have hfin : (univ ×ˢ {h : List Z | h.length < T} : Set (E × List Z)).Finite :=
    Set.finite_univ.prod (List.finite_length_lt Z T)
  have hev : ∀ᶠ K in 𝓝 K₀, ∀ eh ∈ (univ ×ˢ {h : List Z | h.length < T} : Set (E × List Z)),
      ∀ a : ↥(Icc (0 : ℝ) M.assetCap),
        dist (maxValue (M.nodeObjective z₀ m₀ V₀ eh.1 eh.2) (M.nodeFeasible z₀ m₀ eh.1 eh.2)
            (a, K eh.2))
          (maxValue (M.nodeObjective z₀ m₀ V₀ eh.1 eh.2) (M.nodeFeasible z₀ m₀ eh.1 eh.2)
            (a, K₀ eh.2)) < ε / 2 := by
    refine (eventually_all_finite hfin).2 fun eh _ => ?_
    exact ((continuous_apply eh.2).tendsto K₀).eventually
      (M.eventually_nodeMax z₀ m₀ V₀ eh.1 eh.2 (K₀ eh.2) (half_pos hε))
  filter_upwards [hev] with K hK
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).2 ?_)
    (half_lt_self hε)
  rintro ⟨a, ⟨e, h⟩⟩
  simp only [scale_apply, Real.dist_eq]
  rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hρ0.le _)]
  by_cases hh : h.length < T
  · have h1 := hK (e, h) ⟨mem_univ _, hh⟩ a
    rw [Real.dist_eq] at h1
    rw [M.bellman_eq_nodeMax z₀ m₀ K, M.bellman_eq_nodeMax z₀ m₀ K₀]
    exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hρ0.le hρ1.le)).trans h1.le
  · have hdep : ρ ^ M.depth (a, ⟨e, h⟩) ≤ ρ ^ T :=
      pow_le_pow_of_le_one hρ0.le hρ1.le (not_lt.1 hh)
    have hdiff : |(M.household z₀ m₀ K).bellman V₀ (a, ⟨e, h⟩)
        - (M.household z₀ m₀ K₀).bellman V₀ (a, ⟨e, h⟩)| ≤ 2 * C := by
      refine (abs_sub _ _).trans ?_
      linarith [hbound K (a, ⟨e, h⟩), hbound K₀ (a, ⟨e, h⟩)]
    have hTε : ρ ^ T * (2 * C) ≤ ε / 2 := by
      have h4 : ρ ^ T * (4 * (C + 1)) < ε := by
        rwa [lt_div_iff₀ (by positivity)] at hT
      nlinarith [pow_nonneg hρ0.le T]
    calc ρ ^ M.depth (a, ⟨e, h⟩) * |_| ≤ ρ ^ T * (2 * C) :=
          mul_le_mul hdep hdiff (abs_nonneg _) (pow_nonneg hρ0.le _)
      _ ≤ ε / 2 := hTε

/-- **The depth-scaled value function moves continuously with the path of capital**, in the
supremum norm and the product topology. -/
theorem continuousAt_normalisedValue (K₀ : List Z → ℝ) :
    ContinuousAt (fun K => (M.weightedHousehold z₀ m₀ K hρ hρ1).normalisedValue) K₀ :=
  continuousAt_fixedPoint (K := ⟨M.discount / ρ, div_nonneg M.discount_pos.le (M.rho_pos hρ).le⟩)
    (fun K => (M.weightedHousehold z₀ m₀ K hρ hρ1).blackwell.lipschitzWith)
    (M.weightedHousehold z₀ m₀ K₀ hρ hρ1).modulus_lt_one
    (fun K => (M.weightedHousehold z₀ m₀ K hρ hρ1).bellman_normalisedValue)
    (M.continuousAt_weighted_bellman z₀ m₀ hρ hρ1 K₀)

omit hρ hρ1 in
/-- **The household's value at each state moves continuously with the path of capital**, in the
product topology. -/
theorem continuousAt_valueFunction (K₀ : List Z → ℝ) (s : M.State) :
    ContinuousAt (fun K => (M.household z₀ m₀ K).valueFunction s) K₀ := by
  have hρ : M.discount < (M.discount + 1) / 2 := by linarith [M.discount_lt_one]
  have hρ1 : (M.discount + 1) / 2 < 1 := by linarith [M.discount_lt_one]
  have heq : (fun K => (M.household z₀ m₀ K).valueFunction s)
      = fun K => (M.weightedHousehold z₀ m₀ K hρ hρ1).normalisedValue s
          * ((M.discount + 1) / 2)⁻¹ ^ M.depth s := by
    funext K
    rw [← M.weightedHousehold_valueFunction z₀ m₀ K hρ hρ1 s]
    rfl
  rw [heq]
  exact (((continuous_eval_const s).continuousAt).comp
    (M.continuousAt_normalisedValue z₀ m₀ hρ hρ1 K₀)).mul continuousAt_const

end KSModel

end KrusellSmith

end LeanEconomics
