/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Continuity

/-!
# The household's saving policy: unique, and continuous in assets and the path

The equilibrium map of the existence proof pushes the distribution of households forward by
their saving policy, so the policy must be a function, and a continuous one, of both the
household's assets and the path of aggregate capital.

* `concaveOn_valueFunction`: along a capital path, the value at every node is **concave in
  assets**. The Bellman operator preserves concavity along each label's slice: with prices fixed
  at the node, cash on hand is affine in assets, the cap `min` is concave, utility is concave,
  and the continuation is a nonnegative combination of concave functions. The slice version of
  Blackwell's argument, `Blackwell.forall_concaveOn_valueFunction`, passes it to the limit.
* `optimal_saving_unique`: **the optimal saving is unique**. Two optima with different savings
  have different consumption, and their midpoint does strictly better by strict concavity of
  utility.
* `policy`, `argmax_eq_singleton`: the optimal saving as a function of the path and the state.
* `continuous_policy`: **the policy is jointly continuous** in the path (product topology) and
  the state. This is Berge's argmax half on the parameter space of pairs (path, state), with the
  value function jointly continuous by `continuousAt_normalisedValue` and the continuity of
  evaluation of bounded continuous functions.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z) (m₀ : E → ℝ)

/-! ### Concavity in assets -/

theorem clampAssets_of_mem {a : ℝ} (ha : a ∈ Icc 0 M.assetCap) :
    M.clampAssets a = ⟨a, ha⟩ :=
  projIcc_of_mem _ ha

/-- Cash on hand is affine in assets at a fixed label. -/
theorem cash_clampAssets (K : List Z → ℝ) {a : ℝ} (ha : a ∈ Icc 0 M.assetCap) (l : Label Z E) :
    M.cash z₀ m₀ K (M.clampAssets a, l)
      = M.returnAt z₀ m₀ K l.node * a + M.wageAt z₀ m₀ K l.node * M.efficiency l.idio := by
  simp only [cash, M.clampAssets_of_mem ha]

theorem mem_Icc_of_mem_feasible (K : List Z → ℝ) {s : M.State} {a : ℝ}
    (ha : a ∈ (M.household z₀ m₀ K).feasible s) : a ∈ Icc 0 M.assetCap :=
  ⟨ha.1, ha.2.trans (min_le_left _ _)⟩

/-- The household objective, written out on feasible choices. -/
theorem objective_eq (K : List Z → ℝ) (v : M.State →ᵇ ℝ) {s : M.State} {a : ℝ}
    (ha : a ∈ (M.household z₀ m₀ K).feasible s) :
    (M.household z₀ m₀ K).objective v s a
      = M.utility (M.cash z₀ m₀ K s - a)
        + M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, a)
            * v (M.clampAssets a, ⟨ze.2, ze.1 :: s.2.node⟩) := by
  rw [StochasticDynamicProgram.objective, M.reward_eq_of_mem_feasible z₀ m₀ K ha]
  rfl

/-- **The Bellman operator preserves concavity in assets** along every label's slice. -/
theorem concaveOn_bellman (K : List Z → ℝ) (v : M.State →ᵇ ℝ)
    (hv : ∀ l : Label Z E, ConcaveOn ℝ (Icc 0 M.assetCap) fun a => v (M.clampAssets a, l))
    (l : Label Z E) :
    ConcaveOn ℝ (Icc 0 M.assetCap) fun a => (M.household z₀ m₀ K).bellman v (M.clampAssets a, l)
    := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  set D := M.household z₀ m₀ K with hD
  obtain ⟨ax, hax, heqx, -⟩ := D.exists_optimal_action v (M.clampAssets x, l)
  obtain ⟨ay, hay, heqy, -⟩ := D.exists_optimal_action v (M.clampAssets y, l)
  have hmix : θ * x + φ * y ∈ Icc 0 M.assetCap := by
    simpa using convex_Icc 0 M.assetCap hx hy hθ hφ hθφ
  have haxI := M.mem_Icc_of_mem_feasible z₀ m₀ K hax
  have hayI := M.mem_Icc_of_mem_feasible z₀ m₀ K hay
  have hcx := M.cash_clampAssets z₀ m₀ K hx l
  have hcy := M.cash_clampAssets z₀ m₀ K hy l
  have hcm := M.cash_clampAssets z₀ m₀ K hmix l
  have hcmix : M.cash z₀ m₀ K (M.clampAssets (θ * x + φ * y), l)
      = θ * M.cash z₀ m₀ K (M.clampAssets x, l) + φ * M.cash z₀ m₀ K (M.clampAssets y, l) := by
    rw [hcm, hcx, hcy]
    linear_combination (M.wageAt z₀ m₀ K l.node * M.efficiency l.idio) * hθφ.symm
  -- the mixed saving is feasible at the mixed state
  have hfeas : θ * ax + φ * ay ∈ D.feasible (M.clampAssets (θ * x + φ * y), l) := by
    refine ⟨add_nonneg (mul_nonneg hθ hax.1) (mul_nonneg hφ hay.1), le_min ?_ ?_⟩
    · have hcap : θ * M.assetCap + φ * M.assetCap = M.assetCap := by
        rw [← add_mul, hθφ, one_mul]
      linarith [mul_le_mul_of_nonneg_left haxI.2 hθ, mul_le_mul_of_nonneg_left hayI.2 hφ]
    · rw [hcmix]
      have hfl : θ * M.consFloor + φ * M.consFloor = M.consFloor := by
        rw [← add_mul, hθφ, one_mul]
      linarith [mul_le_mul_of_nonneg_left (hax.2.trans (min_le_right _ _)) hθ,
        mul_le_mul_of_nonneg_left (hay.2.trans (min_le_right _ _)) hφ]
  have hle := D.le_bellmanFn v hfeas
  rw [M.objective_eq z₀ m₀ K v hfeas] at hle
  -- utility is concave
  have hc0x : M.consFloor ≤ M.cash z₀ m₀ K (M.clampAssets x, l) - ax :=
    le_sub_comm.1 (hax.2.trans (min_le_right _ _))
  have hc0y : M.consFloor ≤ M.cash z₀ m₀ K (M.clampAssets y, l) - ay :=
    le_sub_comm.1 (hay.2.trans (min_le_right _ _))
  have hu := M.strictConcaveOn_utility.concaveOn.2 (mem_Ici.2 hc0x) (mem_Ici.2 hc0y) hθ hφ hθφ
  simp only [smul_eq_mul] at hu
  have hcons : M.cash z₀ m₀ K (M.clampAssets (θ * x + φ * y), l) - (θ * ax + φ * ay)
      = θ * (M.cash z₀ m₀ K (M.clampAssets x, l) - ax)
        + φ * (M.cash z₀ m₀ K (M.clampAssets y, l) - ay) := by
    rw [hcmix]
    ring
  -- the continuation is concave, termwise
  have hexp : θ * (∑ ze : Z × E, M.shockProb z₀ ze ((M.clampAssets x, l), ax)
          * v (M.clampAssets ax, ⟨ze.2, ze.1 :: l.node⟩))
      + φ * (∑ ze : Z × E, M.shockProb z₀ ze ((M.clampAssets y, l), ay)
          * v (M.clampAssets ay, ⟨ze.2, ze.1 :: l.node⟩))
      ≤ ∑ ze : Z × E, M.shockProb z₀ ze ((M.clampAssets (θ * x + φ * y), l), θ * ax + φ * ay)
          * v (M.clampAssets (θ * ax + φ * ay), ⟨ze.2, ze.1 :: l.node⟩) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ze _ => ?_
    have hvz := (hv ⟨ze.2, ze.1 :: l.node⟩).2 haxI hayI hθ hφ hθφ
    simp only [smul_eq_mul] at hvz
    have hp : 0 ≤ M.shockProb z₀ ze ((M.clampAssets x, l), ax) :=
      mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _)
    change θ * (M.shockProb z₀ ze ((M.clampAssets x, l), ax) * _)
        + φ * (M.shockProb z₀ ze ((M.clampAssets x, l), ax) * _)
      ≤ M.shockProb z₀ ze ((M.clampAssets x, l), ax) * _
    nlinarith
  have hβ : 0 ≤ M.discount := M.discount_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hexp hβ
  -- the values at `x` and `y` are those of their optimal savings
  have hbx : D.bellman v (M.clampAssets x, l) = M.utility (M.cash z₀ m₀ K (M.clampAssets x, l) - ax)
      + M.discount * ∑ ze : Z × E, M.shockProb z₀ ze ((M.clampAssets x, l), ax)
          * v (M.clampAssets ax, ⟨ze.2, ze.1 :: l.node⟩) := by
    rw [heqx, M.objective_eq z₀ m₀ K v hax]
  have hby : D.bellman v (M.clampAssets y, l) = M.utility (M.cash z₀ m₀ K (M.clampAssets y, l) - ay)
      + M.discount * ∑ ze : Z × E, M.shockProb z₀ ze ((M.clampAssets y, l), ay)
          * v (M.clampAssets ay, ⟨ze.2, ze.1 :: l.node⟩) := by
    rw [heqy, M.objective_eq z₀ m₀ K v hay]
  simp only [smul_eq_mul]
  change θ * D.bellman v (M.clampAssets x, l) + φ * D.bellman v (M.clampAssets y, l)
    ≤ D.bellmanFn v (M.clampAssets (θ * x + φ * y), l)
  rw [hbx, hby]
  rw [hcons] at hle
  nlinarith

/-- **The value function is concave in assets at every node**, along any capital path. -/
theorem concaveOn_valueFunction (K : List Z → ℝ) (l : Label Z E) :
    ConcaveOn ℝ (Icc 0 M.assetCap)
      fun a => (M.household z₀ m₀ K).valueFunction (M.clampAssets a, l) :=
  Blackwell.forall_concaveOn_valueFunction (convex_Icc _ _)
    (fun (l : Label Z E) (a : ℝ) => (M.clampAssets a, l)) (M.household z₀ m₀ K).blackwell
    (M.household z₀ m₀ K).discount_lt_one (fun v hv => M.concaveOn_bellman z₀ m₀ K v hv) l

/-! ### Uniqueness and the policy -/

/-- **The optimal saving is unique.** -/
theorem optimal_saving_unique (K : List Z → ℝ) {s : M.State} {a₀ a₁ : ℝ}
    (h₀ : a₀ ∈ (M.household z₀ m₀ K).feasible s) (h₁ : a₁ ∈ (M.household z₀ m₀ K).feasible s)
    (hm₀ : (M.household z₀ m₀ K).objective (M.household z₀ m₀ K).valueFunction s a₀
      = (M.household z₀ m₀ K).bellmanFn (M.household z₀ m₀ K).valueFunction s)
    (hm₁ : (M.household z₀ m₀ K).objective (M.household z₀ m₀ K).valueFunction s a₁
      = (M.household z₀ m₀ K).bellmanFn (M.household z₀ m₀ K).valueFunction s) :
    a₀ = a₁ := by
  by_contra hne
  set D := M.household z₀ m₀ K with hD
  set V := D.valueFunction with hV
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hsum : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
  have hmid : (1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁ ∈ D.feasible s := by
    have h := convex_Icc (0 : ℝ) (M.maxSaving z₀ m₀ K s) h₀ h₁ hhalf.le hhalf.le hsum
    simp only [smul_eq_mul] at h
    exact h
  have h₀I := M.mem_Icc_of_mem_feasible z₀ m₀ K h₀
  have h₁I := M.mem_Icc_of_mem_feasible z₀ m₀ K h₁
  have hc₀ : M.consFloor ≤ M.cash z₀ m₀ K s - a₀ := le_sub_comm.1 (h₀.2.trans (min_le_right _ _))
  have hc₁ : M.consFloor ≤ M.cash z₀ m₀ K s - a₁ := le_sub_comm.1 (h₁.2.trans (min_le_right _ _))
  have hcne : M.cash z₀ m₀ K s - a₀ ≠ M.cash z₀ m₀ K s - a₁ := fun h => hne (by linarith)
  have hu := M.strictConcaveOn_utility.2 (mem_Ici.2 hc₀) (mem_Ici.2 hc₁) hcne hhalf hhalf hsum
  simp only [smul_eq_mul] at hu
  have hcmid : M.cash z₀ m₀ K s - ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁)
      = (1 / 2 : ℝ) * (M.cash z₀ m₀ K s - a₀) + (1 / 2 : ℝ) * (M.cash z₀ m₀ K s - a₁) := by
    ring
  have hexp : (1 / 2 : ℝ) * (∑ ze : Z × E, M.shockProb z₀ ze (s, a₀)
          * V (M.clampAssets a₀, ⟨ze.2, ze.1 :: s.2.node⟩))
      + (1 / 2 : ℝ) * (∑ ze : Z × E, M.shockProb z₀ ze (s, a₁)
          * V (M.clampAssets a₁, ⟨ze.2, ze.1 :: s.2.node⟩))
      ≤ ∑ ze : Z × E, M.shockProb z₀ ze (s, (1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁)
          * V (M.clampAssets ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁), ⟨ze.2, ze.1 :: s.2.node⟩) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ze _ => ?_
    have hvz := (M.concaveOn_valueFunction z₀ m₀ K ⟨ze.2, ze.1 :: s.2.node⟩).2 h₀I h₁I
      hhalf.le hhalf.le hsum
    simp only [smul_eq_mul] at hvz
    have hp : 0 ≤ M.shockProb z₀ ze (s, a₀) :=
      mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _)
    change (1 / 2 : ℝ) * (M.shockProb z₀ ze (s, a₀) * _)
        + (1 / 2 : ℝ) * (M.shockProb z₀ ze (s, a₀) * _)
      ≤ M.shockProb z₀ ze (s, a₀) * _
    nlinarith
  have hβ : 0 ≤ M.discount := M.discount_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hexp hβ
  have hle := D.le_bellmanFn V hmid
  rw [M.objective_eq z₀ m₀ K V hmid, hcmid] at hle
  rw [M.objective_eq z₀ m₀ K V h₀] at hm₀
  rw [M.objective_eq z₀ m₀ K V h₁] at hm₁
  nlinarith

/-- The optimal saving along the path `K` at the state `s`. -/
noncomputable def policy (K : List Z → ℝ) (s : M.State) : ℝ :=
  Classical.choose ((M.household z₀ m₀ K).exists_optimal_action
    (M.household z₀ m₀ K).valueFunction s)

theorem policy_mem (K : List Z → ℝ) (s : M.State) :
    M.policy z₀ m₀ K s ∈ (M.household z₀ m₀ K).feasible s :=
  (Classical.choose_spec ((M.household z₀ m₀ K).exists_optimal_action
    (M.household z₀ m₀ K).valueFunction s)).1

theorem policy_optimal (K : List Z → ℝ) (s : M.State) :
    (M.household z₀ m₀ K).bellman (M.household z₀ m₀ K).valueFunction s
      = (M.household z₀ m₀ K).objective (M.household z₀ m₀ K).valueFunction s
          (M.policy z₀ m₀ K s) :=
  (Classical.choose_spec ((M.household z₀ m₀ K).exists_optimal_action
    (M.household z₀ m₀ K).valueFunction s)).2.1

theorem policy_mem_Icc (K : List Z → ℝ) (s : M.State) :
    M.policy z₀ m₀ K s ∈ Icc 0 M.assetCap :=
  M.mem_Icc_of_mem_feasible z₀ m₀ K (M.policy_mem z₀ m₀ K s)

theorem argmax_eq_singleton (K : List Z → ℝ) (s : M.State) :
    argmax ((M.household z₀ m₀ K).objective (M.household z₀ m₀ K).valueFunction)
      (M.household z₀ m₀ K).feasible s = {M.policy z₀ m₀ K s} := by
  set D := M.household z₀ m₀ K
  ext a
  simp only [argmax, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ha, hmax⟩
    refine M.optimal_saving_unique z₀ m₀ K ha (M.policy_mem z₀ m₀ K s)
      (le_antisymm (D.le_bellmanFn _ ha) ?_) ?_
    · change D.bellman D.valueFunction s ≤ _
      rw [M.policy_optimal z₀ m₀ K s]
      exact isMaxOn_iff.mp hmax _ (M.policy_mem z₀ m₀ K s)
    · exact (M.policy_optimal z₀ m₀ K s).symm
  · rintro rfl
    refine ⟨M.policy_mem z₀ m₀ K s, isMaxOn_iff.mpr fun b hb => ?_⟩
    rw [← M.policy_optimal z₀ m₀ K s]
    exact D.le_bellmanFn _ hb

/-! ### Joint continuity in the path and the state -/

/-- A function on paths and labels that depends on the path only at the label's node is
continuous, whenever it is continuous in capital at each node. -/
theorem continuous_atNode {f : Label Z E → ℝ → ℝ} (hf : ∀ l, Continuous (f l)) :
    Continuous fun p : (List Z → ℝ) × M.State => f p.2.2 (p.1 p.2.2.node) := by
  have hF : Continuous fun q : Label Z E × ℝ => f q.1 q.2 :=
    continuous_prod_of_discrete_left.2 hf
  have hK : Continuous fun q : (List Z → ℝ) × Label Z E => q.1 q.2.node :=
    continuous_prod_of_discrete_right.2 fun l => continuous_apply l.node
  exact hF.comp ((continuous_snd.comp continuous_snd).prodMk
    (hK.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))

theorem continuous_cash_joint :
    Continuous fun p : (List Z → ℝ) × M.State => M.cash z₀ m₀ p.1 p.2 := by
  have hR := M.continuous_atNode (f := fun l k =>
    M.grossReturn (shockAt z₀ l.node) k (M.labour z₀ m₀ l.node))
    fun l => (M.continuous_grossReturn _).comp (continuous_id.prodMk continuous_const)
  have hw := M.continuous_atNode (f := fun l k =>
    M.wage (shockAt z₀ l.node) k (M.labour z₀ m₀ l.node) * M.efficiency l.idio)
    fun l => ((M.continuous_wage _).comp (continuous_id.prodMk continuous_const)).mul
      continuous_const
  exact (hR.mul (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).add hw

/-- **The value function is jointly continuous** in the path and the state. -/
theorem continuous_valueFunction_joint :
    Continuous fun p : (List Z → ℝ) × M.State => (M.household z₀ m₀ p.1).valueFunction p.2 := by
  have hρ : M.discount < (M.discount + 1) / 2 := by linarith [M.discount_lt_one]
  have hρ1 : (M.discount + 1) / 2 < 1 := by linarith [M.discount_lt_one]
  have hn : Continuous fun K => (M.weightedHousehold z₀ m₀ K hρ hρ1).normalisedValue :=
    continuous_iff_continuousAt.2 fun K₀ => M.continuousAt_normalisedValue z₀ m₀ hρ hρ1 K₀
  have heq : (fun p : (List Z → ℝ) × M.State => (M.household z₀ m₀ p.1).valueFunction p.2)
      = fun p => (M.weightedHousehold z₀ m₀ p.1 hρ hρ1).normalisedValue p.2
          * ((M.discount + 1) / 2)⁻¹ ^ M.depth p.2 := by
    funext p
    rw [← M.weightedHousehold_valueFunction z₀ m₀ p.1 hρ hρ1 p.2]
    rfl
  rw [heq]
  exact (continuous_eval.comp (hn.prodMap continuous_id)).mul
    ((M.continuous_pow_depth _).comp continuous_snd)

/-- **The saving policy is jointly continuous** in the path of capital (product topology) and
the household's state. -/
theorem continuous_policy :
    Continuous fun p : (List Z → ℝ) × M.State => M.policy z₀ m₀ p.1 p.2 := by
  set f : (List Z → ℝ) × M.State → ℝ → ℝ := fun p a =>
    (M.household z₀ m₀ p.1).objective (M.household z₀ m₀ p.1).valueFunction p.2 a with hf
  set Γ : (List Z → ℝ) × M.State → Set ℝ := fun p => (M.household z₀ m₀ p.1).feasible p.2
    with hΓ
  have hcash := M.continuous_cash_joint z₀ m₀
  have hg : Continuous fun p : (List Z → ℝ) × M.State =>
      min M.assetCap (M.cash z₀ m₀ p.1 p.2 - M.consFloor) :=
    continuous_const.min (hcash.sub continuous_const)
  have hg0 : ∀ p : (List Z → ℝ) × M.State,
      (0 : ℝ) ≤ min M.assetCap (M.cash z₀ m₀ p.1 p.2 - M.consFloor) :=
    fun p => le_min M.assetCap_pos.le (sub_nonneg.2 (M.consFloor_le_cash z₀ m₀ p.1 p.2))
  have hfc : Continuous ↿f := by
    have hc : Continuous fun q : ((List Z → ℝ) × M.State) × ℝ =>
        max M.consFloor (min (max M.consFloor M.maxCash) (M.cash z₀ m₀ q.1.1 q.1.2 - q.2)) :=
      continuous_const.max (continuous_const.min ((hcash.comp continuous_fst).sub continuous_snd))
    have hu : Continuous fun q : ((List Z → ℝ) × M.State) × ℝ =>
        M.utility (max M.consFloor
          (min (max M.consFloor M.maxCash) (M.cash z₀ m₀ q.1.1 q.1.2 - q.2))) :=
      (M.continuousOn_utility.mono Icc_subset_Ici_self).comp_continuous hc fun q =>
        ⟨le_max_left _ _, max_le (le_max_left _ _) (min_le_left _ _)⟩
    have hV := M.continuous_valueFunction_joint z₀ m₀
    have hexp : Continuous fun q : ((List Z → ℝ) × M.State) × ℝ =>
        ∑ ze : Z × E, M.shockProb z₀ ze (q.1.2, q.2)
          * (M.household z₀ m₀ q.1.1).valueFunction (M.transition ze (q.1.2, q.2)) := by
      refine continuous_finsetSum _ fun ze _ => ?_
      refine ((M.shockProb z₀ ze).continuous.comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).mul ?_
      exact hV.comp ((continuous_fst.comp continuous_fst).prodMk ((M.transition ze).continuous.comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
    exact hu.add (continuous_const.mul hexp)
  have huhc : UpperHemicontinuous (argmax f Γ) := fun p =>
    upperHemicontinuousAt_argmax hfc (fun p => nonempty_Icc.2 (hg0 p)) (fun _ => isCompact_Icc)
      (upperHemicontinuous_Icc continuous_const hg p)
      (lowerHemicontinuous_Icc continuous_const hg hg0 p)
  exact continuous_of_upperHemicontinuous_singleton huhc
    fun p => M.argmax_eq_singleton z₀ m₀ p.1 p.2

end KSModel

end KrusellSmith

end LeanEconomics
