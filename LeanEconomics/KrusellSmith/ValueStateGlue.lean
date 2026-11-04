/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ValueState

/-!
# Gluing: the recursive equilibrium on the extended state generates a sequential equilibrium

Milestone V3 of `VALUESTATE_PLAN.md` (Miao 2006, Theorem 2). Start from an extended state `ξ₀`
and follow the next-state map down the tree (`ExtState.tree`). At every node the extended state
was produced by its own chosen sequential equilibrium, and the equilibrium chosen at a child need
not be the continuation of the one chosen at its parent. Glue them: capital at node `h` is mean
assets of the distribution of the extended state at `h` (`gluedPath`).

**The glued path is a sequential equilibrium** (`isSequentialEquilibrium_glued`), and along it

* prices at `h` are those of the extended state at `h`, because idiosyncratic masses follow the
  labour recursion (`initMass_tree`, `labour_tree`, `cash_glued`);
* the households' value function is the glued values `W (a, e, h) = v_h (a, e)`
  (`valueFunction_glued`): node by node, `W` satisfies the Bellman equation, because each `v_h`
  is the value of saving optimally against the next states' values (V2), and the Bellman operator
  has only one bounded fixed point. This is where it does not matter which equilibrium was
  chosen below a child: only its value enters today's decision;
* households save by the extended state's policy (`policy_glued`), by uniqueness of the optimal
  saving;
* distributions are those of the extended states (`nodeDist_glued`).

The values are uniformly bounded (`abs_value_le`): the reward bound does not depend on the path
(`norm_reward_le`), and the value function is bounded by it over `1 - β`
(`StochasticDynamicProgram.norm_valueFunction_le`).
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- A bound on utility over the consumption range, the same for every path. -/
noncomputable def utilityBound : ℝ := M.exists_bound_utility.choose

theorem utilityBound_nonneg : 0 ≤ M.utilityBound :=
  (norm_nonneg _).trans (M.exists_bound_utility.choose_spec M.consFloor
    ⟨le_rfl, le_max_left _ _⟩)

/-- **The reward bound does not depend on the path.** -/
theorem norm_reward_le (z : Z) (K : List Z → ℝ × ℝ) : ‖M.reward z K‖ ≤ M.utilityBound :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ M.utilityBound_nonneg _

/-- **The household's value is bounded uniformly over paths.** -/
theorem norm_valueFunction_le (z : Z) (K : List Z → ℝ × ℝ) :
    ‖(M.household z K).valueFunction‖ ≤ M.utilityBound / (1 - M.discount) := by
  have h1 := (M.household z K).norm_valueFunction_le
  have h2 : ‖(M.household z K).reward‖ ≤ M.utilityBound := M.norm_reward_le z K
  have hβ : 0 < 1 - M.discount := sub_pos.2 M.discount_lt_one
  exact h1.trans (div_le_div_of_nonneg_right h2 hβ.le)

namespace ExtState

variable {M}

theorem abs_value_le (ξ : M.ExtState) (x : M.AState) :
    |ξ.value x| ≤ M.utilityBound / (1 - M.discount) := by
  rw [← ξ.rootValue_path]
  have h := ((M.household ξ.shock ξ.prices).valueFunction).norm_coe_le_norm (M.placeAt [] x)
  rw [Real.norm_eq_abs] at h
  exact h.trans (M.norm_valueFunction_le ξ.shock ξ.prices)

/-! ### The tree of extended states and the glued path -/

/-- **The tree of extended states** from `ξ₀`, following the next-state map. -/
noncomputable def tree (ξ₀ : M.ExtState) : List Z → M.ExtState
  | [] => ξ₀
  | z' :: h => (tree ξ₀ h).next z'

theorem tree_shock (ξ₀ : M.ExtState) : ∀ h, (ξ₀.tree h).shock = shockAt ξ₀.shock h
  | [] => rfl
  | _ :: _ => rfl

/-- **The glued path**: capital at each node is mean assets of the extended state there. -/
noncomputable def gluedPath (ξ₀ : M.ExtState) (h : List Z) : ℝ := (ξ₀.tree h).capital

/-- Prices along the glued path. -/
noncomputable def gluedPrices (ξ₀ : M.ExtState) : List Z → ℝ × ℝ :=
  M.pricePath ξ₀.shock (M.initMass (ξ₀.dist : Measure M.AState)) ξ₀.gluedPath

/-- **Idiosyncratic masses along the tree follow the labour recursion.** -/
theorem initMass_tree (ξ₀ : M.ExtState) : ∀ h,
    M.initMass ((ξ₀.tree h).dist : Measure M.AState)
      = M.stateMass ξ₀.shock (M.initMass (ξ₀.dist : Measure M.AState)) h
  | [] => rfl
  | z' :: h => by
    funext e'
    change M.initMass (((ξ₀.tree h).next z').dist : Measure M.AState) e' = _
    rw [ExtState.initMass_next, initMass_tree ξ₀ h, tree_shock]
    rfl

theorem labour_tree (ξ₀ : M.ExtState) (h : List Z) :
    M.labour ξ₀.shock (M.initMass (ξ₀.dist : Measure M.AState)) h = (ξ₀.tree h).labour := by
  unfold KSModel.labour ExtState.labour
  rw [initMass_tree]

theorem returnAt_glued (ξ₀ : M.ExtState) (h : List Z) :
    M.returnAt ξ₀.shock ξ₀.gluedPrices h = M.returnAt (ξ₀.tree h).shock (ξ₀.tree h).prices [] := by
  rw [ExtState.returnAt_nil, tree_shock, ← labour_tree]
  rfl

theorem wageAt_glued (ξ₀ : M.ExtState) (h : List Z) :
    M.wageAt ξ₀.shock ξ₀.gluedPrices h = M.wageAt (ξ₀.tree h).shock (ξ₀.tree h).prices [] := by
  rw [ExtState.wageAt_nil, tree_shock, ← labour_tree]
  rfl

/-- **Cash on hand along the glued path** is cash on hand at the extended state of the node. -/
theorem cash_glued (ξ₀ : M.ExtState) (s : M.State) :
    M.cash ξ₀.shock ξ₀.gluedPrices s = (ξ₀.tree s.2.node).cash (s.1, ⟨s.2.idio⟩) := by
  simp only [KSModel.cash, ExtState.cash, placeAt, returnAt_glued, wageAt_glued]

theorem maxSaving_glued (ξ₀ : M.ExtState) (s : M.State) :
    M.maxSaving ξ₀.shock ξ₀.gluedPrices s = (ξ₀.tree s.2.node).maxSaving (s.1, ⟨s.2.idio⟩) := by
  simp only [KSModel.maxSaving]
  rw [cash_glued]
  rfl

theorem mem_feasible_glued (ξ₀ : M.ExtState) (s : M.State) (a : ℝ) :
    a ∈ (M.household ξ₀.shock ξ₀.gluedPrices).feasible s
      ↔ a ∈ Icc 0 ((ξ₀.tree s.2.node).maxSaving (s.1, ⟨s.2.idio⟩)) := by
  change a ∈ Icc 0 (M.maxSaving ξ₀.shock ξ₀.gluedPrices s) ↔ _
  rw [maxSaving_glued]

/-! ### The glued values solve the Bellman equation -/

/-- **The glued values**: at node `h`, the value of the extended state there. -/
noncomputable def gluedValue (ξ₀ : M.ExtState) : M.State →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s : M.State => (ξ₀.tree s.2.node).value (s.1, ⟨s.2.idio⟩))
    (continuous_prod_of_discrete_right.2 fun l =>
      ((ξ₀.tree l.node).value.continuous).comp (continuous_id.prodMk
        (continuous_const : Continuous fun _ : ↥(Icc (0 : ℝ) M.assetCap) => (⟨l.idio⟩ : Idio E))))
    (M.utilityBound / (1 - M.discount))
    (fun s => by
      rw [Real.norm_eq_abs]
      exact abs_value_le _ _)

theorem gluedValue_apply (ξ₀ : M.ExtState) (s : M.State) :
    ξ₀.gluedValue s = (ξ₀.tree s.2.node).value (s.1, ⟨s.2.idio⟩) := rfl

/-- The household's objective against the glued values is the objective at the extended state of
the node. -/
theorem objective_glued (ξ₀ : M.ExtState) (s : M.State) {a : ℝ}
    (ha : a ∈ (M.household ξ₀.shock ξ₀.gluedPrices).feasible s) :
    (M.household ξ₀.shock ξ₀.gluedPrices).objective ξ₀.gluedValue s a
      = (ξ₀.tree s.2.node).objective (s.1, ⟨s.2.idio⟩) a := by
  rw [M.objective_eq _ _ _ ha, cash_glued]
  have hz := tree_shock ξ₀ s.2.node
  simp only [ExtState.objective, ExtState.shockProb, hz]
  rfl

/-- **The glued values are a fixed point of the Bellman operator along the glued path.** -/
theorem bellman_gluedValue (ξ₀ : M.ExtState) :
    (M.household ξ₀.shock ξ₀.gluedPrices).bellman ξ₀.gluedValue = ξ₀.gluedValue := by
  ext s
  apply le_antisymm
  · obtain ⟨a, ha, hb, -⟩ :=
      (M.household ξ₀.shock ξ₀.gluedPrices).exists_optimal_action ξ₀.gluedValue s
    rw [hb, objective_glued ξ₀ s ha, gluedValue_apply]
    exact (ξ₀.tree s.2.node).objective_le_value _ ((mem_feasible_glued ξ₀ s a).1 ha)
  · have hp := (mem_feasible_glued ξ₀ s _).2 ((ξ₀.tree s.2.node).policy_mem (s.1, ⟨s.2.idio⟩))
    rw [gluedValue_apply, ExtState.value_eq, ← objective_glued ξ₀ s hp]
    exact (M.household ξ₀.shock ξ₀.gluedPrices).le_bellmanFn _ hp

/-- **The households' value function along the glued path is the glued values.** -/
theorem valueFunction_glued (ξ₀ : M.ExtState) :
    (M.household ξ₀.shock ξ₀.gluedPrices).valueFunction = ξ₀.gluedValue :=
  ((M.household ξ₀.shock ξ₀.gluedPrices).eq_valueFunction ξ₀.bellman_gluedValue).symm

/-- **Households save by the extended state's policy along the glued path.** -/
theorem policy_glued (ξ₀ : M.ExtState) (s : M.State) :
    M.policy ξ₀.shock ξ₀.gluedPrices s = (ξ₀.tree s.2.node).policy (s.1, ⟨s.2.idio⟩) := by
  have hp := (mem_feasible_glued ξ₀ s _).2 ((ξ₀.tree s.2.node).policy_mem (s.1, ⟨s.2.idio⟩))
  refine M.optimal_saving_unique ξ₀.shock ξ₀.gluedPrices (M.policy_mem _ _ s) hp ?_ ?_
  · exact (M.policy_optimal ξ₀.shock ξ₀.gluedPrices s).symm
  · rw [valueFunction_glued, objective_glued ξ₀ s hp, ← ExtState.value_eq]
    change _ = (M.household ξ₀.shock ξ₀.gluedPrices).bellman ξ₀.gluedValue s
    rw [bellman_gluedValue]
    rfl

/-! ### Distributions and equilibrium -/

/-- **The distributions along the glued path are those of the extended states.** -/
theorem nodeDist_glued (ξ₀ : M.ExtState) : ∀ h,
    M.nodeDist ξ₀.shock (ξ₀.dist : Measure M.AState) ξ₀.gluedPrices h
      = ((ξ₀.tree h).dist : Measure M.AState)
  | [] => rfl
  | z' :: h => by
    change M.pushNode ξ₀.shock ξ₀.gluedPrices h z'
        (M.nodeDist ξ₀.shock (ξ₀.dist : Measure M.AState) ξ₀.gluedPrices h)
      = (((ξ₀.tree h).next z').dist : Measure M.AState)
    rw [nodeDist_glued ξ₀ h, ExtState.next_dist_eq]
    refine M.pushNode_congr (by rw [shockAt_nil, tree_shock]) (fun e' x => ?_) z' _
    change (M.clampAssets (M.policy ξ₀.shock ξ₀.gluedPrices (x.1, ⟨x.2.idio, h⟩)), _) = _
    rw [policy_glued]
    rfl

/-- **The glued path is a sequential equilibrium** from `(z₀, μ₀)`. -/
theorem isSequentialEquilibrium_glued (ξ₀ : M.ExtState) :
    M.IsSequentialEquilibrium ξ₀.shock (ξ₀.dist : Measure M.AState) ξ₀.gluedPath := by
  intro h
  change ξ₀.gluedPath h
    = ∫ x, M.assets x ∂(M.nodeDist ξ₀.shock (ξ₀.dist : Measure M.AState) ξ₀.gluedPrices h)
  rw [nodeDist_glued]
  rfl

/-- **The households' value at every node of the glued path** is the value of the extended state
there. -/
theorem nodeValue_glued (ξ₀ : M.ExtState) (h : List Z) :
    M.nodeValue ξ₀.shock (ξ₀.dist : Measure M.AState) ξ₀.gluedPath h = (ξ₀.tree h).value := by
  ext x
  rw [nodeValue_apply]
  change (M.household ξ₀.shock ξ₀.gluedPrices).valueFunction _ = _
  rw [valueFunction_glued]
  rfl

theorem rootValue_glued (ξ₀ : M.ExtState) :
    M.rootValue ξ₀.shock (ξ₀.dist : Measure M.AState) ξ₀.gluedPath = ξ₀.value :=
  ξ₀.nodeValue_glued []

end ExtState

end KSModel

end KrusellSmith

end LeanEconomics
