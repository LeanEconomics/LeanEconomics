/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Model
import LeanEconomics.DynamicProgramming.Stochastic
import LeanEconomics.Topology.IccCorrespondence

/-!
# The Krusell–Smith household facing a path of capital and labour

Given a path `K` of price inputs on the tree of histories, aggregate capital `(K h).1` and
aggregate labour `(K h).2` at every node `h`, prices at every node are known: the gross return
`R_h` and the wage `w_h` are the model's price functions at the shock, capital and labour of `h`.
(The equilibrium modules feed in labour from the exogenous recursion `labour`; keeping it in the
path lets every continuity result hold jointly in capital and labour, hence in the initial
distribution.) The household's problem is then an ordinary stochastic dynamic
program, an instance of `LeanEconomics.StochasticDynamicProgram`:

* the **state** is the asset holding `a ∈ [0, assetCap]` together with a discrete **label**
  carrying the idiosyncratic state `e` and the node `h`;
* the **action** is next period's asset holding `a'`, feasible in
  `[0, min(assetCap, R_h a + w_h e − c̲)]`, where `c̲` is the consumption floor `consFloor`;
* the **shock** is the pair `(z', e')`, with probability `aggProb z_h z' * idioProb z_h z' e e'`,
  and it moves the label to `(e', z' :: h)`;
* the **reward** is utility of consumption `R_h a + w_h e − a'`. The framework asks for a reward
  bounded and continuous at every action, so consumption is clamped to `[c̲, c̄]` with `c̄` the
  largest cash on hand anywhere; on feasible actions the clamp does nothing
  (`reward_eq_of_mem_feasible`).

The node lives in the state rather than in the program, so one program covers the whole tree and
its value function is a single bounded continuous function: `valueFunction` evaluated at
`(a, ⟨e, h⟩)` is the value at node `h`. The label's topology is discrete, so continuity of the
data is continuity in assets alone.

This module only builds the program; that its value function and policy move continuously with
the path `K` in the product topology is the next module.
-/

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

namespace LeanEconomics

namespace KrusellSmith

/-- The discrete part of a household's state: its idiosyncratic state and its node in the tree
of histories. -/
structure Label (Z E : Type*) where
  /-- The idiosyncratic state. -/
  idio : E
  /-- The node: the aggregate shocks drawn since the start, newest first. -/
  node : List Z

instance (Z E : Type*) : TopologicalSpace (Label Z E) := ⊥

instance (Z E : Type*) : DiscreteTopology (Label Z E) := ⟨rfl⟩

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- A household's state: assets in `[0, assetCap]` and a label. -/
abbrev State := ↥(Icc (0 : ℝ) M.assetCap) × Label Z E

/-- The largest cash on hand anywhere: an upper bound on consumption. -/
noncomputable def maxCash : ℝ := M.returnBound * M.assetCap + M.wageBound * ∑ e, M.efficiency e

variable (z₀ : Z) (K : List Z → ℝ × ℝ)

/-- The gross return at node `h` along the path `K`. -/
noncomputable def returnAt (h : List Z) : ℝ :=
  M.grossReturn (shockAt z₀ h) (K h).1 (K h).2

/-- The wage at node `h` along the path `K`. -/
noncomputable def wageAt (h : List Z) : ℝ :=
  M.wage (shockAt z₀ h) (K h).1 (K h).2

/-- Cash on hand: the return on assets plus labour income. -/
noncomputable def cash (s : M.State) : ℝ :=
  M.returnAt z₀ K s.2.node * s.1 + M.wageAt z₀ K s.2.node * M.efficiency s.2.idio
    - M.returnAt z₀ K s.2.node * M.borrowLimit

/-- The largest feasible saving: cash on hand less the consumption floor, capped at
`assetCap`. -/
noncomputable def maxSaving (s : M.State) : ℝ := min M.assetCap (M.cash z₀ K s - M.consFloor)

/-- **Cash covers the floor**: debt service at the borrowing limit is afforded by labour income. -/
theorem consFloor_le_cash (s : M.State) : M.consFloor ≤ M.cash z₀ K s := by
  have h := M.consFloor_le_income (shockAt z₀ s.2.node) (K s.2.node).1 (K s.2.node).2 s.2.idio
  have ha := mul_nonneg (M.grossReturn_nonneg (shockAt z₀ s.2.node) (K s.2.node).1
    (K s.2.node).2) s.1.2.1
  simp only [cash, returnAt, wageAt]
  linarith

theorem cash_nonneg (s : M.State) : 0 ≤ M.cash z₀ K s :=
  M.consFloor_nonneg.trans (M.consFloor_le_cash z₀ K s)

theorem cash_le_maxCash (s : M.State) : M.cash z₀ K s ≤ M.maxCash := by
  have heff : M.efficiency s.2.idio ≤ ∑ e, M.efficiency e :=
    Finset.single_le_sum (fun e _ => M.efficiency_nonneg e) (Finset.mem_univ _)
  have hR := M.grossReturn_le (shockAt z₀ s.2.node) (K s.2.node).1 (K s.2.node).2
  have hw := M.wage_le (shockAt z₀ s.2.node) (K s.2.node).1 (K s.2.node).2
  have hR0 := M.grossReturn_nonneg (shockAt z₀ s.2.node) (K s.2.node).1 (K s.2.node).2
  have hw0 := M.wage_nonneg (shockAt z₀ s.2.node) (K s.2.node).1 (K s.2.node).2
  have ha := s.1.2
  have he := M.efficiency_nonneg s.2.idio
  have hb := mul_nonneg hR0 M.borrowLimit_nonneg
  simp only [cash, returnAt, wageAt, maxCash]
  have h1 : M.grossReturn (shockAt z₀ s.2.node) (K s.2.node).1 (K s.2.node).2 * s.1
      ≤ M.returnBound * M.assetCap :=
    mul_le_mul hR ha.2 ha.1 (hR0.trans hR)
  have h2 : M.wage (shockAt z₀ s.2.node) (K s.2.node).1 (K s.2.node).2
      * M.efficiency s.2.idio ≤ M.wageBound * ∑ e, M.efficiency e :=
    mul_le_mul hw heff he (hw0.trans hw)
  linarith

theorem maxSaving_nonneg (s : M.State) : 0 ≤ M.maxSaving z₀ K s :=
  le_min M.assetCap_pos.le (sub_nonneg.2 (M.consFloor_le_cash z₀ K s))

theorem continuous_cash : Continuous (M.cash z₀ K) := by
  have hR : Continuous fun s : M.State => M.returnAt z₀ K s.2.node :=
    (continuous_of_discreteTopology (f := fun l : Label Z E => M.returnAt z₀ K l.node)).comp
      continuous_snd
  have hw : Continuous fun s : M.State => M.wageAt z₀ K s.2.node * M.efficiency s.2.idio :=
    (continuous_of_discreteTopology
      (f := fun l : Label Z E => M.wageAt z₀ K l.node * M.efficiency l.idio)).comp
      continuous_snd
  exact ((hR.mul (continuous_subtype_val.comp continuous_fst)).add hw).sub
    (hR.mul continuous_const)

theorem continuous_maxSaving : Continuous (M.maxSaving z₀ K) :=
  continuous_const.min ((M.continuous_cash z₀ K).sub continuous_const)

/-- Consumption, clamped to `[consFloor, max consFloor maxCash]`: the argument of utility in the
reward. -/
noncomputable def clampedConsumption (p : M.State × ℝ) : ℝ :=
  max M.consFloor (min (max M.consFloor M.maxCash) (M.cash z₀ K p.1 - p.2))

theorem continuous_clampedConsumption : Continuous (M.clampedConsumption z₀ K) :=
  continuous_const.max (continuous_const.min
    (((M.continuous_cash z₀ K).comp continuous_fst).sub continuous_snd))

theorem clampedConsumption_mem (p : M.State × ℝ) :
    M.clampedConsumption z₀ K p ∈ Icc M.consFloor (max M.consFloor M.maxCash) :=
  ⟨le_max_left _ _, max_le (le_max_left _ _) (min_le_left _ _)⟩

theorem continuous_rewardFn :
    Continuous fun p : M.State × ℝ => M.utility (M.clampedConsumption z₀ K p) :=
  (M.continuousOn_utility.mono Icc_subset_Ici_self).comp_continuous
    (M.continuous_clampedConsumption z₀ K) (M.clampedConsumption_mem z₀ K)

theorem exists_bound_utility :
    ∃ C, ∀ c ∈ Icc M.consFloor (max M.consFloor M.maxCash), ‖M.utility c‖ ≤ C :=
  isCompact_Icc.exists_bound_of_continuousOn (M.continuousOn_utility.mono Icc_subset_Ici_self)

/-- The household's **reward**: utility of clamped consumption, bounded and continuous. -/
noncomputable def reward : (M.State × ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => M.utility (M.clampedConsumption z₀ K p)) (M.continuous_rewardFn z₀ K)
    M.exists_bound_utility.choose
    fun p => M.exists_bound_utility.choose_spec _ (M.clampedConsumption_mem z₀ K p)

/-- The asset coordinate of a choice, clamped into `[0, assetCap]`. -/
noncomputable def clampAssets (a : ℝ) : ↥(Icc (0 : ℝ) M.assetCap) :=
  projIcc 0 M.assetCap M.assetCap_pos.le a

/-- The state reached after saving `a'` when the shock `(z', e')` occurs. -/
noncomputable def transition (ze : Z × E) : C(M.State × ℝ, M.State) where
  toFun p := (M.clampAssets p.2, ⟨ze.2, ze.1 :: p.1.2.node⟩)
  continuous_toFun := by
    refine Continuous.prodMk ((continuous_projIcc).comp continuous_snd) ?_
    exact (continuous_of_discreteTopology
      (f := fun l : Label Z E => (⟨ze.2, ze.1 :: l.node⟩ : Label Z E))).comp
      (continuous_snd.comp continuous_fst)

/-- The probability of the shock `(z', e')` at node `h` in idiosyncratic state `e`. -/
noncomputable def shockProb (ze : Z × E) : C(M.State × ℝ, ℝ) where
  toFun p := M.aggProb (shockAt z₀ p.1.2.node) ze.1
    * M.idioProb (shockAt z₀ p.1.2.node) ze.1 p.1.2.idio ze.2
  continuous_toFun := (continuous_of_discreteTopology (f := fun l : Label Z E =>
    M.aggProb (shockAt z₀ l.node) ze.1 * M.idioProb (shockAt z₀ l.node) ze.1 l.idio ze.2)).comp
    (continuous_snd.comp continuous_fst)

theorem shockProb_sum (p : M.State × ℝ) : ∑ ze, M.shockProb z₀ ze p = 1 := by
  simp only [shockProb, ContinuousMap.coe_mk]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, M.idioProb_sum, mul_one, M.aggProb_sum]

/-- **The household's problem** along the path `K`, as a stochastic dynamic program. -/
noncomputable def household : StochasticDynamicProgram M.State ℝ (Z × E) where
  feasible s := Icc 0 (M.maxSaving z₀ K s)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty s := nonempty_Icc.2 (M.maxSaving_nonneg z₀ K s)
  upperHemicontinuous_feasible :=
    upperHemicontinuous_Icc continuous_const (M.continuous_maxSaving z₀ K)
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const (M.continuous_maxSaving z₀ K)
      (M.maxSaving_nonneg z₀ K)
  reward := M.reward z₀ K
  transition := M.transition
  prob := M.shockProb z₀
  prob_nonneg _ _ := mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _)
  prob_sum := M.shockProb_sum z₀
  discount := ⟨M.discount, M.discount_pos.le⟩
  discount_lt_one := M.discount_lt_one

/-- On feasible choices consumption is in `[consFloor, maxCash]`, so the clamp does nothing and the
reward is utility of consumption. -/
theorem reward_eq_of_mem_feasible {s : M.State} {a : ℝ}
    (ha : a ∈ (M.household z₀ K).feasible s) :
    (M.household z₀ K).reward (s, a) = M.utility (M.cash z₀ K s - a) := by
  change M.utility (M.clampedConsumption z₀ K (s, a)) = _
  have h1 : M.consFloor ≤ M.cash z₀ K s - a := le_sub_comm.1 (ha.2.trans (min_le_right _ _))
  have h2 : M.cash z₀ K s - a ≤ max M.consFloor M.maxCash :=
    ((sub_le_self _ ha.1).trans (M.cash_le_maxCash z₀ K s)).trans (le_max_right _ _)
  simp only [clampedConsumption, min_eq_right h2, max_eq_right h1]

/-- On feasible choices next period's assets are the choice itself. -/
theorem transition_eq_of_mem_feasible {s : M.State} {a : ℝ}
    (ha : a ∈ (M.household z₀ K).feasible s) (ze : Z × E) :
    (M.household z₀ K).transition ze (s, a)
      = (⟨a, ha.1, ha.2.trans (min_le_left _ _)⟩, ⟨ze.2, ze.1 :: s.2.node⟩) := by
  change (M.clampAssets a, _) = _
  simp only [clampAssets, projIcc_of_mem _ ⟨ha.1, ha.2.trans (min_le_left _ _)⟩]

/-- **The household's Bellman equation along a path.** At every state some feasible
saving attains the value: utility of consumption plus discounted expected value at the
successor nodes. -/
theorem exists_optimal_saving (s : M.State) :
    ∃ a ∈ Icc 0 (M.maxSaving z₀ K s),
      (M.household z₀ K).valueFunction s
        = M.utility (M.cash z₀ K s - a)
          + M.discount * ∑ ze : Z × E, M.aggProb (shockAt z₀ s.2.node) ze.1
              * M.idioProb (shockAt z₀ s.2.node) ze.1 s.2.idio ze.2
              * (M.household z₀ K).valueFunction
                  ((M.household z₀ K).transition ze (s, a)) := by
  obtain ⟨a, ha, hv⟩ := (M.household z₀ K).exists_optimal_policy s
  refine ⟨a, ha, ?_⟩
  rw [hv, M.reward_eq_of_mem_feasible z₀ K ha]
  rfl

end KSModel

end KrusellSmith

end LeanEconomics
