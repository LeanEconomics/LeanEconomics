/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.ExtendedStochastic
import LeanEconomics.Topology.IccCorrespondence
import LeanEconomics.Models.ConsumptionSavingsUnbounded

/-!
# The income fluctuation problem

The canonical incomplete-markets household: income follows a finite Markov chain, assets
earn interest, borrowing is ruled out, and the household chooses savings. The state is the
pair `(a, z)` of assets and income state, and

  `V (a, z) = max { u c + β * ∑ z', P z z' * V (a', z') }`.

Period utility may fall to `-∞` at zero consumption, so this covers log and CRRA with
`σ ≥ 1`.

## Retrofitted onto extended-real rewards

This file used a floor, with the same apparatus as the deterministic models: `floor`,
`cFloor`, and a chain of results establishing that the floor never binds. All of it is
gone. The reward is `-∞` where consumption vanishes, and positive consumption at the
optimum follows from the value function being real rather than from an argument.

The stochastic case needed `LeanEconomics.DynamicProgramming.ExtendedStochastic`, since the
continuation here is an expectation over shocks rather than `v` at a single point. That
turned out to be routine: the expectation is a sum of reals, so the objective is again an
extended real plus a finite coercion, and the reward's `-∞` never meets the expectation's
arithmetic.

## Unchanged

Discreteness of the income state is still what makes every function of `z` continuous, so
the budget correspondence is continuous in the pair. Consumption is still clamped above and
assets still capped -- the ordinary boundedness requirement, unrelated to the floor. Cash on
hand is computed from `max 0 a`, as in the deterministic retrofits, so that the value stays
finite at every state.
-/

open scoped NNReal
open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

/-- The income fluctuation problem, with period utility unbounded below. -/
structure IncomeFluctuation (Z : Type*) [Fintype Z] [Nonempty Z] [TopologicalSpace Z]
    [DiscreteTopology Z] where
  /-- Income in each state. -/
  income : Z → ℝ
  /-- The Markov transition matrix on income states. -/
  transitionMatrix : Z → Z → ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The upper bound imposed on asset holdings. -/
  assetCap : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  /-- Period utility, required to behave only on positive consumption. -/
  u : ℝ → ℝ
  /-- A lower bound on income. -/
  minIncome : ℝ
  /-- An upper bound on income. -/
  maxIncome : ℝ
  minIncome_pos : 0 < minIncome
  minIncome_le : ∀ z, minIncome ≤ income z
  le_maxIncome : ∀ z, income z ≤ maxIncome
  transitionMatrix_nonneg : ∀ z z', 0 ≤ transitionMatrix z z'
  transitionMatrix_sum : ∀ z, ∑ z', transitionMatrix z z' = 1
  interest_gt_neg_one : 0 < 1 + interest
  assetCap_nonneg : 0 ≤ assetCap
  discount_lt_one : discount < 1
  continuousOn_u : ContinuousOn u (Ioi 0)
  monotoneOn_u : MonotoneOn u (Ioi 0)
  /-- Utility falls to `-∞` as consumption vanishes. -/
  tendsto_atBot_u : Tendsto u (𝓝[>] 0) atBot

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable (P : IncomeFluctuation Z)

/-- Cash on hand, with assets read as nonnegative. -/
noncomputable def resources (s : ℝ × Z) : ℝ := P.income s.2 + (1 + P.interest) * max 0 s.1

/-- The largest consumption the capped problem allows. -/
noncomputable def maxConsumption : ℝ := P.maxIncome + (1 + P.interest) * P.assetCap

/-- The largest asset holding that can be carried forward. -/
noncomputable def maxSaving (s : ℝ × Z) : ℝ := max 0 (min P.assetCap (P.resources s))

/-- Consumption on the budget line. -/
noncomputable def consumption (s : ℝ × Z) (a' : ℝ) : ℝ := P.resources s - a'

/-- The reward: utility of consumption clamped above, and `-∞` where consumption vanishes.
No floor. -/
noncomputable def rewardFn (p : (ℝ × Z) × ℝ) : EReal :=
  extendBot P.u (min P.maxConsumption (P.consumption p.1 p.2))

theorem minIncome_le_resources (s : ℝ × Z) : P.minIncome ≤ P.resources s := by
  have : 0 ≤ (1 + P.interest) * max 0 s.1 :=
    mul_nonneg P.interest_gt_neg_one.le (le_max_left _ _)
  have := P.minIncome_le s.2
  simp only [resources]; linarith

theorem resources_pos (s : ℝ × Z) : 0 < P.resources s :=
  lt_of_lt_of_le P.minIncome_pos (P.minIncome_le_resources s)

theorem minIncome_le_maxIncome : P.minIncome ≤ P.maxIncome :=
  (P.minIncome_le Classical.ofNonempty).trans (P.le_maxIncome _)

theorem minIncome_le_maxConsumption : P.minIncome ≤ P.maxConsumption := by
  have : 0 ≤ (1 + P.interest) * P.assetCap :=
    mul_nonneg P.interest_gt_neg_one.le P.assetCap_nonneg
  simp only [maxConsumption]; linarith [P.minIncome_le_maxIncome]

theorem maxConsumption_pos : 0 < P.maxConsumption :=
  lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxConsumption

/-- Discreteness of `Z` is what makes this continuous. -/
theorem continuous_resources : Continuous P.resources :=
  (continuous_of_discreteTopology.comp continuous_snd).add
    (continuous_const.mul (continuous_const.max continuous_fst))

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max (continuous_const.min P.continuous_resources)

theorem continuous_rewardFn : Continuous P.rewardFn := by
  refine (continuous_extendBot P.continuousOn_u P.tendsto_atBot_u).comp
    (continuous_const.min ?_)
  exact (P.continuous_resources.comp continuous_fst).sub continuous_snd

/-- The problem as a stochastic dynamic program with an extended-real reward. -/
noncomputable def toExtended : ExtendedStochasticProgram (ℝ × Z) ℝ Z where
  feasible s := Icc 0 (P.maxSaving s)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  reward := ⟨P.rewardFn, P.continuous_rewardFn⟩
  rewardMax := P.u P.maxConsumption
  reward_le := by
    intro s a _
    simp only [ContinuousMap.coe_mk, rewardFn]
    rcases le_or_gt (min P.maxConsumption (P.consumption s a)) 0 with h | h
    · rw [extendBot_of_nonpos h]
      exact bot_le
    · rw [extendBot_of_pos h, EReal.coe_le_coe_iff]
      exact P.monotoneOn_u h P.maxConsumption_pos (min_le_left _ _)
  select := ⟨fun _ => 0, continuous_const⟩
  select_mem := fun _ => ⟨le_rfl, le_max_left _ _⟩
  rewardMin := P.u P.minIncome
  le_reward_select := by
    intro s
    simp only [ContinuousMap.coe_mk, rewardFn]
    have h : P.minIncome ≤ min P.maxConsumption (P.consumption s 0) := by
      refine le_min P.minIncome_le_maxConsumption ?_
      simp only [consumption, sub_zero]
      exact P.minIncome_le_resources s
    rw [extendBot_of_pos (lt_of_lt_of_le P.minIncome_pos h), EReal.coe_le_coe_iff]
    exact P.monotoneOn_u P.minIncome_pos (lt_of_lt_of_le P.minIncome_pos h) h
  transition z' := ⟨fun p => (p.2, z'), continuous_snd.prodMk continuous_const⟩
  prob z' := ⟨fun p => P.transitionMatrix p.1.2 z',
    (continuous_of_discreteTopology (f := fun z => P.transitionMatrix z z')).comp
      (continuous_snd.comp continuous_fst)⟩
  prob_nonneg _ _ := P.transitionMatrix_nonneg _ _
  prob_sum p := P.transitionMatrix_sum _
  discount := P.discount
  discount_lt_one := P.discount_lt_one

@[simp]
theorem feasible_eq (s : ℝ × Z) : P.toExtended.feasible s = Icc 0 (P.maxSaving s) := rfl

theorem consumption_le_maxConsumption {s : ℝ × Z} {a' : ℝ} (hs : s.1 ∈ Icc 0 P.assetCap)
    (ha' : 0 ≤ a') : P.consumption s a' ≤ P.maxConsumption := by
  have hmax : max 0 s.1 = s.1 := max_eq_right hs.1
  have : (1 + P.interest) * s.1 ≤ (1 + P.interest) * P.assetCap :=
    mul_le_mul_of_nonneg_left hs.2 P.interest_gt_neg_one.le
  simp only [consumption, resources, maxConsumption, hmax]
  linarith [P.le_maxIncome s.2]

/-- **The stochastic Bellman equation, with honest utility and positive consumption.** That
consumption is positive at the optimum is a consequence of the value being real, not a
separate development. -/
theorem exists_optimal_saving {s : ℝ × Z} (hs : s.1 ∈ Icc 0 P.assetCap) :
    ∃ a' ∈ Icc 0 (P.maxSaving s), 0 < P.consumption s a' ∧
      P.toExtended.valueFunction s
        = P.u (P.consumption s a')
          + P.discount * ∑ z', P.transitionMatrix s.2 z'
              * P.toExtended.valueFunction (a', z') := by
  obtain ⟨a', ha', heq⟩ := P.toExtended.exists_optimal_policy s
  have hne : P.rewardFn (s, a') ≠ ⊥ := by
    intro hb
    rw [show P.toExtended.reward (s, a') = P.rewardFn (s, a') from rfl, hb,
      EReal.bot_add _] at heq
    exact EReal.coe_ne_bot _ heq
  have hpos : 0 < min P.maxConsumption (P.consumption s a') := by
    by_contra hle
    push Not at hle
    exact hne (extendBot_of_nonpos hle)
  have hc : 0 < P.consumption s a' := lt_of_lt_of_le hpos (min_le_right _ _)
  have hclamp : min P.maxConsumption (P.consumption s a') = P.consumption s a' :=
    min_eq_right (P.consumption_le_maxConsumption hs ha'.1)
  refine ⟨a', ha', hc, ?_⟩
  have hrw : P.toExtended.reward (s, a') = ((P.u (P.consumption s a') : ℝ) : EReal) :=
    calc P.toExtended.reward (s, a')
        = extendBot P.u (min P.maxConsumption (P.consumption s a')) := rfl
      _ = extendBot P.u (P.consumption s a') := by rw [hclamp]
      _ = _ := extendBot_of_pos hc
  rw [hrw, ← EReal.coe_add, EReal.coe_eq_coe_iff] at heq
  exact heq

/-- A two-state calibration with `σ = 2`, where CES utility is `-1 / c`. -/
noncomputable def calibrated : IncomeFluctuation (Fin 2) where
  income z := if z = 0 then 1 / 2 else 3 / 2
  transitionMatrix _ _ := 1 / 2
  interest := 1 / 20
  assetCap := 10
  discount := 24 / 25
  u := fun c => -c⁻¹
  minIncome := 1 / 2
  maxIncome := 3 / 2
  minIncome_pos := by norm_num
  minIncome_le z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  assetCap_nonneg := by norm_num
  discount_lt_one := by norm_num
  continuousOn_u := (continuousOn_id.inv₀ fun x hx => ne_of_gt hx).neg
  monotoneOn_u := by
    intro x hx y _ hxy
    have : (0 : ℝ) < x := hx
    simp only [neg_le_neg_iff]
    gcongr
  tendsto_atBot_u := tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero

end IncomeFluctuation

end LeanEconomics
