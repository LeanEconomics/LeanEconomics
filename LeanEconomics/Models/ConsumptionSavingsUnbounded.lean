/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Extended
import LeanEconomics.Topology.IccCorrespondence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Consumption and savings with period utility unbounded below

Period utility may fall to `-∞` at zero consumption, which covers `σ ≥ 1` in the CES family
and log utility. Assets are capped.

## This file used to use a floor

It replaced `u` by `max floor u` to keep the reward real-valued and bounded, and then had
to prove the floor never binds: bounds on the value function above and below, then
`floor_lt_rewardFn_optimal`, then `cFloor_le_consumption_optimal`. Four structure fields
(`floor`, `cFloor`, `u_cFloor_le_floor`, `floor_lt`) and about a hundred and fifty lines of
proof existed only to establish that a device introduced for technical reasons was
invisible in the answer.

With `LeanEconomics.DynamicProgramming.Extended` the reward is simply `-∞` there. All of
that machinery is gone. What replaces it is a single hypothesis, `tendsto_atBot_u`, saying
utility falls to `-∞` at zero consumption -- which is not an extra assumption at all, since
it is precisely the situation that forced the floor.

**Positive consumption at the optimum now comes for free.** It used to be the conclusion of
the floor argument. Now it follows from the value function being real: if the optimal
action left zero consumption the reward would be `-∞`, so the value would be `-∞`, and it
is not. That is `exists_optimal_saving`, which returns `0 < consumption` as part of its
conclusion rather than requiring a separate development.

## What is unchanged

Consumption is still clamped *above*, and assets are still capped. Neither has anything to
do with `-∞`; both are the ordinary requirement that the reward be bounded above, which the
weighted theory addresses separately.

Cash on hand is now computed from `max 0 a` rather than `a`. With a floor, a state with
negative cash on hand received the floor value; without one it would receive `-∞`, which
the framework does not allow. Reading assets as nonnegative keeps the value finite
everywhere, and changes nothing on `[0, assetCap]`, which is where the results are stated.
-/

open scoped NNReal
open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

/-- A consumption-savings problem whose period utility is unbounded below. -/
structure ConsumptionSavingsUnbounded where
  /-- Constant labour income. -/
  income : ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The upper bound imposed on asset holdings. -/
  assetCap : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  /-- Period utility, required to behave only on positive consumption. -/
  u : ℝ → ℝ
  income_pos : 0 < income
  interest_gt_neg_one : 0 < 1 + interest
  assetCap_nonneg : 0 ≤ assetCap
  discount_lt_one : discount < 1
  continuousOn_u : ContinuousOn u (Ioi 0)
  monotoneOn_u : MonotoneOn u (Ioi 0)
  /-- Utility falls to `-∞` as consumption vanishes. This single hypothesis replaces the
  four fields the floored version needed. -/
  tendsto_atBot_u : Tendsto u (𝓝[>] 0) atBot

namespace ConsumptionSavingsUnbounded

variable (P : ConsumptionSavingsUnbounded)

/-- Cash on hand, with assets read as nonnegative. -/
noncomputable def resources (a : ℝ) : ℝ := P.income + (1 + P.interest) * max 0 a

/-- The largest consumption the capped problem allows. -/
noncomputable def maxConsumption : ℝ := P.income + (1 + P.interest) * P.assetCap

/-- The largest asset holding that can be carried forward. -/
noncomputable def maxSaving (a : ℝ) : ℝ := max 0 (min P.assetCap (P.resources a))

/-- Consumption on the budget line. -/
noncomputable def consumption (a a' : ℝ) : ℝ := P.resources a - a'

/-- The reward: utility of consumption clamped above, and `-∞` where consumption vanishes.
No floor. -/
noncomputable def rewardFn (p : ℝ × ℝ) : EReal :=
  extendBot P.u (min P.maxConsumption (P.consumption p.1 p.2))

theorem income_le_resources (a : ℝ) : P.income ≤ P.resources a := by
  have : 0 ≤ (1 + P.interest) * max 0 a :=
    mul_nonneg P.interest_gt_neg_one.le (le_max_left _ _)
  simp only [resources]; linarith

theorem resources_pos (a : ℝ) : 0 < P.resources a :=
  lt_of_lt_of_le P.income_pos (P.income_le_resources a)

theorem income_le_maxConsumption : P.income ≤ P.maxConsumption := by
  have : 0 ≤ (1 + P.interest) * P.assetCap :=
    mul_nonneg P.interest_gt_neg_one.le P.assetCap_nonneg
  simp only [maxConsumption]; linarith

theorem maxConsumption_pos : 0 < P.maxConsumption :=
  lt_of_lt_of_le P.income_pos P.income_le_maxConsumption

theorem continuous_resources : Continuous P.resources :=
  continuous_const.add (continuous_const.mul (continuous_const.max continuous_id))

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max (continuous_const.min P.continuous_resources)

theorem continuous_rewardFn : Continuous P.rewardFn := by
  refine (continuous_extendBot P.continuousOn_u P.tendsto_atBot_u).comp
    (continuous_const.min ?_)
  exact (P.continuous_resources.comp continuous_fst).sub continuous_snd

/-- The problem as a dynamic program with an extended-real reward. -/
noncomputable def toExtended : ExtendedProgram ℝ ℝ where
  feasible a := Icc 0 (P.maxSaving a)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  reward := ⟨P.rewardFn, P.continuous_rewardFn⟩
  rewardMax := P.u P.maxConsumption
  reward_le := by
    intro s a _
    rcases le_or_gt (min P.maxConsumption (P.consumption s a)) 0 with h | h
    · simp only [ContinuousMap.coe_mk, rewardFn]
      rw [extendBot_of_nonpos h]
      exact bot_le
    · simp only [ContinuousMap.coe_mk, rewardFn]
      rw [extendBot_of_pos h, EReal.coe_le_coe_iff]
      exact P.monotoneOn_u h P.maxConsumption_pos (min_le_left _ _)
  select := ⟨fun _ => 0, continuous_const⟩
  select_mem := fun _ => ⟨le_rfl, le_max_left _ _⟩
  rewardMin := P.u P.income
  le_reward_select := by
    intro s
    have h : P.income ≤ min P.maxConsumption (P.consumption s 0) := by
      refine le_min P.income_le_maxConsumption ?_
      simp only [consumption, sub_zero]
      exact P.income_le_resources s
    simp only [ContinuousMap.coe_mk, rewardFn]
    rw [extendBot_of_pos (lt_of_lt_of_le P.income_pos h), EReal.coe_le_coe_iff]
    exact P.monotoneOn_u P.income_pos (lt_of_lt_of_le P.income_pos h) h
  transition := ⟨fun p => p.2, continuous_snd⟩
  discount := P.discount
  discount_lt_one := P.discount_lt_one

@[simp]
theorem feasible_eq (a : ℝ) : P.toExtended.feasible a = Icc 0 (P.maxSaving a) := rfl

theorem consumption_le_maxConsumption {a a' : ℝ} (ha : a ∈ Icc 0 P.assetCap) (ha' : 0 ≤ a') :
    P.consumption a a' ≤ P.maxConsumption := by
  have hmax : max 0 a = a := max_eq_right ha.1
  have : (1 + P.interest) * a ≤ (1 + P.interest) * P.assetCap :=
    mul_le_mul_of_nonneg_left ha.2 P.interest_gt_neg_one.le
  simp only [consumption, resources, maxConsumption, hmax]
  linarith

/-- **The Bellman equation, with honest utility and positive consumption.** That
consumption is positive at the optimum is not assumed and not separately proved: a zero
would make the reward `-∞` and hence the value `-∞`, and the value is real. -/
theorem exists_optimal_saving {a : ℝ} (ha : a ∈ Icc 0 P.assetCap) :
    ∃ a' ∈ Icc 0 (P.maxSaving a), 0 < P.consumption a a' ∧
      P.toExtended.valueFunction a
        = P.u (P.consumption a a') + P.discount * P.toExtended.valueFunction a' := by
  obtain ⟨a', ha', heq⟩ := P.toExtended.exists_optimal_policy a
  -- the reward at the optimum cannot be `⊥`, or the value would not be real
  have hne : P.rewardFn (a, a') ≠ ⊥ := by
    intro hb
    rw [show P.toExtended.reward (a, a') = P.rewardFn (a, a') from rfl, hb,
      EReal.bot_add _] at heq
    exact EReal.coe_ne_bot _ heq
  have hpos : 0 < min P.maxConsumption (P.consumption a a') := by
    by_contra hle
    push Not at hle
    exact hne (extendBot_of_nonpos hle)
  have hc : 0 < P.consumption a a' := lt_of_lt_of_le hpos (min_le_right _ _)
  have hclamp : min P.maxConsumption (P.consumption a a') = P.consumption a a' :=
    min_eq_right (P.consumption_le_maxConsumption ha ha'.1)
  refine ⟨a', ha', hc, ?_⟩
  have hrw : P.toExtended.reward (a, a') = ((P.u (P.consumption a a') : ℝ) : EReal) :=
    calc P.toExtended.reward (a, a')
        = extendBot P.u (min P.maxConsumption (P.consumption a a')) := rfl
      _ = extendBot P.u (P.consumption a a') := by rw [hclamp]
      _ = _ := extendBot_of_pos hc
  rw [hrw, ← EReal.coe_add, EReal.coe_eq_coe_iff] at heq
  exact heq

/-! ### Utilities that qualify -/

/-- CES period utility. -/
noncomputable def crra (σ c : ℝ) : ℝ := c ^ (1 - σ) / (1 - σ)

theorem continuousOn_crra {σ : ℝ} : ContinuousOn (crra σ) (Ioi 0) := fun c hc =>
  (((Real.continuousAt_rpow_const c (1 - σ) (Or.inl (ne_of_gt hc))).div_const _)).continuousWithinAt

theorem monotoneOn_crra {σ : ℝ} (hσ : 1 < σ) : MonotoneOn (crra σ) (Ioi 0) := by
  intro x hx y _ hxy
  have hneg : (1 : ℝ) - σ < 0 := by linarith
  simp only [crra]
  rw [div_le_div_right_of_neg hneg]
  exact Real.rpow_le_rpow_of_nonpos hx hxy hneg.le

theorem continuousOn_log : ContinuousOn Real.log (Ioi 0) :=
  Real.continuousOn_log.mono fun _ hx => ne_of_gt hx

theorem monotoneOn_log : MonotoneOn Real.log (Ioi 0) := Real.strictMonoOn_log.monotoneOn

/-- A calibration with `σ = 2`, where CES utility is `-1 / c`. -/
noncomputable def calibrated : ConsumptionSavingsUnbounded where
  income := 1
  interest := 1 / 20
  assetCap := 10
  discount := 24 / 25
  u := fun c => -c⁻¹
  income_pos := by norm_num
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

/-- A log calibration (`σ = 1`). -/
noncomputable def calibratedLog : ConsumptionSavingsUnbounded where
  income := 1
  interest := 1 / 20
  assetCap := 10
  discount := 24 / 25
  u := Real.log
  income_pos := by norm_num
  interest_gt_neg_one := by norm_num
  assetCap_nonneg := by norm_num
  discount_lt_one := by norm_num
  continuousOn_u := continuousOn_log
  monotoneOn_u := monotoneOn_log
  tendsto_atBot_u := Real.tendsto_log_nhdsGT_zero

end ConsumptionSavingsUnbounded

end LeanEconomics
