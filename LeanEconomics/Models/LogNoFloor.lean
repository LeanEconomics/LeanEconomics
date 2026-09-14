/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Extended
import LeanEconomics.Topology.IccCorrespondence
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Log consumption and savings, without a floor

The same problem as the log case of `LeanEconomics.Models.ConsumptionSavingsUnbounded`, but
posed with an extended-real reward rather than a floored one.

The contrast is the point. There, `u` was replaced by `max floor u` to keep the reward
real-valued, and a chain of results -- bounds on the value function above and below, then
`floor_lt_rewardFn_optimal`, then `cFloor_le_consumption_optimal` -- was needed to show the
floor never binds and so that the model was the advertised one. Here the reward is simply
`-∞` where consumption is zero. `reward_eq_bot` states that outright, at a genuinely
feasible action, and nothing has to be proved about it afterwards.

## The two hypotheses that keep the value finite

Both are supplied by the economics rather than contrived:

* the reward is bounded above on the feasible graph, by `log maxConsumption`;
* saving nothing is always feasible and leaves consumption at least `income`, so the reward
  along that policy is at least `log income`. This is `ExtendedProgram.select`.

## What is not removed

Consumption is still clamped *above*. That has nothing to do with `-∞`: it is the ordinary
boundedness requirement that the weighted theory of
`LeanEconomics.DynamicProgramming.Weighted` exists to relax, and it is orthogonal to the
floor. Combining the extended-real reward with a weight is not done here.
-/

open scoped NNReal
open Set BoundedContinuousFunction

namespace LeanEconomics

/-- Logarithm as a map into the extended reals, taking the value `-∞` at zero and below.
Built from Mathlib's `ENNReal.log`, which is a homeomorphism, so continuity is free. -/
noncomputable def logE (c : ℝ) : EReal := ENNReal.log (ENNReal.ofReal c)

theorem continuous_logE : Continuous logE :=
  ENNReal.logHomeomorph.continuous.comp ENNReal.continuous_ofReal

theorem logE_mono : Monotone logE := fun _ _ h =>
  ENNReal.log_le_log (ENNReal.ofReal_le_ofReal h)

theorem logE_of_pos {c : ℝ} (hc : 0 < c) : logE c = (Real.log c : EReal) :=
  ENNReal.log_ofReal_of_pos hc

@[simp] theorem logE_zero : logE 0 = ⊥ := by simp [logE]

/-- A log consumption-savings problem with a cap on assets. -/
structure LogProgram where
  /-- Constant labour income. -/
  income : ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The upper bound imposed on asset holdings. -/
  assetCap : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  income_pos : 0 < income
  interest_gt_neg_one : 0 < 1 + interest
  assetCap_nonneg : 0 ≤ assetCap
  discount_lt_one : discount < 1

namespace LogProgram

variable (P : LogProgram)

/-- Cash on hand, with assets read as nonnegative so that it never falls below income. -/
noncomputable def resources (a : ℝ) : ℝ := P.income + (1 + P.interest) * max 0 a

/-- The largest consumption the capped problem allows. -/
noncomputable def maxConsumption : ℝ := P.income + (1 + P.interest) * P.assetCap

/-- The largest asset holding that can be carried forward. -/
noncomputable def maxSaving (a : ℝ) : ℝ := max 0 (min P.assetCap (P.resources a))

/-- Consumption on the budget line. -/
noncomputable def consumption (a a' : ℝ) : ℝ := P.resources a - a'

/-- The reward: the logarithm of consumption, clamped above, and `-∞` where consumption is
zero or negative. -/
noncomputable def rewardFn (p : ℝ × ℝ) : EReal :=
  logE (min P.maxConsumption (P.consumption p.1 p.2))

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

theorem maxSaving_le_resources (a : ℝ) : P.maxSaving a ≤ P.resources a :=
  max_le (P.resources_pos a).le (min_le_right _ _)

theorem continuous_resources : Continuous P.resources :=
  continuous_const.add (continuous_const.mul (continuous_const.max continuous_id))

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max (continuous_const.min P.continuous_resources)

theorem continuous_rewardFn : Continuous P.rewardFn := by
  refine continuous_logE.comp (continuous_const.min ?_)
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
  rewardMax := Real.log P.maxConsumption
  reward_le := by
    intro s a _
    have h : min P.maxConsumption (P.consumption s a) ≤ P.maxConsumption := min_le_left _ _
    exact le_trans (logE_mono h) (le_of_eq (logE_of_pos P.maxConsumption_pos))
  select := ⟨fun _ => 0, continuous_const⟩
  select_mem := fun _ => ⟨le_rfl, le_max_left _ _⟩
  rewardMin := Real.log P.income
  le_reward_select := by
    intro s
    have h : P.income ≤ min P.maxConsumption (P.consumption s 0) := by
      refine le_min P.income_le_maxConsumption ?_
      simp only [consumption, sub_zero]
      exact P.income_le_resources s
    exact le_trans (le_of_eq (logE_of_pos P.income_pos).symm) (logE_mono h)
  transition := ⟨fun p => p.2, continuous_snd⟩
  discount := P.discount
  discount_lt_one := P.discount_lt_one

@[simp]
theorem feasible_eq (a : ℝ) : P.toExtended.feasible a = Icc 0 (P.maxSaving a) := rfl

/-- **The reward really is `-∞`, at a genuinely feasible action.** Whenever cash on hand
fits under the asset cap, saving all of it is available and leaves nothing to consume. This
is the situation every earlier model in this library had to legislate away with a floor;
here it is simply expressed. -/
theorem reward_eq_bot {a : ℝ} (h : P.resources a ≤ P.assetCap) :
    P.resources a ∈ P.toExtended.feasible a ∧ P.rewardFn (a, P.resources a) = ⊥ := by
  refine ⟨⟨(P.resources_pos a).le, ?_⟩, ?_⟩
  · simp only [maxSaving, min_eq_right h]
    exact le_max_right _ _
  · have hc : P.consumption a (P.resources a) = 0 := by simp [consumption]
    rw [rewardFn, hc, min_eq_right P.maxConsumption_pos.le, logE_zero]

/-- **The Bellman equation**, with the reward an extended real and no floor anywhere in the
statement or in anything it depends on. -/
theorem exists_optimal_saving (a : ℝ) :
    ∃ a' ∈ Icc 0 (P.maxSaving a), ((P.toExtended.valueFunction a : ℝ) : EReal)
      = logE (min P.maxConsumption (P.consumption a a'))
        + ((P.discount * P.toExtended.valueFunction a' : ℝ) : EReal) :=
  P.toExtended.exists_optimal_policy a

/-- A calibration, to witness that the hypotheses are satisfiable. -/
noncomputable def calibrated : LogProgram where
  income := 1
  interest := 1 / 20
  assetCap := 10
  discount := 24 / 25
  income_pos := by norm_num
  interest_gt_neg_one := by norm_num
  assetCap_nonneg := by norm_num
  discount_lt_one := by norm_num

end LogProgram

end LeanEconomics
