/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.ConsumptionSavingsUnbounded

/-!
# Consumption and savings with `σ > 1` and no cap on assets

Period utility unbounded *below*, assets unbounded *above*, and -- since this file was
retrofitted onto `LeanEconomics.DynamicProgramming.Extended` -- no floor and no clamp of
any kind.

## Why no weight is needed

CES utility with `σ > 1` has a negative exponent over a negative denominator: it is
negative everywhere and rises to `0` as consumption grows, so it is bounded above with no
cap at all. That is the hypothesis `u_le`. Only the fall to `-∞` at zero consumption is a
problem, and the extended-real reward takes it literally rather than flooring it.

There is no impatience condition either. `β (1 + r) < 1` is needed when a weight is
involved; with utility bounded above the value is finite whatever the household does. The
calibration takes `β (1 + r) = 1.008 > 1` to make the point.

## What the retrofit removed

The fields `floor`, `cFloor`, `u_cFloor_le_floor` and `floor_lt`, and with them
`valueFunction_le`, `le_valueFunction`, `floor_lt_rewardFn_optimal` and
`cFloor_le_consumption_optimal`. Since this model needs no clamp above either, the reward
is now literally `extendBot u (consumption a a')` and nothing stands between the statement
and the economics.
-/

open scoped NNReal
open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

/-- A consumption-savings problem with utility unbounded below but bounded above, and no
cap on assets. -/
structure ConsumptionSavingsUncappedCRRA where
  /-- Constant labour income. -/
  income : ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  /-- Period utility. -/
  u : ℝ → ℝ
  /-- An upper bound on utility. Its existence is what removes the need for a cap. -/
  uBound : ℝ
  income_pos : 0 < income
  interest_gt_neg_one : 0 < 1 + interest
  discount_lt_one : discount < 1
  continuousOn_u : ContinuousOn u (Ioi 0)
  monotoneOn_u : MonotoneOn u (Ioi 0)
  /-- **Utility is bounded above.** -/
  u_le : ∀ c ∈ Ioi (0 : ℝ), u c ≤ uBound
  /-- **Utility falls to `-∞` at zero consumption.** -/
  tendsto_atBot_u : Tendsto u (𝓝[>] 0) atBot

namespace ConsumptionSavingsUncappedCRRA

variable (P : ConsumptionSavingsUncappedCRRA)

/-- Cash on hand, with assets read as nonnegative. -/
noncomputable def resources (a : ℝ) : ℝ := P.income + (1 + P.interest) * max 0 a

/-- Consumption on the budget line. -/
noncomputable def consumption (a a' : ℝ) : ℝ := P.resources a - a'

/-- The reward: utility of consumption, `-∞` where consumption vanishes. No floor, and no
clamp -- utility is bounded above already. -/
noncomputable def rewardFn (p : ℝ × ℝ) : EReal := extendBot P.u (P.consumption p.1 p.2)

theorem income_le_resources (a : ℝ) : P.income ≤ P.resources a := by
  have : 0 ≤ (1 + P.interest) * max 0 a :=
    mul_nonneg P.interest_gt_neg_one.le (le_max_left _ _)
  simp only [resources]; linarith

theorem resources_pos (a : ℝ) : 0 < P.resources a :=
  lt_of_lt_of_le P.income_pos (P.income_le_resources a)

theorem continuous_resources : Continuous P.resources :=
  continuous_const.add (continuous_const.mul (continuous_const.max continuous_id))

theorem monotone_resources : Monotone P.resources := by
  intro x y hxy
  simp only [resources]
  have h := mul_le_mul_of_nonneg_left (max_le_max (le_refl 0) hxy) P.interest_gt_neg_one.le
  linarith

theorem continuous_rewardFn : Continuous P.rewardFn :=
  (continuous_extendBot P.continuousOn_u P.tendsto_atBot_u).comp
    ((P.continuous_resources.comp continuous_fst).sub continuous_snd)

/-- The problem as a dynamic program with an extended-real reward. -/
noncomputable def toExtended : ExtendedProgram ℝ ℝ where
  feasible a := Icc 0 (P.resources a)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty a := nonempty_Icc.mpr (P.resources_pos a).le
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_resources
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_resources fun a =>
      (P.resources_pos a).le
  reward := ⟨P.rewardFn, P.continuous_rewardFn⟩
  rewardMax := P.uBound
  reward_le := by
    intro s a _
    simp only [ContinuousMap.coe_mk, rewardFn]
    rcases le_or_gt (P.consumption s a) 0 with h | h
    · rw [extendBot_of_nonpos h]
      exact bot_le
    · rw [extendBot_of_pos h, EReal.coe_le_coe_iff]
      exact P.u_le _ h
  select := ⟨fun _ => 0, continuous_const⟩
  select_mem := fun a => ⟨le_rfl, (P.resources_pos a).le⟩
  rewardMin := P.u P.income
  le_reward_select := by
    intro s
    simp only [ContinuousMap.coe_mk, rewardFn]
    have hc : P.consumption s 0 = P.resources s := by simp [consumption]
    rw [hc, extendBot_of_pos (P.resources_pos s), EReal.coe_le_coe_iff]
    exact P.monotoneOn_u P.income_pos (P.resources_pos s) (P.income_le_resources s)
  transition := ⟨fun p => p.2, continuous_snd⟩
  discount := P.discount
  discount_lt_one := P.discount_lt_one

@[simp]
theorem feasible_eq (a : ℝ) : P.toExtended.feasible a = Icc 0 (P.resources a) := rfl

/-- **The Bellman equation, with honest utility and positive consumption**, and no upper
bound on assets. -/
theorem exists_optimal_saving (a : ℝ) :
    ∃ a' ∈ Icc 0 (P.resources a), 0 < P.consumption a a' ∧
      P.toExtended.valueFunction a
        = P.u (P.consumption a a') + P.discount * P.toExtended.valueFunction a' := by
  obtain ⟨a', ha', heq⟩ := P.toExtended.exists_optimal_policy a
  have hne : P.rewardFn (a, a') ≠ ⊥ := by
    intro hb
    rw [show P.toExtended.reward (a, a') = P.rewardFn (a, a') from rfl, hb,
      EReal.bot_add _] at heq
    exact EReal.coe_ne_bot _ heq
  have hc : 0 < P.consumption a a' := by
    by_contra hle
    push Not at hle
    exact hne (extendBot_of_nonpos hle)
  refine ⟨a', ha', hc, ?_⟩
  have hrw : P.toExtended.reward (a, a') = ((P.u (P.consumption a a') : ℝ) : EReal) :=
    extendBot_of_pos hc
  rw [hrw, ← EReal.coe_add, EReal.coe_eq_coe_iff] at heq
  exact heq

/-- **The value function is increasing in assets.** -/
theorem monotone_valueFunction : Monotone ⇑P.toExtended.valueFunction := by
  refine P.toExtended.monotone_valueFunction ?_ ?_ ?_
  · intro s s' hss
    exact Icc_subset_Icc (le_refl 0) (P.monotone_resources hss)
  · intro a' x y hxy
    have hcons : P.consumption x a' ≤ P.consumption y a' := by
      simp only [consumption]
      linarith [P.monotone_resources hxy]
    have h : P.rewardFn (x, a') ≤ P.rewardFn (y, a') := extendBot_mono P.monotoneOn_u hcons
    exact h
  · intro a' x y _
    exact le_rfl

/-- A calibration with `σ = 2`, where CES utility is `-1 / c`, so `uBound = 0`. Note
`β (1 + r) = 1.008 > 1`: no impatience condition is needed here. -/
noncomputable def calibrated : ConsumptionSavingsUncappedCRRA where
  income := 1
  interest := 1 / 20
  discount := 24 / 25
  u := fun c => -c⁻¹
  uBound := 0
  income_pos := by norm_num
  interest_gt_neg_one := by norm_num
  discount_lt_one := by norm_num
  continuousOn_u := (continuousOn_id.inv₀ fun x hx => ne_of_gt hx).neg
  monotoneOn_u := by
    intro x hx y _ hxy
    have : (0 : ℝ) < x := hx
    simp only [neg_le_neg_iff]
    gcongr
  u_le c hc := by
    have : (0 : ℝ) < c := hc
    simp only [neg_nonpos]
    positivity
  tendsto_atBot_u := tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero

end ConsumptionSavingsUncappedCRRA

end LeanEconomics
