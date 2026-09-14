/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.ConsumptionSavings

/-!
# Consumption and savings with period utility unbounded below

`LeanEconomics.ConsumptionSavings` requires `σ < 1`, because for `σ ≥ 1` the CES utility
`c ^ (1 - σ) / (1 - σ)` tends to `-∞` as `c → 0` and cannot be a bounded reward. Since
`σ ≥ 1` covers log utility and essentially every calibration in use, that restriction is
the one worth removing. This file removes it.

## What the obstruction actually is

"Unbounded rewards" names two different problems, and only one of them is in play here.

The *usual* one is a reward unbounded as a function of the **state** -- utility growing
without bound as wealth grows. The standard fix is a weighted supremum norm (Boyd 1990):
work in `{v | sup |v s| / w s < ∞}` for a weight `w`. That machinery does not help here.

The problem here is that the reward is `-∞` at a **feasible action**: from any state the
agent may save everything, leaving `c = 0`, and `u 0 = -∞`. No weight on the state can
repair a reward that is infinite at an interior point of the choice set, so a weighted norm
is the wrong tool.

## The fix, and why it is not a fudge

The reward is `u` floored at a constant `floor`, applied to consumption clamped into
`[cFloor, maxConsumption]`. This is bounded and continuous, so the existing theory applies
unchanged: contraction, unique fixed point, value function iteration, error bound.

That would be worthless if the floor were doing work, so it is proved that it does not.
The argument is self-contained and runs entirely inside the fixed point:

* `valueFunction_le` : since every reward is at most `u maxConsumption`, the value is at
  most `u maxConsumption / (1 - β)`.
* `le_valueFunction` : saving nothing is always feasible and yields at least `u income`
  each period, so the value is at least `u income / (1 - β)`.
* `floor_lt_reward_optimal` : at an optimal action the reward exceeds `floor`, because a
  reward of `floor` would drag the value below the bound just established.

`cFloor_le_consumption_optimal` then rules out the lower clamp the same way, so
`exists_optimal_saving` states the Bellman equation with honest `u` of actual consumption,
no floor and no clamp. Both are devices for making the operator well defined on all of
`ℝ × ℝ`; the agent never visits either. `floor_lt` is exactly the hypothesis that makes the
floor low enough for this, and `exists_floor` shows it can always be met.

## The price

The state space is still capped, as in the bounded case. And `cFloor` must be supplied with
a proof that `u cFloor ≤ floor`: the structure does not assume `u` tends to `-∞`, it just
asks for one consumption level where `u` is already below the floor.
-/

open scoped NNReal
open Set BoundedContinuousFunction

namespace LeanEconomics

/-- A deterministic consumption-savings problem whose period utility is unbounded below.
`u` need only be continuous and increasing on `(0, ∞)`; `floor` and `cFloor` describe a
level below which `u` is replaced by a constant. -/
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
  /-- The constant that replaces `u` at very low consumption. -/
  floor : ℝ
  /-- A consumption level at which `u` has already fallen below `floor`. -/
  cFloor : ℝ
  income_pos : 0 < income
  interest_gt_neg_one : 0 < 1 + interest
  assetCap_nonneg : 0 ≤ assetCap
  discount_lt_one : discount < 1
  continuousOn_u : ContinuousOn u (Ioi 0)
  monotoneOn_u : MonotoneOn u (Ioi 0)
  cFloor_pos : 0 < cFloor
  cFloor_le_income : cFloor ≤ income
  u_cFloor_le_floor : u cFloor ≤ floor
  /-- The floor is low enough that an optimising agent never reaches it. -/
  floor_lt : floor * (1 - discount)
    < u income - discount * u (income + (1 + interest) * assetCap)

namespace ConsumptionSavingsUnbounded

variable (P : ConsumptionSavingsUnbounded)

/-- Cash on hand. -/
noncomputable def resources (a : ℝ) : ℝ := P.income + (1 + P.interest) * a

/-- Consumption implied by the budget constraint. -/
noncomputable def consumption (a a' : ℝ) : ℝ := P.resources a - a'

/-- The largest asset holding that can be carried forward. -/
noncomputable def maxSaving (a : ℝ) : ℝ := max 0 (min P.assetCap (P.resources a))

/-- The largest consumption attainable from the capped state space. -/
noncomputable def maxConsumption : ℝ := P.resources P.assetCap

/-- Consumption clamped into `[cFloor, maxConsumption]`, where `u` is well behaved. -/
noncomputable def clampC (c : ℝ) : ℝ := min P.maxConsumption (max P.cFloor c)

/-- The reward: utility of clamped consumption, floored. -/
noncomputable def rewardFn (p : ℝ × ℝ) : ℝ :=
  max P.floor (P.u (P.clampC (P.consumption p.1 p.2)))

theorem discount_lt_one' : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one

theorem one_sub_discount_pos : 0 < 1 - (P.discount : ℝ) := by
  linarith [P.discount_lt_one']

/-- `floor_lt`, restated with `maxConsumption` folded up. The structure field spells the
expression out, which leaves `linarith` treating the two forms as unrelated atoms. -/
theorem floor_lt' : P.floor * (1 - (P.discount : ℝ))
    < P.u P.income - P.discount * P.u P.maxConsumption := by
  simpa [maxConsumption, resources] using P.floor_lt

theorem income_le_maxConsumption : P.income ≤ P.maxConsumption := by
  have : 0 ≤ (1 + P.interest) * P.assetCap :=
    mul_nonneg P.interest_gt_neg_one.le P.assetCap_nonneg
  simp only [maxConsumption, resources]; linarith

theorem income_mem : P.income ∈ Ioi (0 : ℝ) := P.income_pos

theorem maxConsumption_mem : P.maxConsumption ∈ Ioi (0 : ℝ) :=
  lt_of_lt_of_le P.income_pos P.income_le_maxConsumption

theorem cFloor_le_maxConsumption : P.cFloor ≤ P.maxConsumption :=
  P.cFloor_le_income.trans P.income_le_maxConsumption

theorem clampC_mem_Icc (c : ℝ) : P.clampC c ∈ Icc P.cFloor P.maxConsumption :=
  ⟨le_min P.cFloor_le_maxConsumption (le_max_left _ _), min_le_left _ _⟩

theorem clampC_mem (c : ℝ) : P.clampC c ∈ Ioi (0 : ℝ) :=
  lt_of_lt_of_le P.cFloor_pos (P.clampC_mem_Icc c).1

theorem u_income_le_u_maxConsumption : P.u P.income ≤ P.u P.maxConsumption :=
  P.monotoneOn_u P.income_mem P.maxConsumption_mem P.income_le_maxConsumption

/-- The floor sits strictly below the utility of income, hence below every utility the
agent can actually achieve. -/
theorem floor_lt_u_income : P.floor < P.u P.income := by
  have h := P.floor_lt'
  have hβ := P.one_sub_discount_pos
  have hprod : (P.discount : ℝ) * P.u P.income ≤ P.discount * P.u P.maxConsumption :=
    mul_le_mul_of_nonneg_left P.u_income_le_u_maxConsumption P.discount.coe_nonneg
  have key : P.floor * (1 - (P.discount : ℝ)) < P.u P.income * (1 - P.discount) := by nlinarith
  exact lt_of_mul_lt_mul_right key hβ.le

theorem floor_le_u_maxConsumption : P.floor ≤ P.u P.maxConsumption :=
  (P.floor_lt_u_income.trans_le P.u_income_le_u_maxConsumption).le

theorem u_clampC_le (c : ℝ) : P.u (P.clampC c) ≤ P.u P.maxConsumption :=
  P.monotoneOn_u (P.clampC_mem c) P.maxConsumption_mem (P.clampC_mem_Icc c).2

theorem rewardFn_le (p : ℝ × ℝ) : P.rewardFn p ≤ P.u P.maxConsumption :=
  max_le P.floor_le_u_maxConsumption (P.u_clampC_le _)

theorem floor_le_rewardFn (p : ℝ × ℝ) : P.floor ≤ P.rewardFn p := le_max_left _ _

theorem continuous_resources : Continuous P.resources :=
  continuous_const.add (continuous_const.mul continuous_id)

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max (continuous_const.min P.continuous_resources)

theorem continuous_rewardFn : Continuous P.rewardFn := by
  have hc : Continuous fun p : ℝ × ℝ => P.clampC (P.consumption p.1 p.2) := by
    have : Continuous fun p : ℝ × ℝ => P.consumption p.1 p.2 :=
      (continuous_const.add (continuous_const.mul continuous_fst)).sub continuous_snd
    exact continuous_const.min (continuous_const.max this)
  exact continuous_const.max (P.continuousOn_u.comp_continuous hc fun p => P.clampC_mem _)

theorem abs_rewardFn_le (p : ℝ × ℝ) :
    |P.rewardFn p| ≤ max |P.floor| |P.u P.maxConsumption| := by
  rw [abs_le]
  refine ⟨?_, (P.rewardFn_le p).trans ((le_abs_self _).trans (le_max_right _ _))⟩
  have h1 : -|P.floor| ≤ P.floor := neg_abs_le _
  have h2 : -(max |P.floor| |P.u P.maxConsumption|) ≤ -|P.floor| :=
    neg_le_neg (le_max_left _ _)
  linarith [P.floor_le_rewardFn p]

/-- The problem as a dynamic program. -/
noncomputable def toDynamicProgram : DynamicProgram ℝ ℝ where
  feasible a := Icc 0 (P.maxSaving a)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  reward := BoundedContinuousFunction.ofNormedAddCommGroup P.rewardFn P.continuous_rewardFn
    (max |P.floor| |P.u P.maxConsumption|) fun p => by
      simpa [Real.norm_eq_abs] using P.abs_rewardFn_le p
  transition := ⟨fun p => p.2, continuous_snd⟩
  discount := P.discount
  discount_lt_one := P.discount_lt_one

@[simp]
theorem feasible_eq (a : ℝ) : P.toDynamicProgram.feasible a = Icc 0 (P.maxSaving a) := rfl

@[simp]
theorem objective_eq (v : ℝ →ᵇ ℝ) (a a' : ℝ) :
    P.toDynamicProgram.objective v a a' = P.rewardFn (a, a') + P.discount * v a' := rfl

theorem zero_mem_feasible (a : ℝ) : (0 : ℝ) ∈ P.toDynamicProgram.feasible a :=
  ⟨le_refl 0, le_max_left _ _⟩

theorem valueFunction_eq_bellmanFn (a : ℝ) :
    P.toDynamicProgram.valueFunction a
      = P.toDynamicProgram.bellmanFn P.toDynamicProgram.valueFunction a := by
  conv_lhs => rw [← P.toDynamicProgram.bellman_valueFunction]
  rfl

/-- **Upper bound on the value.** No reward exceeds `u maxConsumption`, so no discounted
stream of them exceeds `u maxConsumption / (1 - β)`. -/
theorem valueFunction_le (a : ℝ) :
    P.toDynamicProgram.valueFunction a ≤ P.u P.maxConsumption / (1 - P.discount) := by
  set V := P.toDynamicProgram.valueFunction with hV
  have hbdd : BddAbove (Set.range fun s => V s) := by
    refine ⟨‖V‖, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (abs_le.mp (by simpa [Real.norm_eq_abs] using V.norm_coe_le_norm s)).2
  have hVM : ∀ s, V s ≤ ⨆ s, V s := fun s => le_ciSup hbdd s
  have hstep : ∀ s, V s ≤ P.u P.maxConsumption + P.discount * ⨆ s, V s := by
    intro s
    rw [hV, P.valueFunction_eq_bellmanFn s]
    refine P.toDynamicProgram.bellmanFn_le _ fun a' _ => ?_
    rw [P.objective_eq]
    have := P.rewardFn_le (s, a')
    have hβ := P.discount.coe_nonneg
    nlinarith [hVM a']
  have hM : (⨆ s, V s) ≤ P.u P.maxConsumption + P.discount * ⨆ s, V s := ciSup_le hstep
  have hβ := P.one_sub_discount_pos
  have : (⨆ s, V s) ≤ P.u P.maxConsumption / (1 - P.discount) := by
    rw [le_div_iff₀ hβ]; nlinarith
  exact (hVM a).trans this

/-- **Lower bound on the value.** Saving nothing is always feasible and leaves the agent
consuming at least `income` every period. -/
theorem le_valueFunction {a : ℝ} (ha : 0 ≤ a) :
    P.u P.income / (1 - P.discount) ≤ P.toDynamicProgram.valueFunction a := by
  set V := P.toDynamicProgram.valueFunction with hV
  -- the reward from saving nothing is at least `u income`
  have hrew : ∀ b : ℝ, 0 ≤ b → P.u P.income ≤ P.rewardFn (b, 0) := by
    intro b hb
    have hres : P.income ≤ P.resources b := by
      have : 0 ≤ (1 + P.interest) * b := mul_nonneg P.interest_gt_neg_one.le hb
      simp only [resources]; linarith
    have hcl : P.income ≤ P.clampC (P.consumption b 0) := by
      simp only [clampC, consumption, sub_zero]
      exact le_min P.income_le_maxConsumption (le_max_of_le_right hres)
    refine le_trans ?_ (le_max_right _ _)
    exact P.monotoneOn_u P.income_mem (P.clampC_mem _) hcl
  -- hence the value at any nonnegative state dominates the value at 0, one step on
  have hstep : ∀ b : ℝ, 0 ≤ b → P.u P.income + P.discount * V 0 ≤ V b := by
    intro b hb
    rw [hV, P.valueFunction_eq_bellmanFn b]
    refine le_trans ?_ (P.toDynamicProgram.le_bellmanFn _ (P.zero_mem_feasible b))
    rw [P.objective_eq]
    have := hrew b hb
    have hβ := P.discount.coe_nonneg
    nlinarith
  have h0 := hstep 0 le_rfl
  have hβ := P.one_sub_discount_pos
  have hV0 : P.u P.income / (1 - P.discount) ≤ V 0 := by
    rw [div_le_iff₀ hβ]; nlinarith
  refine le_trans ?_ (hstep a ha)
  have hβ' := P.discount.coe_nonneg
  rw [div_le_iff₀ hβ] at hV0 ⊢
  nlinarith

/-- **The floor never binds at an optimal choice.** A reward of `floor` would leave the
agent below the lower bound on the value, which the fixed point forbids. -/
theorem floor_lt_rewardFn_optimal {a a' : ℝ} (ha : 0 ≤ a)
    (heq : P.toDynamicProgram.valueFunction a
      = P.rewardFn (a, a') + P.discount * P.toDynamicProgram.valueFunction a') :
    P.floor < P.rewardFn (a, a') := by
  have hlo := P.le_valueFunction ha
  have hhi := P.valueFunction_le a'
  have hβ := P.discount.coe_nonneg
  have hβ1 := P.one_sub_discount_pos
  have hfl := P.floor_lt'
  rw [heq] at hlo
  rw [div_le_iff₀ hβ1] at hlo
  rw [le_div_iff₀ hβ1] at hhi
  -- discounting the upper bound is the one nonlinear step
  have hprod : (P.discount : ℝ) * (P.toDynamicProgram.valueFunction a' * (1 - P.discount))
      ≤ P.discount * P.u P.maxConsumption := mul_le_mul_of_nonneg_left hhi hβ
  have key : P.floor * (1 - (P.discount : ℝ))
      < P.rewardFn (a, a') * (1 - P.discount) := by nlinarith
  exact lt_of_mul_lt_mul_right key hβ1.le

/-- Consumption never exceeds what the capped state space allows. -/
theorem consumption_le_maxConsumption {a a' : ℝ} (ha : a ≤ P.assetCap) (ha' : 0 ≤ a') :
    P.consumption a a' ≤ P.maxConsumption := by
  have : (1 + P.interest) * a ≤ (1 + P.interest) * P.assetCap :=
    mul_le_mul_of_nonneg_left ha P.interest_gt_neg_one.le
  simp only [consumption, maxConsumption, resources]; linarith

/-- **The lower clamp does not bind at an optimal choice either.** Consumption below
`cFloor` would put utility below `floor`, which the previous result rules out. -/
theorem cFloor_le_consumption_optimal {a a' : ℝ}
    (h : P.floor < P.u (P.clampC (P.consumption a a'))) : P.cFloor ≤ P.consumption a a' := by
  by_contra hlt
  push Not at hlt
  rw [show P.clampC (P.consumption a a') = P.cFloor by
    simp only [clampC, max_eq_left hlt.le, min_eq_right P.cFloor_le_maxConsumption]] at h
  exact absurd h (not_lt.mpr P.u_cFloor_le_floor)

/-- **The Bellman equation with honest, unfloored utility.** From any state in the capped
range there is an optimal saving choice, and the value is the true period utility of the
consumption it leaves plus the discounted value of the assets carried forward. -/
theorem exists_optimal_saving {a : ℝ} (ha : a ∈ Icc 0 P.assetCap) :
    ∃ a' ∈ Icc 0 (P.maxSaving a),
      P.toDynamicProgram.valueFunction a
        = P.u (P.consumption a a') + P.discount * P.toDynamicProgram.valueFunction a' := by
  obtain ⟨a', ha', heq⟩ := P.toDynamicProgram.exists_optimal_policy a
  have heq' : P.toDynamicProgram.valueFunction a
      = P.rewardFn (a, a') + P.discount * P.toDynamicProgram.valueFunction a' := heq
  refine ⟨a', ha', ?_⟩
  have hlt : P.floor < P.u (P.clampC (P.consumption a a')) := by
    have h := P.floor_lt_rewardFn_optimal ha.1 heq'
    simp only [rewardFn] at h
    rcases lt_max_iff.mp h with h' | h'
    · exact absurd h' (lt_irrefl _)
    · exact h'
  have hclamp : P.clampC (P.consumption a a') = P.consumption a a' := by
    simp only [clampC]
    rw [max_eq_right (P.cFloor_le_consumption_optimal hlt),
      min_eq_right (P.consumption_le_maxConsumption ha.2 ha'.1)]
  rw [heq']
  simp only [rewardFn]
  rw [max_eq_right hlt.le, hclamp]

/-- A floor low enough to satisfy `floor_lt` always exists. -/
theorem exists_floor (u : ℝ → ℝ) (income interest assetCap : ℝ) (β : ℝ≥0) (hβ : (β : ℝ) < 1) :
    ∃ L : ℝ, L * (1 - β) < u income - β * u (income + (1 + interest) * assetCap) := by
  refine ⟨(u income - β * u (income + (1 + interest) * assetCap)) / (1 - β) - 1, ?_⟩
  have h : (0 : ℝ) < 1 - β := by linarith
  rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt h)]
  linarith

/-! ### CES / CRRA period utility with `σ > 1` -/

/-- CES (CRRA) period utility `c ^ (1 - σ) / (1 - σ)`. For `σ > 1` this is negative,
increasing, and tends to `-∞` as `c → 0`, so it is exactly the case the bounded-reward
theory cannot reach. -/
noncomputable def crra (σ c : ℝ) : ℝ := c ^ (1 - σ) / (1 - σ)

theorem continuousOn_crra {σ : ℝ} : ContinuousOn (crra σ) (Ioi 0) := fun c hc =>
  (((Real.continuousAt_rpow_const c (1 - σ) (Or.inl (ne_of_gt hc))).div_const _)).continuousWithinAt

/-- With `σ > 1` the exponent is negative, so `c ^ (1 - σ)` falls as `c` rises; dividing by
the negative `1 - σ` flips that back, and utility increases in consumption. -/
theorem monotoneOn_crra {σ : ℝ} (hσ : 1 < σ) : MonotoneOn (crra σ) (Ioi 0) := by
  intro x hx y _ hxy
  have hneg : (1 : ℝ) - σ < 0 := by linarith
  simp only [crra]
  rw [div_le_div_right_of_neg hneg]
  exact Real.rpow_le_rpow_of_nonpos hx hxy hneg.le

/-- CES utility at `σ = 2` is `-1 / c`. Proved rather than asserted, so that `calibrated`
below is demonstrably a `σ = 2` model and not merely something shaped like one. -/
theorem crra_two (c : ℝ) : crra 2 c = -c⁻¹ := by
  rw [crra, show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one, div_neg, div_one]

/-- A calibration with `σ = 2`, which `LeanEconomics.ConsumptionSavings` cannot express at
all: income 1, interest 5%, assets capped at 10, `β = 0.96`. CRRA with `σ = 2` is
`c ^ (-1) / (-1) = -1 / c` by `crra_two`, and is written here in the latter form so the
numeric side conditions are rational arithmetic. Recorded to witness that the hypotheses
are satisfiable. -/
noncomputable def calibrated : ConsumptionSavingsUnbounded where
  income := 1
  interest := 1 / 20
  assetCap := 10
  discount := 24 / 25
  u := fun c => -c⁻¹
  floor := -100
  cFloor := 1 / 100
  income_pos := by norm_num
  interest_gt_neg_one := by norm_num
  assetCap_nonneg := by norm_num
  discount_lt_one := by norm_num
  continuousOn_u := (continuousOn_id.inv₀ fun x hx => ne_of_gt hx).neg
  monotoneOn_u := by
    intro x hx y _ hxy
    have : (0:ℝ) < x := hx
    simp only [neg_le_neg_iff]
    gcongr
  cFloor_pos := by norm_num
  cFloor_le_income := by norm_num
  u_cFloor_le_floor := by norm_num
  floor_lt := by push_cast; norm_num

end ConsumptionSavingsUnbounded

end LeanEconomics
