/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.ConsumptionSavingsUnbounded

/-!
# Consumption and savings with `σ > 1` and no cap on assets

The last corner: period utility unbounded *below*, as in
`LeanEconomics.Models.ConsumptionSavingsUnbounded`, together with assets unbounded
*above*, as in `LeanEconomics.Models.ConsumptionSavingsUncapped`.

## The surprise: no weight is needed

Removing the cap for `σ < 1` needed the weighted theory, because utility grows without
bound as consumption does. For `σ > 1` it does not, and the reason is worth stating.

CES utility `c ^ (1 - σ) / (1 - σ)` with `σ > 1` has a negative exponent over a negative
denominator: it is **negative everywhere and rises to `0` as consumption grows**. So it is
bounded above with no cap at all. Only the fall to `-∞` at zero consumption is a problem,
and that is what the floor already handles. The reward therefore lies in
`[floor, uBound]` -- bounded -- and the ordinary bounded theory applies directly.

The hypothesis that does the work is `u_le : ∀ c > 0, u c ≤ uBound`. The cap in
`ConsumptionSavingsUnbounded` existed only to supply such a bound, via
`u maxConsumption`; supplied directly, the cap is unnecessary.

**There is no impatience condition here.** `β (1 + r) < 1` was needed in the `σ < 1`
uncapped model to make the drift condition hold. With utility bounded above the value is
finite whatever the household does, so no such restriction appears. A household with
`β (1 + r) > 1` accumulates without bound, consumption tends to infinity, and utility
tends to `0` from below -- perfectly finite.

## What this does not cover

`σ = 1` exactly. Log utility is unbounded *both* ways: it falls to `-∞` at zero
consumption and rises without bound as consumption grows. The floor handles the first, but
the second needs the weighted theory, and then the argument that the floor never binds
runs into trouble. That argument compares the value at a state to the value at its
successor, and with a weight those bounds grow with the state, so the comparison needs the
value function to be monotone in assets -- which this library does not yet prove. Uncapped
log is therefore still open, and `LeanEconomics.Models.ConsumptionSavingsUnbounded` remains
the only file covering it, with its cap.
-/

open scoped NNReal
open Set BoundedContinuousFunction

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
  /-- Period utility, required to behave only on positive consumption. -/
  u : ℝ → ℝ
  /-- An upper bound on utility. Its existence is what removes the need for a cap. -/
  uBound : ℝ
  /-- The constant that replaces `u` at very low consumption. -/
  floor : ℝ
  /-- A consumption level at which `u` has already fallen below `floor`. -/
  cFloor : ℝ
  income_pos : 0 < income
  interest_gt_neg_one : 0 < 1 + interest
  discount_lt_one : discount < 1
  continuousOn_u : ContinuousOn u (Ioi 0)
  monotoneOn_u : MonotoneOn u (Ioi 0)
  /-- **Utility is bounded above.** -/
  u_le : ∀ c ∈ Ioi (0 : ℝ), u c ≤ uBound
  cFloor_pos : 0 < cFloor
  cFloor_le_income : cFloor ≤ income
  u_cFloor_le_floor : u cFloor ≤ floor
  /-- The floor is low enough that an optimising household never reaches it. -/
  floor_lt : floor * (1 - discount) < u income - discount * uBound

namespace ConsumptionSavingsUncappedCRRA

variable (P : ConsumptionSavingsUncappedCRRA)

/-- Cash on hand. -/
noncomputable def resources (a : ℝ) : ℝ := P.income + (1 + P.interest) * a

/-- Consumption on the budget line. -/
noncomputable def consumption (a a' : ℝ) : ℝ := P.resources a - a'

/-- The largest asset holding that can be carried forward. There is no cap: the household
may save all of its cash on hand. -/
noncomputable def maxSaving (a : ℝ) : ℝ := max 0 (P.resources a)

/-- Consumption clamped below at `cFloor`, where `u` is well behaved. No upper clamp is
needed, because `u` is bounded above. -/
noncomputable def clampC (c : ℝ) : ℝ := max P.cFloor c

/-- The reward: utility of clamped consumption, floored. -/
noncomputable def rewardFn (p : ℝ × ℝ) : ℝ :=
  max P.floor (P.u (P.clampC (P.consumption p.1 p.2)))

theorem discount_lt_one' : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one

theorem one_sub_discount_pos : 0 < 1 - (P.discount : ℝ) := by linarith [P.discount_lt_one']

theorem income_mem : P.income ∈ Ioi (0 : ℝ) := P.income_pos

theorem clampC_mem (c : ℝ) : P.clampC c ∈ Ioi (0 : ℝ) :=
  lt_of_lt_of_le P.cFloor_pos (le_max_left _ _)

theorem cFloor_le_clampC (c : ℝ) : P.cFloor ≤ P.clampC c := le_max_left _ _

theorem u_income_le_uBound : P.u P.income ≤ P.uBound := P.u_le _ P.income_mem

/-- The floor sits strictly below the utility of income. -/
theorem floor_lt_u_income : P.floor < P.u P.income := by
  have h := P.floor_lt
  have hβ := P.one_sub_discount_pos
  have hprod : (P.discount : ℝ) * P.u P.income ≤ P.discount * P.uBound :=
    mul_le_mul_of_nonneg_left P.u_income_le_uBound P.discount.coe_nonneg
  have key : P.floor * (1 - (P.discount : ℝ)) < P.u P.income * (1 - P.discount) := by nlinarith
  exact lt_of_mul_lt_mul_right key hβ.le

theorem floor_le_uBound : P.floor ≤ P.uBound :=
  (P.floor_lt_u_income.trans_le P.u_income_le_uBound).le

theorem rewardFn_le (p : ℝ × ℝ) : P.rewardFn p ≤ P.uBound :=
  max_le P.floor_le_uBound (P.u_le _ (P.clampC_mem _))

theorem floor_le_rewardFn (p : ℝ × ℝ) : P.floor ≤ P.rewardFn p := le_max_left _ _

theorem continuous_resources : Continuous P.resources :=
  continuous_const.add (continuous_const.mul continuous_id)

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max P.continuous_resources

theorem continuous_rewardFn : Continuous P.rewardFn := by
  have hc : Continuous fun p : ℝ × ℝ => P.clampC (P.consumption p.1 p.2) := by
    have : Continuous fun p : ℝ × ℝ => P.consumption p.1 p.2 :=
      (continuous_const.add (continuous_const.mul continuous_fst)).sub continuous_snd
    exact continuous_const.max this
  exact continuous_const.max (P.continuousOn_u.comp_continuous hc fun p => P.clampC_mem _)

theorem abs_rewardFn_le (p : ℝ × ℝ) : |P.rewardFn p| ≤ max |P.floor| |P.uBound| := by
  rw [abs_le]
  refine ⟨?_, (P.rewardFn_le p).trans ((le_abs_self _).trans (le_max_right _ _))⟩
  have h1 : -|P.floor| ≤ P.floor := neg_abs_le _
  have h2 : -(max |P.floor| |P.uBound|) ≤ -|P.floor| := neg_le_neg (le_max_left _ _)
  linarith [P.floor_le_rewardFn p]

/-- The problem as a dynamic program. Note the feasible set is `[0, cash on hand]` with no
upper cap. -/
noncomputable def toDynamicProgram : DynamicProgram ℝ ℝ where
  feasible a := Icc 0 (P.maxSaving a)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  reward := BoundedContinuousFunction.ofNormedAddCommGroup P.rewardFn P.continuous_rewardFn
    (max |P.floor| |P.uBound|) fun p => by
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

/-- **Upper bound on the value**, from the bound on utility -- no cap involved. -/
theorem valueFunction_le (a : ℝ) :
    P.toDynamicProgram.valueFunction a ≤ P.uBound / (1 - P.discount) := by
  set V := P.toDynamicProgram.valueFunction with hV
  have hbdd : BddAbove (Set.range fun s => V s) := by
    refine ⟨‖V‖, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (abs_le.mp (by simpa [Real.norm_eq_abs] using V.norm_coe_le_norm s)).2
  have hVM : ∀ s, V s ≤ ⨆ s, V s := fun s => le_ciSup hbdd s
  have hstep : ∀ s, V s ≤ P.uBound + P.discount * ⨆ s, V s := by
    intro s
    rw [hV, P.valueFunction_eq_bellmanFn s]
    refine P.toDynamicProgram.bellmanFn_le _ fun a' _ => ?_
    rw [P.objective_eq]
    have := P.rewardFn_le (s, a')
    have hβ := P.discount.coe_nonneg
    nlinarith [hVM a']
  have hM : (⨆ s, V s) ≤ P.uBound + P.discount * ⨆ s, V s := ciSup_le hstep
  have hβ := P.one_sub_discount_pos
  have : (⨆ s, V s) ≤ P.uBound / (1 - P.discount) := by
    rw [le_div_iff₀ hβ]; nlinarith
  exact (hVM a).trans this

/-- Saving nothing always leaves consumption at least `income`. -/
theorem u_income_le_rewardFn {a : ℝ} (ha : 0 ≤ a) : P.u P.income ≤ P.rewardFn (a, 0) := by
  have hres : P.income ≤ P.resources a := by
    have : 0 ≤ (1 + P.interest) * a := mul_nonneg P.interest_gt_neg_one.le ha
    simp only [resources]; linarith
  have hcl : P.income ≤ P.clampC (P.consumption a 0) := by
    simp only [clampC, consumption, sub_zero]
    exact le_max_of_le_right hres
  exact le_trans (P.monotoneOn_u P.income_mem (P.clampC_mem _) hcl) (le_max_right _ _)

/-- **Lower bound on the value.** -/
theorem le_valueFunction {a : ℝ} (ha : 0 ≤ a) :
    P.u P.income / (1 - P.discount) ≤ P.toDynamicProgram.valueFunction a := by
  set V := P.toDynamicProgram.valueFunction with hV
  have hstep : ∀ b : ℝ, 0 ≤ b → P.u P.income + P.discount * V 0 ≤ V b := by
    intro b hb
    rw [hV, P.valueFunction_eq_bellmanFn b]
    refine le_trans ?_ (P.toDynamicProgram.le_bellmanFn _ (P.zero_mem_feasible b))
    rw [P.objective_eq]
    have := P.u_income_le_rewardFn hb
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

/-- **The floor never binds at an optimal choice.** -/
theorem floor_lt_rewardFn_optimal {a a' : ℝ} (ha : 0 ≤ a)
    (heq : P.toDynamicProgram.valueFunction a
      = P.rewardFn (a, a') + P.discount * P.toDynamicProgram.valueFunction a') :
    P.floor < P.rewardFn (a, a') := by
  have hlo := P.le_valueFunction ha
  have hhi := P.valueFunction_le a'
  have hβ := P.discount.coe_nonneg
  have hβ1 := P.one_sub_discount_pos
  have hfl := P.floor_lt
  rw [heq] at hlo
  rw [div_le_iff₀ hβ1] at hlo
  rw [le_div_iff₀ hβ1] at hhi
  have hprod : (P.discount : ℝ) * (P.toDynamicProgram.valueFunction a' * (1 - P.discount))
      ≤ P.discount * P.uBound := mul_le_mul_of_nonneg_left hhi hβ
  have key : P.floor * (1 - (P.discount : ℝ))
      < P.rewardFn (a, a') * (1 - P.discount) := by nlinarith
  exact lt_of_mul_lt_mul_right key hβ1.le

/-- The clamp does not bind at an optimal choice either. -/
theorem cFloor_le_consumption_optimal {a a' : ℝ}
    (h : P.floor < P.u (P.clampC (P.consumption a a'))) : P.cFloor ≤ P.consumption a a' := by
  by_contra hlt
  push Not at hlt
  rw [show P.clampC (P.consumption a a') = P.cFloor by
    simp only [clampC, max_eq_left hlt.le]] at h
  exact absurd h (not_lt.mpr P.u_cFloor_le_floor)

/-- **The Bellman equation with honest utility and no cap on assets.** The hypothesis is
only that assets are nonnegative. -/
theorem exists_optimal_saving {a : ℝ} (ha : 0 ≤ a) :
    ∃ a' ∈ Icc 0 (P.maxSaving a),
      P.toDynamicProgram.valueFunction a
        = P.u (P.consumption a a') + P.discount * P.toDynamicProgram.valueFunction a' := by
  obtain ⟨a', ha', heq⟩ := P.toDynamicProgram.exists_optimal_policy a
  have heq' : P.toDynamicProgram.valueFunction a
      = P.rewardFn (a, a') + P.discount * P.toDynamicProgram.valueFunction a' := heq
  refine ⟨a', ha', ?_⟩
  have hlt : P.floor < P.u (P.clampC (P.consumption a a')) := by
    have h := P.floor_lt_rewardFn_optimal ha heq'
    simp only [rewardFn] at h
    rcases lt_max_iff.mp h with h' | h'
    · exact absurd h' (lt_irrefl _)
    · exact h'
  have hclamp : P.clampC (P.consumption a a') = P.consumption a a' :=
    max_eq_right (P.cFloor_le_consumption_optimal hlt)
  rw [heq']
  simp only [rewardFn]
  rw [max_eq_right hlt.le, hclamp]

/-- A calibration with `σ = 2`: income 1, interest 5%, `β = 0.96`, assets unbounded. CES at
`σ = 2` is `-1 / c`, which is negative everywhere, so `uBound = 0`. Note `β (1 + r) = 1.008
> 1`: no impatience condition is needed here, and this calibration would not satisfy one. -/
noncomputable def calibrated : ConsumptionSavingsUncappedCRRA where
  income := 1
  interest := 1 / 20
  discount := 24 / 25
  u := fun c => -c⁻¹
  uBound := 0
  floor := -100
  cFloor := 1 / 100
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
  cFloor_pos := by norm_num
  cFloor_le_income := by norm_num
  u_cFloor_le_floor := by norm_num
  floor_lt := by push_cast; norm_num

end ConsumptionSavingsUncappedCRRA

end LeanEconomics
