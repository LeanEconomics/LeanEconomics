/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Bellman
import LeanEconomics.Topology.IccCorrespondence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Deterministic consumption and savings

The textbook problem: an agent with constant income `y` and assets `a` earning interest `r`
chooses next period's assets `a'` subject to

  `a' + c = y + (1 + r) * a`,   `c ≥ 0`,   `a' ≥ 0`,

maximising `∑ βᵗ u(cₜ)` with CES (CRRA) period utility `u c = c ^ (1 - σ) / (1 - σ)`.
Labour supply is exogenous and there are no shocks, so `y` is a constant.

This is the first model in this library with a genuinely state-dependent feasible set: the
budget set `[0, y + (1+r)a]` moves with `a`. `LeanEconomics.upperHemicontinuous_Icc` and
`LeanEconomics.lowerHemicontinuous_Icc` discharge the hemicontinuity that Berge needs.

## Two compromises, both forced, both checked

**Assets are capped.** The state space is `[0, ā]`. Some cap is unavoidable: the reward
must be bounded, and with `r > 0` consumption grows without bound as assets do. The
feasible set is therefore `[0, max 0 (min ā (y + (1+r)a))]`. `feasible_subset_Icc` proves
`[0, ā]` is forward-invariant, so the cap is a restriction on where the agent may start,
not a distortion of the problem inside.

**Utility is evaluated at clamped consumption.** `DynamicProgram` requires a reward that is
bounded and continuous on *all* of `ℝ × ℝ`, including points off the budget line where
consumption would be negative and `c ^ (1 - σ)` misbehaves. The reward therefore applies
`u` to `max 0 (min cmax c)`. `rewardFn_eq_utility` proves both clamps are inactive
everywhere on the feasible region, so on the set where the model lives the reward *is* CES
utility of consumption. Without that lemma the formalisation would be of a different model
than the one advertised.

**`σ < 1` is required and is a real restriction.** For `σ ≥ 1`, `u` is unbounded below as
`c → 0` and no bounded-reward formulation can accommodate it. Since most calibrations use
`σ ≥ 1`, covering them means extending the theory to unbounded rewards -- weighted
supremum norms -- which this library does not yet have.

## Main results

* `LeanEconomics.ConsumptionSavings.toDynamicProgram` : the model as a `DynamicProgram`.
* `LeanEconomics.ConsumptionSavings.rewardFn_eq_utility` : the clamps do not bind.
* `LeanEconomics.ConsumptionSavings.bellman_valueFunction` : the value function exists, is
  unique, and satisfies the Bellman equation with honest CES utility.
-/

open scoped NNReal
open Set BoundedContinuousFunction

namespace LeanEconomics

/-- Parameters of the deterministic consumption-savings problem. -/
structure ConsumptionSavings where
  /-- Constant labour income. -/
  income : ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The upper bound imposed on asset holdings. -/
  assetCap : ℝ
  /-- The coefficient of relative risk aversion `σ` in `c ^ (1 - σ) / (1 - σ)`. -/
  crra : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  income_pos : 0 < income
  /-- The gross interest rate is positive. -/
  interest_gt_neg_one : 0 < 1 + interest
  assetCap_nonneg : 0 ≤ assetCap
  crra_nonneg : 0 ≤ crra
  /-- Needed for boundedness of utility; see the module docstring. -/
  crra_lt_one : crra < 1
  discount_lt_one : discount < 1

namespace ConsumptionSavings

variable (P : ConsumptionSavings)

/-- Cash on hand: income plus the gross return on assets. -/
noncomputable def resources (a : ℝ) : ℝ := P.income + (1 + P.interest) * a

/-- Consumption implied by the budget constraint `a' + c = y + (1 + r) a`. -/
noncomputable def consumption (a a' : ℝ) : ℝ := P.resources a - a'

/-- The largest asset holding the agent can carry into next period: all of cash on hand,
capped at `assetCap`, and never negative. -/
noncomputable def maxSaving (a : ℝ) : ℝ := max 0 (min P.assetCap (P.resources a))

/-- The largest consumption attainable from a state in `[0, assetCap]`. -/
noncomputable def maxConsumption : ℝ := P.resources P.assetCap

/-- CES period utility `c ^ (1 - σ) / (1 - σ)`. -/
noncomputable def utility (c : ℝ) : ℝ := c ^ (1 - P.crra) / (1 - P.crra)

/-- The reward, with consumption clamped into `[0, maxConsumption]` so that it is bounded
and continuous on all of `ℝ × ℝ`. `rewardFn_eq_utility` shows the clamping is inactive
wherever the model actually lives. -/
noncomputable def rewardFn (p : ℝ × ℝ) : ℝ :=
  P.utility (max 0 (min P.maxConsumption (P.consumption p.1 p.2)))

theorem one_sub_crra_pos : 0 < 1 - P.crra := by linarith [P.crra_lt_one]

theorem maxConsumption_nonneg : 0 ≤ P.maxConsumption := by
  have := P.income_pos
  have := P.interest_gt_neg_one
  have := P.assetCap_nonneg
  have : 0 ≤ (1 + P.interest) * P.assetCap :=
    mul_nonneg P.interest_gt_neg_one.le P.assetCap_nonneg
  simp only [maxConsumption, resources]
  linarith

theorem continuous_resources : Continuous P.resources :=
  continuous_const.add (continuous_const.mul continuous_id)

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max (continuous_const.min P.continuous_resources)

theorem continuous_utility : Continuous P.utility :=
  (Real.continuous_rpow_const P.one_sub_crra_pos.le).div_const _

theorem continuous_rewardFn : Continuous P.rewardFn := by
  have hc : Continuous fun p : ℝ × ℝ => P.consumption p.1 p.2 :=
    (continuous_const.add (continuous_const.mul continuous_fst)).sub continuous_snd
  exact P.continuous_utility.comp (continuous_const.max (continuous_const.min hc))

theorem rewardFn_nonneg (p : ℝ × ℝ) : 0 ≤ P.rewardFn p :=
  div_nonneg (Real.rpow_nonneg (le_max_left _ _) _) P.one_sub_crra_pos.le

theorem rewardFn_le (p : ℝ × ℝ) : P.rewardFn p ≤ P.utility P.maxConsumption := by
  have h : max 0 (min P.maxConsumption (P.consumption p.1 p.2)) ^ (1 - P.crra)
      ≤ P.maxConsumption ^ (1 - P.crra) :=
    Real.rpow_le_rpow (le_max_left _ _)
      (max_le P.maxConsumption_nonneg (min_le_left _ _)) P.one_sub_crra_pos.le
  simp only [rewardFn, utility]
  exact div_le_div_of_nonneg_right h P.one_sub_crra_pos.le

theorem abs_rewardFn_le (p : ℝ × ℝ) : |P.rewardFn p| ≤ P.utility P.maxConsumption :=
  abs_le.mpr ⟨by linarith [P.rewardFn_nonneg p, P.rewardFn_le p], P.rewardFn_le p⟩

/-- The consumption-savings problem as a dynamic program. -/
noncomputable def toDynamicProgram : DynamicProgram ℝ ℝ where
  feasible a := Icc 0 (P.maxSaving a)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  reward := BoundedContinuousFunction.ofNormedAddCommGroup P.rewardFn P.continuous_rewardFn
    (P.utility P.maxConsumption) fun p => by simpa [Real.norm_eq_abs] using P.abs_rewardFn_le p
  transition := ⟨fun p => p.2, continuous_snd⟩
  discount := P.discount
  discount_lt_one := P.discount_lt_one

@[simp]
theorem feasible_eq (a : ℝ) : P.toDynamicProgram.feasible a = Icc 0 (P.maxSaving a) := rfl

/-- **The asset cap is forward-invariant.** From a state in `[0, ā]` every feasible choice
lands back in `[0, ā]`, so capping assets restricts where the agent may start but does not
distort the problem from there on. -/
theorem feasible_subset_Icc (a : ℝ) : P.toDynamicProgram.feasible a ⊆ Icc 0 P.assetCap := by
  rintro a' ⟨h0, h1⟩
  exact ⟨h0, h1.trans (max_le P.assetCap_nonneg (min_le_left _ _))⟩

/-- **The clamps do not bind.** On the feasible region the reward is exactly CES utility of
consumption, so the dynamic program above is the advertised model and not a truncation of
it. -/
theorem rewardFn_eq_utility {a a' : ℝ} (ha : a ∈ Icc 0 P.assetCap)
    (ha' : a' ∈ P.toDynamicProgram.feasible a) :
    P.rewardFn (a, a') = P.utility (P.consumption a a') := by
  obtain ⟨ha0, hacap⟩ := ha
  obtain ⟨ha'0, ha'max⟩ := ha'
  have hres : 0 ≤ P.resources a := by
    have : 0 ≤ (1 + P.interest) * a := mul_nonneg P.interest_gt_neg_one.le ha0
    simp only [resources]; linarith [P.income_pos]
  -- consumption is nonnegative: the agent cannot save more than cash on hand
  have hc0 : 0 ≤ P.consumption a a' := by
    have : a' ≤ P.resources a := ha'max.trans (max_le hres (min_le_right _ _))
    simp only [consumption]; linarith
  -- and no larger than the most attainable from the capped state space
  have hcmax : P.consumption a a' ≤ P.maxConsumption := by
    have : (1 + P.interest) * a ≤ (1 + P.interest) * P.assetCap :=
      mul_le_mul_of_nonneg_left hacap P.interest_gt_neg_one.le
    simp only [consumption, maxConsumption, resources]
    linarith
  simp only [rewardFn, min_eq_right hcmax, max_eq_right hc0]

/-- The value function satisfies the **Bellman equation** of the consumption-savings
problem, with honest CES utility: from any state in the capped range there is an optimal
saving choice, and the value is the utility of the consumption it leaves plus the
discounted value of the assets carried forward. -/
theorem exists_optimal_saving {a : ℝ} (ha : a ∈ Icc 0 P.assetCap) :
    ∃ a' ∈ Icc 0 (P.maxSaving a),
      P.toDynamicProgram.valueFunction a
        = P.utility (P.consumption a a') + P.discount * P.toDynamicProgram.valueFunction a' := by
  obtain ⟨a', ha', heq⟩ := P.toDynamicProgram.exists_optimal_policy a
  refine ⟨a', ha', ?_⟩
  rw [heq, ← P.rewardFn_eq_utility ha ha']
  rfl

/-- The Bellman equation, as a fixed point statement. -/
theorem bellman_valueFunction :
    P.toDynamicProgram.bellman P.toDynamicProgram.valueFunction
      = P.toDynamicProgram.valueFunction :=
  P.toDynamicProgram.bellman_valueFunction

/-- The value function is the unique bounded continuous solution. -/
theorem eq_valueFunction {v : ℝ →ᵇ ℝ} (hv : P.toDynamicProgram.bellman v = v) :
    v = P.toDynamicProgram.valueFunction :=
  P.toDynamicProgram.eq_valueFunction hv

/-! ### Concavity of the value function

The criterion of `LeanEconomics.DynamicProgram.concaveOn_valueFunction`, discharged on the
compact convex region `[0, assetCap]`. The clamps in `rewardFn` are inactive at every point
involved -- all four lie in the feasible region -- so the reward reduces to CES utility of a
consumption that is affine in the state and the action. -/

theorem concaveOn_utility : ConcaveOn ℝ (Ici 0) P.utility := by
  have hp0 : (0 : ℝ) ≤ 1 - P.crra := P.one_sub_crra_pos.le
  have hp1 : (1 : ℝ) - P.crra ≤ 1 := by linarith [P.crra_nonneg]
  have h := Real.concaveOn_rpow hp0 hp1
  have heq : P.utility = fun c => (1 / (1 - P.crra)) • (c ^ (1 - P.crra)) := by
    funext c
    simp only [utility, smul_eq_mul]
    ring
  rw [heq]
  exact h.smul (div_nonneg zero_le_one P.one_sub_crra_pos.le)

theorem resources_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ P.resources a := by
  have : 0 ≤ (1 + P.interest) * a := mul_nonneg P.interest_gt_neg_one.le ha
  simp only [resources]; linarith [P.income_pos]

/-- On the region the outer clamp in `maxSaving` is inactive, leaving a concave function. -/
theorem maxSaving_eq {a : ℝ} (ha : 0 ≤ a) :
    P.maxSaving a = min P.assetCap (P.resources a) :=
  max_eq_right (le_min P.assetCap_nonneg (P.resources_nonneg ha))

theorem maxSaving_le_assetCap (a : ℝ) : P.maxSaving a ≤ P.assetCap :=
  max_le P.assetCap_nonneg (min_le_left _ _)

/-- Cash on hand is affine in assets. -/
theorem resources_affine {x y θ φ : ℝ} (hθφ : θ + φ = 1) :
    P.resources (θ • x + φ • y) = θ * P.resources x + φ * P.resources y := by
  simp only [resources, smul_eq_mul]
  linear_combination (-P.income) * hθφ

theorem feasible_convex {x y : ℝ} (hx : x ∈ Icc 0 P.assetCap) (hy : y ∈ Icc 0 P.assetCap)
    {ax ay θ φ : ℝ} (hax : ax ∈ P.toDynamicProgram.feasible x)
    (hay : ay ∈ P.toDynamicProgram.feasible y) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hθφ : θ + φ = 1) :
    θ • ax + φ • ay ∈ P.toDynamicProgram.feasible (θ • x + φ • y) := by
  obtain ⟨hax0, haxm⟩ := hax
  obtain ⟨hay0, haym⟩ := hay
  rw [P.maxSaving_eq hx.1] at haxm
  rw [P.maxSaving_eq hy.1] at haym
  have hmix : (0 : ℝ) ≤ θ • x + φ • y := by
    simp only [smul_eq_mul]
    have := mul_nonneg hθ hx.1
    have := mul_nonneg hφ hy.1
    linarith
  refine ⟨by simp only [smul_eq_mul]; nlinarith, ?_⟩
  rw [P.maxSaving_eq hmix]
  refine le_min ?_ ?_
  · have h1 : ax ≤ P.assetCap := haxm.trans (min_le_left _ _)
    have h2 : ay ≤ P.assetCap := haym.trans (min_le_left _ _)
    simp only [smul_eq_mul]
    nlinarith
  · have h1 : ax ≤ P.resources x := haxm.trans (min_le_right _ _)
    have h2 : ay ≤ P.resources y := haym.trans (min_le_right _ _)
    rw [P.resources_affine hθφ]
    simp only [smul_eq_mul]
    nlinarith

theorem consumption_nonneg {x ax : ℝ} (hx : 0 ≤ x)
    (hax : ax ∈ P.toDynamicProgram.feasible x) : 0 ≤ P.consumption x ax := by
  obtain ⟨-, haxm⟩ := hax
  rw [P.maxSaving_eq hx] at haxm
  have : ax ≤ P.resources x := haxm.trans (min_le_right _ _)
  simp only [consumption]; linarith

/-- **The value function is concave on `[0, assetCap]`.** This is what makes the optimal
policy unique, and so what makes an agent distribution a well-defined object. -/
theorem concaveOn_valueFunction :
    ConcaveOn ℝ (Icc 0 P.assetCap) ⇑P.toDynamicProgram.valueFunction := by
  refine P.toDynamicProgram.concaveOn_valueFunction (convex_Icc _ _) ?_ ?_ ?_ ?_
  · intro x hx y hy ax hax ay hay θ φ hθ hφ hθφ
    exact P.feasible_convex hx hy hax hay hθ hφ hθφ
  · intro x hx y hy ax hax ay hay θ φ hθ hφ hθφ
    have hmix : θ • x + φ • y ∈ Icc 0 P.assetCap := convex_Icc _ _ hx hy hθ hφ hθφ
    have hmixa := P.feasible_convex hx hy hax hay hθ hφ hθφ
    have hrx : P.toDynamicProgram.reward (x, ax) = P.utility (P.consumption x ax) :=
      P.rewardFn_eq_utility hx hax
    have hry : P.toDynamicProgram.reward (y, ay) = P.utility (P.consumption y ay) :=
      P.rewardFn_eq_utility hy hay
    have hrm : P.toDynamicProgram.reward (θ • x + φ • y, θ • ax + φ • ay)
        = P.utility (P.consumption (θ • x + φ • y) (θ • ax + φ • ay)) :=
      P.rewardFn_eq_utility hmix hmixa
    have hcmix : P.consumption (θ • x + φ • y) (θ • ax + φ • ay)
        = θ * P.consumption x ax + φ * P.consumption y ay := by
      simp only [consumption]
      rw [P.resources_affine hθφ]
      simp only [smul_eq_mul]
      ring
    rw [hrx, hry, hrm, hcmix]
    have h := P.concaveOn_utility.2 (P.consumption_nonneg hx.1 hax)
      (P.consumption_nonneg hy.1 hay) hθ hφ hθφ
    simpa [smul_eq_mul] using h
  · intro x y ax ay θ φ
    rfl
  · intro x _ a ha
    exact ⟨ha.1, ha.2.trans (P.maxSaving_le_assetCap x)⟩

/-- A calibration: income 1, interest 5%, assets capped at 10, `σ = 1/2`, `β = 0.96`.
Recorded to witness that the parameter restrictions can all hold at once -- otherwise
everything above would be vacuous. -/
noncomputable def calibrated : ConsumptionSavings where
  income := 1
  interest := 1 / 20
  assetCap := 10
  crra := 1 / 2
  discount := 24 / 25
  income_pos := by norm_num
  interest_gt_neg_one := by norm_num
  assetCap_nonneg := by norm_num
  crra_nonneg := by norm_num
  crra_lt_one := by norm_num
  discount_lt_one := by norm_num

end ConsumptionSavings

end LeanEconomics
