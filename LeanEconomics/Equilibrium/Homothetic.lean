/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.ComparativeStatics
import LeanEconomics.Models.BoundedIncomeFluctuation

/-!
# Homotheticity: scaling the economy

Multiply every income and the asset cap by `λ > 0`. For CRRA the household's problem is the same
problem in different units: the value function is rescaled, the policy scales one for one, and so
does aggregate capital. This is Açıkgöz's Proposition 7 -- aggregate savings homogeneous of
degree one in the wage -- and it is the one comparative static of POLICY that costs nothing,
because it comes from uniqueness of the Bellman fixed point rather than from any comparison of
argmaxes.

## The hypothesis, in the form that covers log

CRRA and log scale differently: `(λc) ^ (1-γ) / (1-γ) = λ ^ (1-γ) · c ^ (1-γ) / (1-γ)` is
multiplicative, while `log (λ c) = log λ + log c` is additive. Both are the affine law

  `u (λ c) = k · u c + m`,  `k > 0`,

with `(k, m) = (λ ^ (1-γ), 0)` for `γ ≠ 1` and `(1, log λ)` for log. The value function then obeys
`V (λ a, z) = k · V (a, z) + m / (1 - β)`, and in both cases the POLICY scales exactly:
`m / (1 - β)` is a constant, and a constant does not move an argmax.

## Why this one is cheap

Every other policy comparison in the development needs Carroll and Kimball. This one does not,
because it is not really a comparison: the scaled problem IS the original problem, and the proof
is to write down the rescaled value function and check it solves the scaled Bellman equation.
Uniqueness of the fixed point does the rest.
-/

open scoped NNReal
open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z assetCap) {lam : ℝ}

/-- **The economy in different units**: every income and the asset cap multiplied by `λ > 0`.
Preferences are untouched -- it is CRRA's own scaling law that makes this a rescaling rather than
a different model. -/
noncomputable def scale (hlam : 0 < lam) : IncomeFluctuation Z (lam * assetCap) where
  income z := lam * P.income z
  transitionMatrix := P.transitionMatrix
  interest := P.interest
  discount := P.discount
  u := P.u
  minIncome := lam * P.minIncome
  maxIncome := lam * P.maxIncome
  minIncome_pos := mul_pos hlam P.minIncome_pos
  minIncome_le z := mul_le_mul_of_nonneg_left (P.minIncome_le z) hlam.le
  le_maxIncome z := mul_le_mul_of_nonneg_left (P.le_maxIncome z) hlam.le
  transitionMatrix_nonneg := P.transitionMatrix_nonneg
  transitionMatrix_sum := P.transitionMatrix_sum
  interest_gt_neg_one := P.interest_gt_neg_one
  assetCap_nonneg := mul_nonneg hlam.le P.assetCap_nonneg
  discount_lt_one := P.discount_lt_one
  dom := P.dom
  Ioi_subset_dom := P.Ioi_subset_dom
  dom_subset_Ici := P.dom_subset_Ici
  continuousOn_u_dom := P.continuousOn_u_dom
  monotoneOn_u_dom := P.monotoneOn_u_dom
  strictConcaveOn_u_dom := P.strictConcaveOn_u_dom
  continuousOn_extendDom := P.continuousOn_extendDom

@[simp] theorem scale_u (hlam : 0 < lam) : (P.scale hlam).u = P.u := rfl
@[simp] theorem scale_dom (hlam : 0 < lam) : (P.scale hlam).dom = P.dom := rfl
@[simp] theorem scale_interest (hlam : 0 < lam) : (P.scale hlam).interest = P.interest := rfl
@[simp] theorem scale_discount (hlam : 0 < lam) :
    ((P.scale hlam).discount : ℝ) = (P.discount : ℝ) := rfl
@[simp] theorem scale_transitionMatrix (hlam : 0 < lam) (z z' : Z) :
    (P.scale hlam).transitionMatrix z z' = P.transitionMatrix z z' := rfl

/-! ### Everything in the budget set scales -/

theorem scale_resources (hlam : 0 < lam) (a : ℝ) (z : Z) :
    (P.scale hlam).resources (lam * a, z) = lam * P.resources (a, z) := by
  simp only [resources, scale, IncomeFluctuation.resources]
  rw [show max 0 (lam * a) = lam * max 0 a from by
    rcases le_total a 0 with h | h
    · rw [max_eq_left h, max_eq_left (by nlinarith)]; ring
    · rw [max_eq_right h, max_eq_right (by positivity)]]
  ring

theorem scale_maxConsumption (hlam : 0 < lam) :
    (P.scale hlam).maxConsumption = lam * P.maxConsumption := by
  simp only [maxConsumption, scale]
  ring

theorem scale_maxSaving (hlam : 0 < lam) (a : ℝ) (z : Z) :
    (P.scale hlam).maxSaving (lam * a, z) = lam * P.maxSaving (a, z) := by
  simp only [maxSaving, P.scale_resources hlam a z]
  rw [show min (lam * assetCap) (lam * P.resources (a, z))
      = lam * min assetCap (P.resources (a, z)) from (mul_min_of_nonneg _ _ hlam.le).symm,
    show max 0 (lam * min assetCap (P.resources (a, z)))
      = lam * max 0 (min assetCap (P.resources (a, z))) from by
        rcases le_total (min assetCap (P.resources (a, z))) 0 with h | h
        · rw [max_eq_left h, max_eq_left (by nlinarith)]; ring
        · rw [max_eq_right h, max_eq_right (by positivity)]]

theorem scale_consumption (hlam : 0 < lam) (a a' : ℝ) (z : Z) :
    (P.scale hlam).consumption (lam * a, z) (lam * a') = lam * P.consumption (a, z) a' := by
  simp only [consumption, P.scale_resources hlam a z]; ring

theorem scale_clampedConsumption (hlam : 0 < lam) (a a' : ℝ) (z : Z) :
    (P.scale hlam).clampedConsumption ((lam * a, z), lam * a')
      = lam * P.clampedConsumption ((a, z), a') := by
  simp only [clampedConsumption]
  rw [P.scale_consumption hlam a a' z, P.scale_maxConsumption hlam]
  rw [show max 0 (lam * P.consumption (a, z) a') = lam * max 0 (P.consumption (a, z) a') from by
    rcases le_total (P.consumption (a, z) a') 0 with h | h
    · rw [max_eq_left h, max_eq_left (by nlinarith)]; ring
    · rw [max_eq_right h, max_eq_right (by positivity)]]
  exact (mul_min_of_nonneg _ _ hlam.le).symm

theorem scale_feasible (hlam : 0 < lam) {a a' : ℝ} {z : Z} :
    lam * a' ∈ (P.scale hlam).toExtended.feasible (lam * a, z)
      ↔ a' ∈ P.toExtended.feasible (a, z) := by
  rw [(P.scale hlam).feasible_eq, P.feasible_eq, P.scale_maxSaving hlam a z]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨nonneg_of_mul_nonneg_right h1 hlam, le_of_mul_le_mul_left h2 hlam⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by positivity, mul_le_mul_of_nonneg_left h2 hlam.le⟩

/-! ### The rescaled value function

`u (λ c) = k · u c + m` is the only thing asked of preferences. The candidate value function for
the scaled economy is `k · V (·/λ) + m/(1-β)`, and the work is to check it solves the scaled
Bellman equation; uniqueness of the fixed point then identifies it. -/

variable {k m : ℝ}

/-- The candidate: the original value function, rescaled. -/
noncomputable def scaledValue (_hlam : 0 < lam) (k m : ℝ) : (ℝ × Z) →ᵇ ℝ :=
  k • (P.toExtended.valueFunction.compContinuous
      ⟨fun p => (p.1 / lam, p.2), by fun_prop⟩)
    + BoundedContinuousFunction.const _ (m / (1 - P.discount))

theorem scaledValue_apply (hlam : 0 < lam) (x : ℝ) (z : Z) :
    P.scaledValue hlam k m (x, z)
      = k * P.toExtended.valueFunction (x / lam, z) + m / (1 - P.discount) := rfl

theorem scaledValue_scaled (hlam : 0 < lam) (a : ℝ) (z : Z) :
    P.scaledValue hlam k m (lam * a, z)
      = k * P.toExtended.valueFunction (a, z) + m / (1 - P.discount) := by
  rw [scaledValue_apply, mul_div_cancel_left₀ a hlam.ne']

/-- The expectation rescales, because the income process is untouched. -/
theorem scale_expect (hlam : 0 < lam) (a a' : ℝ) (z : Z) :
    (P.scale hlam).toExtended.expect (P.scaledValue hlam k m) ((lam * a, z), lam * a')
      = k * P.toExtended.expect P.toExtended.valueFunction ((a, z), a')
        + m / (1 - P.discount) := by
  simp only [ExtendedStochasticProgram.expect]
  have hterm : ∀ z' : Z,
      (P.scale hlam).toExtended.prob z' ((lam * a, z), lam * a')
          * P.scaledValue hlam k m ((P.scale hlam).toExtended.transition z'
              ((lam * a, z), lam * a'))
        = P.transitionMatrix z z'
            * (k * P.toExtended.valueFunction (a', z') + m / (1 - P.discount)) := by
    intro z'
    rw [show (P.scale hlam).toExtended.prob z' ((lam * a, z), lam * a')
        = P.transitionMatrix z z' from rfl,
      show (P.scale hlam).toExtended.transition z' ((lam * a, z), lam * a')
        = (lam * a', z') from rfl, P.scaledValue_scaled hlam a' z']
  have hRHS : ∑ z' : Z, P.toExtended.prob z' ((a, z), a')
        * P.toExtended.valueFunction (P.toExtended.transition z' ((a, z), a'))
      = ∑ z' : Z, P.transitionMatrix z z' * P.toExtended.valueFunction (a', z') := rfl
  rw [Finset.sum_congr rfl fun z' _ => hterm z', hRHS,
    show (∑ z' : Z, P.transitionMatrix z z'
          * (k * P.toExtended.valueFunction (a', z') + m / (1 - P.discount)))
        = k * (∑ z' : Z, P.transitionMatrix z z' * P.toExtended.valueFunction (a', z'))
          + (∑ z' : Z, P.transitionMatrix z z') * (m / (1 - P.discount)) from by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z' _ => by ring,
    P.transitionMatrix_sum, one_mul]

/-- The reward rescales where utility is defined. -/
theorem scale_reward_of_mem (hlam : 0 < lam) (hdom : ∀ c : ℝ, lam * c ∈ P.dom ↔ c ∈ P.dom)
    (hu : ∀ c ∈ P.dom, P.u (lam * c) = k * P.u c + m) {a a' : ℝ} {z : Z}
    (hmem : P.clampedConsumption ((a, z), a') ∈ P.dom) :
    (P.scale hlam).toExtended.reward ((lam * a, z), lam * a')
      = ((k * P.u (P.clampedConsumption ((a, z), a')) + m : ℝ) : EReal) := by
  have hcl := P.scale_clampedConsumption hlam a a' z
  have hmem' : (P.scale hlam).clampedConsumption ((lam * a, z), lam * a')
      ∈ (P.scale hlam).dom := by
    rw [hcl, P.scale_dom hlam]; exact (hdom _).mpr hmem
  change extendDom (P.scale hlam).dom (P.scale hlam).u _ = _
  rw [extendDom_of_mem hmem', hcl]
  exact congrArg _ (hu _ hmem)

/-- And it is `⊥` exactly where the original reward is. -/
theorem scale_reward_of_not_mem (hlam : 0 < lam)
    (hdom : ∀ c : ℝ, lam * c ∈ P.dom ↔ c ∈ P.dom) {a a' : ℝ} {z : Z}
    (hmem : P.clampedConsumption ((a, z), a') ∉ P.dom) :
    (P.scale hlam).toExtended.reward ((lam * a, z), lam * a') = ⊥ := by
  have hcl := P.scale_clampedConsumption hlam a a' z
  have hmem' : (P.scale hlam).clampedConsumption ((lam * a, z), lam * a')
      ∉ (P.scale hlam).dom := by
    rw [hcl, P.scale_dom hlam]; exact fun h => hmem ((hdom _).mp h)
  change extendDom (P.scale hlam).dom (P.scale hlam).u _ = _
  rw [extendDom_of_not_mem hmem']

theorem reward_eq_of_mem {a a' : ℝ} {z : Z}
    (hmem : P.clampedConsumption ((a, z), a') ∈ P.dom) :
    P.toExtended.reward ((a, z), a')
      = ((P.u (P.clampedConsumption ((a, z), a')) : ℝ) : EReal) :=
  extendDom_of_mem hmem

theorem reward_eq_bot_of_not_mem {a a' : ℝ} {z : Z}
    (hmem : P.clampedConsumption ((a, z), a') ∉ P.dom) :
    P.toExtended.reward ((a, z), a') = ⊥ :=
  extendDom_of_not_mem hmem

/-! ### The scaled Bellman equation, and homotheticity -/

/-- The objectives correspond, action by action. -/
theorem scale_objectiveE (hlam : 0 < lam) (hdom : ∀ c : ℝ, lam * c ∈ P.dom ↔ c ∈ P.dom)
    (hu : ∀ c ∈ P.dom, P.u (lam * c) = k * P.u c + m) (_hk : 0 < k) {a a' : ℝ} {z : Z}
    (hmem : P.clampedConsumption ((a, z), a') ∈ P.dom) {r : ℝ}
    (hr : P.toExtended.objectiveE P.toExtended.valueFunction (a, z) a' = ((r : ℝ) : EReal)) :
    (P.scale hlam).toExtended.objectiveE (P.scaledValue hlam k m) (lam * a, z) (lam * a')
      = ((k * r + m / (1 - P.discount) : ℝ) : EReal) := by
  have hβ : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
  have hne : (1 : ℝ) - P.discount ≠ 0 := by linarith
  rw [ExtendedStochasticProgram.objectiveE] at hr ⊢
  rw [P.reward_eq_of_mem hmem, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hr
  rw [P.scale_reward_of_mem hlam hdom hu hmem, P.scale_expect hlam a a' z,
    ← EReal.coe_add, EReal.coe_eq_coe_iff]
  rw [show (((P.scale hlam).toExtended.discount : ℝ)) = (P.discount : ℝ) from rfl] at *
  rw [show ((P.toExtended.discount : ℝ)) = (P.discount : ℝ) from rfl] at hr
  have hid : m + (P.discount : ℝ) * (m / (1 - P.discount)) = m / (1 - P.discount) := by
    field_simp; ring
  linear_combination k * hr + hid

/-- **The rescaled value function solves the scaled Bellman equation.** -/
theorem bellman_scaledValue (hlam : 0 < lam) (hdom : ∀ c : ℝ, lam * c ∈ P.dom ↔ c ∈ P.dom)
    (hu : ∀ c ∈ P.dom, P.u (lam * c) = k * P.u c + m) (hk : 0 < k) :
    (P.scale hlam).toExtended.bellman (P.scaledValue hlam k m) = P.scaledValue hlam k m := by
  refine BoundedContinuousFunction.ext fun s => ?_
  obtain ⟨x, z⟩ := s
  obtain ⟨a, rfl⟩ : ∃ a : ℝ, x = lam * a := ⟨x / lam, (mul_div_cancel₀ x hlam.ne').symm⟩
  rw [ExtendedStochasticProgram.bellman_apply, P.scaledValue_scaled hlam a z]
  have hfix : P.toExtended.bellmanFn P.toExtended.valueFunction (a, z)
      = P.toExtended.valueFunction (a, z) := by
    conv_rhs => rw [← P.toExtended.bellman_valueFunction]
    rfl
  refine le_antisymm ?_ ?_
  · -- nothing feasible in the scaled economy beats the rescaled value
    refine (P.scale hlam).toExtended.bellmanFn_le _ fun b hb => ?_
    obtain ⟨b', rfl⟩ : ∃ b', b = lam * b' := ⟨b / lam, (mul_div_cancel₀ b hlam.ne').symm⟩
    have hb' : b' ∈ P.toExtended.feasible (a, z) := (P.scale_feasible hlam).mp hb
    by_cases hmem : P.clampedConsumption ((a, z), b') ∈ P.dom
    · set r : ℝ := P.u (P.clampedConsumption ((a, z), b'))
          + (P.discount : ℝ)
            * P.toExtended.expect P.toExtended.valueFunction ((a, z), b') with hrdef
      have hr : P.toExtended.objectiveE P.toExtended.valueFunction (a, z) b'
          = ((r : ℝ) : EReal) := by
        rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_of_mem hmem, ← EReal.coe_add]
        rfl
      have hle := P.toExtended.le_bellmanFn P.toExtended.valueFunction hb'
      rw [hr, hfix, EReal.coe_le_coe_iff] at hle
      rw [P.scale_objectiveE hlam hdom hu hk hmem hr, EReal.coe_le_coe_iff]
      nlinarith [hle, hk]
    · rw [ExtendedStochasticProgram.objectiveE,
        P.scale_reward_of_not_mem hlam hdom hmem, EReal.bot_add]
      exact bot_le
  · -- and the optimal action of the original economy, rescaled, attains it
    obtain ⟨ã, hã, heq⟩ := P.toExtended.exists_optimal_action P.toExtended.valueFunction (a, z)
    rw [hfix] at heq
    have hmem : P.clampedConsumption ((a, z), ã) ∈ P.dom := by
      by_contra hcon
      rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_bot_of_not_mem hcon,
        EReal.bot_add] at heq
      exact EReal.coe_ne_bot _ heq.symm
    have hfeas : lam * ã ∈ (P.scale hlam).toExtended.feasible (lam * a, z) :=
      (P.scale_feasible hlam).mpr hã
    have hle := (P.scale hlam).toExtended.le_bellmanFn (P.scaledValue hlam k m) hfeas
    rw [P.scale_objectiveE hlam hdom hu hk hmem heq] at hle
    exact EReal.coe_le_coe_iff.mp hle

/-- **Homotheticity of the value function.** -/
theorem valueFunction_scale (hlam : 0 < lam) (hdom : ∀ c : ℝ, lam * c ∈ P.dom ↔ c ∈ P.dom)
    (hu : ∀ c ∈ P.dom, P.u (lam * c) = k * P.u c + m) (hk : 0 < k) (a : ℝ) (z : Z) :
    (P.scale hlam).toExtended.valueFunction (lam * a, z)
      = k * P.toExtended.valueFunction (a, z) + m / (1 - P.discount) := by
  have h := (P.scale hlam).toExtended.eq_valueFunction (P.bellman_scaledValue hlam hdom hu hk)
  rw [← h, P.scaledValue_scaled hlam a z]

/-! ### The policy scales one for one

The additive constant `m / (1 - β)` does not move an argmax, so the policy scales exactly even in
the log case, where the value function only shifts. -/

/-- **Homotheticity of the policy.** -/
theorem policy_scale (hlam : 0 < lam) (hdom : ∀ c : ℝ, lam * c ∈ P.dom ↔ c ∈ P.dom)
    (hu : ∀ c ∈ P.dom, P.u (lam * c) = k * P.u c + m) (hk : 0 < k)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.scale hlam).policy (lam * a, z) = lam * P.policy (a, z) := by
  have hamem : lam * a ∈ Icc (0 : ℝ) (lam * assetCap) :=
    ⟨mul_nonneg hlam.le ha.1, mul_le_mul_of_nonneg_left ha.2 hlam.le⟩
  -- the rescaled optimum is optimal in the scaled economy, and the optimum is unique
  refine ((P.scale hlam).eq_policy_of_optimal hamem
    ((P.scale_feasible hlam).mpr (P.policy_mem (a, z))) ?_).symm
  have heq := P.policy_optimal (a, z)
  have hfix : P.toExtended.bellmanFn P.toExtended.valueFunction (a, z)
      = P.toExtended.valueFunction (a, z) := by
    conv_rhs => rw [← P.toExtended.bellman_valueFunction]
    rfl
  rw [hfix] at heq
  have hmem : P.clampedConsumption ((a, z), P.policy (a, z)) ∈ P.dom := by
    by_contra hcon
    rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_bot_of_not_mem hcon,
      EReal.bot_add] at heq
    exact EReal.coe_ne_bot _ heq.symm
  have hV : P.scaledValue hlam k m = (P.scale hlam).toExtended.valueFunction :=
    (P.scale hlam).toExtended.eq_valueFunction (P.bellman_scaledValue hlam hdom hu hk)
  rw [← hV, P.scale_objectiveE hlam hdom hu hk hmem heq]
  have hfixQ : (P.scale hlam).toExtended.bellmanFn (P.scaledValue hlam k m) (lam * a, z)
      = P.scaledValue hlam k m (lam * a, z) := by
    conv_rhs => rw [← P.bellman_scaledValue hlam hdom hu hk]
    rfl
  rw [hfixQ, P.scaledValue_scaled hlam a z]

/-! ### The CRRA and log instances -/

/-- CRRA scales multiplicatively. -/
theorem crraUtility_scale {γ : ℝ} (hγ : γ ≠ 1) (hlam : 0 < lam) (c : ℝ) (hc : 0 ≤ c) :
    crraUtility γ (lam * c) = lam ^ (1 - γ) * crraUtility γ c + 0 := by
  rw [crraUtility_of_ne hγ, crraUtility_of_ne hγ, Real.mul_rpow hlam.le hc]
  ring

/-- Log scales additively: the value function shifts rather than rescaling, and the policy still
scales exactly. -/
theorem log_scale (hlam : 0 < lam) (c : ℝ) (hc : 0 < c) :
    Real.log (lam * c) = 1 * Real.log c + Real.log lam := by
  rw [Real.log_mul hlam.ne' hc.ne']
  ring

/-- Both admissible domains are invariant under positive scaling, which is what lets the argument
run at all. -/
theorem dom_scale_invariant_of_unbounded (hlam : 0 < lam) (hd : P.Unbounded) (c : ℝ) :
    lam * c ∈ P.dom ↔ c ∈ P.dom := by
  rw [hd]
  simp only [mem_Ioi]
  constructor
  · intro h
    have := div_pos h hlam
    rwa [mul_div_cancel_left₀ c hlam.ne'] at this
  · intro h; positivity

theorem dom_scale_invariant_of_bounded (hlam : 0 < lam) (hb : P.Bounded) (c : ℝ) :
    lam * c ∈ P.dom ↔ c ∈ P.dom := by
  rw [hb]
  simp only [mem_Ici]
  constructor
  · intro h
    have := div_nonneg h hlam.le
    rwa [mul_div_cancel_left₀ c hlam.ne'] at this
  · intro h; exact mul_nonneg hlam.le h

/-- **Homotheticity for CES with `γ < 1`.** Scale every income and the cap by `λ`: the policy
scales by `λ` exactly. -/
theorem crra_policy_scale {γ : ℝ} (_hγ0 : 0 < γ) (hγ1 : γ < 1) (hlam : 0 < lam)
    (hb : P.Bounded) (hu : P.u = crraUtility γ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.scale hlam).policy (lam * a, z) = lam * P.policy (a, z) := by
  refine P.policy_scale (k := lam ^ (1 - γ)) (m := 0) hlam
    (P.dom_scale_invariant_of_bounded hlam hb) ?_ (Real.rpow_pos_of_pos hlam _) ha z
  intro c hc
  rw [hu]
  exact crraUtility_scale (by linarith) hlam c (by rw [hb] at hc; exact hc)

end IncomeFluctuation

end LeanEconomics
