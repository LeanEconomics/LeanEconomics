/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Bounds.Basic

/-!
# The closed form for log utility

The classical solution of the savings problem with logarithmic utility: the household
consumes a fixed fraction `1 - β` of gross wealth and its value function is
`log W / (1 - β)` plus a constant. Here `W` is total wealth and `R = 1 + r` the gross
return, so the budget is `c + W' = R * W`.

  `V W = A * log W + B`,  `A = 1 / (1 - β)`,  `c = (1 - β) * R * W`,  `W' = β * R * W`.

## Why this is here

`LeanEconomics.Models.ConsumptionSavingsUnbounded` covers log utility only with a cap on
assets, and the uncapped case resisted the general machinery: the reward is `-∞` at zero
consumption, the device for handling that is a floor, and the floor inflates the only
a-priori bound on the value function available for proving the floor is never reached. The
argument is circular.

Exhibiting the solution sidesteps it entirely. No floor, no weight, no cap, no a-priori
bound: `isGreatest_bellman` says directly that the closed form satisfies the Bellman
equation and that the stated policy attains it.

## What this does and does not claim

It is a *verification* result, pointwise in `W`: the closed form solves the Bellman
equation and the maximum is attained at `policy W`. It is **not** a uniqueness result --
nothing here shows this is the only solution, because that needs a fixed point argument on
a function space, which is exactly what the `-∞` at zero consumption obstructs. Uniqueness
would need an operator admitting extended-real rewards, which this library does not have.

## The open interval is deliberate

The supremum is taken over `W' ∈ Ioo 0 (R * W)`, the strict interior of the budget set,
and not the closed interval. This is not tidiness. Mathlib defines `Real.log 0 = 0` as a
junk value, so at `W' = R * W` the term `log (R * W - W')` evaluates to `0` rather than
`-∞`, and over the closed interval the statement would be false -- a household "consuming
nothing" would appear to collect zero utility rather than `-∞`. The interior is where the
economics lives and where `log` means what it should.

## Main results

* `LeanEconomics.LogSavings.objective_policy` : the closed form satisfies the Bellman
  equation at the stated policy.
* `LeanEconomics.LogSavings.isGreatest_bellman` : and that policy attains the maximum.
-/

open Set

namespace LeanEconomics

/-- A savings problem with log utility, in total wealth. -/
structure LogSavings where
  /-- The gross return `R = 1 + r`. -/
  gross : ℝ
  /-- The discount factor. -/
  discount : ℝ
  gross_pos : 0 < gross
  discount_pos : 0 < discount
  discount_lt_one : discount < 1

namespace LogSavings

variable (P : LogSavings)

theorem one_sub_discount_pos : 0 < 1 - P.discount := by linarith [P.discount_lt_one]

/-- The coefficient on `log W` in the value function. -/
noncomputable def A : ℝ := 1 / (1 - P.discount)

/-- The constant term in the value function. -/
noncomputable def B : ℝ :=
  (Real.log ((1 - P.discount) * P.gross)
    + (P.discount / (1 - P.discount)) * Real.log (P.discount * P.gross)) / (1 - P.discount)

/-- The value function. -/
noncomputable def value (W : ℝ) : ℝ := P.A * Real.log W + P.B

/-- The saving policy: carry forward a fraction `β` of gross wealth. -/
noncomputable def policy (W : ℝ) : ℝ := P.discount * P.gross * W

/-- The consumption policy: consume a fraction `1 - β` of gross wealth. -/
noncomputable def consumption (W : ℝ) : ℝ := (1 - P.discount) * P.gross * W

/-- Current utility plus the discounted value of wealth carried forward. -/
noncomputable def objective (W W' : ℝ) : ℝ :=
  Real.log (P.gross * W - W') + P.discount * P.value W'

theorem A_pos : 0 < P.A := by
  simp only [A]
  exact div_pos one_pos P.one_sub_discount_pos

theorem policy_mem {W : ℝ} (hW : 0 < W) : P.policy W ∈ Ioo 0 (P.gross * W) := by
  have hR := P.gross_pos
  have hβ := P.discount_pos
  constructor
  · simp only [policy]; positivity
  · simp only [policy]
    have h : 0 < (1 - P.discount) * (P.gross * W) :=
      mul_pos P.one_sub_discount_pos (mul_pos hR hW)
    linarith

/-- Consumption under the policy is what the budget leaves. -/
theorem gross_sub_policy (W : ℝ) : P.gross * W - P.policy W = P.consumption W := by
  simp only [policy, consumption]; ring

/-- **The closed form satisfies the Bellman equation** at the stated policy. -/
theorem objective_policy {W : ℝ} (hW : 0 < W) : P.objective W (P.policy W) = P.value W := by
  have h1β := P.one_sub_discount_pos
  have hR := P.gross_pos
  have hβ := P.discount_pos
  have hc : (0 : ℝ) < (1 - P.discount) * P.gross := by positivity
  have hs : (0 : ℝ) < P.discount * P.gross := by positivity
  simp only [objective, policy, value, A, B]
  rw [show P.gross * W - P.discount * P.gross * W = (1 - P.discount) * P.gross * W by ring,
    Real.log_mul (ne_of_gt hc) (ne_of_gt hW), Real.log_mul (ne_of_gt hs) (ne_of_gt hW)]
  field_simp
  ring

/-- The tangent line bound for `log`: the logarithm lies below its tangent at any point. -/
theorem log_le_tangent {t t₀ : ℝ} (ht : 0 < t) (ht₀ : 0 < t₀) :
    Real.log t ≤ Real.log t₀ + (t - t₀) / t₀ := by
  have h := Real.log_le_sub_one_of_pos (div_pos ht ht₀)
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt ht₀)] at h
  have heq : t / t₀ - 1 = (t - t₀) / t₀ := by field_simp
  linarith [heq ▸ h]

/-- **No feasible choice beats the policy.** The proof is the tangent line bound applied to
both terms; the first order condition is exactly the statement that the two linear
corrections cancel. -/
theorem objective_le {W : ℝ} (hW : 0 < W) {W' : ℝ} (hW' : W' ∈ Ioo 0 (P.gross * W)) :
    P.objective W W' ≤ P.value W := by
  obtain ⟨hW'0, hW'lt⟩ := hW'
  have h1β := P.one_sub_discount_pos
  have hR := P.gross_pos
  have hβ := P.discount_pos
  have hc0 : 0 < P.gross * W - W' := by linarith
  have hcs0 : 0 < P.consumption W := by simp only [consumption]; positivity
  have hWs0 : 0 < P.policy W := by simp only [policy]; positivity
  -- the two tangent line bounds
  have h1 : Real.log (P.gross * W - W')
      ≤ Real.log (P.consumption W) + (P.gross * W - W' - P.consumption W) / P.consumption W :=
    log_le_tangent hc0 hcs0
  have h2 : Real.log W' ≤ Real.log (P.policy W) + (W' - P.policy W) / P.policy W :=
    log_le_tangent hW'0 hWs0
  have hA : 0 ≤ P.discount * P.A := le_of_lt (mul_pos hβ P.A_pos)
  have hscaled : P.discount * P.A * Real.log W'
      ≤ P.discount * P.A * (Real.log (P.policy W) + (W' - P.policy W) / P.policy W) :=
    mul_le_mul_of_nonneg_left h2 hA
  -- the first order condition: the linear corrections cancel exactly
  have hfoc : (P.gross * W - W' - P.consumption W) / P.consumption W
      + P.discount * P.A * ((W' - P.policy W) / P.policy W) = 0 := by
    simp only [consumption, policy, A]
    field_simp
    ring
  -- assemble, then compare with the value at the policy
  have hval := P.objective_policy hW
  simp only [objective, value] at hval ⊢
  rw [P.gross_sub_policy] at hval
  linarith

/-- **The closed form solves the Bellman equation and the policy attains the maximum.**
This is the verification theorem: no floor, no weight, no cap, and no a-priori bound on the
value function anywhere in the statement or the proof. -/
theorem isGreatest_bellman {W : ℝ} (hW : 0 < W) :
    IsGreatest (P.objective W '' Ioo 0 (P.gross * W)) (P.value W) :=
  ⟨⟨P.policy W, P.policy_mem hW, P.objective_policy hW⟩, by
    rintro _ ⟨W', hW', rfl⟩
    exact P.objective_le hW hW'⟩

/-- The Bellman equation as an economist would write it: consume a fraction `1 - β` of
gross wealth and carry forward the rest. -/
theorem value_eq {W : ℝ} (hW : 0 < W) :
    P.value W = Real.log (P.consumption W) + P.discount * P.value (P.policy W) := by
  rw [← P.objective_policy hW, objective, P.gross_sub_policy]

end LogSavings

end LeanEconomics
