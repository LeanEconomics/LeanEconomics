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

/-! ### Uniqueness

The verification theorem above says the closed form solves the Bellman equation. This says
nothing else does -- among solutions lying a bounded distance from it.

The argument needs no function space, no contraction and no operator, which is what makes
it available here at all: the machinery those would require is exactly what the `-∞` at
zero consumption obstructs. Instead, a bound of `K` on the deviation improves itself to a
bound of `β * K` in one step, straight from `isGreatest_bellman`, and iterating sends it to
zero. -/

/-- One step of the self-improving bound: if a solution lies within `K` of the closed form,
it lies within `β * K`. -/
theorem abs_sub_value_le_of_bound {v : ℝ → ℝ} {K : ℝ}
    (hv : ∀ W, 0 < W → IsLUB ((fun W' => Real.log (P.gross * W - W') + P.discount * v W') ''
      Ioo 0 (P.gross * W)) (v W))
    (hbound : ∀ W, 0 < W → |v W - P.value W| ≤ K)
    {W : ℝ} (hW : 0 < W) : |v W - P.value W| ≤ P.discount * K := by
  have hβ := P.discount_pos
  rw [abs_le]
  constructor
  · -- the closed form's own policy is available to `v`, and costs at most `β * K`
    have hmem := P.policy_mem hW
    have hle := (hv W hW).1 ⟨P.policy W, hmem, rfl⟩
    have hb := abs_le.mp (hbound (P.policy W) hmem.1)
    have hpol := P.objective_policy hW
    simp only [objective] at hpol
    have hmul := mul_le_mul_of_nonneg_left hb.1 hβ.le
    linarith
  · -- every choice available to `v` is worth at most the closed form's value plus `β * K`
    have hub : v W ≤ P.value W + P.discount * K := by
      refine (hv W hW).2 ?_
      rintro _ ⟨W', hW', rfl⟩
      have hb := abs_le.mp (hbound W' hW'.1)
      have hup := P.objective_le hW hW'
      simp only [objective] at hup
      have hmul := mul_le_mul_of_nonneg_left hb.2 hβ.le
      linarith
    linarith

/-- **Uniqueness of the closed form.** Any solution of the Bellman equation lying a bounded
distance from the closed form equals it. The deviation is squeezed by `βⁿ`. -/
theorem eq_value_of_isLUB {v : ℝ → ℝ} {M : ℝ}
    (hv : ∀ W, 0 < W → IsLUB ((fun W' => Real.log (P.gross * W - W') + P.discount * v W') ''
      Ioo 0 (P.gross * W)) (v W))
    (hM : ∀ W, 0 < W → |v W - P.value W| ≤ M)
    {W : ℝ} (hW : 0 < W) : v W = P.value W := by
  have hβ := P.discount_pos
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 1 one_pos)
  have hiter : ∀ n : ℕ, ∀ X, 0 < X → |v X - P.value X| ≤ P.discount ^ n * M := by
    intro n
    induction n with
    | zero => simpa using hM
    | succ k ih =>
      intro X hX
      have h := P.abs_sub_value_le_of_bound hv ih hX
      calc |v X - P.value X| ≤ P.discount * (P.discount ^ k * M) := h
        _ = P.discount ^ (k + 1) * M := by ring
  have hlim : Filter.Tendsto (fun n : ℕ => P.discount ^ n * M) Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le P.discount_lt_one).mul_const M
  have hle : |v W - P.value W| ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hiter n W hW)
  have : v W - P.value W = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  linarith

end LogSavings

end LeanEconomics
