/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# The increment of capital supply, when Theorem 1 fails

Single crossing does not need capital supply to RISE with the rate. Clearing in wage units is
`S(r) = D(r)` with `D` strictly decreasing and explicit, so uniqueness needs only

  `S(r₂) - S(r₁) > D(r₂) - D(r₁)`  for `r₁ < r₂`,

that supply not fall faster than demand. Measured at the calibration over the bracket `[2%, 8%]`
the two sides differ by a factor of two and more, so a proof may be lossy and still close.

## The coupling

Run the two economies on a common earnings path from the common start `a₀ = 0`, and let
`x j` be the asset gap `a_j(r₂) - a_j(r₁)`. Splitting the step at the lower-rate state,

  `x (j+1) = [g_j²(a_j²) - g_j²(a_j¹)] + [g_j²(a_j¹) - g_j¹(a_j¹)]`,

the first bracket is at least `-L j * negPart (x j)` when saving is nondecreasing in assets and
Lipschitz with constant `L j`, and the second is at least `-e j`, where `e j` measures the failure
of Theorem 1 at age `j`. That is the hypothesis `hrec` below, and it is all the economics the
induction needs.

## Why the bound is not worst-case

`negPart` turns the recursion into one that EXPECTATIONS pass through: from
`x (j+1) ≥ -L j * negPart (x j) - e j` one gets `negPart (x (j+1)) ≤ L j * negPart (x j) + e j`,
whose right-hand side is linear, so averaging over the cohort replaces `e j` by the
MASS-WEIGHTED failure of Theorem 1 rather than its worst case over states. At `γ = 5` that is the
difference between a bound of `0.76` and one of `0.0046` against a budget of `0.67` — between
failing and passing with two orders of magnitude to spare. Theorem 1 may fail, and fail by a lot,
provided it fails on little mass.

## What still has to be supplied

Three inputs, in the order they are needed, none of them about mean field games:

* `L j = (1 - κ_k)(1 + r₂)`, which is saving Lipschitz in assets, i.e. the propensity to consume
  at least `κ_k`. Terminal condition: at the last stage the propensity is exactly `1 = κ₀`. This
  is the companion of `MPCBound`'s upper bound on the slope and is not yet proved.
* `cohortAssets` Lipschitz in assets with constant `cohortSlope`, which follows from the above by
  the induction already written for `cohortFloor`.
* the mass-weighted failure `e j`, for which the accumulation below must come in under
  `D(r₁) - D(r₂)`.
-/

namespace LeanEconomics

namespace OLG

/-- The accumulated gap: `f 0 = 0`, `f (j+1) = L j * f j + e j`. -/
noncomputable def gapAccum (L e : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => L j * gapAccum L e j + e j

@[simp] theorem gapAccum_zero (L e : ℕ → ℝ) : gapAccum L e 0 = 0 := rfl

theorem gapAccum_succ (L e : ℕ → ℝ) (j : ℕ) :
    gapAccum L e (j + 1) = L j * gapAccum L e j + e j := rfl

theorem gapAccum_nonneg {L e : ℕ → ℝ} (hL : ∀ j, 0 ≤ L j) (he : ∀ j, 0 ≤ e j) (j : ℕ) :
    0 ≤ gapAccum L e j := by
  induction j with
  | zero => simp
  | succ j ih => rw [gapAccum_succ]; exact add_nonneg (mul_nonneg (hL j) ih) (he j)

/-- **The gap envelope.** A gap that starts nonnegative and loses at most `L j` times its own
shortfall plus `e j` at each step is never below `-gapAccum L e`. Stated through the negative part,
so that the same proof serves the pathwise and the averaged readings. -/
theorem negPart_le_gapAccum {L e x : ℕ → ℝ} (hL : ∀ j, 0 ≤ L j) (he : ∀ j, 0 ≤ e j)
    (hx0 : 0 ≤ x 0) (hrec : ∀ j, -(L j * max (-(x j)) 0) - e j ≤ x (j + 1)) (j : ℕ) :
    max (-(x j)) 0 ≤ gapAccum L e j := by
  induction j with
  | zero =>
    rw [gapAccum_zero]
    exact max_le (neg_nonpos.2 hx0) le_rfl
  | succ j ih =>
    have hstep : L j * max (-(x j)) 0 ≤ L j * gapAccum L e j :=
      mul_le_mul_of_nonneg_left ih (hL j)
    have hr := hrec j
    have h₂ : -(x (j + 1)) ≤ gapAccum L e (j + 1) := by
      rw [gapAccum_succ]; linarith
    exact max_le h₂ (gapAccum_nonneg hL he (j + 1))

theorem neg_gapAccum_le {L e x : ℕ → ℝ} (hL : ∀ j, 0 ≤ L j) (he : ∀ j, 0 ≤ e j) (hx0 : 0 ≤ x 0)
    (hrec : ∀ j, -(L j * max (-(x j)) 0) - e j ≤ x (j + 1)) (j : ℕ) :
    -gapAccum L e j ≤ x j := by
  have h := le_trans (le_max_left (-(x j)) 0) (negPart_le_gapAccum hL he hx0 hrec j)
  linarith

/-- **The aggregate form.** Averaging over ages, the increment in capital supply is bounded below
by minus the average accumulated gap. This is the quantity that must come in under the fall in the
firm's demand over the same interval of rates. -/
theorem sum_neg_gapAccum_le {L e x : ℕ → ℝ} (hL : ∀ j, 0 ≤ L j) (he : ∀ j, 0 ≤ e j)
    (hx0 : 0 ≤ x 0) (hrec : ∀ j, -(L j * max (-(x j)) 0) - e j ≤ x (j + 1)) (n : ℕ) :
    -∑ j ∈ Finset.range n, gapAccum L e j ≤ ∑ j ∈ Finset.range n, x j := by
  have hneg : -∑ j ∈ Finset.range n, gapAccum L e j
      = ∑ j ∈ Finset.range n, -gapAccum L e j := by simp
  rw [hneg]
  exact Finset.sum_le_sum fun j _ => neg_gapAccum_le hL he hx0 hrec j

/-- **Single crossing from the increment bound.** If supply's increment is at least `-B` and
demand's fall over the same interval strictly exceeds `B`, then excess supply has strictly
increased, which is all single crossing asks of the interval. -/
theorem lt_of_increment_bound {S₁ S₂ D₁ D₂ B : ℝ} (hS : -B ≤ S₂ - S₁) (hD : B < D₁ - D₂) :
    D₂ - D₁ < S₂ - S₁ := by linarith

end OLG

end LeanEconomics
