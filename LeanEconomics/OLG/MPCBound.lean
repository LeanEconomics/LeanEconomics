/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.LifeCycle

/-!
# An upper bound on the propensity to consume

The modulus of `BorrowingLimit` bounds the effect of the borrowing limit by a shift in wealth, so
what converts it into a bound on consumption is an upper bound on the propensity to consume out of
wealth. The repository has the minimal propensity, a lower bound; this file supplies the upper
one, and it does so without derivatives, by the same two-point Euler comparison the rest of the
development uses.

## The step

Write the bound as a secant slope in assets, so that `s_k` bounds
`c_k(a₂) - c_k(a₁)` by `s_k (a₂ - a₁)`. In the last period consumption is cash on hand and the
slope is exactly `R`. One step back, at a state where the lower household saves, the two Euler
inequalities give `c(a₂) ≤ c(a₁)(1 + s_k δ / c_{\min})` with `δ` the difference in saving, and the
budget turns that into

  `s_{k+1} = R · ν/(1+ν)`,  `ν = c · s_k / c_{\min}`

(`stageConsumption_sub_le_of_slope`), with `c` the lower household's consumption and `c_min` a
floor on consumption next period. The map `ν ↦ ν/(1+ν)` is a contraction towards
`1 - 1/ν`, so the slope falls from `R` towards `R(1 - c_min/(c\,s))` as the horizon lengthens:
the longer the life, the smaller the share of an extra unit of wealth that is consumed at once.

## What it is worth

At Aiyagari's calibration, read at zero wealth in the highest earnings state, `c ≈ 1.32` and
`c_min ≈ 0.88`, so `ν ≈ 1.5 s_k` and the recursion settles at a propensity of about `0.36`. The
true propensity there is about `0.04`, the minimal one. The bound is therefore nine times too
large, and nine times too large is not enough: fed through the modulus it bounds the effect of the
borrowing limit on consumption by about `2.5` where the truth is about `0.04`. The loss is the
ratio `c/c_min` of consumption today to the worst consumption tomorrow, which is exactly where the
sandwich's slack of order human wealth enters, and it is the same obstruction that closed the
infinite-horizon routes. So the bound below is a theorem and a useful one, and it is not the last
piece of the threshold argument.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **The terminal slope is `R`.** In the last period consumption is cash on hand. -/
theorem stageConsumption_sub_zero {a₁ a₂ : ℝ} (ha₁ : a₁ ∈ Icc (0 : ℝ) assetCap)
    (ha₂ : a₂ ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.stageConsumption 0 z a₂ - P.stageConsumption 0 z a₁ = (1 + P.interest) * (a₂ - a₁) := by
  rw [P.stageConsumption_zero ha₁ z, P.stageConsumption_zero ha₂ z,
    P.resources_eq_of_mem ha₁ z, P.resources_eq_of_mem ha₂ z]
  ring

/-- **One step of the upper bound on the propensity to consume.** If consumption at stage `k` has
secant slope at most `s` in assets and is at least `cmin`, then at stage `k+1` the slope is at
most `R ν/(1+ν)` with `ν = c s / cmin`, where `c` is consumption at the lower wealth level. No
derivative is taken: the argument is the two-point Euler comparison. -/
theorem stageConsumption_sub_le_of_slope {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, P.stagePolicy j (b, w) < assetCap)
    {s cmin : ℝ} (hs : 0 ≤ s) (hcmin : 0 < cmin) (k : ℕ)
    (hstep : ∀ w : Z, ∀ b₁ ∈ Icc (0 : ℝ) assetCap, ∀ b₂ ∈ Icc (0 : ℝ) assetCap, b₁ ≤ b₂ →
      P.stageConsumption k w b₂ - P.stageConsumption k w b₁ ≤ s * (b₂ - b₁))
    (hfloor : ∀ w : Z, ∀ b ∈ Icc (0 : ℝ) assetCap, cmin ≤ P.stageConsumption k w b)
    (z : Z) {a₁ a₂ : ℝ} (ha₁ : a₁ ∈ Icc (0 : ℝ) assetCap)
    (ha₂ : a₂ ∈ Icc (0 : ℝ) assetCap) (hle : a₁ ≤ a₂)
    (hint : 0 < P.stagePolicy (k + 1) (a₁, z)) :
    P.stageConsumption (k + 1) z a₂ - P.stageConsumption (k + 1) z a₁
      ≤ (P.stageConsumption (k + 1) z a₁ * s / cmin)
        / (1 + P.stageConsumption (k + 1) z a₁ * s / cmin) * ((1 + P.interest) * (a₂ - a₁)) := by
  classical
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  set c₁ : ℝ := P.stageConsumption (k + 1) z a₁ with hc₁
  set c₂ : ℝ := P.stageConsumption (k + 1) z a₂ with hc₂
  have hc₁0 : 0 < c₁ := P.stageConsumption_pos hd _ z ha₁
  have hc₂0 : 0 < c₂ := P.stageConsumption_pos hd _ z ha₂
  set ν : ℝ := c₁ * s / cmin with hν
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hden : (0 : ℝ) < 1 + ν := by linarith
  set b₁ : ℝ := P.stagePolicy (k + 1) (a₁, z) with hb₁
  set b₂ : ℝ := P.stagePolicy (k + 1) (a₂, z) with hb₂
  have hb₁mem : b₁ ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
  have hb₂mem : b₂ ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
  have hbmono : b₁ ≤ b₂ := P.stagePolicy_mono (k + 1) ha₁ ha₂ hle
  -- the budget identity
  have hbudget : c₂ - c₁ = (1 + P.interest) * (a₂ - a₁) - (b₂ - b₁) := by
    have e₁ : c₁ = P.resources (a₁, z) - b₁ := rfl
    have e₂ : c₂ = P.resources (a₂, z) - b₂ := rfl
    rw [e₁, e₂, P.resources_eq_of_mem ha₁ z, P.resources_eq_of_mem ha₂ z]
    ring
  rcases le_or_gt (c₂ - c₁) 0 with hD | hD
  · refine hD.trans ?_
    have : (0 : ℝ) ≤ ν / (1 + ν) := div_nonneg hν0 hden.le
    have h2 : (0 : ℝ) ≤ (1 + P.interest) * (a₂ - a₁) := by
      have : (0 : ℝ) ≤ a₂ - a₁ := by linarith
      positivity
    positivity
  -- the two Euler inequalities
  have hcons : ∀ w : Z, 0 < P.stageConsumption k w b₁ := fun w =>
    P.stageConsumption_pos hd k w hb₁mem
  have hcons₂ : ∀ w : Z, 0 < P.stageConsumption k w b₂ := fun w =>
    P.stageConsumption_pos hd k w hb₂mem
  have hslack₁ : ∀ w : Z, P.stagePolicy k (b₁, w) < P.maxSaving (b₁, w) := by
    intro w
    rw [maxSaving_eq]
    refine lt_min (hslack k b₁ hb₁mem w) ?_
    have h0 : 0 < P.resources (b₁, w) - P.stagePolicy k (b₁, w) := hcons w
    linarith
  have hE₁ := P.stage_euler_ge hu hd k z ha₁ hint hslack₁
  have hroom₂ : b₂ < P.maxSaving (a₂, z) := by
    rw [maxSaving_eq]
    refine lt_min (hslack (k + 1) a₂ ha₂ z) ?_
    have h0 : 0 < P.resources (a₂, z) - b₂ := hc₂0
    linarith
  have hE₂ := P.stage_euler_le hu hd k z ha₂ hroom₂
  -- tomorrow's consumption rises by at most `s δ`, so marginal utility falls by a bounded factor
  set δ : ℝ := b₂ - b₁ with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hfac : (0 : ℝ) < 1 + s * δ / cmin := by positivity
  have hterm : ∀ w : Z, ((1 + s * δ / cmin) * P.stageConsumption k w b₁) ^ (-γ)
      ≤ (P.stageConsumption k w b₂) ^ (-γ) := by
    intro w
    refine rpow_neg_antitone hγ0 (hcons₂ w) ?_
    have h1 := hstep w b₁ hb₁mem b₂ hb₂mem hbmono
    have h2 : s * δ ≤ s * δ / cmin * P.stageConsumption k w b₁ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hcmin]
      exact mul_le_mul_of_nonneg_left (hfloor w b₁ hb₁mem) (by positivity)
    rw [← hδ] at h1
    nlinarith [h1, h2]
  have hsum : ∑ w, P.transitionMatrix z w
        * ((1 + s * δ / cmin) * P.stageConsumption k w b₁) ^ (-γ)
      ≤ ∑ w, P.transitionMatrix z w * (P.stageConsumption k w b₂) ^ (-γ) :=
    Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (hterm w) (P.transitionMatrix_nonneg z w)
  have hpull : ∑ w, P.transitionMatrix z w
        * ((1 + s * δ / cmin) * P.stageConsumption k w b₁) ^ (-γ)
      = (1 + s * δ / cmin) ^ (-γ)
        * ∑ w, P.transitionMatrix z w * (P.stageConsumption k w b₁) ^ (-γ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.mul_rpow hfac.le (hcons w).le]
    ring
  rw [hpull] at hsum
  -- chain: `c₂ ≤ c₁ (1 + s δ / cmin)`
  have hβ0 : (0 : ℝ) ≤ (P.discount : ℝ) := hβ.le
  have hchain : ((1 + s * δ / cmin) * c₁) ^ (-γ) ≤ c₂ ^ (-γ) := by
    have h1 : ((1 + s * δ / cmin) * c₁) ^ (-γ)
        = (1 + s * δ / cmin) ^ (-γ) * c₁ ^ (-γ) := Real.mul_rpow hfac.le hc₁0.le
    have h2 : (1 + s * δ / cmin) ^ (-γ) * c₁ ^ (-γ)
        ≤ (1 + s * δ / cmin) ^ (-γ) * ((P.discount : ℝ) * ((1 + P.interest)
          * ∑ w, P.transitionMatrix z w * (P.stageConsumption k w b₁) ^ (-γ))) :=
      mul_le_mul_of_nonneg_left hE₁ (Real.rpow_nonneg hfac.le _)
    have h3 := mul_le_mul_of_nonneg_left hsum (mul_nonneg hβ0 hR.le)
    rw [h1]
    nlinarith [h2, h3, hE₂]
  have hle₂ : c₂ ≤ (1 + s * δ / cmin) * c₁ :=
    le_of_rpow_neg_le (by positivity) hc₂0 hγ0 hchain
  -- and the budget closes it
  have hcne : cmin ≠ 0 := hcmin.ne'
  have hDν : c₂ - c₁ ≤ ν * δ := by
    have heq : (1 + s * δ / cmin) * c₁ = c₁ + ν * δ := by
      rw [hν]; field_simp
    rw [heq] at hle₂
    linarith
  have hδeq : δ = (1 + P.interest) * (a₂ - a₁) - (c₂ - c₁) := by rw [hbudget]; ring
  rw [hδeq] at hDν
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [hDν]

end IncomeFluctuation

end LeanEconomics
