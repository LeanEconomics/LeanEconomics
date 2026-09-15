/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Decreasing increments of a concave function

A concave function's increment over an interval of fixed length shrinks as the interval
slides right. In economics this is the increasing-differences (supermodularity) condition
that monotone-comparative-statics arguments run on, usually stated as a cross partial
`-u'' > 0`. Stated this way it needs no derivatives and no smoothness at all.

The proof is two applications of concavity. Writing `L = (c₂ + Δ) - c₁`, the two interior
points `c₁ + Δ` and `c₂` are *complementary* convex combinations of the endpoints `c₁` and
`c₂ + Δ`: the weights on `c₂ + Δ` are `Δ / L` and `(c₂ - c₁) / L`, which sum to one. Adding
the two concavity inequalities makes the weights cancel.
-/

open Set

/-- **Decreasing increments.** For a concave `u`, sliding an interval to the right by `Δ`
cannot increase the increment of `u` across it. -/
theorem ConcaveOn.sub_le_sub_of_shift {s : Set ℝ} {u : ℝ → ℝ} (hu : ConcaveOn ℝ s u)
    {c₁ c₂ Δ : ℝ} (h₁ : c₁ ∈ s) (h₂ : c₂ + Δ ∈ s) (hc : c₁ ≤ c₂) (hΔ : 0 ≤ Δ) :
    u (c₂ + Δ) - u (c₁ + Δ) ≤ u c₂ - u c₁ := by
  rcases eq_or_lt_of_le (show c₁ ≤ c₂ + Δ by linarith) with hdeg | hpos
  · -- `c₁ = c₂ + Δ` forces `Δ = 0` and `c₁ = c₂`, and the claim is an equality
    have hΔ0 : Δ = 0 := by linarith
    have hcc : c₁ = c₂ := by linarith
    subst hΔ0
    simp [hcc]
  · have hL : 0 < c₂ + Δ - c₁ := by linarith
    set θ : ℝ := Δ / (c₂ + Δ - c₁) with hθdef
    have hθ0 : 0 ≤ θ := div_nonneg hΔ hL.le
    have hθ1 : 0 ≤ 1 - θ := by
      rw [hθdef, sub_nonneg, div_le_one hL]
      linarith
    -- `c₁ + Δ` and `c₂` are complementary convex combinations of `c₁` and `c₂ + Δ`
    have e1 : (1 - θ) * c₁ + θ * (c₂ + Δ) = c₁ + Δ := by
      rw [hθdef]; field_simp; ring
    have e2 : θ * c₁ + (1 - θ) * (c₂ + Δ) = c₂ := by
      rw [hθdef]; field_simp; ring
    have i1 := hu.2 h₁ h₂ hθ1 hθ0 (by ring)
    have i2 := hu.2 h₁ h₂ hθ0 hθ1 (by ring)
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, e1] at i1
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, e2] at i2
    nlinarith [i1, i2]
