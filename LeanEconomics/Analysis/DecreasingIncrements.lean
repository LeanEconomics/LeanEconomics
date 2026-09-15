/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Slope

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

/-! ### Lipschitz away from the left endpoint

A concave function on `Ioi 0` need not be Lipschitz there -- utility functions used in
economics are exactly the ones that are not, diverging at zero -- but it IS Lipschitz on
`[δ, ∞)` for any `δ > 0`, with a constant read off a single secant. No differentiability is
needed: the bound comes from antitonicity of secant slopes.

This is what lets a marginal argument be run without a derivative. Where the textbook
argument bounds the marginal utility of consumption by `u'(δ)`, this bounds it by the slope
of `u` across `[δ/2, δ]`, which is available from concavity alone. -/

/-- The secant slope of `u` across `[δ/2, δ]`, which bounds every slope further right. -/
noncomputable def slopeBound (u : ℝ → ℝ) (δ : ℝ) : ℝ := (u δ - u (δ / 2)) / (δ / 2)

theorem slopeBound_nonneg {u : ℝ → ℝ} (hmono : MonotoneOn u (Ioi 0)) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ slopeBound u δ := by
  refine div_nonneg (sub_nonneg.mpr (hmono ?_ ?_ (by linarith))) (by linarith)
  · exact mem_Ioi.mpr (by linarith)
  · exact mem_Ioi.mpr hδ

/-- The one-sided bound: moving right from `a ≥ δ` raises `u` by at most the slope bound
times the distance. -/
theorem ConcaveOn.sub_le_slopeBound_mul {u : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u) {δ : ℝ}
    (hδ : 0 < δ) {a b : ℝ} (ha : δ ≤ a) (hab : a ≤ b) :
    u b - u a ≤ slopeBound u δ * (b - a) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hmemh : δ / 2 ∈ Ioi (0 : ℝ) := mem_Ioi.mpr hhalf
  have hmemd : δ ∈ Ioi (0 : ℝ) := mem_Ioi.mpr hδ
  have hmema : a ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  have hmemb : b ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  -- the slope across `[a, b]` is at most the slope bound
  have hkey : (u b - u a) / (b - a) ≤ slopeBound u δ := by
    rcases eq_or_lt_of_le ha with rfl | hgt
    · -- `a = δ`: one step
      have h := hu.slope_anti_adjacent hmemh hmemb (by linarith) hlt
      simpa only [slopeBound, show δ - δ / 2 = δ / 2 by ring] using h
    · -- `a > δ`: chain two steps through `δ`
      have h1 := hu.slope_anti_adjacent hmemd hmemb hgt hlt
      have h2 := hu.slope_anti_adjacent hmemh hmema (by linarith) hgt
      simp only [slopeBound, show δ - δ / 2 = δ / 2 by ring] at h2 ⊢
      linarith
  rw [div_le_iff₀ (by linarith)] at hkey
  linarith

/-- **A concave function is Lipschitz away from the left endpoint**, with an explicit
constant and no appeal to differentiability. -/
theorem ConcaveOn.abs_sub_le_slopeBound_mul {u : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u)
    (hmono : MonotoneOn u (Ioi 0)) {δ : ℝ} (hδ : 0 < δ) {x y : ℝ}
    (hx : δ ≤ x) (hy : δ ≤ y) :
    |u x - u y| ≤ slopeBound u δ * |x - y| := by
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (hmono (mem_Ioi.mpr (by linarith))
      (mem_Ioi.mpr (by linarith)) h)), abs_of_nonneg (by linarith)]
    exact hu.sub_le_slopeBound_mul hδ hy h
  · rw [abs_sub_comm, abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.mpr (hmono (mem_Ioi.mpr (by linarith))
        (mem_Ioi.mpr (by linarith)) h)), abs_of_nonneg (by linarith)]
    exact hu.sub_le_slopeBound_mul hδ hx h
