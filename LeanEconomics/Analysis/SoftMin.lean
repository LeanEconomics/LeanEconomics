/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The weighted soft minimum

The analytic engine of Carroll and Kimball (1996) for the CARA branch of HARA, where `PowerMean`
is the engine for the CRRA branch. With `u' c = exp (-α c)` the first-order condition of a
consumption–saving problem reads

  `exp (-α c) = β R · ∑ π z' · exp (-α c' z')`,

so

  `c = -(1/α) · log (β R) + softMin π α c'`,   `softMin w α x = -(1/α) log (∑ wᵢ exp (-α xᵢ))`,

the weighted SOFT MINIMUM of next period's consumptions. It sits between the minimum and the
weighted mean, and tends to the minimum as `α → ∞` — precautionary saving reading off the worst
case more sharply the more risk-averse the household is.

What Carroll and Kimball's induction needs of it is what it needed of the power mean: that it is
CONCAVE and NONDECREASING, so it carries concavity of next period's consumption functions to
concavity of this period's.

## The proof

Concavity of the soft minimum is convexity of log-sum-exp, and that is Hölder's inequality:

  `∑ wᵢ aᵢ^θ bᵢ^φ ≤ (∑ wᵢ aᵢ)^θ (∑ wᵢ bᵢ)^φ`   for `θ + φ = 1`,

with `aᵢ = exp (-α xᵢ)` and `bᵢ = exp (-α yᵢ)`, for which `aᵢ^θ bᵢ^φ` is EXACTLY
`exp (-α (θ xᵢ + φ yᵢ))`. Hölder in turn is weighted arithmetic–geometric means applied term by
term after dividing through by the two sums, which is `Real.geom_mean_le_arith_mean2_weighted`.

No derivatives, and unlike the power mean no positivity: `softMin` is defined for consumptions
of either sign, which is the point of CARA.
-/

open Set Finset

namespace LeanEconomics

variable {ι : Type*} [Fintype ι] {w x y : ι → ℝ} {α θ φ : ℝ}

/-! ### Hölder's inequality for a weighted finite sum -/

/-- **Hölder's inequality**, in the form the soft minimum needs: a weighted sum of geometric
means is at most the geometric mean of the weighted sums. -/
theorem sum_mul_rpow_le {a b : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hA : 0 < ∑ i, w i * a i) (hB : 0 < ∑ i, w i * b i)
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hθφ : θ + φ = 1) :
    ∑ i, w i * (a i ^ θ * b i ^ φ) ≤ (∑ i, w i * a i) ^ θ * (∑ i, w i * b i) ^ φ := by
  set A : ℝ := ∑ i, w i * a i with hAdef
  set B : ℝ := ∑ i, w i * b i with hBdef
  have hAne : A ≠ 0 := ne_of_gt hA
  have hBne : B ≠ 0 := ne_of_gt hB
  have hpow : (0 : ℝ) < A ^ θ * B ^ φ := by positivity
  -- the normalised inequality, term by term
  have key : ∀ i, (a i / A) ^ θ * (b i / B) ^ φ ≤ θ * (a i / A) + φ * (b i / B) := fun i =>
    Real.geom_mean_le_arith_mean2_weighted hθ hφ (div_nonneg (ha i).le hA.le)
      (div_nonneg (hb i).le hB.le) hθφ
  have hsum : ∑ i, w i * ((a i / A) ^ θ * (b i / B) ^ φ) ≤ 1 := by
    calc ∑ i, w i * ((a i / A) ^ θ * (b i / B) ^ φ)
        ≤ ∑ i, w i * (θ * (a i / A) + φ * (b i / B)) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (key i) (hw i)
      _ = (θ / A) * A + (φ / B) * B := by
          rw [hAdef, hBdef, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          field_simp
      _ = 1 := by field_simp; linarith [hθφ]
  -- undo the normalisation
  have hrw : ∀ i, w i * ((a i / A) ^ θ * (b i / B) ^ φ)
      = (w i * (a i ^ θ * b i ^ φ)) / (A ^ θ * B ^ φ) := by
    intro i
    rw [Real.div_rpow (ha i).le hA.le, Real.div_rpow (hb i).le hB.le]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => hrw i, ← Finset.sum_div, div_le_one hpow] at hsum
  exact hsum

/-! ### The soft minimum -/

/-- The weighted **soft minimum** with risk aversion `α`. -/
noncomputable def softMin (w : ι → ℝ) (α : ℝ) (x : ι → ℝ) : ℝ :=
  -(1 / α) * Real.log (∑ i, w i * Real.exp (-α * x i))

theorem sum_exp_pos (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (α : ℝ) (x : ι → ℝ) :
    0 < ∑ i, w i * Real.exp (-α * x i) := by
  obtain ⟨i₀, -, hi₀⟩ : ∃ i ∈ Finset.univ, 0 < w i := by
    by_contra h
    simp only [not_exists, not_and, not_lt] at h
    have hzero : ∑ i, w i = 0 := Finset.sum_eq_zero fun i hi => le_antisymm (h i hi) (hw i)
    rw [hw1] at hzero
    norm_num at hzero
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le)
    ⟨i₀, Finset.mem_univ _, mul_pos hi₀ (Real.exp_pos _)⟩

/-- **The soft minimum is nondecreasing** in every argument. -/
theorem softMin_mono (hα : 0 < α) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hxy : ∀ i, x i ≤ y i) : softMin w α x ≤ softMin w α y := by
  have hx := sum_exp_pos hw hw1 α x
  have hy := sum_exp_pos hw hw1 α y
  have hsum : ∑ i, w i * Real.exp (-α * y i) ≤ ∑ i, w i * Real.exp (-α * x i) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [hxy i])) (hw i)
  have hlog := Real.log_le_log hy hsum
  simp only [softMin]
  have hcoef : (0 : ℝ) < 1 / α := by positivity
  nlinarith [hlog, hcoef]

/-- **The soft minimum is concave.** Convexity of log-sum-exp, by Hölder. -/
theorem softMin_concave (hα : 0 < α) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hθφ : θ + φ = 1) :
    θ * softMin w α x + φ * softMin w α y ≤ softMin w α fun i => θ * x i + φ * y i := by
  set A : ℝ := ∑ i, w i * Real.exp (-α * x i) with hAdef
  set B : ℝ := ∑ i, w i * Real.exp (-α * y i) with hBdef
  have hA : 0 < A := sum_exp_pos hw hw1 α x
  have hB : 0 < B := sum_exp_pos hw hw1 α y
  -- the combination's weights are exactly the two geometric means
  have hterm : ∀ i, Real.exp (-α * (θ * x i + φ * y i))
      = Real.exp (-α * x i) ^ θ * Real.exp (-α * y i) ^ φ := by
    intro i
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    ring_nf
  have hholder := sum_mul_rpow_le (w := w) (a := fun i => Real.exp (-α * x i))
    (b := fun i => Real.exp (-α * y i)) hw (fun i => Real.exp_pos _) (fun i => Real.exp_pos _)
    hA hB hθ hφ hθφ
  have hle : ∑ i, w i * Real.exp (-α * (θ * x i + φ * y i)) ≤ A ^ θ * B ^ φ := by
    refine le_trans (le_of_eq ?_) hholder
    exact Finset.sum_congr rfl fun i _ => by rw [hterm i]
  -- take logs
  have hpos : (0 : ℝ) < ∑ i, w i * Real.exp (-α * (θ * x i + φ * y i)) :=
    sum_exp_pos hw hw1 α _
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hA, Real.log_rpow hB] at hlog
  simp only [softMin]
  have hcoef : (0 : ℝ) < 1 / α := by positivity
  nlinarith [hlog, hcoef]

/-! ### Composed with concave functions -/

/-- **The soft minimum of concave functions is concave.** -/
theorem concaveOn_softMin_comp {D : Set ℝ} (hD : Convex ℝ D) (hα : 0 < α)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {f : ι → ℝ → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ D (f i)) :
    ConcaveOn ℝ D fun a => softMin w α fun i => f i a := by
  refine ⟨hD, fun a ha b hb θ φ hθ hφ hθφ => ?_⟩
  have hm : θ • a + φ • b ∈ D := hD ha hb hθ hφ hθφ
  have hstep : ∀ i, θ * f i a + φ * f i b ≤ f i (θ • a + φ • b) := by
    intro i
    have := (hconc i).2 ha hb hθ hφ hθφ
    simpa only [smul_eq_mul] using this
  refine le_trans (softMin_concave (x := fun i => f i a) (y := fun i => f i b)
    hα hw hw1 hθ hφ hθφ) ?_
  exact softMin_mono hα hw hw1 fun i => hstep i

/-- **The soft minimum of nondecreasing functions is nondecreasing.** -/
theorem monotoneOn_softMin_comp {D : Set ℝ} (hα : 0 < α) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {f : ι → ℝ → ℝ} (hmono : ∀ i, MonotoneOn (f i) D) :
    MonotoneOn (fun a => softMin w α fun i => f i a) D := fun _a ha _b hb hab =>
  softMin_mono hα hw hw1 fun i => hmono i ha hb hab

end LeanEconomics
