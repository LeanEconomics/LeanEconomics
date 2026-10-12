/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# When is the state transition a contraction for every shock?

`ApproxLikelihoodModel` derives the assumptions of Corrected Proposition 2′ from a transition that
is an `α`-contraction for every shock, in some metric. This file shows the condition is less
restrictive than it looks.

* **Weighted metrics** (`weighted_contraction`). With state `(x, ζ)`, an exogenous component that
  contracts by `ρ < 1` and an endogenous one with `|Δx'| ≤ a |Δx| + b |Δζ|`, `a < 1`, the metric
  `|Δx| + λ |Δζ|` with `λ > b / (1 - ρ)` makes the transition a contraction with factor
  `max a (ρ + b / λ) < 1`. The endogenous state need only contract in its own argument.
* **Brock–Mirman** (`brockMirman_contraction`, `brockMirman_mapsTo`). With log utility,
  Cobb–Douglas production and full depreciation, `log k' = log (θβ) + log z + θ log k`. In log
  coordinates and the weighted metric this contracts for every shock, globally, and a compact
  rectangle is invariant.
* **Local contraction** (`local_contraction`). A `C¹` transition whose state Jacobian at a
  deterministic steady state has norm below `α < 1` is, for small enough shocks, an
  `α`-contraction on a closed ball around the steady state, and maps the ball into itself; so does
  any computed transition within `δ ≤ (1 - α) r / 2` of it.
-/

open Metric Set Filter Topology

namespace LeanEconomics

namespace ApproxLikelihood

/-! ### Weighted metrics -/

/-- **A weighted metric absorbs the effect of the exogenous state.** -/
theorem weighted_contraction {a b ρ lam dx dζ dx' dζ' : ℝ} (hlam : 0 < lam)
    (hx : |dx'| ≤ a * |dx| + b * |dζ|) (hζ : |dζ'| ≤ ρ * |dζ|) :
    |dx'| + lam * |dζ'| ≤ max a (ρ + b / lam) * (|dx| + lam * |dζ|) := by
  have h1 : a ≤ max a (ρ + b / lam) := le_max_left _ _
  have h2 : ρ + b / lam ≤ max a (ρ + b / lam) := le_max_right _ _
  have e : b * |dζ| + lam * (ρ * |dζ|) = (ρ + b / lam) * (lam * |dζ|) := by
    field_simp; ring
  have hdx := abs_nonneg dx
  have hdζ : 0 ≤ lam * |dζ| := mul_nonneg hlam.le (abs_nonneg dζ)
  calc |dx'| + lam * |dζ'| ≤ a * |dx| + b * |dζ| + lam * (ρ * |dζ|) := by
        have := mul_le_mul_of_nonneg_left hζ hlam.le; linarith
    _ = a * |dx| + (ρ + b / lam) * (lam * |dζ|) := by rw [add_assoc, e]
    _ ≤ max a (ρ + b / lam) * |dx| + max a (ρ + b / lam) * (lam * |dζ|) := by
        gcongr
    _ = max a (ρ + b / lam) * (|dx| + lam * |dζ|) := by ring

/-- The weighted factor is below one once the weight is large enough. -/
theorem weighted_factor_lt_one {a b ρ lam : ℝ} (ha : a < 1) (hb : 0 ≤ b) (hρ : ρ < 1)
    (hlam : b / (1 - ρ) < lam) : max a (ρ + b / lam) < 1 := by
  have h1 : 0 < 1 - ρ := by linarith
  have hlam0 : 0 < lam := lt_of_le_of_lt (div_nonneg hb h1.le) hlam
  refine max_lt ha ?_
  have : b < (1 - ρ) * lam := by rwa [div_lt_iff₀ h1, mul_comm] at hlam
  have : b / lam < 1 - ρ := by rw [div_lt_iff₀ hlam0]; linarith
  linarith

/-! ### Brock–Mirman -/

/-- The Brock–Mirman transition in logs: `x = log k`, `ζ = log z`. -/
noncomputable def brockMirman (θ β ρ : ℝ) (s : ℝ × ℝ) (ε : ℝ) : ℝ × ℝ :=
  (Real.log (θ * β) + s.2 + θ * s.1, ρ * s.2 + ε)

/-- **Brock–Mirman contracts for every shock** in the weighted log metric, with factor
`max θ (ρ + 1 / λ)`. -/
theorem brockMirman_contraction {θ β ρ lam : ℝ} (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) (hlam : 0 < lam)
    (s s' : ℝ × ℝ) (ε : ℝ) :
    |(brockMirman θ β ρ s ε).1 - (brockMirman θ β ρ s' ε).1|
        + lam * |(brockMirman θ β ρ s ε).2 - (brockMirman θ β ρ s' ε).2|
      ≤ max θ (ρ + 1 / lam) * (|s.1 - s'.1| + lam * |s.2 - s'.2|) := by
  refine weighted_contraction (b := 1) hlam ?_ ?_
  · simp only [brockMirman]
    calc |Real.log (θ * β) + s.2 + θ * s.1 - (Real.log (θ * β) + s'.2 + θ * s'.1)|
        = |θ * (s.1 - s'.1) + (s.2 - s'.2)| := by ring_nf
      _ ≤ |θ * (s.1 - s'.1)| + |s.2 - s'.2| := abs_add_le _ _
      _ = θ * |s.1 - s'.1| + 1 * |s.2 - s'.2| := by rw [abs_mul, abs_of_nonneg hθ, one_mul]
  · simp only [brockMirman]
    rw [show ρ * s.2 + ε - (ρ * s'.2 + ε) = ρ * (s.2 - s'.2) by ring, abs_mul, abs_of_nonneg hρ]

/-- **A compact invariant rectangle** for Brock–Mirman: `|ζ| ≤ ζ̄` and
`x ∈ [(log (θβ) - ζ̄)/(1 - θ), (log (θβ) + ζ̄)/(1 - θ)]`, for shocks `|ε| ≤ (1 - ρ) ζ̄`. -/
theorem brockMirman_mapsTo {θ β ρ ζbar ε : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hρ : 0 ≤ ρ)
    (hε : |ε| ≤ (1 - ρ) * ζbar) {s : ℝ × ℝ}
    (hx : (Real.log (θ * β) - ζbar) / (1 - θ) ≤ s.1 ∧ s.1 ≤ (Real.log (θ * β) + ζbar) / (1 - θ))
    (hζ : |s.2| ≤ ζbar) :
    ((Real.log (θ * β) - ζbar) / (1 - θ) ≤ (brockMirman θ β ρ s ε).1 ∧
        (brockMirman θ β ρ s ε).1 ≤ (Real.log (θ * β) + ζbar) / (1 - θ)) ∧
      |(brockMirman θ β ρ s ε).2| ≤ ζbar := by
  have h1 : 0 < 1 - θ := by linarith
  obtain ⟨hlo, hhi⟩ := hx
  rw [div_le_iff₀ h1] at hlo
  rw [le_div_iff₀ h1] at hhi
  have hζ' := abs_le.mp hζ
  simp only [brockMirman]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [div_le_iff₀ h1]; nlinarith [hζ'.1]
  · rw [le_div_iff₀ h1]; nlinarith [hζ'.2]
  · calc |ρ * s.2 + ε| ≤ |ρ * s.2| + |ε| := abs_add_le _ _
      _ = ρ * |s.2| + |ε| := by rw [abs_mul, abs_of_nonneg hρ]
      _ ≤ ρ * ζbar + (1 - ρ) * ζbar := by gcongr
      _ = ζbar := by ring

/-! ### Local contraction near a stable steady state -/

section Local

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Local contraction.** Let `φ : E × F → E` (state, shock) be `C¹`, with deterministic steady
state `φ (s̄, 0) = s̄`, and let the state Jacobian at the steady state have operator norm below
`α < 1`. Then there are `r > 0` and `η > 0` such that for every shock with `‖w‖ ≤ η`:
`φ (·, w)` is an `α`-contraction on the closed ball of radius `r` about `s̄`, and every map within
`δ ≤ (1 - α) r / 2` of `φ (·, w)` (in particular `φ (·, w)` itself) maps that ball into itself. -/
theorem local_contraction (φ : E × F → E) (hφ : ContDiff ℝ 1 φ) (sbar : E)
    (hss : φ (sbar, 0) = sbar) {α : ℝ} (hα1 : α < 1)
    (hA : ‖(fderiv ℝ φ (sbar, 0)).comp (ContinuousLinearMap.inl ℝ E F)‖ < α) :
    ∃ r > 0, ∃ η > 0, ∀ w : F, ‖w‖ ≤ η →
      (∀ s ∈ closedBall sbar r, ∀ s' ∈ closedBall sbar r,
          ‖φ (s, w) - φ (s', w)‖ ≤ α * ‖s - s'‖) ∧
      (∀ δ : ℝ, δ ≤ (1 - α) * r / 2 → ∀ φj : E → E, (∀ s, ‖φj s - φ (s, w)‖ ≤ δ) →
          ∀ s ∈ closedBall sbar r, φj s ∈ closedBall sbar r) := by
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hfd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  set A : E × F → E →L[ℝ] E := fun p ↦ (fderiv ℝ φ p).comp (ContinuousLinearMap.inl ℝ E F)
  set B : E × F → F →L[ℝ] E := fun p ↦ (fderiv ℝ φ p).comp (ContinuousLinearMap.inr ℝ E F)
  have hAc : Continuous A := hfd.clm_comp continuous_const
  have hBc : Continuous B := hfd.clm_comp continuous_const
  set C : ℝ := ‖B (sbar, 0)‖ + 1 with hCdef
  have hC : 0 < C := by positivity
  have hα0 : 0 < α := lt_of_le_of_lt (norm_nonneg _) hA
  have hev : ∀ᶠ p in 𝓝 (sbar, (0 : F)), ‖A p‖ < α ∧ ‖B p‖ < C :=
    (hAc.norm.continuousAt.eventually_lt continuousAt_const hA).and
      (hBc.norm.continuousAt.eventually_lt continuousAt_const (by rw [hCdef]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hnear : ∀ s w, ‖s - sbar‖ ≤ r → ‖w‖ ≤ r → ‖A (s, w)‖ < α ∧ ‖B (s, w)‖ < C := by
    intro s w hs hw
    apply hball
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm, sub_zero]
    exact max_lt (by linarith) (by linarith)
  refine ⟨r, hr0, min r ((1 - α) * r / (2 * C)), lt_min hr0 (by
    have : 0 < 1 - α := by linarith
    positivity), fun w hw ↦ ?_⟩
  have hwr : ‖w‖ ≤ r := hw.trans (min_le_left _ _)
  have hwC : C * ‖w‖ ≤ (1 - α) * r / 2 := by
    have := hw.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  -- (i) contraction on the ball, by the mean value inequality in the state
  have hcontr : ∀ s ∈ closedBall sbar r, ∀ s' ∈ closedBall sbar r,
      ‖φ (s, w) - φ (s', w)‖ ≤ α * ‖s - s'‖ := by
    intro s hs s' hs'
    have hder : ∀ x ∈ closedBall sbar r,
        HasFDerivWithinAt (fun x ↦ φ (x, w)) (A (x, w)) (closedBall sbar r) x := by
      intro x _
      exact ((hdiff (x, w)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x w)).hasFDerivWithinAt
    have hbd : ∀ x ∈ closedBall sbar r, ‖A (x, w)‖ ≤ α := by
      intro x hx
      rw [mem_closedBall, dist_eq_norm] at hx
      exact (hnear x w hx hwr).1.le
    exact (convex_closedBall sbar r).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbd hs' hs
  refine ⟨hcontr, fun δ hδ φj hφj s hs ↦ ?_⟩
  -- the shock moves the steady state by at most `C ‖w‖`, by the mean value inequality in the shock
  have hshock : ‖φ (sbar, w) - sbar‖ ≤ C * ‖w‖ := by
    have hder : ∀ v ∈ closedBall (0 : F) r,
        HasFDerivWithinAt (fun v ↦ φ (sbar, v)) (B (sbar, v)) (closedBall 0 r) v := by
      intro v _
      exact ((hdiff (sbar, v)).hasFDerivAt.comp v
        (hasFDerivAt_prodMk_right sbar v)).hasFDerivWithinAt
    have hbd : ∀ v ∈ closedBall (0 : F) r, ‖B (sbar, v)‖ ≤ C := by
      intro v hv
      rw [mem_closedBall, dist_zero_right] at hv
      exact (hnear sbar v (by simp; linarith) hv).2.le
    have := (convex_closedBall (0 : F) r).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbd
      (mem_closedBall_self hr0.le) (by rwa [mem_closedBall, dist_zero_right])
    simpa [hss] using this
  rw [mem_closedBall, dist_eq_norm] at hs ⊢
  have h1 := hφj s
  have h2 := hcontr s (by rwa [mem_closedBall, dist_eq_norm]) sbar (mem_closedBall_self hr0.le)
  calc ‖φj s - sbar‖
      ≤ ‖φj s - φ (s, w)‖ + ‖φ (s, w) - φ (sbar, w)‖ + ‖φ (sbar, w) - sbar‖ := by
        have := norm_add₃_le (a := φj s - φ (s, w)) (b := φ (s, w) - φ (sbar, w))
          (c := φ (sbar, w) - sbar)
        simpa using this
    _ ≤ δ + α * ‖s - sbar‖ + C * ‖w‖ := by gcongr
    _ ≤ (1 - α) * r / 2 + α * r + (1 - α) * r / 2 := by gcongr
    _ = r := by ring

end Local

end ApproxLikelihood

end LeanEconomics
