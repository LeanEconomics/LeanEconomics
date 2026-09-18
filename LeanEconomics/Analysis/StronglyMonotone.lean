/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Strongly monotone operators: a unique zero, and a damped iteration that finds it

Graber and Matter (2024) prove uniqueness for a mean field game of controls by showing that the
*error map* `E[Q] = Q - (aggregate best response to Q)` is strongly monotone,
`⟪E[Q₁] - E[Q₀], Q₁ - Q₀⟫ ≥ (1 - δ)‖Q₁ - Q₀‖²`, and then invoking the Minty–Browder theorem for
existence and uniqueness of its zero. In a heterogeneous-agent economy the error map is EXCESS
SUPPLY `r ↦ K_s(r) - K_d(r)`, and its monotonicity is Light's single crossing.

This file records the quantitative half of that argument in the form that needs no functional
analysis beyond Banach's fixed point theorem (Zarantonello's theorem): a strongly monotone
Lipschitz operator on a real inner product space has

* a damped map `x ↦ x - τ F x` that is a CONTRACTION for `τ = m / L²`, with modulus
  `√(1 - m²/L²)` (`contractingWith_damped`);
* hence, on a complete space, a unique zero, which the damped iteration reaches from every
  starting point at a geometric rate (`exists_unique_zero_of_stronglyMonotone`,
  `tendsto_damped_iterate`).

On the line (`stronglyMonotone_of_slope`) strong monotonicity is a slope floor
`m(y - x) ≤ f y - f x`, so the damped map is a tâtonnement `r ↦ r - τ·(excess supply)` whose
convergence is certified. The pure best-response iteration `r ↦ r_d(K_s(r))` has NEGATIVE slope
and can oscillate even when the equilibrium is unique — the stability question Hajek and Livesay
(2019) raise for the mean-field best-response map — which is why the damped form, or the
bisection in `Equilibrium.Bisection`, is the right algorithm.
-/

open Filter Topology Function

namespace LeanEconomics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Strong monotonicity with modulus `m`**: `⟪F x - F y, x - y⟫ ≥ m ‖x - y‖²`. -/
def StronglyMonotone (m : ℝ) (F : E → E) : Prop :=
  ∀ x y, m * ‖x - y‖ ^ 2 ≤ inner ℝ (F x - F y) (x - y)

/-- The damped map `x ↦ x - τ • F x`; its fixed points are the zeros of `F`. -/
def damped (τ : ℝ) (F : E → E) (x : E) : E := x - τ • F x

theorem isFixedPt_damped_iff {τ : ℝ} (hτ : τ ≠ 0) (F : E → E) (x : E) :
    IsFixedPt (damped τ F) x ↔ F x = 0 := by
  simp only [IsFixedPt, damped, sub_eq_self, smul_eq_zero, hτ, false_or]

/-- The one-step contraction estimate: `‖(x - τFx) - (y - τFy)‖² ≤ (1 - 2τm + τ²L²)‖x - y‖²`. -/
theorem norm_damped_sub_sq_le {m L τ : ℝ} {F : E → E} (hm : StronglyMonotone m F)
    (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hτ : 0 ≤ τ) (x y : E) :
    ‖damped τ F x - damped τ F y‖ ^ 2 ≤ (1 - 2 * τ * m + τ ^ 2 * L ^ 2) * ‖x - y‖ ^ 2 := by
  have h1 : damped τ F x - damped τ F y = (x - y) - τ • (F x - F y) := by
    simp only [damped, smul_sub]; abel
  rw [h1, norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs,
    abs_of_nonneg hτ, real_inner_comm]
  have h2 := hm x y
  have h3 : ‖F x - F y‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    have := hL x y
    calc ‖F x - F y‖ ^ 2 ≤ (L * ‖x - y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = L ^ 2 * ‖x - y‖ ^ 2 := by ring
  have h4 : τ * (m * ‖x - y‖ ^ 2) ≤ τ * inner ℝ (F x - F y) (x - y) :=
    mul_le_mul_of_nonneg_left h2 hτ
  have h5 : τ ^ 2 * ‖F x - F y‖ ^ 2 ≤ τ ^ 2 * (L ^ 2 * ‖x - y‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h3 (sq_nonneg τ)
  nlinarith [h4, h5]

/-- With the step `τ = m / L²` the coefficient is `1 - m²/L²`. -/
theorem norm_damped_sub_le {m L : ℝ} {F : E → E} (hm0 : 0 < m) (hL0 : 0 < L)
    (hm : StronglyMonotone m F) (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖damped (m / L ^ 2) F x - damped (m / L ^ 2) F y‖
      ≤ √(1 - m ^ 2 / L ^ 2) * ‖x - y‖ := by
  have hτ : 0 ≤ m / L ^ 2 := by positivity
  have hsq := norm_damped_sub_sq_le hm hL hτ x y
  have hcoef : 1 - 2 * (m / L ^ 2) * m + (m / L ^ 2) ^ 2 * L ^ 2 = 1 - m ^ 2 / L ^ 2 := by
    field_simp
    ring
  rw [hcoef] at hsq
  rcases (norm_nonneg (damped (m / L ^ 2) F x - damped (m / L ^ 2) F y)).lt_or_eq with h | h
  · calc ‖damped (m / L ^ 2) F x - damped (m / L ^ 2) F y‖
        ≤ √((1 - m ^ 2 / L ^ 2) * ‖x - y‖ ^ 2) := (Real.le_sqrt' h).2 hsq
      _ = √(1 - m ^ 2 / L ^ 2) * ‖x - y‖ := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  · rw [← h]
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)

/-- **The damped map is a contraction** (Graber–Matter Thm. 2.7 / Zarantonello). -/
theorem contractingWith_damped {m L : ℝ} {F : E → E} (hm0 : 0 < m) (hL0 : 0 < L)
    (hm : StronglyMonotone m F) (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) :
    ContractingWith ⟨√(1 - m ^ 2 / L ^ 2), Real.sqrt_nonneg _⟩ (damped (m / L ^ 2) F) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  · apply NNReal.coe_lt_coe.mp
    change √(1 - m ^ 2 / L ^ 2) < 1
    rw [Real.sqrt_lt' one_pos]
    have : 0 < m ^ 2 / L ^ 2 := by positivity
    linarith
  · rw [dist_eq_norm, dist_eq_norm]
    change _ ≤ √(1 - m ^ 2 / L ^ 2) * _
    exact norm_damped_sub_le hm0 hL0 hm hL x y

/-- **A strongly monotone Lipschitz operator has exactly one zero** (the Minty–Browder
conclusion, by Banach's fixed point theorem). -/
theorem exists_unique_zero_of_stronglyMonotone [CompleteSpace E] {m L : ℝ} {F : E → E}
    (hm0 : 0 < m) (hL0 : 0 < L) (hm : StronglyMonotone m F)
    (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) : ∃! x, F x = 0 := by
  have hc := contractingWith_damped hm0 hL0 hm hL
  have hτ : m / L ^ 2 ≠ 0 := by positivity
  refine ⟨ContractingWith.fixedPoint _ hc, (isFixedPt_damped_iff hτ F _).1 hc.fixedPoint_isFixedPt,
    fun y hy => hc.fixedPoint_unique ((isFixedPt_damped_iff hτ F y).2 hy)⟩

/-- **The damped iteration converges to the zero from every start**, at the geometric rate
`√(1 - m²/L²)`. -/
theorem tendsto_damped_iterate [CompleteSpace E] {m L : ℝ} {F : E → E}
    (hm0 : 0 < m) (hL0 : 0 < L) (hm : StronglyMonotone m F)
    (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) {x : E} (hx : F x = 0) (x₀ : E) :
    Tendsto (fun n => (damped (m / L ^ 2) F)^[n] x₀) atTop (𝓝 x) ∧
      ∀ n, dist ((damped (m / L ^ 2) F)^[n] x₀) x
        ≤ dist x₀ (damped (m / L ^ 2) F x₀) * √(1 - m ^ 2 / L ^ 2) ^ n
          / (1 - √(1 - m ^ 2 / L ^ 2)) := by
  have hc := contractingWith_damped hm0 hL0 hm hL
  have hτ : m / L ^ 2 ≠ 0 := by positivity
  have hfix : x = ContractingWith.fixedPoint _ hc :=
    hc.fixedPoint_unique ((isFixedPt_damped_iff hτ F x).2 hx)
  refine ⟨hfix ▸ hc.tendsto_iterate_fixedPoint x₀, fun n => ?_⟩
  rw [hfix]
  exact hc.apriori_dist_iterate_fixedPoint_le x₀ n

/-! ### On the line: a slope floor -/

/-- **On `ℝ`, a slope floor is strong monotonicity.** For excess supply this reads
`m (r₂ - r₁) ≤ E r₂ - E r₁`: supply minus demand rises at least at rate `m`. -/
theorem stronglyMonotone_of_slope {m : ℝ} {f : ℝ → ℝ}
    (h : ∀ x y, x ≤ y → m * (y - x) ≤ f y - f x) : StronglyMonotone m f := by
  intro x y
  simp only [RCLike.inner_apply, RCLike.conj_to_real, Real.norm_eq_abs, sq_abs]
  rcases le_total x y with hxy | hxy
  · have := h x y hxy
    nlinarith [sub_nonneg.2 hxy]
  · have := h y x hxy
    nlinarith [sub_nonneg.2 hxy]

/-- **A Lipschitz excess-supply schedule with a slope floor has exactly one zero, and the damped
tâtonnement `r ↦ r - (m/L²)·E r` finds it.** -/
theorem exists_unique_zero_of_slope {m L : ℝ} {E : ℝ → ℝ} (hm0 : 0 < m) (hL0 : 0 < L)
    (hslope : ∀ x y, x ≤ y → m * (y - x) ≤ E y - E x)
    (hL : ∀ x y, |E x - E y| ≤ L * |x - y|) :
    (∃! r, E r = 0) ∧ ∀ r, E r = 0 → ∀ r₀,
      Tendsto (fun n => (damped (m / L ^ 2) E)^[n] r₀) atTop (𝓝 r) := by
  have hm := stronglyMonotone_of_slope hslope
  have hL' : ∀ x y, ‖E x - E y‖ ≤ L * ‖x - y‖ := by
    intro x y; simpa only [Real.norm_eq_abs] using hL x y
  exact ⟨exists_unique_zero_of_stronglyMonotone hm0 hL0 hm hL',
    fun r hr r₀ => (tendsto_damped_iterate hm0 hL0 hm hL' hr r₀).1⟩

end LeanEconomics
