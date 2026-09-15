/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Analysis.DecreasingIncrements
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Relative risk aversion at most one

Light (2018) proves that individual saving rises with the interest rate — his Theorem 1, the
household half of the uniqueness argument — under the assumption that `u'(c) · c` is
non-decreasing. With `u' > 0` that is exactly relative risk aversion `-c u''/u' ≤ 1`, because

  `d/dc [c u'(c)] = u'(c) · (1 - RRA(c))`.

Economically it is the condition under which the substitution effect of a higher interest rate
dominates the income effect. It is the boundary of the region where the model is known to have
a unique equilibrium: Açıkgöz (2018) exhibits multiplicity at `γ = 6.5`, and Walsh and Young
(2025) report never seeing multiplicity below about `γ = 1.49`.

## Stating it without derivatives

`u'(c) · c` is the derivative of `t ↦ u(eᵗ)`, so the assumption says precisely that **`u` is
convex as a function of log consumption**, and that is how it is defined here. The definition
needs no differentiability, and neither does its main consequence: increments of `u` across a
fixed PROPORTIONAL change in consumption grow as consumption grows,

  `u(α c₁) - u(c₁) ≤ u(α c₂) - u(c₂)`  for `0 < c₁ ≤ c₂` and `α ≥ 1`,

which is `sub_le_sub_of_scale` below. This is the multiplicative twin of
`ConcaveOn.sub_le_sub_of_shift`, and it is the form the comparative-statics argument uses, since
a change in the interest rate scales the return on saving rather than shifting it.

Where derivatives are available the two formulations agree, and `relativeRiskAversionLeOne_iff`
proves that. The examples at the end pin the boundary down: CRRA satisfies the condition exactly
when `γ ≤ 1`, log utility sits on the boundary (convex in log consumption because it is AFFINE
there), and for `γ > 1` it fails — indeed `u ∘ exp` is then strictly concave, so the condition
fails as badly as it can.
-/

open Set

namespace LeanEconomics

/-- **Relative risk aversion at most one**, stated without derivatives: `u` is convex as a
function of log consumption. Where `u` is differentiable with `u' > 0` this is equivalent to
`-c u''(c) / u'(c) ≤ 1`; see `relativeRiskAversionLeOne_iff`. -/
def RelativeRiskAversionLeOne (u : ℝ → ℝ) : Prop :=
  ConvexOn ℝ univ fun t => u (Real.exp t)

/-- **The derivative-free content of `u'(c) · c` increasing.** The gain from a fixed
PROPORTIONAL rise in consumption is larger at higher consumption.

This is the multiplicative counterpart of `ConcaveOn.sub_le_sub_of_shift`, and it is the form
the comparative statics uses: a higher interest rate scales the payoff to saving. -/
theorem RelativeRiskAversionLeOne.sub_le_sub_of_scale {u : ℝ → ℝ}
    (hu : RelativeRiskAversionLeOne u) {c₁ c₂ α : ℝ} (h₁ : 0 < c₁) (h₁₂ : c₁ ≤ c₂) (hα : 1 ≤ α) :
    u (α * c₁) - u c₁ ≤ u (α * c₂) - u c₂ := by
  have h₂ : 0 < c₂ := lt_of_lt_of_le h₁ h₁₂
  have hα0 : 0 < α := lt_of_lt_of_le one_pos hα
  have hconv : ConvexOn ℝ (univ : Set ℝ) fun t => u (Real.exp t) := hu
  -- the concave shift lemma applied to the negation, in log consumption
  have hcon : ConcaveOn ℝ (univ : Set ℝ) (-fun t => u (Real.exp t)) := hconv.neg
  have hlog : Real.log c₁ ≤ Real.log c₂ := Real.log_le_log h₁ h₁₂
  have hΔ : 0 ≤ Real.log α := Real.log_nonneg hα
  have key := hcon.sub_le_sub_of_shift (mem_univ (Real.log c₁))
    (mem_univ (Real.log c₂ + Real.log α)) hlog hΔ
  have e1 : Real.exp (Real.log c₁ + Real.log α) = α * c₁ := by
    rw [Real.exp_add, Real.exp_log h₁, Real.exp_log hα0]; ring
  have e2 : Real.exp (Real.log c₂ + Real.log α) = α * c₂ := by
    rw [Real.exp_add, Real.exp_log h₂, Real.exp_log hα0]; ring
  simp only [Pi.neg_apply, e1, e2, Real.exp_log h₁, Real.exp_log h₂] at key
  linarith

/-! ### The equivalence with `u'(c) · c` increasing -/

/-- Where `u` is differentiable on `(0, ∞)`, `t ↦ u(eᵗ)` is differentiable with derivative
`eᵗ u'(eᵗ)` — which is `u'(c) · c` read at `c = eᵗ`. -/
theorem hasDerivAt_comp_exp {u du : ℝ → ℝ} (hd : ∀ c ∈ Ioi (0 : ℝ), HasDerivAt u (du c) c)
    (t : ℝ) :
    HasDerivAt (fun s => u (Real.exp s)) (Real.exp t * du (Real.exp t)) t := by
  have h := (hd _ (mem_Ioi.mpr (Real.exp_pos t))).comp t (Real.hasDerivAt_exp t)
  simpa [Function.comp_def, mul_comm] using h

/-- If `u'(c) · c` is non-decreasing then relative risk aversion is at most one. -/
theorem relativeRiskAversionLeOne_of_monotoneOn {u du : ℝ → ℝ}
    (hd : ∀ c ∈ Ioi (0 : ℝ), HasDerivAt u (du c) c)
    (hm : MonotoneOn (fun c => c * du c) (Ioi 0)) :
    RelativeRiskAversionLeOne u := by
  refine Monotone.convexOn_univ_of_deriv
    (fun t => (hasDerivAt_comp_exp hd t).differentiableAt) ?_
  intro s t hst
  rw [(hasDerivAt_comp_exp hd s).deriv, (hasDerivAt_comp_exp hd t).deriv]
  exact hm (mem_Ioi.mpr (Real.exp_pos s)) (mem_Ioi.mpr (Real.exp_pos t)) (Real.exp_le_exp.mpr hst)

/-- Conversely, relative risk aversion at most one makes `u'(c) · c` non-decreasing. -/
theorem RelativeRiskAversionLeOne.monotoneOn_mul_deriv {u du : ℝ → ℝ}
    (hu : RelativeRiskAversionLeOne u) (hd : ∀ c ∈ Ioi (0 : ℝ), HasDerivAt u (du c) c) :
    MonotoneOn (fun c => c * du c) (Ioi 0) := by
  have hconv : ConvexOn ℝ (univ : Set ℝ) fun t => u (Real.exp t) := hu
  intro a ha b hb hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  have ha0 : 0 < a := mem_Ioi.mp ha
  have hb0 : 0 < b := mem_Ioi.mp hb
  have hlog : Real.log a < Real.log b := Real.log_lt_log ha0 hlt
  -- the derivative at the left end of a secant is below its slope, and at the right end above
  have h1 := hconv.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) hlog
    (hasDerivAt_comp_exp hd (Real.log a))
  have h2 := hconv.slope_le_of_hasDerivAt (mem_univ _) (mem_univ _) hlog
    (hasDerivAt_comp_exp hd (Real.log b))
  rw [Real.exp_log ha0] at h1
  rw [Real.exp_log hb0] at h2
  exact h1.trans h2

/-- **Relative risk aversion at most one is exactly `u'(c) · c` non-decreasing.** -/
theorem relativeRiskAversionLeOne_iff {u du : ℝ → ℝ}
    (hd : ∀ c ∈ Ioi (0 : ℝ), HasDerivAt u (du c) c) :
    RelativeRiskAversionLeOne u ↔ MonotoneOn (fun c => c * du c) (Ioi 0) :=
  ⟨fun h => h.monotoneOn_mul_deriv hd, relativeRiskAversionLeOne_of_monotoneOn hd⟩

/-! ### Where the boundary is

CRRA utility in log consumption is `eᵏᵗ / k` with `k = 1 - γ`, so everything below turns on the
sign of `k`. -/

/-- CRRA utility written in log consumption. -/
theorem crra_comp_exp (k : ℝ) :
    (fun t => Real.exp t ^ k / k) = fun t => Real.exp (k * t) / k := by
  funext t
  rw [← Real.exp_mul, mul_comm]

theorem hasDerivAt_expScaled {k : ℝ} (hk : k ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (k * s) / k) (Real.exp (k * t)) t := by
  have h : HasDerivAt (fun s => Real.exp (k * s)) (Real.exp (k * t) * k) t := by
    simpa using ((hasDerivAt_id t).const_mul k).exp
  simpa [mul_div_assoc, div_self hk] using h.div_const k

theorem deriv_expScaled {k : ℝ} (hk : k ≠ 0) :
    deriv (fun s => Real.exp (k * s) / k) = fun t => Real.exp (k * t) :=
  funext fun t => (hasDerivAt_expScaled hk t).deriv

/-- **CRRA with `γ < 1` has relative risk aversion at most one.** In log consumption the
utility is `e^{(1-γ)t} / (1-γ)`, whose derivative `e^{(1-γ)t}` rises because `1 - γ > 0`. -/
theorem relativeRiskAversionLeOne_crra {γ : ℝ} (hγ : γ < 1) :
    RelativeRiskAversionLeOne fun c => c ^ (1 - γ) / (1 - γ) := by
  have hk : 0 < 1 - γ := by linarith
  change ConvexOn ℝ univ fun t => Real.exp t ^ (1 - γ) / (1 - γ)
  rw [crra_comp_exp]
  refine Monotone.convexOn_univ_of_deriv
    (fun t => (hasDerivAt_expScaled hk.ne' t).differentiableAt) ?_
  rw [deriv_expScaled hk.ne']
  exact fun s t hst => Real.exp_le_exp.mpr (by nlinarith)

/-- **Log utility sits exactly on the boundary**: in log consumption it is the identity, which
is affine, hence convex — but only barely, since it is concave too. Log utility is `γ = 1`. -/
theorem relativeRiskAversionLeOne_log : RelativeRiskAversionLeOne Real.log := by
  have h : (fun t => Real.log (Real.exp t)) = _root_.id := by funext t; simp
  change ConvexOn ℝ univ fun t => Real.log (Real.exp t)
  rw [h]
  exact convexOn_id convex_univ

/-- **CRRA with `γ > 1` fails, and fails strictly.** In log consumption the utility is
`e^{(1-γ)t} / (1-γ)` with a negative exponent and a negative divisor, whose derivative
`e^{(1-γ)t}` strictly falls, so it is strictly CONCAVE in log consumption.

This is the reason the uniqueness literature stops at `γ ≤ 1`: beyond it the household's
response to the interest rate is not signed by this argument, and Açıkgöz (2018) and Walsh and
Young (2025) find calibrations where capital supply genuinely bends back. -/
theorem strictConcaveOn_crra_comp_exp {γ : ℝ} (hγ : 1 < γ) :
    StrictConcaveOn ℝ univ fun t => (Real.exp t : ℝ) ^ (1 - γ) / (1 - γ) := by
  have hk : 1 - γ < 0 := by linarith
  rw [crra_comp_exp]
  refine StrictAnti.strictConcaveOn_univ_of_deriv
    (Continuous.div_const (by fun_prop) _) ?_
  rw [deriv_expScaled hk.ne]
  exact fun s t hst => Real.exp_lt_exp.mpr (by nlinarith)

theorem not_relativeRiskAversionLeOne_crra {γ : ℝ} (hγ : 1 < γ) :
    ¬ RelativeRiskAversionLeOne fun c => c ^ (1 - γ) / (1 - γ) := by
  intro h
  have hconv : ConvexOn ℝ (univ : Set ℝ) fun t => Real.exp t ^ (1 - γ) / (1 - γ) := h
  have hconc := strictConcaveOn_crra_comp_exp hγ
  -- the midpoint of `0` and `1` separates them
  have h1 := hconv.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have h2 := hconc.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) (by norm_num : (0:ℝ) ≠ 1)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  simp only [smul_eq_mul] at h1 h2
  linarith

end LeanEconomics
