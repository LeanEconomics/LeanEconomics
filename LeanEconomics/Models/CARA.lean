/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuation
import LeanEconomics.Analysis.RelativeRiskAversion

/-!
# CARA utility

`u c = -exp (-α c) / α`, the `b = 0` branch of HARA: constant ABSOLUTE risk aversion `α`, and
relative risk aversion `α c`, which grows without bound. It is the one HARA branch the
shifted-CRRA parameterisation of `Analysis.HARA` does not reach, and the one whose
Carroll–Kimball step needs a different aggregator — the soft minimum of `Analysis.SoftMin`
rather than the power mean.

## What it is and is not good for here

On `Ici 0` it is bounded on both sides: `u 0 = -1/α` and `u c ↗ 0`, so a capped model admits it
— the reward is bounded above (which the extended program requires) and bounded below at the
selection. Marginal utility at zero consumption is finite, so this is a member of the BOUNDED
family, like CES with `γ < 1`, and it needs the same consumption-floor machinery rather than an
Inada condition.

What it does NOT satisfy is Light's condition: relative risk aversion is `α c`, so `c · u' c`
= `c · exp (-α c)` rises only while `c < 1/α`. So CARA is available for Carroll–Kimball and for
the existence results, and is outside the uniqueness argument unless consumption is capped below
`1/α`.
-/

open Set Filter Topology

namespace LeanEconomics

/-- **CARA utility** with absolute risk aversion `α`. -/
noncomputable def caraUtility (α c : ℝ) : ℝ := -Real.exp (-α * c) / α

@[simp] theorem caraUtility_zero (α : ℝ) : caraUtility α 0 = -1 / α := by
  simp [caraUtility]

theorem caraUtility_neg {α : ℝ} (hα : 0 < α) (c : ℝ) : caraUtility α c < 0 := by
  have := Real.exp_pos (-α * c)
  simp only [caraUtility]
  apply div_neg_of_neg_of_pos <;> linarith

/-- **Marginal utility is `exp (-α c)`.** -/
theorem hasDerivAt_caraUtility {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    HasDerivAt (caraUtility α) (Real.exp (-α * c)) c := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (-α * x)) (Real.exp (-α * c) * -α) c := by
    simpa using ((hasDerivAt_id c).const_mul (-α)).exp
  have h2 := (h.neg).div_const α
  have hrw : -(Real.exp (-α * c) * -α) / α = Real.exp (-α * c) := by field_simp
  rw [hrw] at h2
  exact h2

theorem deriv_caraUtility {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    deriv (caraUtility α) c = Real.exp (-α * c) := (hasDerivAt_caraUtility hα c).deriv

theorem continuous_caraUtility {α : ℝ} (hα : α ≠ 0) : Continuous (caraUtility α) :=
  continuous_iff_continuousAt.mpr fun c => (hasDerivAt_caraUtility hα c).continuousAt

theorem strictMono_caraUtility {α : ℝ} (hα : 0 < α) : StrictMono (caraUtility α) := by
  refine strictMono_of_deriv_pos fun c => ?_
  rw [deriv_caraUtility (ne_of_gt hα) c]
  exact Real.exp_pos _

theorem monotoneOn_caraUtility {α : ℝ} (hα : 0 < α) (s : Set ℝ) :
    MonotoneOn (caraUtility α) s := (strictMono_caraUtility hα).monotone.monotoneOn s

theorem strictConcaveOn_caraUtility {α : ℝ} (hα : 0 < α) :
    StrictConcaveOn ℝ univ (caraUtility α) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv convex_univ
    (continuous_caraUtility (ne_of_gt hα)).continuousOn fun x _ y _ hxy => ?_
  rw [deriv_caraUtility (ne_of_gt hα), deriv_caraUtility (ne_of_gt hα)]
  exact Real.exp_lt_exp.mpr (by nlinarith)

/-- **Relative risk aversion is `α c`**, read off the product that `RelativeRiskAversionLeOne`
is about: `c · u' c = c · exp (-α c)` falls once `c` passes `1 / α`, so Light's condition fails
for every `α > 0` on any consumption range reaching that far. -/
theorem not_monotoneOn_mul_deriv_caraUtility {α : ℝ} (hα : 0 < α) :
    ¬ MonotoneOn (fun c => c * Real.exp (-α * c)) (Ioi (0 : ℝ)) := by
  intro hmono
  have h1 : (1 / α) ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by positivity)
  have h2 : (2 / α) ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by positivity)
  have hle : (1 / α) ≤ 2 / α := by
    rw [div_le_div_iff_of_pos_right hα]; norm_num
  have h := hmono h1 h2 hle
  simp only [] at h
  have he1 : -α * (1 / α) = -1 := by field_simp
  have he2 : -α * (2 / α) = -2 := by field_simp
  rw [he1, he2] at h
  -- `(1/α) e⁻¹ ≤ (2/α) e⁻²` is `e ≤ 2`, which is false
  have hexp : Real.exp 1 ≤ 2 := by
    have hpos : (0 : ℝ) < Real.exp (-2) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hα)
    rw [show α * (1 / α * Real.exp (-1)) = Real.exp (-1) by field_simp,
      show α * (2 / α * Real.exp (-2)) = 2 * Real.exp (-2) by field_simp] at hmul
    have hrw : Real.exp (-1) = Real.exp 1 * Real.exp (-2) := by
      rw [← Real.exp_add]; norm_num
    rw [hrw] at hmul
    exact le_of_mul_le_mul_right (by linarith) hpos
  linarith [Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero]

end LeanEconomics
