/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuation
import LeanEconomics.Analysis.HARA

/-!
# The quadratic branch of HARA: excluded, and why

`IncomeFluctuationHARA` covers the `b ≠ 0` branch (shifted CRRA) and `IncomeFluctuationCARA` the
`b = 0` branch, each with a witness whose consumption function is concave outright. The third
branch, `b < 0`, is quadratic utility

  `u c = -(s - c)² / 2`,   `u' c = s - c`,

and it is the one branch this development cannot host. Every other exclusion in the tree is a
calibration that has not been checked; this one is a theorem, and this file proves it rather
than asserting it.

## The obstruction is satiation, not the formalisation

`quadUtility` has a bliss point at `s`: marginal utility vanishes there and is NEGATIVE beyond,
so utility falls. `not_monotoneOn_quadUtility` says it is therefore not monotone on any set
containing a neighbourhood of `s` — and the income-fluctuation structure asks for monotonicity
on the whole of `dom`, which contains `Ioi 0`. `no_incomeFluctuation_quadUtility` concludes: no
economy in this development has quadratic utility, whatever the bliss point.

It is worth being precise that this is not the structure being fussy. A utility that agrees with
a quadratic near its bliss point cannot be extended to a strictly increasing function at all:
`not_monotoneOn_of_deriv_neg` needs only that the derivative goes negative somewhere. Raising the
bliss point above the whole consumption range does not help either, because the structure's `dom`
is all of the non-negative half-line and a quadratic satiates somewhere on it whatever `s` is.

## What the branch would give, if it could be hosted

The Euler equation `s - c = β R Σ π (s - c')` is LINEAR in consumption, so it rearranges to

  `c = s (1 - β R) + β R · Σ π c'`,

consumption as an affine function of expected next-period consumption. That is Hall's (1978)
certainty equivalence: the aggregator is the plain weighted MEAN, not a power mean (CRRA) or a
soft minimum (CARA), there is no precautionary motive at all, and Carroll and Kimball's theorem
is immediate because an affine function of concave functions is concave. `quad_egm_of_euler` and
`concaveOn_quadEgm_comp` record that, at the level of real numbers, since there is no economy to
state it in.
-/

open Set

namespace LeanEconomics

/-! ### Quadratic utility -/

/-- **Quadratic utility** with bliss point `s`. -/
noncomputable def quadUtility (s c : ℝ) : ℝ := -(s - c) ^ 2 / 2

theorem hasDerivAt_quadUtility (s c : ℝ) : HasDerivAt (quadUtility s) (s - c) c := by
  have h : HasDerivAt (fun x : ℝ => -(s - x) ^ 2 / 2) (-(2 * (s - c) ^ 1 * -1) / 2) c :=
    (((hasDerivAt_id c).const_sub s).pow 2).neg.div_const 2
  have he : -(2 * (s - c) ^ 1 * -1) / 2 = s - c := by ring
  rw [he] at h
  exact h

@[simp] theorem quadUtility_bliss (s : ℝ) : quadUtility s s = 0 := by simp [quadUtility]

theorem quadUtility_le_zero (s c : ℝ) : quadUtility s c ≤ 0 := by
  simp only [quadUtility]
  have : (0 : ℝ) ≤ (s - c) ^ 2 := sq_nonneg _
  linarith

/-- **Satiation.** Beyond the bliss point utility strictly falls. -/
theorem quadUtility_lt_of_gt {s c : ℝ} (hc : s < c) : quadUtility s c < quadUtility s s := by
  rw [quadUtility_bliss]
  simp only [quadUtility]
  have hpos : (0 : ℝ) < c - s := by linarith
  nlinarith [hpos]

/-- **Quadratic utility is not monotone on the positives**, for any bliss point. Above `s` it
falls; at or below `0` it is falling everywhere on `Ioi 0`. -/
theorem not_monotoneOn_quadUtility (s : ℝ) : ¬ MonotoneOn (quadUtility s) (Ioi (0 : ℝ)) := by
  intro hmono
  rcases le_or_gt s 0 with hs | hs
  · -- already past the bliss point: compare `1` and `2`
    have h := hmono (mem_Ioi.mpr one_pos) (mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
      (by norm_num)
    simp only [quadUtility] at h
    nlinarith [h]
  · -- the bliss point is positive: compare `s` and `s + 1`
    have h := hmono (mem_Ioi.mpr hs) (mem_Ioi.mpr (by linarith : (0 : ℝ) < s + 1)) (by linarith)
    have hlt := quadUtility_lt_of_gt (s := s) (c := s + 1) (by linarith)
    linarith

/-- **No economy in this development has quadratic utility.** The income-fluctuation structure
requires utility to be monotone on its whole domain, and the domain contains `Ioi 0`. -/
theorem no_incomeFluctuation_quadUtility {Z : Type*} [Fintype Z] [Nonempty Z]
    [TopologicalSpace Z] [DiscreteTopology Z] {assetFloor assetCap : ℝ}
    (P : IncomeFluctuation Z assetFloor assetCap) (s : ℝ) : P.u ≠ quadUtility s := by
  intro hu
  refine not_monotoneOn_quadUtility s ?_
  rw [← hu]
  exact P.monotoneOn_u_dom.mono P.Ioi_subset_dom

/-- **The obstruction is satiation, not quadratic-ness.** Any utility whose marginal value goes
negative is non-monotone there, so no strictly increasing utility can agree with a quadratic past
its bliss point. -/
theorem not_monotoneOn_of_deriv_neg {u du : ℝ → ℝ} {s t : ℝ} (hst : s < t) (hs : 0 < s)
    (hderiv : ∀ c, HasDerivAt u (du c) c) (hneg : ∀ c ∈ Ioo s t, du c < 0) :
    ¬ MonotoneOn u (Ioi (0 : ℝ)) := by
  intro hmono
  have hanti : StrictAntiOn u (Icc s t) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc s t)
      (fun c _ => (hderiv c).continuousAt.continuousWithinAt) fun c hc => ?_
    rw [interior_Icc] at hc
    rw [(hderiv c).deriv]
    exact hneg c hc
  have hlt := hanti (left_mem_Icc.mpr hst.le) (right_mem_Icc.mpr hst.le) hst
  have hle := hmono (mem_Ioi.mpr hs) (mem_Ioi.mpr (by linarith)) hst.le
  linarith

/-! ### Certainty equivalence

What the branch would give if it could be hosted: the Euler equation is linear, so the
endogenous-gridpoint map is the weighted MEAN of next period's consumptions, shifted. -/

variable {ι : Type*} [Fintype ι]

/-- **Hall (1978).** With quadratic utility the Euler equation makes consumption affine in
expected next-period consumption. -/
theorem quad_egm_of_euler {K s C : ℝ} {w c : ι → ℝ} (hw1 : ∑ i, w i = 1)
    (heuler : s - C = K * ∑ i, w i * (s - c i)) :
    C = s * (1 - K) + K * ∑ i, w i * c i := by
  have hsplit : ∑ i, w i * (s - c i) = s - ∑ i, w i * c i := by
    rw [show ∑ i, w i * (s - c i) = ∑ i, (w i * s - w i * c i) from
      Finset.sum_congr rfl fun i _ => by ring, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1]
    ring
  rw [hsplit] at heuler
  linarith

/-- The aggregator is affine in next period's consumptions, so it is concave in assets whenever
they are — Carroll and Kimball with nothing to prove, and no precautionary motive. -/
theorem concaveOn_quadEgm_comp {D : Set ℝ} (hD : Convex ℝ D) {K s : ℝ} (hK : 0 ≤ K)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {f : ι → ℝ → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ D (f i)) :
    ConcaveOn ℝ D fun a => s * (1 - K) + K * ∑ i, w i * f i a := by
  refine ⟨hD, fun a ha b hb θ φ hθ hφ hθφ => ?_⟩
  have hstep : ∀ i, θ * (w i * f i a) + φ * (w i * f i b) ≤ w i * f i (θ * a + φ * b) := by
    intro i
    have h := (hconc i).2 ha hb hθ hφ hθφ
    simp only [smul_eq_mul] at h
    have hmul := mul_le_mul_of_nonneg_left h (hw i)
    linear_combination hmul
  have hsum : θ * ∑ i, w i * f i a + φ * ∑ i, w i * f i b
      ≤ ∑ i, w i * f i (θ * a + φ * b) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hstep i
  simp only [smul_eq_mul] at hsum ⊢
  have hconst : θ * (s * (1 - K)) + φ * (s * (1 - K)) = s * (1 - K) := by
    rw [← add_mul, hθφ, one_mul]
  have hscaled := mul_le_mul_of_nonneg_left hsum hK
  nlinarith [hconst, hscaled]

end LeanEconomics
