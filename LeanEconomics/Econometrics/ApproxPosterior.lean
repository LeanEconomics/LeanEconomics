/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Posteriors from a multiplicatively perturbed likelihood

Proposition 2′ (`ApproxLikelihood.likelihood_le_exp_mul`) says the computed likelihood is within
a factor `exp (± D)` of the exact one. If that holds at every parameter value `γ` with a common
`D`, the Bayesian objects built from the two likelihoods are close, with explicit constants:

* the marginal likelihoods (evidence) are within `exp (± D)` (`evidence_le_exp_mul`);
* likelihood ratios, and so Metropolis–Hastings acceptance ratios, are within `exp (± 2D)`
  (`ratio_le_exp_mul_ratio`);
* the posterior densities with respect to the prior are within `exp (± 2D)`
  (`postDens_le_exp_mul`);
* the `L¹` distance between the posteriors (twice their total variation distance) is at most
  `exp (2D) - 1` (`integral_abs_postDens_sub_le`);
* posterior expectations of a function bounded by `B` differ by at most `B (exp (2D) - 1)`
  (`abs_integral_postDens_sub_le`). This covers posterior means, probabilities of sets, and
  FRS's Corollary 4.

These are the explicit, non-asymptotic counterpart of the Hellinger bound of Dashti and Stuart
(*The Bayesian Approach to Inverse Problems*, Theorem 4.9 of arXiv:1302.6989v4), which assumes
`|Φ - Φ_N| ≤ M₂ ψ(N)` for the negative log likelihoods `Φ` and concludes
`d_Hell (μ, μ_N) ≤ C ψ (N)` for `N` large.
-/

open MeasureTheory Real

namespace LeanEconomics

namespace ApproxPosterior

variable {Γ : Type*} [MeasurableSpace Γ] {pr : Measure Γ} {L Lj : Γ → ℝ} {D : ℝ}

/-- The posterior density with respect to the prior: likelihood over evidence. -/
noncomputable def postDens (pr : Measure Γ) (L : Γ → ℝ) (γ : Γ) : ℝ := L γ / ∫ g, L g ∂pr

/-- **The evidence.** -/
theorem evidence_le_exp_mul (hLj0 : ∀ γ, 0 ≤ Lj γ) (hL : Integrable L pr)
    (h : ∀ γ, Lj γ ≤ exp D * L γ) : ∫ γ, Lj γ ∂pr ≤ exp D * ∫ γ, L γ ∂pr := by
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall hLj0) (hL.const_mul _)
    (Filter.Eventually.of_forall h)

omit [MeasurableSpace Γ] in
/-- **Likelihood ratios** (Metropolis–Hastings acceptance ratios, FRS's Corollary 1). -/
theorem ratio_le_exp_mul_ratio (hL : ∀ γ, 0 < L γ) (hLj : ∀ γ, 0 < Lj γ)
    (h1 : ∀ γ, Lj γ ≤ exp D * L γ) (h2 : ∀ γ, L γ ≤ exp D * Lj γ) (γ γ' : Γ) :
    Lj γ' / Lj γ ≤ exp (2 * D) * (L γ' / L γ) := by
  rw [div_le_iff₀ (hLj γ), show 2 * D = D + D by ring, exp_add]
  have e : exp D * exp D * (L γ' / L γ) * Lj γ = exp D * L γ' * (exp D * Lj γ / L γ) := by
    field_simp
  rw [e]
  have h3 : 1 ≤ exp D * Lj γ / L γ := by rw [le_div_iff₀ (hL γ)]; linarith [h2 γ]
  have h4 : 0 ≤ exp D * L γ' := by have := hL γ'; positivity
  nlinarith [h1 γ']

variable (hL : ∀ γ, 0 < L γ) (hLj : ∀ γ, 0 < Lj γ)
  (h1 : ∀ γ, Lj γ ≤ exp D * L γ) (h2 : ∀ γ, L γ ≤ exp D * Lj γ)
  (hiL : Integrable L pr) (hiLj : Integrable Lj pr) (hZ : 0 < ∫ γ, L γ ∂pr)
include hL hLj h1 h2 hiL hiLj hZ

omit hLj h1 hiL in
theorem evidence_pos : 0 < ∫ γ, Lj γ ∂pr := by
  have h := evidence_le_exp_mul (fun γ ↦ (hL γ).le) hiLj h2
  have : 0 < exp D * ∫ γ, Lj γ ∂pr := hZ.trans_le h
  exact pos_of_mul_pos_right this (exp_pos D).le

omit hLj hiL in
/-- **The posterior densities** are within a factor `exp (2D)`. -/
theorem postDens_le_exp_mul (γ : Γ) : postDens pr Lj γ ≤ exp (2 * D) * postDens pr L γ := by
  have hZj := evidence_pos hL h2 hiLj hZ
  have hE := evidence_le_exp_mul (fun γ ↦ (hL γ).le) hiLj h2
  unfold postDens
  rw [div_le_iff₀ hZj, show 2 * D = D + D by ring, exp_add]
  have e : exp D * exp D * (L γ / ∫ g, L g ∂pr) * ∫ g, Lj g ∂pr
      = exp D * L γ * (exp D * (∫ g, Lj g ∂pr) / ∫ g, L g ∂pr) := by field_simp
  rw [e]
  have h3 : 1 ≤ exp D * (∫ g, Lj g ∂pr) / ∫ g, L g ∂pr := by rw [le_div_iff₀ hZ]; linarith
  have h4 : 0 ≤ exp D * L γ := by have := hL γ; positivity
  nlinarith [h1 γ]

omit hL hLj h1 h2 hiL hiLj in
/-- The posterior density integrates to one against the prior. -/
theorem integral_postDens : ∫ γ, postDens pr L γ ∂pr = 1 := by
  unfold postDens
  rw [integral_div, div_self hZ.ne']

theorem abs_postDens_sub_le (γ : Γ) :
    |postDens pr Lj γ - postDens pr L γ| ≤ (exp (2 * D) - 1) * postDens pr L γ := by
  have hZj := evidence_pos hL h2 hiLj hZ
  have ha := postDens_le_exp_mul hL h1 h2 hiLj hZ γ
  have hb := postDens_le_exp_mul (pr := pr) hLj h2 h1 hiL hZj γ
  have hp : 0 < postDens pr L γ := div_pos (hL γ) hZ
  have hq : 0 < postDens pr Lj γ := div_pos (hLj γ) hZj
  have hE : 1 ≤ exp (2 * D) := by
    have e : exp (2 * D) = exp D * exp D := by rw [← exp_add]; ring_nf
    have h3 : Lj γ ≤ exp D * (exp D * Lj γ) :=
      (h1 γ).trans (mul_le_mul_of_nonneg_left (h2 γ) (exp_pos D).le)
    have h4 : 1 * Lj γ ≤ exp (2 * D) * Lj γ := by rw [e]; nlinarith [h3]
    exact le_of_mul_le_mul_right h4 (hLj γ)
  -- `b ≤ e a` gives `b - a ≤ (e - 1) a`, and `a ≤ e b` gives `a - b ≤ (1 - 1/e) a ≤ (e - 1) a`
  rw [abs_le]
  constructor
  · have hinv : postDens pr L γ ≤ exp (2 * D) * postDens pr Lj γ := hb
    have key : postDens pr L γ - postDens pr Lj γ ≤ (exp (2 * D) - 1) * postDens pr L γ := by
      have h5 : postDens pr L γ * 1 ≤ exp (2 * D) * postDens pr Lj γ := by linarith
      have h6 : (2 : ℝ) - exp (2 * D) ≤ 1 / exp (2 * D) := by
        rw [le_div_iff₀ (exp_pos _)]; nlinarith [hE]
      have h7 : postDens pr L γ / exp (2 * D) ≤ postDens pr Lj γ := by
        rw [div_le_iff₀ (exp_pos _)]; linarith
      have h8 : (2 - exp (2 * D)) * postDens pr L γ ≤ postDens pr L γ / exp (2 * D) := by
        rw [div_eq_mul_one_div, mul_comm (postDens pr L γ)]
        exact mul_le_mul_of_nonneg_right h6 hp.le
      nlinarith
    linarith
  · linarith

/-- **The posteriors are close in `L¹` (twice total variation).** -/
theorem integral_abs_postDens_sub_le :
    ∫ γ, |postDens pr Lj γ - postDens pr L γ| ∂pr ≤ exp (2 * D) - 1 := by
  have hint : Integrable (postDens pr L) pr := hiL.div_const _
  calc ∫ γ, |postDens pr Lj γ - postDens pr L γ| ∂pr
      ≤ ∫ γ, (exp (2 * D) - 1) * postDens pr L γ ∂pr :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
          (hint.const_mul _) (Filter.Eventually.of_forall
            (abs_postDens_sub_le hL hLj h1 h2 hiL hiLj hZ))
    _ = exp (2 * D) - 1 := by
        rw [integral_const_mul, integral_postDens hZ, mul_one]

/-- **Posterior expectations.** For `|h| ≤ B`, the two posterior means of `h` differ by at most
`B (exp (2D) - 1)`. -/
theorem abs_integral_postDens_sub_le {h : Γ → ℝ} {B : ℝ} (hm : AEStronglyMeasurable h pr)
    (hB0 : 0 ≤ B) (hB : ∀ γ, |h γ| ≤ B) :
    |∫ γ, h γ * postDens pr Lj γ ∂pr - ∫ γ, h γ * postDens pr L γ ∂pr|
      ≤ B * (exp (2 * D) - 1) := by
  have hZj := evidence_pos hL h2 hiLj hZ
  have hiP : Integrable (postDens pr L) pr := hiL.div_const _
  have hiPj : Integrable (postDens pr Lj) pr := hiLj.div_const _
  have hbd : ∀ {f : Γ → ℝ}, Integrable f pr → Integrable (fun γ ↦ h γ * f γ) pr :=
    fun hf ↦ hf.bdd_mul hm (Filter.Eventually.of_forall fun γ ↦ by
      rw [Real.norm_eq_abs]; exact hB γ)
  rw [← integral_sub (hbd hiPj) (hbd hiP)]
  calc |∫ γ, (h γ * postDens pr Lj γ - h γ * postDens pr L γ) ∂pr|
      ≤ ∫ γ, |h γ * postDens pr Lj γ - h γ * postDens pr L γ| ∂pr :=
        abs_integral_le_integral_abs
    _ ≤ ∫ γ, B * |postDens pr Lj γ - postDens pr L γ| ∂pr := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
          (((hiPj.sub hiP).abs).const_mul _) (Filter.Eventually.of_forall fun γ ↦ ?_)
        dsimp only
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_right (hB γ) (abs_nonneg _)
    _ = B * ∫ γ, |postDens pr Lj γ - postDens pr L γ| ∂pr := integral_const_mul _ _
    _ ≤ B * (exp (2 * D) - 1) := by
        gcongr
        exact integral_abs_postDens_sub_le hL hLj h1 h2 hiL hiLj hZ

end ApproxPosterior

end LeanEconomics
