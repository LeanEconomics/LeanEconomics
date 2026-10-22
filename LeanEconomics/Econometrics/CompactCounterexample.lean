/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A counterexample to FRS's Proposition 2 with compact support (Example 2 of the comment)

Ackerberg, Geweke and Hahn's counterexample uses a Gaussian shock, outside FRS's compact-support
assumption. Example 2 of the comment gives one with compact support.

* **The density** (`bumpDensity`). `f` is Mathlib's normalised smooth bump centred at `1/2` with
  inner radius `1/4` and outer radius `1/2`: smooth (`contDiff_bumpDensity`), nonnegative,
  positive exactly on `(0, 1)` (`support_bumpDensity`), integrating to one
  (`integral_bumpDensity`), and equal to the constant `c₀ = 1 / ∫ bump ≥ 1` on `[1/4, 3/4]`
  (`bumpDensity_eq_c0`, `one_le_c0`).
* **The model** `y = γ v`, `v ∼ f`, approximated by `y = (1 + δ) γ v`, so the approximation error is
  at most `γ δ` on the support (`abs_scale_sub_le`). The law of `γ v` has density `f (y/γ) / γ`
  (`map_scale_withDensity`).
* **The likelihoods.** For data in `[γ (1 + δ)/4, 3γ/4]` the exact and computed densities are
  `M = c₀/γ` and `M/(1 + δ)` (`density_eq_on_plateau`), so `L = Mᵀ`, `L_j = (M/(1 + δ))ᵀ`,
  `L - L_j = Mᵀ (1 - (1 + δ)⁻ᵀ)` (`lik_sub_lik`) and `log L - log L_j = T log (1 + δ)`
  (`log_lik_sub_log_lik`).
* **The conclusion.** If `M > 1` the difference eventually exceeds every bound linear in `T`
  (`not_exists_linear_bound_lik_sub`); if `M < 1` it tends to zero (`tendsto_lik_sub_zero`).
-/

open MeasureTheory Real Set Filter Topology

namespace LeanEconomics

namespace ApproxLikelihood

/-! ### The density -/

/-- The smooth bump on `ℝ` centred at `1/2`, equal to one on `[1/4, 3/4]`, positive on `(0, 1)`. -/
noncomputable def bump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- **The density of Example 2**: the bump normalised to integrate to one. -/
noncomputable def bumpDensity : ℝ → ℝ := bump.normed volume

/-- The plateau value `c₀`. -/
noncomputable def c0 : ℝ := 1 / ∫ x, bump x

theorem contDiff_bumpDensity : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bumpDensity :=
  bump.contDiff_normed

theorem bumpDensity_nonneg (x : ℝ) : 0 ≤ bumpDensity x := bump.nonneg_normed x

theorem integral_bumpDensity : ∫ x, bumpDensity x = 1 := bump.integral_normed

theorem ball_half : Metric.ball (1 / 2 : ℝ) (1 / 2) = Ioo 0 1 := by
  rw [Real.ball_eq_Ioo]; norm_num

theorem support_bumpDensity : Function.support bumpDensity = Ioo 0 1 := by
  rw [bumpDensity, bump.support_normed_eq]; exact ball_half

theorem bumpDensity_eq_c0 {x : ℝ} (hx : x ∈ Icc (1 / 4 : ℝ) (3 / 4)) : bumpDensity x = c0 := by
  have hb : x ∈ Metric.closedBall (1 / 2 : ℝ) bump.rIn := by
    rw [Real.closedBall_eq_Icc]
    simp only [bump]
    constructor <;> linarith [hx.1, hx.2]
  rw [bumpDensity, ContDiffBump.normed_def, bump.one_of_mem_closedBall hb, c0]

theorem integral_bump_pos : 0 < ∫ x, bump x := bump.integral_pos

theorem integral_bump_le_one : ∫ x, bump x ≤ 1 := by
  have hle : ∀ x, bump x ≤ (Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · rw [indicator_of_mem hx]; exact bump.le_one
    · rw [indicator_of_notMem hx]
      have : x ∉ Function.support bump := by
        rw [bump.support_eq, show bump.rOut = 1 / 2 from rfl, ball_half]; exact hx
      rw [Function.notMem_support.mp this]
  calc ∫ x, bump x ≤ ∫ x, (Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ)) x :=
        integral_mono bump.integrable
          ((integrableOn_const (C := (1 : ℝ)) (by simp)).integrable_indicator measurableSet_Ioo) hle
    _ = 1 := by
        rw [integral_indicator measurableSet_Ioo, setIntegral_const]
        simp

/-- `c₀ ≥ 1`. -/
theorem one_le_c0 : 1 ≤ c0 := by
  rw [c0, le_div_iff₀ integral_bump_pos, one_mul]; exact integral_bump_le_one

theorem c0_pos : 0 < c0 := lt_of_lt_of_le one_pos one_le_c0

/-! ### The model and its densities -/

/-- The density of `y = γ v` for `v ∼ f`. -/
noncomputable def scaledDensity (γ y : ℝ) : ℝ := bumpDensity (y / γ) / γ

/-- **The law of `γ v` has density `f (y/γ)/γ`.** -/
theorem map_scale_withDensity {γ : ℝ} (hγ : 0 < γ) :
    Measure.map (fun v ↦ γ * v) (volume.withDensity fun v ↦ ENNReal.ofReal (bumpDensity v))
      = volume.withDensity fun y ↦ ENNReal.ofReal (scaledDensity γ y) := by
  have hmf : Measurable bumpDensity := contDiff_bumpDensity.continuous.measurable
  have hmg : Measurable fun v : ℝ ↦ γ * v := measurable_const_mul γ
  have hmG : Measurable fun y ↦ ENNReal.ofReal (scaledDensity γ y) :=
    ENNReal.measurable_ofReal.comp ((hmf.comp (measurable_id.div_const γ)).div_const γ)
  ext s hs
  rw [Measure.map_apply hmg hs, withDensity_apply _ (hmg hs), withDensity_apply _ hs,
    ← lintegral_indicator hs, ← lintegral_indicator (hmg hs)]
  -- `volume = γ • map (γ ·) volume`
  have hvol : (volume : Measure ℝ) = ENNReal.ofReal γ • Measure.map (fun v ↦ γ * v) volume := by
    rw [Real.map_volume_mul_left hγ.ne', smul_smul, abs_inv, abs_of_pos hγ,
      ← ENNReal.ofReal_mul hγ.le, mul_inv_cancel₀ hγ.ne', ENNReal.ofReal_one, one_smul]
  conv_rhs => rw [hvol]
  have hK : Measurable fun a ↦ s.indicator (fun y ↦ ENNReal.ofReal (scaledDensity γ y)) (γ * a) :=
    (hmG.indicator hs).comp hmg
  rw [lintegral_smul_measure, lintegral_map ((hmG.indicator hs)) hmg, smul_eq_mul,
    ← lintegral_const_mul _ hK]
  refine lintegral_congr fun v ↦ ?_
  by_cases hv : γ * v ∈ s
  · have hv' : v ∈ (fun v ↦ γ * v) ⁻¹' s := hv
    simp only [indicator_of_mem hv, indicator_of_mem hv', scaledDensity]
    rw [← ENNReal.ofReal_mul hγ.le, mul_div_cancel_left₀ v hγ.ne']
    congr 1
    field_simp
  · have hv' : v ∉ (fun v ↦ γ * v) ⁻¹' s := hv
    simp [indicator_of_notMem hv, indicator_of_notMem hv']

/-- The approximation `g_j (v) = (1 + δ) γ v` is within `γ δ` of `g (v) = γ v` on the support. -/
theorem abs_scale_sub_le {γ δ v : ℝ} (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hv : v ∈ Icc (0 : ℝ) 1) :
    |(1 + δ) * γ * v - γ * v| ≤ γ * δ := by
  rw [show (1 + δ) * γ * v - γ * v = γ * δ * v by ring, abs_of_nonneg (by
    have := hv.1; positivity)]
  calc γ * δ * v ≤ γ * δ * 1 := mul_le_mul_of_nonneg_left hv.2 (by positivity)
    _ = γ * δ := mul_one _

/-- **On the plateau** `[γ (1 + δ)/4, 3γ/4]` the exact and computed densities are `M = c₀/γ` and
`M/(1 + δ)`. -/
theorem density_eq_on_plateau {γ δ y : ℝ} (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hy : y ∈ Icc (γ * (1 + δ) / 4) (3 * γ / 4)) :
    scaledDensity γ y = c0 / γ ∧ scaledDensity ((1 + δ) * γ) y = c0 / γ / (1 + δ) := by
  obtain ⟨h1, h2⟩ := hy
  have h1δ : 0 < 1 + δ := by linarith
  constructor
  · unfold scaledDensity
    rw [bumpDensity_eq_c0]
    constructor
    · rw [le_div_iff₀ hγ]; nlinarith
    · rw [div_le_iff₀ hγ]; linarith
  · unfold scaledDensity
    rw [bumpDensity_eq_c0]
    · field_simp
    constructor
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · rw [div_le_iff₀ (by positivity)]; nlinarith

/-! ### The likelihoods -/

/-- The likelihood of a sample: the product of the densities. -/
noncomputable def sampleLik (p : ℝ → ℝ) {T : ℕ} (y : Fin T → ℝ) : ℝ := ∏ t, p (y t)

theorem sampleLik_eq_on_plateau {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 ≤ δ) {T : ℕ} {y : Fin T → ℝ}
    (hy : ∀ t, y t ∈ Icc (γ * (1 + δ) / 4) (3 * γ / 4)) :
    sampleLik (scaledDensity γ) y = (c0 / γ) ^ T ∧
      sampleLik (scaledDensity ((1 + δ) * γ)) y = (c0 / γ / (1 + δ)) ^ T := by
  constructor
  · rw [sampleLik, Finset.prod_congr rfl fun t _ ↦ (density_eq_on_plateau hγ hδ (hy t)).1]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [sampleLik, Finset.prod_congr rfl fun t _ ↦ (density_eq_on_plateau hγ hδ (hy t)).2]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **`L - L_j = Mᵀ (1 - (1 + δ)⁻ᵀ)`**, with `M = c₀/γ`. -/
theorem lik_sub_lik {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 ≤ δ) {T : ℕ} {y : Fin T → ℝ}
    (hy : ∀ t, y t ∈ Icc (γ * (1 + δ) / 4) (3 * γ / 4)) :
    sampleLik (scaledDensity γ) y - sampleLik (scaledDensity ((1 + δ) * γ)) y
      = (c0 / γ) ^ T * (1 - ((1 + δ) ^ T)⁻¹) := by
  obtain ⟨h1, h2⟩ := sampleLik_eq_on_plateau hγ hδ hy
  rw [h1, h2, div_pow (c0 / γ) (1 + δ) T]
  ring

/-- **`log L - log L_j = T log (1 + δ)`**: linear in `T`. -/
theorem log_lik_sub_log_lik {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 ≤ δ) {T : ℕ} {y : Fin T → ℝ}
    (hy : ∀ t, y t ∈ Icc (γ * (1 + δ) / 4) (3 * γ / 4)) :
    Real.log (sampleLik (scaledDensity γ) y) - Real.log (sampleLik (scaledDensity ((1 + δ) * γ)) y)
      = T * Real.log (1 + δ) := by
  obtain ⟨h1, h2⟩ := sampleLik_eq_on_plateau hγ hδ hy
  have hM : 0 < c0 / γ := div_pos c0_pos hγ
  have h1δ : 0 < 1 + δ := by linarith
  rw [h1, h2, Real.log_pow, Real.log_pow, Real.log_div hM.ne' h1δ.ne']
  ring

/-- **With `M > 1` the level difference beats every linear bound**: there is no `B` with
`Mᵀ (1 - (1 + δ)⁻ᵀ) ≤ T B` for all `T`. -/
theorem not_exists_linear_bound_lik_sub {M δ : ℝ} (hM : 1 < M) (hδ : 0 < δ) :
    ¬ ∃ B : ℝ, ∀ T : ℕ, M ^ T * (1 - ((1 + δ) ^ T)⁻¹) ≤ T * B := by
  rintro ⟨B, hB⟩
  set κ : ℝ := 1 - (1 + δ)⁻¹ with hκ
  have h1δ : 1 < 1 + δ := by linarith
  have hκ0 : 0 < κ := by
    have : (1 + δ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1δ
    linarith
  set y : ℝ := Real.sqrt M - 1 with hy
  have hy0 : 0 < y := by
    have : 1 < Real.sqrt M := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one hM
    linarith
  have hM0 : 0 ≤ M := by linarith
  -- `Mᵀ ≥ T² y²` from Bernoulli applied to `√M = 1 + y`
  have hsq : ∀ T : ℕ, (T : ℝ) ^ 2 * y ^ 2 ≤ M ^ T := by
    intro T
    have hb : 1 + (T : ℝ) * y ≤ (1 + y) ^ T := one_add_mul_le_pow (by linarith) T
    have h1y : 1 + y = Real.sqrt M := by rw [hy]; ring
    have hTy : (T : ℝ) * y ≤ (Real.sqrt M) ^ T := by rw [← h1y]; linarith
    have hTy0 : 0 ≤ (T : ℝ) * y := by positivity
    calc (T : ℝ) ^ 2 * y ^ 2 = ((T : ℝ) * y) ^ 2 := by ring
      _ ≤ ((Real.sqrt M) ^ T) ^ 2 := pow_le_pow_left₀ hTy0 hTy 2
      _ = M ^ T := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hM0]
  -- for `T ≥ 1`, `(1 + δ)⁻ᵀ ≤ (1 + δ)⁻¹`
  have hinv : ∀ T : ℕ, 1 ≤ T → κ ≤ 1 - ((1 + δ) ^ T)⁻¹ := by
    intro T hT
    have : (1 + δ) ^ 1 ≤ (1 + δ) ^ T := pow_le_pow_right₀ h1δ.le hT
    have : ((1 + δ) ^ T)⁻¹ ≤ (1 + δ)⁻¹ := by
      rw [pow_one] at this; exact inv_anti₀ (by linarith) this
    rw [hκ]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (B / (κ * y ^ 2))
  set T := n + 1
  have hT1 : 1 ≤ T := Nat.le_add_left 1 n
  have hTpos : (0 : ℝ) < T := by positivity
  have key : κ * ((T : ℝ) ^ 2 * y ^ 2) ≤ T * B := by
    calc κ * ((T : ℝ) ^ 2 * y ^ 2) ≤ (1 - ((1 + δ) ^ T)⁻¹) * M ^ T :=
          mul_le_mul (hinv T hT1) (hsq T) (by positivity)
            (by have := hinv T hT1; linarith)
      _ = M ^ T * (1 - ((1 + δ) ^ T)⁻¹) := mul_comm _ _
      _ ≤ T * B := hB T
  have : κ * y ^ 2 * T ≤ B := by
    have := key
    have h' : T * (κ * y ^ 2 * T) ≤ T * B := by nlinarith
    exact le_of_mul_le_mul_left h' hTpos
  have hky : 0 < κ * y ^ 2 := by positivity
  rw [div_lt_iff₀ hky] at hn
  have : (n : ℝ) < T := by simp [T]
  nlinarith

/-- **With `M < 1` the level difference vanishes.** -/
theorem tendsto_lik_sub_zero {M δ : ℝ} (hM0 : 0 ≤ M) (hM : M < 1) (hδ : 0 ≤ δ) :
    Tendsto (fun T : ℕ ↦ M ^ T * (1 - ((1 + δ) ^ T)⁻¹)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℕ ↦ M ^ T) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hM0 hM
  have hb : ∀ T : ℕ, |1 - ((1 + δ) ^ T)⁻¹| ≤ 1 := by
    intro T
    have hp : 1 ≤ (1 + δ) ^ T := one_le_pow₀ (by linarith)
    have h0 : 0 < ((1 + δ) ^ T)⁻¹ := by positivity
    have h1' : ((1 + δ) ^ T)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
    rw [abs_le]; constructor <;> linarith
  refine squeeze_zero_norm (fun T ↦ ?_) h1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hM0 T)]
  calc M ^ T * |1 - ((1 + δ) ^ T)⁻¹| ≤ M ^ T * 1 :=
        mul_le_mul_of_nonneg_left (hb T) (pow_nonneg hM0 T)
    _ = M ^ T := mul_one _

end ApproxLikelihood

end LeanEconomics
