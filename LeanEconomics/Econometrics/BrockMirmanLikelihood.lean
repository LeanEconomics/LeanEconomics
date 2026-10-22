/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Econometrics.ApproxLikelihoodModel

/-!
# Corrected Proposition 2′ for the Brock–Mirman model

`abs_log_likelihood_sub_le_of_primitives` is stated for a compact metric state space on which the
exact transition contracts for every shock. This file instantiates it for Brock–Mirman (log
utility, Cobb–Douglas production with capital share `θ`, full depreciation), whose policy is
`k' = θβ z k^θ` with `log z' = ρ log z + ε`, `|ε| ≤ ε̄`.

The state is `(x, η) = (log k, λ log z)`, on the compact rectangle
`[(a - η̄/λ)/(1 - θ), (a + η̄/λ)/(1 - θ)] × [-η̄, η̄]`
with `a = log (θβ)` and `η̄ = λ ε̄ / (1 - ρ)`,
which is invariant (`bmRect_mapsTo`). With the sup metric this is the weighted metric
`max (|Δ log k|, λ |Δ log z|)`, and the transition contracts for every shock with factor
`max (θ + 1/λ) ρ < 1` once `λ > 1/(1 - θ)` (`bmMap_contraction`). The shock is taken on its compact
support `[-ε̄, ε̄]`.

`brockMirman_abs_log_likelihood_sub_le` is then Corrected Proposition 2′ for Brock–Mirman: the
general theorem with the state space, the exact transition and its contraction supplied, and the
computed transition, the densities and the uniqueness of the two invariant distributions left as
hypotheses, exactly as in the general theorem.
-/

open MeasureTheory Real Function Set

namespace LeanEconomics

namespace ApproxLikelihood

/-- Parameters of the Brock–Mirman model and the metric weight `λ`. -/
structure BMParams where
  θ : ℝ
  β : ℝ
  ρ : ℝ
  lam : ℝ
  εbar : ℝ
  hθ0 : 0 ≤ θ
  hθ1 : θ < 1
  hρ0 : 0 ≤ ρ
  hρ1 : ρ < 1
  hlam : 1 / (1 - θ) < lam
  hε : 0 ≤ εbar

namespace BMParams

variable (p : BMParams)

theorem lam_pos : 0 < p.lam :=
  lt_trans (div_pos one_pos (by linarith [p.hθ1])) p.hlam

/-- `a = log (θβ)`. -/
noncomputable def a : ℝ := Real.log (p.θ * p.β)

/-- The bound on `η = λ log z`. -/
noncomputable def ηbar : ℝ := p.lam * p.εbar / (1 - p.ρ)

theorem ηbar_nonneg : 0 ≤ p.ηbar :=
  div_nonneg (mul_nonneg p.lam_pos.le p.hε) (by linarith [p.hρ1])

noncomputable def xlo : ℝ := (p.a - p.ηbar / p.lam) / (1 - p.θ)
noncomputable def xhi : ℝ := (p.a + p.ηbar / p.lam) / (1 - p.θ)

/-- The compact invariant rectangle in `(x, η) = (log k, λ log z)`. -/
def rect : Set (ℝ × ℝ) := Icc p.xlo p.xhi ×ˢ Icc (-p.ηbar) p.ηbar

/-- The contraction factor `max (θ + 1/λ) ρ`. -/
noncomputable def factor : ℝ := max (p.θ + 1 / p.lam) p.ρ

theorem factor_nonneg : 0 ≤ p.factor := le_max_of_le_right p.hρ0

theorem factor_lt_one : p.factor < 1 := by
  have h1 : 0 < 1 - p.θ := by linarith [p.hθ1]
  have hl := p.lam_pos
  refine max_lt ?_ p.hρ1
  have : 1 < (1 - p.θ) * p.lam := by
    have := p.hlam; rw [div_lt_iff₀ h1] at this; linarith
  have : 1 / p.lam < 1 - p.θ := by rw [div_lt_iff₀ hl]; linarith
  linarith

/-- The Brock–Mirman transition in `(x, η)`. -/
noncomputable def step (s : ℝ × ℝ) (ε : ℝ) : ℝ × ℝ :=
  (p.a + s.2 / p.lam + p.θ * s.1, p.ρ * s.2 + p.lam * ε)

/-- **The rectangle is invariant** under every shock in `[-ε̄, ε̄]`. -/
theorem rect_mapsTo {s : ℝ × ℝ} (hs : s ∈ p.rect) {ε : ℝ} (hε : ε ∈ Icc (-p.εbar) p.εbar) :
    p.step s ε ∈ p.rect := by
  obtain ⟨⟨hx1, hx2⟩, hη1, hη2⟩ := hs
  obtain ⟨he1, he2⟩ := hε
  have h1 : 0 < 1 - p.θ := by linarith [p.hθ1]
  have hρ1 : 0 < 1 - p.ρ := by linarith [p.hρ1]
  have hl := p.lam_pos
  have hθ := p.hθ0
  have hρ := p.hρ0
  have hηdef : p.ηbar * (1 - p.ρ) = p.lam * p.εbar := by
    unfold ηbar; field_simp
  have hη1' : -(p.ηbar / p.lam) ≤ s.2 / p.lam := by
    rw [← neg_div]; exact div_le_div_of_nonneg_right hη1 hl.le
  have hη2' : s.2 / p.lam ≤ p.ηbar / p.lam := div_le_div_of_nonneg_right hη2 hl.le
  unfold xlo at hx1
  unfold xhi at hx2
  rw [div_le_iff₀ h1] at hx1
  rw [le_div_iff₀ h1] at hx2
  simp only [rect, step, mem_prod, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold xlo; rw [div_le_iff₀ h1]; nlinarith
  · unfold xhi; rw [le_div_iff₀ h1]; nlinarith
  · nlinarith
  · nlinarith

/-- **Contraction for every shock**, in the sup metric on `(x, η)`. -/
theorem step_contraction (s s' : ℝ × ℝ) (ε : ℝ) :
    dist (p.step s ε) (p.step s' ε) ≤ p.factor * dist s s' := by
  have hl := p.lam_pos
  have hθ := p.hθ0
  have hρ := p.hρ0
  set d := dist s s'
  have hx : |s.1 - s'.1| ≤ d := by
    simp only [d, Prod.dist_eq, Real.dist_eq]; exact le_max_left _ _
  have hη : |s.2 - s'.2| ≤ d := by
    simp only [d, Prod.dist_eq, Real.dist_eq]; exact le_max_right _ _
  have hd0 : 0 ≤ d := dist_nonneg
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [step]
  refine max_le ?_ ?_
  · calc |p.a + s.2 / p.lam + p.θ * s.1 - (p.a + s'.2 / p.lam + p.θ * s'.1)|
        = |p.θ * (s.1 - s'.1) + (s.2 - s'.2) / p.lam| := by ring_nf
      _ ≤ |p.θ * (s.1 - s'.1)| + |(s.2 - s'.2) / p.lam| := abs_add_le _ _
      _ = p.θ * |s.1 - s'.1| + 1 / p.lam * |s.2 - s'.2| := by
          rw [abs_mul, abs_of_nonneg hθ, abs_div, abs_of_pos hl]; ring
      _ ≤ p.θ * d + 1 / p.lam * d := by gcongr
      _ = (p.θ + 1 / p.lam) * d := by ring
      _ ≤ p.factor * d := mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
  · calc |p.ρ * s.2 + p.lam * ε - (p.ρ * s'.2 + p.lam * ε)| = p.ρ * |s.2 - s'.2| := by
          rw [show p.ρ * s.2 + p.lam * ε - (p.ρ * s'.2 + p.lam * ε) = p.ρ * (s.2 - s'.2) by ring,
            abs_mul, abs_of_nonneg hρ]
      _ ≤ p.ρ * d := by gcongr
      _ ≤ p.factor * d := mul_le_mul_of_nonneg_right (le_max_right _ _) hd0

theorem continuous_step : Continuous fun q : (ℝ × ℝ) × ℝ ↦ p.step q.1 q.2 := by
  unfold step; fun_prop

/-- The state space: the rectangle as a type. -/
abbrev State : Type := ↥p.rect

/-- The shock space: the support `[-ε̄, ε̄]` as a type. -/
abbrev Shock : Type := ↥(Icc (-p.εbar) p.εbar)

instance : CompactSpace p.State :=
  isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)

instance : Nonempty p.State := by
  have h1 : 0 < 1 - p.θ := by linarith [p.hθ1]
  have hle : p.xlo ≤ p.xhi := by
    unfold xlo xhi
    apply div_le_div_of_nonneg_right _ h1.le
    have := div_nonneg p.ηbar_nonneg p.lam_pos.le
    linarith
  exact ⟨⟨(p.xlo, 0), ⟨le_rfl, hle⟩, by have := p.ηbar_nonneg; constructor <;> linarith⟩⟩

/-- The Brock–Mirman transition on the state space. -/
noncomputable def map (s : p.State) (w : p.Shock) : p.State :=
  ⟨p.step s.1 w.1, p.rect_mapsTo s.2 w.2⟩

theorem map_contraction (w : p.Shock) (s s' : p.State) :
    dist (p.map s w) (p.map s' w) ≤ p.factor * dist s s' :=
  p.step_contraction s.1 s'.1 w.1

theorem continuous_uncurry_map : Continuous (uncurry p.map) :=
  Continuous.subtype_mk (p.continuous_step.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))) _

theorem continuous_map (w : p.Shock) : Continuous fun s ↦ p.map s w :=
  p.continuous_uncurry_map.comp (continuous_id.prodMk continuous_const)

theorem measurable_uncurry_map : Measurable (uncurry p.map) :=
  p.continuous_uncurry_map.measurable

end BMParams

/-- **Corrected Proposition 2′ for Brock–Mirman.** For any computed transition `φj` within `δ` of
the Brock–Mirman transition in the weighted metric, and per-state densities as in the general
theorem, with the contraction factor `α = max (θ + 1/λ) ρ`,

  `|log L_j - log L| ≤ T (η + c δ / (1 - α)) / ξ + (c α / ξ) δ / (1 - α)²`. -/
theorem brockMirman_abs_log_likelihood_sub_le (p : BMParams) {T : ℕ}
    {dens densj : Fin T → p.State → ℝ} {ξ M η c δ : ℝ}
    (ν : Measure p.Shock) [IsProbabilityMeasure ν]
    (Q : Measure (ℕ → p.Shock)) [IsProbabilityMeasure Q] (hδ0 : 0 ≤ δ)
    (φj : p.State → p.Shock → p.State)
    (hδ : ∀ s w, dist (φj s w) (p.map s w) ≤ δ)
    (hφjm : Measurable (uncurry φj)) (hφjc : ∀ w, Continuous fun s ↦ φj s w)
    (μs μjs : Measure p.State)
    (huniq : ∀ μ : Measure p.State, IsProbabilityMeasure μ →
      (μ.prod ν).map (uncurry p.map) = μ → μ = μs)
    (huniqj : ∀ μ : Measure p.State, IsProbabilityMeasure μ →
      (μ.prod ν).map (uncurry φj) = μ → μ = μjs)
    (hξ : 0 < ξ) (hlo : ∀ t s, ξ ≤ dens t s) (hloj : ∀ t s, ξ ≤ densj t s)
    (hhi : ∀ t s, dens t s ≤ M) (hhij : ∀ t s, densj t s ≤ M)
    (hdm : ∀ t, Measurable (dens t)) (hdjm : ∀ t, Measurable (densj t))
    (hη : ∀ t s, |densj t s - dens t s| ≤ η) (hc : 0 ≤ c)
    (hlip : ∀ t s s', |dens t s - dens t s'| ≤ c * dist s s') :
    |log (∫ s, initLik (densPath φj densj) Q s ∂μjs)
        - log (∫ s, initLik (densPath p.map dens) Q s ∂μs)|
      ≤ T * ((η + c * (δ / (1 - p.factor))) / ξ)
          + (c * p.factor / ξ) * δ / (1 - p.factor) ^ 2 :=
  abs_log_likelihood_sub_le_of_primitives ν Q p.factor_nonneg p.factor_lt_one hδ0
    (fun w s s' ↦ p.map_contraction w s s') hδ p.measurable_uncurry_map hφjm p.continuous_map
    hφjc μs μjs huniq huniqj hξ hlo hloj hhi hhij hdm hdjm hη hc hlip

end ApproxLikelihood

end LeanEconomics
