/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Econometrics.ApproxLikelihoodModel
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Corrected Proposition 2′ for the Brock–Mirman model

`abs_log_likelihood_sub_le_of_primitives` is stated for a compact metric state space on which the
exact transition contracts for every shock. This file instantiates it for Brock–Mirman (log
utility, Cobb–Douglas production with capital share `θ`, full depreciation), whose policy is
`k' = θβ z k^θ` with `log z' = ρ log z + ε`, `|ε| ≤ ε̄`.

The state is `(x, η) = (log k, λ log z)`, on the compact rectangle
`[(a - η̄/λ)/(1 - θ), (a + η̄/λ)/(1 - θ)] × [-η̄, η̄]`
with `a = log (θβ)` and `η̄ = λ ε̄ / (1 - ρ)`,
which is invariant (`rect_mapsTo`). The ambient space is `WithLp 1 (ℝ × ℝ)`, whose distance is the
sum `|Δx| + |Δη|`, which is the weighted metric `|Δ log k| + λ |Δ log z|` of Remark 12 of the
comment. In it the transition contracts for every shock with factor `max θ (ρ + 1/λ) < 1` once
`λ > 1/(1 - ρ)` (`step_contraction`). The shock is taken on its compact support `[-ε̄, ε̄]`.

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
  hlam : 1 / (1 - ρ) < lam
  hε : 0 ≤ εbar

namespace BMParams

variable (p : BMParams)

theorem lam_pos : 0 < p.lam :=
  lt_trans (div_pos one_pos (by linarith [p.hρ1])) p.hlam

/-- `a = log (θβ)`. -/
noncomputable def a : ℝ := Real.log (p.θ * p.β)

/-- The bound on `η = λ log z`. -/
noncomputable def ηbar : ℝ := p.lam * p.εbar / (1 - p.ρ)

theorem ηbar_nonneg : 0 ≤ p.ηbar :=
  div_nonneg (mul_nonneg p.lam_pos.le p.hε) (by linarith [p.hρ1])

noncomputable def xlo : ℝ := (p.a - p.ηbar / p.lam) / (1 - p.θ)
noncomputable def xhi : ℝ := (p.a + p.ηbar / p.lam) / (1 - p.θ)

/-- The ambient space: `ℝ²` with the sum distance `|Δx| + |Δη|`. -/
abbrev E : Type := WithLp 1 (ℝ × ℝ)

/-- The compact invariant rectangle in `(x, η) = (log k, λ log z)`. -/
def rect : Set E := (WithLp.homeomorphProd 1 ℝ ℝ) ⁻¹' (Icc p.xlo p.xhi ×ˢ Icc (-p.ηbar) p.ηbar)

theorem mem_rect {s : E} :
    s ∈ p.rect ↔ s.fst ∈ Icc p.xlo p.xhi ∧ s.snd ∈ Icc (-p.ηbar) p.ηbar := Iff.rfl

/-- The contraction factor `max θ (ρ + 1/λ)`. -/
noncomputable def factor : ℝ := max p.θ (p.ρ + 1 / p.lam)

theorem factor_nonneg : 0 ≤ p.factor := le_max_of_le_left p.hθ0

theorem factor_lt_one : p.factor < 1 := by
  have h1 : 0 < 1 - p.ρ := by linarith [p.hρ1]
  have hl := p.lam_pos
  refine max_lt p.hθ1 ?_
  have : 1 < (1 - p.ρ) * p.lam := by
    have := p.hlam; rw [div_lt_iff₀ h1] at this; linarith
  have : 1 / p.lam < 1 - p.ρ := by rw [div_lt_iff₀ hl]; linarith
  linarith

/-- The Brock–Mirman transition in `(x, η)`. -/
noncomputable def step (s : E) (ε : ℝ) : E :=
  WithLp.toLp 1 (p.a + s.snd / p.lam + p.θ * s.fst, p.ρ * s.snd + p.lam * ε)

/-- **The rectangle is invariant** under every shock in `[-ε̄, ε̄]`. -/
theorem rect_mapsTo {s : E} (hs : s ∈ p.rect) {ε : ℝ} (hε : ε ∈ Icc (-p.εbar) p.εbar) :
    p.step s ε ∈ p.rect := by
  obtain ⟨⟨hx1, hx2⟩, hη1, hη2⟩ := p.mem_rect.mp hs
  obtain ⟨he1, he2⟩ := hε
  have h1 : 0 < 1 - p.θ := by linarith [p.hθ1]
  have hρ1 : 0 < 1 - p.ρ := by linarith [p.hρ1]
  have hl := p.lam_pos
  have hθ := p.hθ0
  have hρ := p.hρ0
  have hηdef : p.ηbar * (1 - p.ρ) = p.lam * p.εbar := by
    unfold ηbar; field_simp
  have hη1' : -(p.ηbar / p.lam) ≤ s.snd / p.lam := by
    rw [← neg_div]; exact div_le_div_of_nonneg_right hη1 hl.le
  have hη2' : s.snd / p.lam ≤ p.ηbar / p.lam := div_le_div_of_nonneg_right hη2 hl.le
  unfold xlo at hx1
  unfold xhi at hx2
  rw [div_le_iff₀ h1] at hx1
  rw [le_div_iff₀ h1] at hx2
  rw [p.mem_rect]
  simp only [step, WithLp.toLp_fst, WithLp.toLp_snd, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold xlo; rw [div_le_iff₀ h1]; nlinarith
  · unfold xhi; rw [le_div_iff₀ h1]; nlinarith
  · nlinarith
  · nlinarith

/-- **Contraction for every shock**, in the sum metric `|Δx| + |Δη|`. -/
theorem step_contraction (s s' : E) (ε : ℝ) :
    dist (p.step s ε) (p.step s' ε) ≤ p.factor * dist s s' := by
  have hl := p.lam_pos
  have hθ := p.hθ0
  have hρ := p.hρ0
  rw [WithLp.prod_dist_eq_of_L1, WithLp.prod_dist_eq_of_L1, Real.dist_eq, Real.dist_eq,
    Real.dist_eq, Real.dist_eq]
  simp only [step, WithLp.toLp_fst, WithLp.toLp_snd]
  have hx : |p.a + s.snd / p.lam + p.θ * s.fst - (p.a + s'.snd / p.lam + p.θ * s'.fst)|
      ≤ p.θ * |s.fst - s'.fst| + 1 / p.lam * |s.snd - s'.snd| := by
    calc _ = |p.θ * (s.fst - s'.fst) + (s.snd - s'.snd) / p.lam| := by ring_nf
      _ ≤ |p.θ * (s.fst - s'.fst)| + |(s.snd - s'.snd) / p.lam| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg hθ, abs_div, abs_of_pos hl]; ring
  have hη : |p.ρ * s.snd + p.lam * ε - (p.ρ * s'.snd + p.lam * ε)| = p.ρ * |s.snd - s'.snd| := by
    rw [show p.ρ * s.snd + p.lam * ε - (p.ρ * s'.snd + p.lam * ε) = p.ρ * (s.snd - s'.snd) by ring,
      abs_mul, abs_of_nonneg hρ]
  have h1 : p.θ ≤ p.factor := le_max_left _ _
  have h2 : p.ρ + 1 / p.lam ≤ p.factor := le_max_right _ _
  have ha := abs_nonneg (s.fst - s'.fst)
  have hb := abs_nonneg (s.snd - s'.snd)
  calc _ ≤ p.θ * |s.fst - s'.fst| + 1 / p.lam * |s.snd - s'.snd| + p.ρ * |s.snd - s'.snd| := by
        rw [hη]; linarith
    _ = p.θ * |s.fst - s'.fst| + (p.ρ + 1 / p.lam) * |s.snd - s'.snd| := by ring
    _ ≤ p.factor * |s.fst - s'.fst| + p.factor * |s.snd - s'.snd| := by gcongr
    _ = p.factor * (|s.fst - s'.fst| + |s.snd - s'.snd|) := by ring

theorem continuous_step : Continuous fun q : E × ℝ ↦ p.step q.1 q.2 := by
  unfold step
  exact (WithLp.prod_continuous_toLp 1 ℝ ℝ).comp (by fun_prop)

/-- The state space: the rectangle as a type. -/
abbrev State : Type := ↥p.rect

/-- The shock space: the support `[-ε̄, ε̄]` as a type. -/
abbrev Shock : Type := ↥(Icc (-p.εbar) p.εbar)

instance : CompactSpace p.State :=
  isCompact_iff_compactSpace.mp
    ((WithLp.homeomorphProd 1 ℝ ℝ).isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc))

instance : Nonempty p.State := by
  have h1 : 0 < 1 - p.θ := by linarith [p.hθ1]
  have hle : p.xlo ≤ p.xhi := by
    unfold xlo xhi
    apply div_le_div_of_nonneg_right _ h1.le
    have := div_nonneg p.ηbar_nonneg p.lam_pos.le
    linarith
  refine ⟨⟨WithLp.toLp 1 (p.xlo, 0), p.mem_rect.mpr ⟨⟨le_rfl, hle⟩, ?_⟩⟩⟩
  have := p.ηbar_nonneg
  simp only [WithLp.toLp_snd, mem_Icc]; constructor <;> linarith

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
theorem, with the contraction factor `α = max θ (ρ + 1/λ)`,

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
