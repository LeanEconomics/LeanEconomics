/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Econometrics.ApproxLikelihood
import LeanEconomics.Distribution.RandomMap

/-!
# Proposition 2′ from primitives

`ApproxLikelihood` proves Proposition 2′ (the corrected Proposition 2 of Fernández-Villaverde,
Rubio-Ramírez and Santos 2006) from three hypotheses: a per-period density error uniform in `t`,
a log-Lipschitz bound in the initial state, and a coupling of the two invariant distributions.
This file derives all three from primitives on the model.

## The coupling (`exists_coupling`)

Let the exact transition `φ` be a pathwise `α`-contraction and the computed transition `φj` be
within `δ` of it, both continuous in the state, on a compact metric state space. Drive the two
chains by a COMMON shock. The band `D = {(s, s') : dist s' s ≤ δ / (1 - α)}` is closed, hence
compact, and is invariant under the joint chain (`dist_step_le_of_le`). Krylov–Bogolyubov
(`RandomMap.exists_isInvariant`) applied to the joint chain on `D` gives an invariant probability
measure `cpl` on `D`. Its marginals are invariant for the exact and the computed chains, so if each
has a unique invariant distribution, the marginals are `μ*` and `μ*_j`. This `cpl` is the coupling.

## The densities, in the case with no `W₂` (`abs_log_likelihood_sub_le_of_primitives`)

When `dim V = dim Y` the measurement shock alone is recovered from the data, so the state path is
`s_{t+1} = φ (s_t, ω t)`, a function of the initial state and the shock path only, and the
conditional density of the `t`-th observation is `dens t (s_{t+1})` for a function `dens t` of
the current state (the density of `V` at `g⁻¹ (y_t; s)` times the Jacobian). Assume:

* `ξ ≤ dens t, densj t ≤ M` (FRS's Assumptions 4 and 8, and bounded densities);
* `|densj t s - dens t s| ≤ η` at every state (the static measurement error, no `t`-accumulation);
* `dens t` is `c`-Lipschitz in the state.

Then the per-period error is at most `η + c δ / (1 - α)` uniformly in `t`
(`abs_densPath_sub_le`), and the log density is Lipschitz in the initial state with constant
`(c α / ξ) αᵗ` (`densPath_le_exp_mul`), whose sum is bounded uniformly in `T`. The conclusion:

  `|log L_j - log L| ≤ T (η + c δ / (1 - α)) / ξ + (c α / ξ) δ / (1 - α)²`.

Measurability and integrability are derived, not assumed.
-/

open Finset MeasureTheory Real Function

namespace LeanEconomics

namespace ApproxLikelihood

variable {S W : Type*}

/-! ### The coupling of the invariant distributions -/

section Coupling

variable [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [MeasurableSpace W]

/-- The band of state pairs, exact first, computed second, within `ρ` of each other. -/
def band (S : Type*) [MetricSpace S] (ρ : ℝ) : Set (S × S) := {p | dist p.2 p.1 ≤ ρ}

omit [MeasurableSpace S] [BorelSpace S] in
theorem isClosed_band (ρ : ℝ) : IsClosed (band S ρ) :=
  isClosed_le (continuous_snd.dist continuous_fst) continuous_const

instance [CompactSpace S] (ρ : ℝ) : CompactSpace (band S ρ) :=
  isCompact_iff_compactSpace.mp (isClosed_band ρ).isCompact

variable (ν : Measure W) [IsProbabilityMeasure ν] {φ φj : S → W → S} {α δ : ℝ}

/-- The exact chain as a random map. -/
def exactChain (hφm : Measurable (uncurry φ)) (hφc : ∀ w, Continuous fun s ↦ φ s w) :
    RandomMap S W := ⟨ν, inferInstance, φ, hφm, hφc⟩

/-- The joint chain on the band, driven by a common shock. That it stays in the band is
`dist_step_le_of_le`. -/
def jointChain (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hφ : ∀ w s s', dist (φ s w) (φ s' w) ≤ α * dist s s')
    (hδ : ∀ s w, dist (φj s w) (φ s w) ≤ δ)
    (hφm : Measurable (uncurry φ)) (hφjm : Measurable (uncurry φj))
    (hφc : ∀ w, Continuous fun s ↦ φ s w) (hφjc : ∀ w, Continuous fun s ↦ φj s w) :
    RandomMap (band S (δ / (1 - α))) W where
  shock := ν
  isProbabilityMeasure_shock := inferInstance
  map x w := ⟨(φ x.1.1 w, φj x.1.2 w), dist_step_le_of_le hα0 hα1 hφ hδ w x.2⟩
  measurable_map := by
    refine Measurable.subtype_mk (Measurable.prodMk ?_ ?_)
    · exact hφm.comp ((measurable_fst.comp (measurable_subtype_coe.comp measurable_fst)).prodMk
        measurable_snd)
    · exact hφjm.comp ((measurable_snd.comp (measurable_subtype_coe.comp measurable_fst)).prodMk
        measurable_snd)
  continuous_map w := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact (hφc w).comp (continuous_fst.comp continuous_subtype_val)
    · exact (hφjc w).comp (continuous_snd.comp continuous_subtype_val)

omit [MetricSpace S] [BorelSpace S] in
/-- Pushing a coupling forward by the joint chain and then taking a marginal is the same as
taking the marginal and pushing it forward by that model's own chain. -/
theorem push_map_marginal {Y : Type*} [MeasurableSpace Y] (cpl : Measure Y)
    [IsProbabilityMeasure cpl]
    (G : Y → W → Y) (hG : Measurable (uncurry G)) (m : Y → S) (hm : Measurable m)
    (F : S → W → S) (hF : Measurable (uncurry F)) (hcomm : ∀ y w, m (G y w) = F (m y) w) :
    ((cpl.map m).prod ν).map (uncurry F) = ((cpl.prod ν).map (uncurry G)).map m := by
  rw [← Measure.map_id (μ := ν), Measure.map_prod_map cpl ν hm measurable_id, Measure.map_id,
    Measure.map_map hF (hm.prodMap measurable_id), Measure.map_map hm hG]
  congr 1
  funext y
  exact (hcomm y.1 y.2).symm

/-- **The coupling.** Under pathwise contraction of the exact transition, `δ`-closeness of the
computed one, continuity in the state, and uniqueness of each chain's invariant distribution,
there is a probability measure on the band `dist s' s ≤ δ / (1 - α)` whose marginals are the two
invariant distributions. -/
theorem exists_coupling [CompactSpace S] [Nonempty S] (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 ≤ δ)
    (hφ : ∀ w s s', dist (φ s w) (φ s' w) ≤ α * dist s s')
    (hδ : ∀ s w, dist (φj s w) (φ s w) ≤ δ)
    (hφm : Measurable (uncurry φ)) (hφjm : Measurable (uncurry φj))
    (hφc : ∀ w, Continuous fun s ↦ φ s w) (hφjc : ∀ w, Continuous fun s ↦ φj s w)
    (μs μjs : Measure S)
    (huniq : ∀ μ : Measure S, IsProbabilityMeasure μ →
      (μ.prod ν).map (uncurry φ) = μ → μ = μs)
    (huniqj : ∀ μ : Measure S, IsProbabilityMeasure μ →
      (μ.prod ν).map (uncurry φj) = μ → μ = μjs) :
    ∃ cpl : Measure (band S (δ / (1 - α))), IsProbabilityMeasure cpl ∧
      cpl.map (fun x ↦ x.1.1) = μs ∧ cpl.map (fun x ↦ x.1.2) = μjs := by
  have h1 : 0 < 1 - α := by linarith
  have : Nonempty (band S (δ / (1 - α))) := by
    obtain ⟨s⟩ := ‹Nonempty S›
    exact ⟨⟨(s, s), show dist s s ≤ δ / (1 - α) by rw [dist_self]; positivity⟩⟩
  set J := jointChain ν hα0 hα1 hφ hδ hφm hφjm hφc hφjc
  obtain ⟨cpl, hcpl, hinv⟩ := J.exists_isInvariant
  have hm1 : Measurable fun x : band S (δ / (1 - α)) ↦ x.1.1 :=
    measurable_fst.comp measurable_subtype_coe
  have hm2 : Measurable fun x : band S (δ / (1 - α)) ↦ x.1.2 :=
    measurable_snd.comp measurable_subtype_coe
  refine ⟨cpl, hcpl, huniq _ inferInstance ?_,
    huniqj _ inferInstance ?_⟩
  · rw [push_map_marginal ν cpl J.map J.measurable_map _ hm1 φ hφm (fun _ _ ↦ rfl)]
    exact congrArg (Measure.map fun x : band S (δ / (1 - α)) ↦ x.1.1) hinv
  · rw [push_map_marginal ν cpl J.map J.measurable_map _ hm2 φj hφjm (fun _ _ ↦ rfl)]
    exact congrArg (Measure.map fun x : band S (δ / (1 - α)) ↦ x.1.2) hinv

end Coupling

/-! ### The state path and the densities, with no `W₂` -/

section Primitives

variable [MetricSpace S]

/-- The state path from initial state `s` along the shock path `ω`. -/
def statePath (φ : S → W → S) (s : S) (ω : ℕ → W) : ℕ → S
  | 0 => s
  | n + 1 => φ (statePath φ s ω n) (ω n)

variable {φ φj : S → W → S} {α δ : ℝ}

theorem dist_statePath_le (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 ≤ δ)
    (hφ : ∀ w s s', dist (φ s w) (φ s' w) ≤ α * dist s s')
    (hδ : ∀ s w, dist (φj s w) (φ s w) ≤ δ) (s : S) (ω : ℕ → W) (n : ℕ) :
    dist (statePath φj s ω n) (statePath φ s ω n) ≤ δ / (1 - α) := by
  have := dist_iterate_le hα0 hα1 hδ0 hφ hδ ω (statePath φ s ω) (statePath φj s ω)
    (fun _ ↦ rfl) (fun _ ↦ rfl) n
  simpa [statePath] using this

theorem dist_statePath_exact_le (hα0 : 0 ≤ α)
    (hφ : ∀ w s s', dist (φ s w) (φ s' w) ≤ α * dist s s') (s s' : S) (ω : ℕ → W) (n : ℕ) :
    dist (statePath φ s ω n) (statePath φ s' ω n) ≤ α ^ n * dist s s' :=
  dist_iterate_exact_le hα0 hφ ω (statePath φ s ω) (statePath φ s' ω) (fun _ ↦ rfl)
    (fun _ ↦ rfl) n

omit [MetricSpace S] in
theorem measurable_statePath [MeasurableSpace S] [MeasurableSpace W] (hφm : Measurable (uncurry φ)) (n : ℕ) :
    Measurable fun z : S × (ℕ → W) ↦ statePath φ z.1 z.2 n := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih => exact hφm.comp (ih.prodMk ((measurable_pi_apply n).comp measurable_snd))

variable {T : ℕ} {dens densj : Fin T → S → ℝ} {ξ M η c : ℝ}

/-- The conditional density of the `t`-th observation: the density at the state `s_{t+1}`. -/
def densPath (φ : S → W → S) (dens : Fin T → S → ℝ) (t : Fin T) (s : S) (ω : ℕ → W) : ℝ :=
  dens t (statePath φ s ω (t + 1))

/-- **Lemma 6, uniformly in `t`.** -/
theorem abs_densPath_sub_le (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 ≤ δ)
    (hφ : ∀ w s s', dist (φ s w) (φ s' w) ≤ α * dist s s')
    (hδ : ∀ s w, dist (φj s w) (φ s w) ≤ δ)
    (hη : ∀ t s, |densj t s - dens t s| ≤ η) (hc : 0 ≤ c)
    (hlip : ∀ t s s', |dens t s - dens t s'| ≤ c * dist s s') (t : Fin T) (s : S) (ω : ℕ → W) :
    |densPath φj densj t s ω - densPath φ dens t s ω| ≤ η + c * (δ / (1 - α)) := by
  unfold densPath
  set x := statePath φ s ω (t + 1)
  set y := statePath φj s ω (t + 1)
  have hd : dist y x ≤ δ / (1 - α) := dist_statePath_le hα0 hα1 hδ0 hφ hδ s ω _
  calc |densj t y - dens t x| ≤ |densj t y - dens t y| + |dens t y - dens t x| :=
        abs_sub_le _ _ _
    _ ≤ η + c * dist y x := add_le_add (hη t y) (hlip t y x)
    _ ≤ η + c * (δ / (1 - α)) := by gcongr

/-- **Log-Lipschitz in the initial state, with geometric decay.** -/
theorem densPath_le_exp_mul (hα0 : 0 ≤ α) (hφ : ∀ w s s', dist (φ s w) (φ s' w) ≤ α * dist s s')
    (hξ : 0 < ξ) (hξd : ∀ t s, ξ ≤ dens t s) (hc : 0 ≤ c)
    (hlip : ∀ t s s', |dens t s - dens t s'| ≤ c * dist s s') (t : Fin T) (s s' : S)
    (ω : ℕ → W) :
    densPath φ dens t s' ω ≤ exp ((c * α / ξ) * α ^ (t : ℕ) * dist s s') *
      densPath φ dens t s ω := by
  unfold densPath
  have hd := dist_statePath_exact_le hα0 hφ s' s ω (t + 1)
  have h := le_exp_div_mul hξ (hξd t (statePath φ s ω (t + 1)))
    ((hlip t _ _).trans (mul_le_mul_of_nonneg_left hd hc))
  refine h.trans (mul_le_mul_of_nonneg_right (exp_le_exp.mpr (le_of_eq ?_))
    (hξ.le.trans (hξd _ _)))
  rw [dist_comm s' s, pow_succ]
  field_simp

end Primitives

/-! ### Proposition 2′ from primitives -/

section Assembled

variable [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S] [BorelSpace S]
  [MeasurableSpace W] {φ φj : S → W → S} {α δ : ℝ} {T : ℕ} {dens densj : Fin T → S → ℝ}
  {ξ M η c : ℝ}

omit [MetricSpace S] [CompactSpace S] [Nonempty S] [BorelSpace S] in
/-- The conditional likelihood is jointly measurable in the initial state and the shock path. -/
theorem measurable_condLik_densPath (hφm : Measurable (uncurry φ))
    (hdm : ∀ t, Measurable (dens t)) :
    Measurable fun z : S × (ℕ → W) ↦ condLik (densPath φ dens) z.1 z.2 :=
  Finset.measurable_prod _ fun t _ ↦ (hdm t).comp (measurable_statePath hφm _)

omit [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S] [BorelSpace S]
  [MeasurableSpace W] in
/-- Bounds on the conditional likelihood from bounds on the densities. -/
theorem condLik_mem_Icc {p : Fin T → S → (ℕ → W) → ℝ} (hξ : 0 < ξ) (hlo : ∀ t s ω, ξ ≤ p t s ω)
    (hhi : ∀ t s ω, p t s ω ≤ M) (s : S) (ω : ℕ → W) :
    0 ≤ condLik p s ω ∧ condLik p s ω ≤ M ^ T := by
  refine ⟨prod_nonneg fun t _ ↦ (hξ.trans_le (hlo t s ω)).le, ?_⟩
  calc condLik p s ω ≤ ∏ _t : Fin T, M :=
        prod_le_prod₀ (fun t _ ↦ (hξ.trans_le (hlo t s ω)).le) (fun t _ ↦ hhi t s ω)
    _ = M ^ T := by simp

omit [MetricSpace S] [CompactSpace S] [Nonempty S] [BorelSpace S] in
/-- Measurability and integrability of everything Proposition 2′ integrates. -/
theorem integrable_densPath (Q : Measure (ℕ → W)) [IsProbabilityMeasure Q]
    (hφm : Measurable (uncurry φ)) (hdm : ∀ t, Measurable (dens t)) (hξ : 0 < ξ)
    (hlo : ∀ t s, ξ ≤ dens t s) (hhi : ∀ t s, dens t s ≤ M) :
    (∀ s, Integrable (condLik (densPath φ dens) s) Q) ∧
      Measurable (initLik (densPath φ dens) Q) ∧
      ∀ s, 0 ≤ initLik (densPath φ dens) Q s ∧ initLik (densPath φ dens) Q s ≤ M ^ T := by
  have hj := measurable_condLik_densPath hφm hdm
  have hb := condLik_mem_Icc (p := densPath φ dens) hξ (fun t s ω ↦ hlo t _)
    (fun t s ω ↦ hhi t _)
  have hint : ∀ s, Integrable (condLik (densPath φ dens) s) Q := fun s ↦
    Integrable.of_bound (hj.comp measurable_prodMk_left).aestronglyMeasurable (M ^ T)
      (Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_of_nonneg (hb s ω).1]; exact (hb s ω).2)
  refine ⟨hint, hj.stronglyMeasurable.integral_prod_right'.measurable, fun s ↦ ⟨?_, ?_⟩⟩
  · exact integral_nonneg fun ω ↦ (hb s ω).1
  · calc initLik (densPath φ dens) Q s ≤ ∫ _ω, M ^ T ∂Q :=
          integral_mono (hint s) (integrable_const _) fun ω ↦ (hb s ω).2
      _ = M ^ T := by simp

/-- **Proposition 2′ from primitives** (the case with no `W₂`). Let the exact transition be a
pathwise `α`-contraction, the computed one within `δ` of it, both measurable and continuous in
the state on a compact metric state space, each chain with a unique invariant distribution
(`μs`, `μjs`). Let the per-state densities lie in `[ξ, M]`, differ by at most `η`, and the exact
ones be `c`-Lipschitz in the state. Then for every sample length `T` and every law `Q` of the
shock path,

  `|log L_j - log L| ≤ T (η + c δ / (1 - α)) / ξ + (c α / ξ) δ / (1 - α)²`,

where `L = ∫ ∫ ∏ₜ dens t (s_{t+1}) dQ dμs` and `L_j` is the same with the computed objects. -/
theorem abs_log_likelihood_sub_le_of_primitives (ν : Measure W) [IsProbabilityMeasure ν]
    (Q : Measure (ℕ → W)) [IsProbabilityMeasure Q]
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 ≤ δ)
    (hφ : ∀ w s s', dist (φ s w) (φ s' w) ≤ α * dist s s')
    (hδ : ∀ s w, dist (φj s w) (φ s w) ≤ δ)
    (hφm : Measurable (uncurry φ)) (hφjm : Measurable (uncurry φj))
    (hφc : ∀ w, Continuous fun s ↦ φ s w) (hφjc : ∀ w, Continuous fun s ↦ φj s w)
    (μs μjs : Measure S)
    (huniq : ∀ μ : Measure S, IsProbabilityMeasure μ →
      (μ.prod ν).map (uncurry φ) = μ → μ = μs)
    (huniqj : ∀ μ : Measure S, IsProbabilityMeasure μ →
      (μ.prod ν).map (uncurry φj) = μ → μ = μjs)
    (hξ : 0 < ξ) (hlo : ∀ t s, ξ ≤ dens t s) (hloj : ∀ t s, ξ ≤ densj t s)
    (hhi : ∀ t s, dens t s ≤ M) (hhij : ∀ t s, densj t s ≤ M)
    (hdm : ∀ t, Measurable (dens t)) (hdjm : ∀ t, Measurable (densj t))
    (hη : ∀ t s, |densj t s - dens t s| ≤ η) (hc : 0 ≤ c)
    (hlip : ∀ t s s', |dens t s - dens t s'| ≤ c * dist s s') :
    |log (∫ s, initLik (densPath φj densj) Q s ∂μjs)
        - log (∫ s, initLik (densPath φ dens) Q s ∂μs)|
      ≤ T * ((η + c * (δ / (1 - α))) / ξ) + (c * α / ξ) * δ / (1 - α) ^ 2 := by
  obtain ⟨cpl, hcpl, hμs, hμjs⟩ := exists_coupling ν hα0 hα1 hδ0 hφ hδ hφm hφjm hφc hφjc μs μjs
    huniq huniqj
  have ha : Measurable fun x : band S (δ / (1 - α)) ↦ x.1.1 :=
    measurable_fst.comp measurable_subtype_coe
  have hb : Measurable fun x : band S (δ / (1 - α)) ↦ x.1.2 :=
    measurable_snd.comp measurable_subtype_coe
  obtain ⟨hintQp, hmp, hbp⟩ := integrable_densPath Q hφm hdm hξ hlo hhi
  obtain ⟨hintQq, hmq, hbq⟩ := integrable_densPath Q hφjm hdjm hξ hloj hhij
  have hintPp : Integrable (fun x : band S (δ / (1 - α)) ↦ initLik (densPath φ dens) Q x.1.1)
      cpl :=
    Integrable.of_bound (hmp.comp ha).aestronglyMeasurable (M ^ T)
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (hbp _).1]; exact (hbp _).2)
  have hintPq : Integrable (fun x : band S (δ / (1 - α)) ↦ initLik (densPath φj densj) Q x.1.2)
      cpl :=
    Integrable.of_bound (hmq.comp hb).aestronglyMeasurable (M ^ T)
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (hbq _).1]; exact (hbq _).2)
  have hρ : ∀ᵐ x ∂cpl, dist (x : band S (δ / (1 - α))).1.1 x.1.2 ≤ δ / (1 - α) :=
    Filter.Eventually.of_forall fun x ↦ by rw [dist_comm]; exact x.2
  have h := abs_log_likelihood_sub_le_of_geometric (Q := Q) (P := cpl)
    (a := fun x ↦ x.1.1) (b := fun x ↦ x.1.2)
    (ℓ := fun t ↦ (c * α / ξ) * α ^ (t : ℕ)) (c := c * α / ξ)
    hξ (fun t s ω ↦ hlo t _) (fun t s ω ↦ hloj t _)
    (abs_densPath_sub_le hα0 hα1 hδ0 hφ hδ hη hc hlip)
    (fun t ↦ by positivity) (by positivity) hα0 hα1 hδ0 (fun t ↦ le_rfl)
    (densPath_le_exp_mul hα0 hφ hξ hlo hc hlip) hρ hintQp hintQq hintPp hintPq
  rw [← hμs, ← hμjs, integral_map ha.aemeasurable hmp.aestronglyMeasurable,
    integral_map hb.aemeasurable hmq.aestronglyMeasurable]
  exact h

end Assembled

end ApproxLikelihood

end LeanEconomics
