/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The likelihood of a computed dynamic model: a corrected Proposition 2

Fernández-Villaverde, Rubio-Ramírez and Santos (2006, *Econometrica* 74, 93–119; FRS) state, as
their Proposition 2, that if the computed transition and measurement equations are within `δ` of
the exact ones in the sup norm, then the LEVELS of the likelihoods satisfy

  `|L_j(yᵀ) - L(yᵀ)| < (T B χ + L / (1 - α)) δ`

with `B`, `χ`, `L` independent of `T`. Ackerberg, Geweke and Hahn (2009, *Econometrica* 77,
2009–2017) show by a Gaussian counterexample that this is false.

The faulty step is (14) of FRS's appendix, which bounds a difference of two `T`-fold products of
conditional densities by `T B χ δ`. The telescoping identity puts `T - 1` density factors beside
each `χ δ`, so `B` is really `M ^ (T - 1)` with `M` the sup of the density: exponential in `T`.
`not_exists_linear_bound_prod_sub` below makes this precise.

## The rescue

The `T δ` accumulation FRS were after is TRUE for the log likelihood (equivalently the likelihood
RATIO), not for the level. If every conditional density is bounded below by `ξ > 0` (FRS's
Assumptions 4 and 8) and the per-period error is `ε = χ δ`, then each factor moves by at most a
factor `exp (ε / ξ)`, so a product of `T` factors moves by at most `exp (T ε / ξ)`. The only other
source of error is the invariant distribution of the initial state. Coupling the exact and
computed chains through common shocks keeps them within `ρ = δ / (1 - α)` of each other when the
transition is a PATHWISE `α`-contraction, and the log likelihood is `K`-Lipschitz in the initial
state, so this costs a further factor `exp (K ρ)`.

`likelihood_le_exp_mul` and `abs_log_likelihood_sub_le` are Proposition 2′:

  `|log L_j(yᵀ) - log L(yᵀ)| ≤ T ε / ξ + K ρ`,

the same shape as FRS's bound, now for the log. `abs_log_likelihood_sub_le_of_geometric` is the
form in which `K` is bounded uniformly in `T`, which is what pathwise contraction delivers when
the per-period Lipschitz constants decay like `c αᵗ`.

The bound is sharp in its dependence on `T` (`log_prod_div_prod_const`): with every exact density
equal to `M` and every computed one equal to `M + ε`, the log likelihood ratio is exactly
`T log (1 + ε / M)`.

## The hypotheses

The theorems here take three hypotheses: the per-period density error `|q t - p t| ≤ ε`
uniformly in `t` (FRS's Lemma 6, which FRS justify only by "the model is stationary"), a
log-Lipschitz bound in the initial state for the EXACT densities (none is needed for the computed
ones), and a coupling of the two invariant distributions, supplied as a measure `P` on a space
`X` with maps `a b : X → S` and `dist (a x) (b x) ≤ ρ` `P`-almost everywhere.
`ApproxLikelihoodModel` derives all three from primitives: the coupling by Krylov–Bogolyubov
for the joint chain on the band `dist ≤ δ / (1 - α)`, and the other two in the case where the
measurement shock alone is recovered from the data.
-/

open Finset MeasureTheory Real

namespace LeanEconomics

namespace ApproxLikelihood

/-! ### Multiplicative perturbations of a finite product -/

/-- An additive error `ε` in a factor bounded below by `ξ` is a multiplicative error of at most
`exp (ε / ξ)`. -/
theorem le_exp_div_mul {p q ξ ε : ℝ} (hξ : 0 < ξ) (hp : ξ ≤ p) (h : |q - p| ≤ ε) :
    q ≤ exp (ε / ξ) * p := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans h
  have hp0 : 0 < p := hξ.trans_le hp
  have h1 : q ≤ p + ε := by linarith [le_abs_self (q - p)]
  have h2 : ε ≤ ε / ξ * p := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hξ]
    exact mul_le_mul_of_nonneg_left hp hε
  have h3 : 1 + ε / ξ ≤ exp (ε / ξ) := by linarith [add_one_le_exp (ε / ξ)]
  calc q ≤ p + ε / ξ * p := by linarith
    _ = (1 + ε / ξ) * p := by ring
    _ ≤ exp (ε / ξ) * p := mul_le_mul_of_nonneg_right h3 hp0.le

/-- Factorwise multiplicative bounds `q t ≤ exp (c t) * p t` multiply up to
`∏ q ≤ exp (∑ c) * ∏ p`. -/
theorem prod_le_exp_sum_mul_prod {ι : Type*} (s : Finset ι) {p q c : ι → ℝ}
    (hq : ∀ t ∈ s, 0 ≤ q t) (h : ∀ t ∈ s, q t ≤ exp (c t) * p t) :
    ∏ t ∈ s, q t ≤ exp (∑ t ∈ s, c t) * ∏ t ∈ s, p t := by
  calc ∏ t ∈ s, q t ≤ ∏ t ∈ s, (exp (c t) * p t) := prod_le_prod hq h
    _ = exp (∑ t ∈ s, c t) * ∏ t ∈ s, p t := by rw [prod_mul_distrib, exp_sum]

/-- **The corrected step (14).** If every factor is bounded below by `ξ > 0` and the per-factor
error is at most `ε`, the product of `T = card s` factors moves by at most a factor
`exp (T ε / ξ)`. -/
theorem prod_le_exp_card_mul_prod {ι : Type*} (s : Finset ι) {p q : ι → ℝ} {ξ ε : ℝ}
    (hξ : 0 < ξ) (hp : ∀ t ∈ s, ξ ≤ p t) (hq : ∀ t ∈ s, 0 ≤ q t)
    (h : ∀ t ∈ s, |q t - p t| ≤ ε) :
    ∏ t ∈ s, q t ≤ exp (s.card * (ε / ξ)) * ∏ t ∈ s, p t := by
  have := prod_le_exp_sum_mul_prod s (c := fun _ ↦ ε / ξ) hq
    (fun t ht ↦ le_exp_div_mul hξ (hp t ht) (h t ht))
  simpa [sum_const, nsmul_eq_mul] using this

/-! ### Why FRS's step (14) fails -/

/-- **The gap in FRS's Proposition 2.** With every exact density equal to a constant `M > 1` and
every computed density equal to `M + ε`, no constant `B` independent of `T` gives
`|∏ q - ∏ p| ≤ T B ε` for all `T`: the left side is at least `T ε M ^ (T - 1)`. -/
theorem not_exists_linear_bound_prod_sub {M ε : ℝ} (hM : 1 < M) (hε : 0 < ε) :
    ¬ ∃ B : ℝ, ∀ T : ℕ, |(M + ε) ^ T - M ^ T| ≤ T * B * ε := by
  rintro ⟨B, hB⟩
  have hM0 : 0 < M := one_pos.trans hM
  -- `M ^ (n + 1) ≤ B` for every `n`, which the growth of `M ^ n` contradicts
  have key : ∀ n : ℕ, M ^ n ≤ B := by
    intro n
    have h := hB (n + 1)
    have hbern : 1 + (n + 1 : ℕ) * (ε / M) ≤ (1 + ε / M) ^ (n + 1) :=
      one_add_mul_le_pow (by have := div_pos hε hM0; linarith) _
    have hfac : (M + ε) ^ (n + 1) = M ^ (n + 1) * (1 + ε / M) ^ (n + 1) := by
      rw [← mul_pow]; congr 1; field_simp
    have hlow : ((n + 1 : ℕ) : ℝ) * ε * M ^ n ≤ (M + ε) ^ (n + 1) - M ^ (n + 1) := by
      rw [hfac]
      have hMn : 0 ≤ M ^ (n + 1) := by positivity
      have := mul_le_mul_of_nonneg_left hbern hMn
      have e : M ^ (n + 1) * (((n + 1 : ℕ) : ℝ) * (ε / M)) = ((n + 1 : ℕ) : ℝ) * ε * M ^ n := by
        rw [pow_succ]; field_simp
      nlinarith [this, e]
    have hpos : 0 ≤ (M + ε) ^ (n + 1) - M ^ (n + 1) := by
      have : M ^ (n + 1) ≤ (M + ε) ^ (n + 1) :=
        pow_le_pow_left₀ hM0.le (by linarith) _
      linarith
    rw [abs_of_nonneg hpos] at h
    have hc : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * ε := by positivity
    have : ((n + 1 : ℕ) : ℝ) * ε * M ^ n ≤ ((n + 1 : ℕ) : ℝ) * ε * B := by
      calc _ ≤ _ := hlow
        _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hc
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hM
  exact (key n).not_gt hn

/-- **Sharpness in `T` of the corrected bound.** With every exact density `M > 0` and every
computed density `M + ε`, the log likelihood ratio is exactly `T log (1 + ε / M)`: linear in `T`. -/
theorem log_prod_div_prod_const {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (T : ℕ) :
    log ((M + ε) ^ T / M ^ T) = T * log (1 + ε / M) := by
  rw [← div_pow, log_pow]
  congr 2
  field_simp

/-! ### Coupled chains driven by common shocks -/

section Coupling

variable {S W : Type*} [PseudoMetricSpace S] {φ φj : S → W → S} {α δ : ℝ}

/-- One step of the coupled chain: if the exact transition is a pathwise `α`-contraction and the
computed transition is within `δ` of it, the distance between the two states contracts by `α`
up to an additive `δ`. -/
theorem dist_step_le (hφ : ∀ w s s', dist (φ s w) (φ s' w) ≤ α * dist s s')
    (hδ : ∀ s w, dist (φj s w) (φ s w) ≤ δ) (s s' : S) (w : W) :
    dist (φj s' w) (φ s w) ≤ α * dist s' s + δ := by
  calc dist (φj s' w) (φ s w) ≤ dist (φj s' w) (φ s' w) + dist (φ s' w) (φ s w) :=
        dist_triangle _ _ _
    _ ≤ δ + α * dist s' s := add_le_add (hδ s' w) (hφ w s' s)
    _ = α * dist s' s + δ := by ring

/-- The band `dist ≤ δ / (1 - α)` is invariant under the coupled chain. -/
theorem dist_step_le_of_le (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hφ : ∀ w s s', dist (φ s w) (φ s' w) ≤ α * dist s s')
    (hδ : ∀ s w, dist (φj s w) (φ s w) ≤ δ) {s s' : S} (w : W)
    (h : dist s' s ≤ δ / (1 - α)) : dist (φj s' w) (φ s w) ≤ δ / (1 - α) := by
  have h1 : 0 < 1 - α := by linarith
  calc dist (φj s' w) (φ s w) ≤ α * dist s' s + δ := dist_step_le hφ hδ s s' w
    _ ≤ α * (δ / (1 - α)) + δ := by gcongr
    _ = δ / (1 - α) := by field_simp; ring

/-- Along any common shock path, the exact and computed state paths satisfy
`dist ≤ αᵗ · dist₀ + δ / (1 - α)`: the initial gap is forgotten geometrically and the band
`δ / (1 - α)` is what remains. -/
theorem dist_iterate_le (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 ≤ δ)
    (hφ : ∀ w s s', dist (φ s w) (φ s' w) ≤ α * dist s s')
    (hδ : ∀ s w, dist (φj s w) (φ s w) ≤ δ) (w : ℕ → W) (x y : ℕ → S)
    (hx : ∀ t, x (t + 1) = φ (x t) (w t)) (hy : ∀ t, y (t + 1) = φj (y t) (w t)) (t : ℕ) :
    dist (y t) (x t) ≤ α ^ t * dist (y 0) (x 0) + δ / (1 - α) := by
  have h1 : 0 < 1 - α := by linarith
  induction t with
  | zero =>
    have : 0 ≤ δ / (1 - α) := div_nonneg hδ0 h1.le
    simp only [pow_zero, one_mul]; linarith
  | succ t ih =>
    rw [hx, hy]
    calc dist (φj (y t) (w t)) (φ (x t) (w t)) ≤ α * dist (y t) (x t) + δ :=
          dist_step_le hφ hδ _ _ _
      _ ≤ α * (α ^ t * dist (y 0) (x 0) + δ / (1 - α)) + δ := by gcongr
      _ = α ^ (t + 1) * dist (y 0) (x 0) + δ / (1 - α) := by field_simp; ring

/-- The exact chain forgets its initial state geometrically along any common shock path; this is
what makes the per-period Lipschitz constants `ℓ t` of the log density in `S₀` decay like `αᵗ`. -/
theorem dist_iterate_exact_le (hα0 : 0 ≤ α)
    (hφ : ∀ w s s', dist (φ s w) (φ s' w) ≤ α * dist s s') (w : ℕ → W) (x x' : ℕ → S)
    (hx : ∀ t, x (t + 1) = φ (x t) (w t)) (hx' : ∀ t, x' (t + 1) = φ (x' t) (w t)) (t : ℕ) :
    dist (x t) (x' t) ≤ α ^ t * dist (x 0) (x' 0) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hx, hx', pow_succ]
    calc dist (φ (x t) (w t)) (φ (x' t) (w t)) ≤ α * dist (x t) (x' t) := hφ _ _ _
      _ ≤ α * (α ^ t * dist (x 0) (x' 0)) := by gcongr
      _ = α ^ t * α * dist (x 0) (x' 0) := by ring

end Coupling

/-! ### The likelihood -/

section Likelihood

variable {ι S Ω X : Type*} [Fintype ι] [PseudoMetricSpace S] [MeasurableSpace Ω]
  [MeasurableSpace X]

/-- The likelihood of the sample conditional on the initial state `s` and the unobserved shock
path `ω`: the product over periods of the conditional densities `p t s ω`. -/
def condLik (p : ι → S → Ω → ℝ) (s : S) (ω : Ω) : ℝ := ∏ t, p t s ω

/-- The likelihood conditional on the initial state, integrating out the unobserved shock path. -/
noncomputable def initLik (p : ι → S → Ω → ℝ) (Q : Measure Ω) (s : S) : ℝ :=
  ∫ ω, condLik p s ω ∂Q

/-- The likelihood: `initLik` integrated against the distribution of the initial state, which is
the law of `a` under `P`. With `P` a coupling and `a = Prod.fst`, this is integration against the
first marginal, FRS's invariant distribution `μ*`. -/
noncomputable def lik (p : ι → S → Ω → ℝ) (Q : Measure Ω) (P : Measure X) (a : X → S) : ℝ :=
  ∫ x, initLik p Q (a x) ∂P

variable {p q : ι → S → Ω → ℝ} {Q : Measure Ω} {P : Measure X} {a b : X → S}
  {ξ ε ρ : ℝ} {ℓ : ι → ℝ}

/-- One direction of Proposition 2′, with the roles of the two models abstract: the model `q`,
whose initial state is `b`, has likelihood at most `exp (T ε / ξ + K ρ)` times that of the model
`p`, whose initial state is `a`, where `K = ∑ ℓ`. Needs the lower bound `ξ` and the log-Lipschitz
bound only on `p`, and integrability only of `p`'s likelihood. -/
theorem lik_le_exp_mul_lik (hξ : 0 < ξ) (hp : ∀ t s ω, ξ ≤ p t s ω) (hq : ∀ t s ω, 0 ≤ q t s ω)
    (hpq : ∀ t s ω, |q t s ω - p t s ω| ≤ ε) (hℓ : ∀ t, 0 ≤ ℓ t)
    (hlip : ∀ t s s' ω, p t s' ω ≤ exp (ℓ t * dist s s') * p t s ω)
    (hρ : ∀ᵐ x ∂P, dist (a x) (b x) ≤ ρ)
    (hintQ : ∀ s, Integrable (condLik p s) Q)
    (hintP : Integrable (fun x ↦ initLik p Q (a x)) P) :
    lik q Q P b ≤ exp (Fintype.card ι * (ε / ξ) + (∑ t, ℓ t) * ρ) * lik p Q P a := by
  set C := Fintype.card ι * (ε / ξ)
  -- pointwise in `(s, s', ω)`: `condLik q s' ω ≤ exp (C + K dist s s') * condLik p s ω`
  have hcond : ∀ s s' ω, condLik q s' ω ≤ exp (C + (∑ t, ℓ t) * dist s s') * condLik p s ω := by
    intro s s' ω
    have h1 : condLik q s' ω ≤ exp C * condLik p s' ω :=
      prod_le_exp_card_mul_prod univ hξ (fun t _ ↦ hp t s' ω) (fun t _ ↦ hq t s' ω)
        (fun t _ ↦ hpq t s' ω)
    have h2 : condLik p s' ω ≤ exp (∑ t, ℓ t * dist s s') * condLik p s ω :=
      prod_le_exp_sum_mul_prod univ (fun t _ ↦ (hξ.trans_le (hp t s' ω)).le)
        (fun t _ ↦ hlip t s s' ω)
    rw [← sum_mul] at h2
    calc condLik q s' ω ≤ exp C * condLik p s' ω := h1
      _ ≤ exp C * (exp ((∑ t, ℓ t) * dist s s') * condLik p s ω) := by gcongr
      _ = exp (C + (∑ t, ℓ t) * dist s s') * condLik p s ω := by rw [exp_add]; ring
  have hcondq_nonneg : ∀ s ω, 0 ≤ condLik q s ω := fun s ω ↦ prod_nonneg fun t _ ↦ hq t s ω
  have hcondp_nonneg : ∀ s ω, 0 ≤ condLik p s ω :=
    fun s ω ↦ prod_nonneg fun t _ ↦ (hξ.trans_le (hp t s ω)).le
  -- integrate out the shock path
  have hinit : ∀ s s', initLik q Q s' ≤ exp (C + (∑ t, ℓ t) * dist s s') * initLik p Q s := by
    intro s s'
    unfold initLik
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall (hcondq_nonneg s'))
      ((hintQ s).const_mul _) (Filter.Eventually.of_forall (hcond s s'))
  have hinitp_nonneg : ∀ s, 0 ≤ initLik p Q s :=
    fun s ↦ integral_nonneg (hcondp_nonneg s)
  have hK : 0 ≤ ∑ t, ℓ t := sum_nonneg fun t _ ↦ hℓ t
  -- the coupling: `P`-a.e. the two initial states are within `ρ`
  have hae : ∀ᵐ x ∂P, initLik q Q (b x) ≤ exp (C + (∑ t, ℓ t) * ρ) * initLik p Q (a x) := by
    filter_upwards [hρ] with x hx
    calc initLik q Q (b x) ≤ exp (C + (∑ t, ℓ t) * dist (a x) (b x)) * initLik p Q (a x) :=
          hinit _ _
      _ ≤ exp (C + (∑ t, ℓ t) * ρ) * initLik p Q (a x) := by
          gcongr
          · exact hinitp_nonneg _
  unfold lik
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x ↦ integral_nonneg (hcondq_nonneg (b x)))
    (hintP.const_mul _) hae

/-- The other direction of Proposition 2′. The order of the two moves is reversed: first move the
initial state within the EXACT model (so the log-Lipschitz bound is needed only for `p`), then
switch to the computed model at the computed initial state. Needs the lower bound `ξ` on `q`
and integrability of `q`'s likelihood. -/
theorem lik_le_exp_mul_lik_rev (hξ : 0 < ξ) (hq : ∀ t s ω, ξ ≤ q t s ω)
    (hp : ∀ t s ω, 0 ≤ p t s ω) (hpq : ∀ t s ω, |q t s ω - p t s ω| ≤ ε) (hℓ : ∀ t, 0 ≤ ℓ t)
    (hlip : ∀ t s s' ω, p t s' ω ≤ exp (ℓ t * dist s s') * p t s ω)
    (hρ : ∀ᵐ x ∂P, dist (a x) (b x) ≤ ρ)
    (hintQ : ∀ s, Integrable (condLik q s) Q)
    (hintP : Integrable (fun x ↦ initLik q Q (b x)) P) :
    lik p Q P a ≤ exp (Fintype.card ι * (ε / ξ) + (∑ t, ℓ t) * ρ) * lik q Q P b := by
  set C := Fintype.card ι * (ε / ξ)
  have hcond : ∀ s s' ω, condLik p s ω ≤ exp (C + (∑ t, ℓ t) * dist s' s) * condLik q s' ω := by
    intro s s' ω
    have h1 : condLik p s ω ≤ exp (∑ t, ℓ t * dist s' s) * condLik p s' ω :=
      prod_le_exp_sum_mul_prod univ (fun t _ ↦ hp t s ω) (fun t _ ↦ hlip t s' s ω)
    rw [← sum_mul] at h1
    have h2 : condLik p s' ω ≤ exp C * condLik q s' ω :=
      prod_le_exp_card_mul_prod univ hξ (fun t _ ↦ hq t s' ω) (fun t _ ↦ hp t s' ω)
        (fun t _ ↦ by rw [abs_sub_comm]; exact hpq t s' ω)
    calc condLik p s ω ≤ exp ((∑ t, ℓ t) * dist s' s) * condLik p s' ω := h1
      _ ≤ exp ((∑ t, ℓ t) * dist s' s) * (exp C * condLik q s' ω) := by gcongr
      _ = exp (C + (∑ t, ℓ t) * dist s' s) * condLik q s' ω := by rw [exp_add]; ring
  have hcondp_nonneg : ∀ s ω, 0 ≤ condLik p s ω := fun s ω ↦ prod_nonneg fun t _ ↦ hp t s ω
  have hcondq_nonneg : ∀ s ω, 0 ≤ condLik q s ω :=
    fun s ω ↦ prod_nonneg fun t _ ↦ (hξ.trans_le (hq t s ω)).le
  have hinit : ∀ s s', initLik p Q s ≤ exp (C + (∑ t, ℓ t) * dist s' s) * initLik q Q s' := by
    intro s s'
    unfold initLik
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall (hcondp_nonneg s))
      ((hintQ s').const_mul _) (Filter.Eventually.of_forall (hcond s s'))
  have hinitq_nonneg : ∀ s, 0 ≤ initLik q Q s := fun s ↦ integral_nonneg (hcondq_nonneg s)
  have hK : 0 ≤ ∑ t, ℓ t := sum_nonneg fun t _ ↦ hℓ t
  have hae : ∀ᵐ x ∂P, initLik p Q (a x) ≤ exp (C + (∑ t, ℓ t) * ρ) * initLik q Q (b x) := by
    filter_upwards [hρ] with x hx
    calc initLik p Q (a x) ≤ exp (C + (∑ t, ℓ t) * dist (b x) (a x)) * initLik q Q (b x) :=
          hinit _ _
      _ ≤ exp (C + (∑ t, ℓ t) * ρ) * initLik q Q (b x) := by
          gcongr
          · exact hinitq_nonneg _
          · rw [dist_comm]; exact hx
  unfold lik
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x ↦ integral_nonneg (hcondp_nonneg (a x)))
    (hintP.const_mul _) hae

omit [PseudoMetricSpace S] in
/-- With probability measures, the likelihood is at least `ξ ^ T`, so in particular positive. -/
theorem pow_le_lik [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hξ : 0 < ξ)
    (hp : ∀ t s ω, ξ ≤ p t s ω) (hintQ : ∀ s, Integrable (condLik p s) Q)
    (hintP : Integrable (fun x ↦ initLik p Q (a x)) P) :
    ξ ^ Fintype.card ι ≤ lik p Q P a := by
  have hcond : ∀ s ω, ξ ^ Fintype.card ι ≤ condLik p s ω := by
    intro s ω
    rw [← card_univ, ← prod_const]
    exact prod_le_prod (fun _ _ ↦ hξ.le) (fun t _ ↦ hp t s ω)
  have hinit : ∀ s, ξ ^ Fintype.card ι ≤ initLik p Q s := by
    intro s
    have := integral_mono (integrable_const (ξ ^ Fintype.card ι)) (hintQ s) (hcond s)
    simpa [initLik] using this
  have := integral_mono (integrable_const (ξ ^ Fintype.card ι)) hintP (fun x ↦ hinit (a x))
  simpa [lik] using this

/-- **Proposition 2′ (corrected FRS Proposition 2), two-sided multiplicative form.** Let `p` be
the exact and `q` the computed conditional densities, both bounded below by `ξ > 0` and within
`ε` of each other (`ε = χ δ` in FRS's notation), the EXACT densities with log-Lipschitz
constants `ℓ t` in the initial state (nothing of the kind is needed of the computed ones), and let `P` couple the exact initial state `a` with the computed one `b` within
`ρ` (`ρ = δ / (1 - α)` under pathwise contraction). Then with `T = card ι` and `K = ∑ ℓ`,

  `L_j ≤ exp (T ε / ξ + K ρ) · L`   and   `L ≤ exp (T ε / ξ + K ρ) · L_j`. -/
theorem likelihood_le_exp_mul (hξ : 0 < ξ) (hp : ∀ t s ω, ξ ≤ p t s ω)
    (hq : ∀ t s ω, ξ ≤ q t s ω) (hpq : ∀ t s ω, |q t s ω - p t s ω| ≤ ε) (hℓ : ∀ t, 0 ≤ ℓ t)
    (hlipp : ∀ t s s' ω, p t s' ω ≤ exp (ℓ t * dist s s') * p t s ω)
    (hρ : ∀ᵐ x ∂P, dist (a x) (b x) ≤ ρ)
    (hintQp : ∀ s, Integrable (condLik p s) Q) (hintQq : ∀ s, Integrable (condLik q s) Q)
    (hintPp : Integrable (fun x ↦ initLik p Q (a x)) P)
    (hintPq : Integrable (fun x ↦ initLik q Q (b x)) P) :
    lik q Q P b ≤ exp (Fintype.card ι * (ε / ξ) + (∑ t, ℓ t) * ρ) * lik p Q P a ∧
      lik p Q P a ≤ exp (Fintype.card ι * (ε / ξ) + (∑ t, ℓ t) * ρ) * lik q Q P b := by
  exact ⟨lik_le_exp_mul_lik hξ hp (fun t s ω ↦ (hξ.trans_le (hq t s ω)).le) hpq hℓ hlipp hρ
    hintQp hintPp, lik_le_exp_mul_lik_rev hξ hq (fun t s ω ↦ (hξ.trans_le (hp t s ω)).le) hpq hℓ
    hlipp hρ hintQq hintPq⟩

/-- **Proposition 2′, log form.** Under probability measures,

  `|log L_j(yᵀ) - log L(yᵀ)| ≤ T ε / ξ + K ρ`:

FRS's `T`-linear accumulation of approximation error, holding for the log likelihood. -/
theorem abs_log_likelihood_sub_le [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (hξ : 0 < ξ) (hp : ∀ t s ω, ξ ≤ p t s ω)
    (hq : ∀ t s ω, ξ ≤ q t s ω) (hpq : ∀ t s ω, |q t s ω - p t s ω| ≤ ε) (hℓ : ∀ t, 0 ≤ ℓ t)
    (hlipp : ∀ t s s' ω, p t s' ω ≤ exp (ℓ t * dist s s') * p t s ω)
    (hρ : ∀ᵐ x ∂P, dist (a x) (b x) ≤ ρ)
    (hintQp : ∀ s, Integrable (condLik p s) Q) (hintQq : ∀ s, Integrable (condLik q s) Q)
    (hintPp : Integrable (fun x ↦ initLik p Q (a x)) P)
    (hintPq : Integrable (fun x ↦ initLik q Q (b x)) P) :
    |log (lik q Q P b) - log (lik p Q P a)| ≤ Fintype.card ι * (ε / ξ) + (∑ t, ℓ t) * ρ := by
  obtain ⟨h1, h2⟩ := likelihood_le_exp_mul hξ hp hq hpq hℓ hlipp hρ hintQp hintQq
    hintPp hintPq
  have hL : 0 < lik p Q P a := (pow_pos hξ _).trans_le (pow_le_lik hξ hp hintQp hintPp)
  have hLj : 0 < lik q Q P b := (pow_pos hξ _).trans_le (pow_le_lik hξ hq hintQq hintPq)
  set D := Fintype.card ι * (ε / ξ) + (∑ t, ℓ t) * ρ
  have l1 : log (lik q Q P b) ≤ D + log (lik p Q P a) := by
    have := log_le_log hLj h1
    rwa [log_mul (exp_pos D).ne' hL.ne', log_exp] at this
  have l2 : log (lik p Q P a) ≤ D + log (lik q Q P b) := by
    have := log_le_log hL h2
    rwa [log_mul (exp_pos D).ne' hLj.ne', log_exp] at this
  rw [abs_le]; constructor <;> linarith

/-- A geometric bound on the per-period Lipschitz constants bounds their sum uniformly in the
sample length. -/
theorem sum_le_of_geometric {T : ℕ} {ℓ : Fin T → ℝ} {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (h : ∀ t, ℓ t ≤ c * α ^ (t : ℕ)) : ∑ t, ℓ t ≤ c / (1 - α) := by
  have h1 : 0 < 1 - α := by linarith
  calc ∑ t, ℓ t ≤ ∑ t : Fin T, c * α ^ (t : ℕ) := sum_le_sum fun t _ ↦ h t
    _ = c * ∑ t ∈ range T, α ^ t := by rw [← mul_sum, Fin.sum_univ_eq_sum_range (α ^ ·)]
    _ ≤ c * (1 / (1 - α)) := by
        gcongr
        rw [geom_sum_eq (by linarith : α ≠ 1),
          show (α ^ T - 1) / (α - 1) = (1 - α ^ T) / (1 - α) by
            rw [← neg_div_neg_eq, neg_sub, neg_sub]]
        exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hα0 T]) h1.le
    _ = c / (1 - α) := by ring

/-- **Proposition 2′ with constants uniform in `T`.** If the exact transition is a pathwise
`α`-contraction, the coupling band is `ρ = δ / (1 - α)`, and the per-period log-Lipschitz
constants decay like `c αᵗ` (as `dist_iterate_exact_le` gives), then for every sample length `T`

  `|log L_j(yᵀ) - log L(yᵀ)| ≤ T ε / ξ + c δ / (1 - α)²`,

so the average log likelihood error is at most `ε / ξ + c δ / (T (1 - α)²)`, independent of `T`
in the limit. -/
theorem abs_log_likelihood_sub_le_of_geometric {T : ℕ} {p q : Fin T → S → Ω → ℝ}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P] {ℓ : Fin T → ℝ} {c α δ : ℝ}
    (hξ : 0 < ξ) (hp : ∀ t s ω, ξ ≤ p t s ω)
    (hq : ∀ t s ω, ξ ≤ q t s ω) (hpq : ∀ t s ω, |q t s ω - p t s ω| ≤ ε) (hℓ : ∀ t, 0 ≤ ℓ t)
    (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ : 0 ≤ δ)
    (hgeom : ∀ t, ℓ t ≤ c * α ^ (t : ℕ))
    (hlipp : ∀ t s s' ω, p t s' ω ≤ exp (ℓ t * dist s s') * p t s ω)
    (hρ : ∀ᵐ x ∂P, dist (a x) (b x) ≤ δ / (1 - α))
    (hintQp : ∀ s, Integrable (condLik p s) Q) (hintQq : ∀ s, Integrable (condLik q s) Q)
    (hintPp : Integrable (fun x ↦ initLik p Q (a x)) P)
    (hintPq : Integrable (fun x ↦ initLik q Q (b x)) P) :
    |log (lik q Q P b) - log (lik p Q P a)| ≤ T * (ε / ξ) + c * δ / (1 - α) ^ 2 := by
  have h := abs_log_likelihood_sub_le hξ hp hq hpq hℓ hlipp hρ hintQp hintQq hintPp hintPq
  have hK := sum_le_of_geometric hc hα0 hα1 hgeom
  have h1 : 0 < 1 - α := by linarith
  have hρ0 : 0 ≤ δ / (1 - α) := div_nonneg hδ h1.le
  rw [Fintype.card_fin] at h
  calc _ ≤ _ := h
    _ ≤ T * (ε / ξ) + c / (1 - α) * (δ / (1 - α)) := by gcongr
    _ = T * (ε / ξ) + c * δ / (1 - α) ^ 2 := by field_simp

end Likelihood

end ApproxLikelihood

end LeanEconomics
