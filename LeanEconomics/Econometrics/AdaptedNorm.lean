/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# An adapted norm from the spectral radius

`local_contraction` (in `LocalContraction`) assumes a norm in which the state Jacobian `A` at the
steady state has operator norm below `α < 1`. This file proves such a norm exists whenever the
spectral radius of `A` is below `α`, the result usually cited from Horn and Johnson (2013,
Lemma 5.6.10).

* **Gelfand** (`tendsto_norm_pow_rpow`, `exists_norm_pow_le`): for the ℓ∞ operator norm,
  `‖Aᵏ‖^{1/k} → ρ(A)`, so for every `γ > ρ(A)` there is `C` with `‖Aᵏ‖ ≤ C γᵏ` for all `k`. The
  Gelfand part is adapted from the `DynamicProgramming` repository (`RelativeValueIteration`).
* **The adapted norm** (`adaptedNorm`, `exists_adapted_norm`):
  `‖x‖_* = sup_k ‖Aᵏ x‖ / γᵏ`. It is a norm (subadditive, absolutely homogeneous), equivalent to the
  sup norm (`‖x‖ ≤ ‖x‖_* ≤ C ‖x‖`), and `‖A x‖_* ≤ γ ‖x‖_*`: in it `A` has operator norm at
  most `γ`.
-/

open Filter Topology Matrix Finset

namespace LeanEconomics

namespace ApproxLikelihood

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Gelfand's formula for real matrices -/

/-- The complexification of a real matrix. -/
def complexify (A : Matrix X X ℝ) : Matrix X X ℂ := A.map Complex.ofReal

omit [Fintype X] [DecidableEq X] in
theorem complexify_apply (A : Matrix X X ℝ) (i j : X) : complexify A i j = (A i j : ℂ) := rfl

theorem complexify_pow (A : Matrix X X ℝ) (k : ℕ) : complexify (A ^ k) = complexify A ^ k :=
  map_pow (Complex.ofRealHom.mapMatrix (m := X)) A k

theorem nnnorm_complexify (A : Matrix X X ℝ) : ‖complexify A‖₊ = ‖A‖₊ := by
  simp only [Matrix.linfty_opNNNorm_def, complexify_apply, Complex.nnnorm_real]

theorem norm_complexify (A : Matrix X X ℝ) : ‖complexify A‖ = ‖A‖ :=
  congrArg NNReal.toReal (nnnorm_complexify A)

/-- The spectral radius of a real matrix: the largest modulus of a complex eigenvalue. -/
noncomputable def specRad (A : Matrix X X ℝ) : ℝ := (spectralRadius ℂ (complexify A)).toReal

theorem spectralRadius_complexify_ne_top [Nonempty X] (A : Matrix X X ℝ) :
    spectralRadius ℂ (complexify A) ≠ ⊤ := by
  classical
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (complexify A))

theorem specRad_nonneg (A : Matrix X X ℝ) : 0 ≤ specRad A := ENNReal.toReal_nonneg

/-- **Gelfand's formula** for real matrices: `‖Aᵏ‖^{1/k} → ρ(A)`. -/
theorem tendsto_norm_pow_rpow [Nonempty X] (A : Matrix X X ℝ) :
    Tendsto (fun k : ℕ ↦ ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  have h := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A)
  have h2 := (ENNReal.tendsto_toReal (spectralRadius_complexify_ne_top A)).comp h
  refine h2.congr fun k ↦ ?_
  simp only [Function.comp, ← complexify_pow, norm_complexify]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

theorem eventually_norm_pow_le [Nonempty X] (A : Matrix X X ℝ) {r : ℝ}
    (hr : specRad A < r) : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ≤ r ^ k := by
  have hev : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ^ (1 / (k : ℝ)) < r :=
    (tendsto_norm_pow_rpow A).eventually (gt_mem_nhds hr)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  have hnn : 0 ≤ ‖A ^ k‖ := norm_nonneg _
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hk.le (Nat.cast_nonneg k)
  rwa [← Real.rpow_mul hnn, one_div_mul_cancel hkr, Real.rpow_one, Real.rpow_natCast] at this

/-- For every `γ > ρ(A)` there is `C ≥ 0` with `‖Aᵏ‖ ≤ C γᵏ` for all `k`. -/
theorem exists_norm_pow_le [Nonempty X] (A : Matrix X X ℝ) {γ : ℝ} (hγ : specRad A < γ) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ, ‖A ^ k‖ ≤ C * γ ^ k := by
  have hγ0 : 0 < γ := (specRad_nonneg A).trans_lt hγ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_norm_pow_le A hγ)
  refine ⟨1 + ∑ k ∈ range N, ‖A ^ k‖ / γ ^ k, by positivity, fun k ↦ ?_⟩
  rcases lt_or_ge k N with hk | hk
  · have h1 : ‖A ^ k‖ / γ ^ k ≤ ∑ j ∈ range N, ‖A ^ j‖ / γ ^ j :=
      single_le_sum (f := fun j ↦ ‖A ^ j‖ / γ ^ j) (fun j _ ↦ by positivity) (mem_range.2 hk)
    have h2 : ‖A ^ k‖ = ‖A ^ k‖ / γ ^ k * γ ^ k := by field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have h3 := hN k hk
    have h4 : 0 ≤ ∑ j ∈ range N, ‖A ^ j‖ / γ ^ j := sum_nonneg fun j _ ↦ by positivity
    nlinarith [pow_pos hγ0 k]

/-! ### The adapted norm -/

/-- The adapted norm `‖x‖_* = sup_k ‖Aᵏ x‖ / γᵏ`. -/
noncomputable def adaptedNorm (A : Matrix X X ℝ) (γ : ℝ) (x : X → ℝ) : ℝ :=
  ⨆ k : ℕ, ‖(A ^ k) *ᵥ x‖ / γ ^ k

section Adapted

variable {A : Matrix X X ℝ} {γ C : ℝ}

theorem term_le (hγ : 0 < γ) (hC : ∀ k : ℕ, ‖A ^ k‖ ≤ C * γ ^ k) (x : X → ℝ) (k : ℕ) :
    ‖(A ^ k) *ᵥ x‖ / γ ^ k ≤ C * ‖x‖ := by
  rw [div_le_iff₀ (pow_pos hγ k)]
  calc ‖(A ^ k) *ᵥ x‖ ≤ ‖A ^ k‖ * ‖x‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ C * γ ^ k * ‖x‖ := mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _)
    _ = C * ‖x‖ * γ ^ k := by ring

theorem bddAbove_terms (hγ : 0 < γ) (hC : ∀ k : ℕ, ‖A ^ k‖ ≤ C * γ ^ k) (x : X → ℝ) :
    BddAbove (Set.range fun k : ℕ ↦ ‖(A ^ k) *ᵥ x‖ / γ ^ k) :=
  ⟨C * ‖x‖, by rintro _ ⟨k, rfl⟩; exact term_le hγ hC x k⟩

theorem le_adaptedNorm (hγ : 0 < γ) (hC : ∀ k : ℕ, ‖A ^ k‖ ≤ C * γ ^ k) (x : X → ℝ) (k : ℕ) :
    ‖(A ^ k) *ᵥ x‖ / γ ^ k ≤ adaptedNorm A γ x :=
  le_ciSup (bddAbove_terms hγ hC x) k

/-- The adapted norm dominates the sup norm. -/
theorem norm_le_adaptedNorm (hγ : 0 < γ) (hC : ∀ k : ℕ, ‖A ^ k‖ ≤ C * γ ^ k) (x : X → ℝ) :
    ‖x‖ ≤ adaptedNorm A γ x := by
  simpa using le_adaptedNorm hγ hC x 0

/-- The adapted norm is dominated by `C` times the sup norm. -/
theorem adaptedNorm_le (hγ : 0 < γ) (hC : ∀ k : ℕ, ‖A ^ k‖ ≤ C * γ ^ k) (x : X → ℝ) :
    adaptedNorm A γ x ≤ C * ‖x‖ :=
  ciSup_le (term_le hγ hC x)

theorem adaptedNorm_add_le (hγ : 0 < γ) (hC : ∀ k : ℕ, ‖A ^ k‖ ≤ C * γ ^ k) (x y : X → ℝ) :
    adaptedNorm A γ (x + y) ≤ adaptedNorm A γ x + adaptedNorm A γ y := by
  refine ciSup_le fun k ↦ ?_
  rw [mulVec_add]
  calc ‖(A ^ k) *ᵥ x + (A ^ k) *ᵥ y‖ / γ ^ k
      ≤ (‖(A ^ k) *ᵥ x‖ + ‖(A ^ k) *ᵥ y‖) / γ ^ k :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (pow_pos hγ k).le
    _ = ‖(A ^ k) *ᵥ x‖ / γ ^ k + ‖(A ^ k) *ᵥ y‖ / γ ^ k := add_div _ _ _
    _ ≤ _ := add_le_add (le_adaptedNorm hγ hC x k) (le_adaptedNorm hγ hC y k)

theorem adaptedNorm_smul (c : ℝ) (x : X → ℝ) :
    adaptedNorm A γ (c • x) = |c| * adaptedNorm A γ x := by
  unfold adaptedNorm
  rw [Real.mul_iSup_of_nonneg (abs_nonneg c)]
  congr 1
  funext k
  rw [mulVec_smul, norm_smul, Real.norm_eq_abs, mul_div_assoc]

/-- **In the adapted norm, `A` has operator norm at most `γ`.** -/
theorem adaptedNorm_mulVec_le (hγ : 0 < γ) (hC : ∀ k : ℕ, ‖A ^ k‖ ≤ C * γ ^ k) (x : X → ℝ) :
    adaptedNorm A γ (A *ᵥ x) ≤ γ * adaptedNorm A γ x := by
  refine ciSup_le fun k ↦ ?_
  rw [mulVec_mulVec, ← pow_succ]
  have h := le_adaptedNorm hγ hC x (k + 1)
  rw [pow_succ γ k, ← div_div] at h
  calc ‖(A ^ (k + 1)) *ᵥ x‖ / γ ^ k = γ * (‖(A ^ (k + 1)) *ᵥ x‖ / γ ^ k / γ) := by
        field_simp
    _ ≤ γ * adaptedNorm A γ x := mul_le_mul_of_nonneg_left h hγ.le

end Adapted

/-- **An adapted norm exists** (Horn and Johnson 2013, Lemma 5.6.10). If the spectral radius of a
real matrix `A` is below `γ`, there is a norm `N` on `ℝⁿ`, equivalent to the sup norm, in which
`A` has operator norm at most `γ`: `N (A x) ≤ γ N x`. -/
theorem exists_adapted_norm [Nonempty X] (A : Matrix X X ℝ) {γ : ℝ} (hγ : specRad A < γ) :
    ∃ N : (X → ℝ) → ℝ, ∃ C : ℝ,
      (∀ x, ‖x‖ ≤ N x ∧ N x ≤ C * ‖x‖) ∧ (∀ x y, N (x + y) ≤ N x + N y) ∧
      (∀ (c : ℝ) x, N (c • x) = |c| * N x) ∧ ∀ x, N (A *ᵥ x) ≤ γ * N x := by
  have hγ0 : 0 < γ := (specRad_nonneg A).trans_lt hγ
  obtain ⟨C, -, hC⟩ := exists_norm_pow_le A hγ
  exact ⟨adaptedNorm A γ, C, fun x ↦ ⟨norm_le_adaptedNorm hγ0 hC x, adaptedNorm_le hγ0 hC x⟩,
    adaptedNorm_add_le hγ0 hC, adaptedNorm_smul, adaptedNorm_mulVec_le hγ0 hC⟩

end ApproxLikelihood

end LeanEconomics
