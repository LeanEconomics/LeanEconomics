/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.HomotheticLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The law of motion of capital is log-linear only under full depreciation

Krusell and Smith (1998) posit `log K' = b₀(z) + b₁(z) log K`. That is two claims: aggregate
capital is the state, and the law is log-linear. In the homothetic economy with log utility
(`HomotheticLog.lean`) the first holds exactly, with idiosyncratic risk and an evolving wealth
distribution, and the law of motion is explicit. With Cobb–Douglas resources per unit of capital
`g(z, K) = 1 − δ + A(z) K^{α−1}` it is

    K' = β ((1 − δ) K + A(z) K^α).

* **`cdLaw_powerLaw_iff`**: this is a power law `B K^b` on `K > 0` iff `δ = 1`.
* **`cdLaw_logLinear_iff`**: for `δ ≤ 1`, `log K'` is affine in `log K` iff `δ = 1`.
* **`HomotheticEconomy.lawK_logLinear_iff`**: so the exact `(z, K)` law of motion of the
  homothetic log economy is log-linear in a shock `z` iff depreciation is full.

The proof compares three capital levels: a power law `f` satisfies `f(2)² = f(1) f(4)`, and for
`f(K) = (1 − δ) K + A K^α` the two sides differ by `(1 − δ) A (2^α − 2)²`.
-/

namespace LeanEconomics

namespace KrusellSmith

/-- The law of motion of capital with Cobb–Douglas production and saving rate `β`. -/
noncomputable def cdLaw (β δ A α k : ℝ) : ℝ := β * ((1 - δ) * k + A * k ^ α)

/-- **The law of motion is a power law iff depreciation is full.** -/
theorem cdLaw_powerLaw_iff {β δ A α : ℝ} (hβ : 0 < β) (hA : 0 < A) (hα : α ≠ 1) :
    (∃ B b : ℝ, ∀ k : ℝ, 0 < k → cdLaw β δ A α k = B * k ^ b) ↔ δ = 1 := by
  constructor
  · rintro ⟨B, b, h⟩
    set c := 1 - δ with hc
    set p := (2 : ℝ) ^ α with hp
    set q := (2 : ℝ) ^ b with hq
    have h4α : (4 : ℝ) ^ α = p * p := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num)]
    have h4b : (4 : ℝ) ^ b = q * q := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num)]
    have h1 : β * (c + A) = B := by
      have := h 1 one_pos
      simpa [cdLaw, Real.one_rpow] using this
    have h2 : β * (2 * c + A * p) = B * q := by
      have := h 2 (by norm_num)
      rw [cdLaw] at this
      rw [← this]
      ring
    have h3 : β * (4 * c + A * (p * p)) = B * (q * q) := by
      have := h 4 (by norm_num)
      rw [cdLaw, h4α, h4b] at this
      rw [← this]
      ring
    have E : (β * (2 * c + A * p)) ^ 2 = β * (c + A) * (β * (4 * c + A * (p * p))) := by
      rw [h2, h3, h1]
      ring
    have key : β ^ 2 * (c * A * (p - 2) ^ 2) = 0 := by linear_combination (-1 : ℝ) * E
    have hp2 : p ≠ 2 := by
      intro hp2
      have h21 : (2 : ℝ) ^ α = (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hp2
      have hle := (Real.rpow_le_rpow_left_iff (x := 2) (by norm_num)).1 h21.le
      have hge := (Real.rpow_le_rpow_left_iff (x := 2) (by norm_num)).1 h21.ge
      exact hα (le_antisymm hle hge)
    have hc0 : c = 0 := by
      rcases mul_eq_zero.1 key with hβ2 | hrest
      · exact absurd hβ2 (pow_ne_zero 2 hβ.ne')
      · rcases mul_eq_zero.1 hrest with hcA | hsq
        · rcases mul_eq_zero.1 hcA with h0 | h0
          · exact h0
          · exact absurd h0 hA.ne'
        · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 hsq) (sub_ne_zero.2 hp2)
    linarith
  · rintro rfl
    refine ⟨β * A, α, fun k _ => ?_⟩
    rw [cdLaw]
    ring

/-- **The law of motion is log-linear iff depreciation is full.** -/
theorem cdLaw_logLinear_iff {β δ A α : ℝ} (hβ : 0 < β) (hA : 0 < A) (hα : α ≠ 1) (hδ : δ ≤ 1) :
    (∃ b₀ b₁ : ℝ, ∀ k : ℝ, 0 < k → Real.log (cdLaw β δ A α k) = b₀ + b₁ * Real.log k)
      ↔ δ = 1 := by
  have hpos : ∀ k : ℝ, 0 < k → 0 < cdLaw β δ A α k := fun k hk =>
    mul_pos hβ (add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.2 hδ) hk.le)
      (mul_pos hA (Real.rpow_pos_of_pos hk _)))
  rw [← cdLaw_powerLaw_iff hβ hA hα]
  constructor
  · rintro ⟨b₀, b₁, h⟩
    refine ⟨Real.exp b₀, b₁, fun k hk => ?_⟩
    rw [← Real.exp_log (hpos k hk), h k hk, Real.exp_add, Real.rpow_def_of_pos hk, mul_comm b₁]
  · rintro ⟨B, b, h⟩
    have hB : 0 < B := by
      have h1 := h 1 one_pos
      rw [Real.one_rpow, mul_one] at h1
      exact h1 ▸ hpos 1 one_pos
    refine ⟨Real.log B, b, fun k hk => ?_⟩
    rw [h k hk, Real.log_mul hB.ne' (Real.rpow_pos_of_pos hk _).ne', Real.log_rpow hk]

namespace HomotheticEconomy

variable {Z E : Type*} [Fintype Z] [Fintype E] (M : HomotheticEconomy Z E)

/-- With Cobb–Douglas resources per unit of capital, the exact law of motion of the homothetic
log economy is `β ((1 − δ) K + A(z) K^α)`. -/
theorem lawK_cobbDouglas {δ α : ℝ} {A : Z → ℝ}
    (hres : ∀ z k, 0 < k → M.resources z k = 1 - δ + A z * k ^ (α - 1)) (z : Z) {k : ℝ}
    (hk : 0 < k) : M.lawK z k = cdLaw M.discount δ (A z) α k := by
  rw [lawK, hres z k hk, cdLaw, Real.rpow_sub_one hk.ne']
  field_simp

/-- **The exact `(z, K)` law of motion is log-linear iff depreciation is full**: the homothetic
log economy with Cobb–Douglas resources, capital share `α ≠ 1` and `δ ≤ 1`. -/
theorem lawK_logLinear_iff {δ α : ℝ} {A : Z → ℝ}
    (hres : ∀ z k, 0 < k → M.resources z k = 1 - δ + A z * k ^ (α - 1)) (z : Z) (hA : 0 < A z)
    (hα : α ≠ 1) (hδ : δ ≤ 1) :
    (∃ b₀ b₁ : ℝ, ∀ k : ℝ, 0 < k → Real.log (M.lawK z k) = b₀ + b₁ * Real.log k) ↔ δ = 1 := by
  rw [← cdLaw_logLinear_iff M.discount_pos hA hα hδ]
  constructor
  · rintro ⟨b₀, b₁, h⟩
    exact ⟨b₀, b₁, fun k hk => by rw [← M.lawK_cobbDouglas hres z hk]; exact h k hk⟩
  · rintro ⟨b₀, b₁, h⟩
    exact ⟨b₀, b₁, fun k hk => by rw [M.lawK_cobbDouglas hres z hk]; exact h k hk⟩

end HomotheticEconomy

end KrusellSmith

end LeanEconomics
