/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.PropensityFloor
import Mathlib.Analysis.Convex.Slope

/-!
# The interval Euler step: what the enclosure certificate rests on

The certificate `numerics/rational/encl.py` encloses the stage consumption functions at two rates
and feeds the enclosure into the increment envelope of `Increment`. Everything downstream of the
failure bound is formalised there and in `MassWeighted` and `PropensityFloor`; this file proves
the step the certificate takes at every stage and state, so that the computational hypothesis is
the arithmetic alone.

## The step

Write `E_k(x)` for the Euler sum `β R ∑ π(z,z') x(z')^{-γ}` with tomorrow's consumption replaced
by numbers `x z'`. The two Euler inequalities of `LifeCycle` say that today's consumption `c` at
`(a,z)` satisfies `E_k(c_k(g, ·)) ≤ c^{-γ}` always and `c^{-γ} ≤ E_k(c_k(g, ·))` where the
household saves, `g = m - c`. Since `c_k` rises with wealth, `E_k` falls with the saving it is
evaluated at, and the two certifications the certificate uses follow
(`le_stageConsumption_of_cert`, `stageConsumption_le_of_cert`):

* if `c_L ≤ m` and `E_k(ℓ) ≤ c_L^{-γ}` for numbers `ℓ z' ≤ c_k(m - c_L, z')`, then `c_L ≤ c`;
* if `c_H ≤ m` and `c_H^{-γ} ≤ E_k(h)` for numbers `h z' ≥ c_k(m - c_H, z')`, then `c ≤ c_H`.

The first with `c_L = m` is the corner test: `E_k(ℓ) ≤ m^{-γ}` with `ℓ z' ≤ c_k(0, z')` forces
`c = m` (`stageConsumption_eq_resources_of_cert`). In the certificate `ℓ` and `h` are the
enclosure of stage `k` at the one point `m - c_L` or `m - c_H`, which is where the second half
of this file comes in.

## Between grid points

The enclosure is stored at grid points and extended between them by monotonicity and concavity of
consumption in wealth (`stageConsumption_mono`, `concaveOn_stageConsumption`): the chord from below
(`le_of_chord`), the left secant extended forward and the right secant extended backward from above
(`le_of_left_secant`, `le_of_right_secant`), exactly the three bounds in `enc_c`. Beyond the top
of the grid the certificate uses monotonicity below and cash on hand above
(`stageConsumption_le_resources`).

With these, every inequality the certificate checks is an instance of a theorem here; what it
adds is the exact rational arithmetic, rounded outward, and the branch of the corner test.
-/

open Set

namespace LeanEconomics

/-! ### Between grid points, for any concave nondecreasing function -/

section Interpolation

variable {f : ℝ → ℝ} {s : Set ℝ}

/-- **The chord from below.** A concave function lies above the chord of any two of its points,
hence above the chord of lower bounds at them. -/
theorem le_of_chord (hf : ConcaveOn ℝ s f) {a₀ a₁ x ℓ₀ ℓ₁ : ℝ} (ha₀ : a₀ ∈ s) (ha₁ : a₁ ∈ s)
    (h01 : a₀ < a₁) (hx₀ : a₀ ≤ x) (hx₁ : x ≤ a₁) (hℓ₀ : ℓ₀ ≤ f a₀) (hℓ₁ : ℓ₁ ≤ f a₁) :
    ((a₁ - x) * ℓ₀ + (x - a₀) * ℓ₁) / (a₁ - a₀) ≤ f x := by
  have hd : 0 < a₁ - a₀ := by linarith
  set θ : ℝ := (a₁ - x) / (a₁ - a₀) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hd.le
  have hθ1 : 0 ≤ 1 - θ := by
    rw [hθ, sub_nonneg, div_le_one hd]; linarith
  have hne : a₁ - a₀ ≠ 0 := hd.ne'
  have hcomb : θ * a₀ + (1 - θ) * a₁ = x := by
    rw [hθ, div_mul_eq_mul_div, one_sub_div hne, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hne]
    ring
  have h := hf.2 ha₀ ha₁ hθ0 hθ1 (by ring)
  simp only [smul_eq_mul, hcomb] at h
  have h1θ : 1 - θ = (x - a₀) / (a₁ - a₀) := by
    rw [hθ, one_sub_div hne]; congr 1; ring
  calc ((a₁ - x) * ℓ₀ + (x - a₀) * ℓ₁) / (a₁ - a₀)
      = θ * ℓ₀ + (1 - θ) * ℓ₁ := by rw [hθ, h1θ]; ring
    _ ≤ θ * f a₀ + (1 - θ) * f a₁ := by
        gcongr
    _ ≤ f x := h

/-- **The left secant extended forward.** For a concave function the secant through the two grid
points to the left bounds the function above beyond them:
`f x ≤ h₀ + (x - a₀) (h₀ - ℓm)/(a₀ - am)`, with `h₀ ≥ f a₀` and `ℓm ≤ f am`. -/
theorem le_of_left_secant (hf : ConcaveOn ℝ s f) {am a₀ x ℓm h₀ : ℝ} (ham : am ∈ s) (hx : x ∈ s)
    (hm0 : am < a₀) (hx₀ : a₀ ≤ x) (hℓ : ℓm ≤ f am) (hh : f a₀ ≤ h₀) :
    f x ≤ h₀ + (x - a₀) * ((h₀ - ℓm) / (a₀ - am)) := by
  have hd : 0 < a₀ - am := by linarith
  rcases eq_or_lt_of_le hx₀ with hxe | hxlt
  · subst hxe; simpa using hh
  have hs := hf.slope_anti_adjacent ham hx hm0 hxlt
  have hnum : (f a₀ - f am) / (a₀ - am) ≤ (h₀ - ℓm) / (a₀ - am) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hxd : 0 < x - a₀ := by linarith
  have h1 : f x - f a₀ ≤ (x - a₀) * ((h₀ - ℓm) / (a₀ - am)) := by
    have := le_trans hs hnum
    rwa [div_le_iff₀ hxd, mul_comm] at this
  linarith

/-- **The right secant extended backward.** For a concave nondecreasing function the secant
through the two grid points to the right bounds the function above before them:
`f x ≤ h₁ - (a₁ - x) max 0 ((ℓ₂ - h₁)/(a₂ - a₁))`, with `h₁ ≥ f a₁` and `ℓ₂ ≤ f a₂`. -/
theorem le_of_right_secant (hf : ConcaveOn ℝ s f) (hmono : MonotoneOn f s) {x a₁ a₂ h₁ ℓ₂ : ℝ}
    (hx : x ∈ s) (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s) (hx₁ : x ≤ a₁) (h₁₂ : a₁ < a₂)
    (hh : f a₁ ≤ h₁) (hℓ : ℓ₂ ≤ f a₂) :
    f x ≤ h₁ - (a₁ - x) * max 0 ((ℓ₂ - h₁) / (a₂ - a₁)) := by
  have hd : 0 < a₂ - a₁ := by linarith
  rcases eq_or_lt_of_le hx₁ with hxe | hxlt
  · subst hxe; simpa using hh
  have hs := hf.slope_anti_adjacent hx ha₂ hxlt h₁₂
  have hlow : (ℓ₂ - h₁) / (a₂ - a₁) ≤ (f a₂ - f a₁) / (a₂ - a₁) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hxd : 0 < a₁ - x := by linarith
  have hnn : 0 ≤ (f a₁ - f x) / (a₁ - x) :=
    div_nonneg (sub_nonneg.2 (hmono hx ha₁ hx₁)) hxd.le
  have hmax : max 0 ((ℓ₂ - h₁) / (a₂ - a₁)) ≤ (f a₁ - f x) / (a₁ - x) :=
    max_le hnn (le_trans hlow hs)
  have h1 : (a₁ - x) * max 0 ((ℓ₂ - h₁) / (a₂ - a₁)) ≤ f a₁ - f x := by
    rw [le_div_iff₀ hxd, mul_comm] at hmax; exact hmax
  linarith

end Interpolation

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### The Euler sum with tomorrow's consumption replaced by numbers -/

/-- `E_k(x) = β R ∑ π(z,z') x(z')^{-γ}`: the certificate's `Ψ`, in marginal-utility form. -/
noncomputable def eulerSum (γ : ℝ) (z : Z) (x : Z → ℝ) : ℝ :=
  (P.discount : ℝ) * ((1 + P.interest) * ∑ z', P.transitionMatrix z z' * (x z') ^ (-γ))

/-- The Euler sum falls when the consumption numbers rise. -/
theorem eulerSum_anti {γ : ℝ} (hγ0 : 0 < γ) (z : Z) {x y : Z → ℝ} (hx : ∀ z', 0 < x z')
    (hxy : ∀ z', x z' ≤ y z') : P.eulerSum γ z y ≤ P.eulerSum γ z x := by
  unfold eulerSum
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hR : (0 : ℝ) ≤ 1 + P.interest := by linarith [P.interest_gt_neg_one]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hR) hβ
  exact Finset.sum_le_sum fun z' _ =>
    mul_le_mul_of_nonneg_left (rpow_neg_antitone hγ0 (hx z') (hxy z'))
      (P.transitionMatrix_nonneg z z')

/-- Consumption never exceeds cash on hand. -/
theorem stageConsumption_le_resources (k : ℕ) (z : Z) (a : ℝ) :
    P.stageConsumption k z a ≤ P.resources (a, z) := by
  rw [P.stageConsumption_eq]
  linarith [(P.stagePolicy_mem_region k (a, z)).1]

/-! ### The two certifications -/

/-- **Lower certification.** If `c_L ≤ m` and `E_k(ℓ) ≤ c_L^{-γ}` for numbers `ℓ` below tomorrow's
consumption at the saving `m - c_L`, then today's consumption is at least `c_L`. Should it be
less, the household saves more than `m - c_L`, its Euler equation holds above the floor, and
monotonicity of tomorrow's consumption chains into `c^{-γ} ≤ c_L^{-γ}`. -/
theorem le_stageConsumption_of_cert {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hd : P.Unbounded) (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hslackg : ∀ z' : Z, P.stagePolicy k (P.stagePolicy (k + 1) (a, z), z')
      < P.maxSaving (P.stagePolicy (k + 1) (a, z), z'))
    {cL : ℝ} (hcL : 0 < cL) (hcLm : cL ≤ P.resources (a, z)) {ℓ : Z → ℝ} (hℓ : ∀ z', 0 < ℓ z')
    (hℓle : ∀ z', ℓ z' ≤ P.stageConsumption k z' (P.resources (a, z) - cL))
    (hcert : P.eulerSum γ z ℓ ≤ cL ^ (-γ)) :
    cL ≤ P.stageConsumption (k + 1) z a := by
  by_contra hcon
  push Not at hcon
  have hcg : P.stageConsumption (k + 1) z a
      = P.resources (a, z) - P.stagePolicy (k + 1) (a, z) := P.stageConsumption_eq _ _ _
  have hgmem : P.stagePolicy (k + 1) (a, z) ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
  have hgpos : 0 < P.stagePolicy (k + 1) (a, z) := by linarith
  have hpt : P.resources (a, z) - cL ∈ Icc (0 : ℝ) assetCap := ⟨by linarith, by linarith [hgmem.2]⟩
  have hmono : ∀ z', ℓ z' ≤ P.stageConsumption k z' (P.stagePolicy (k + 1) (a, z)) := fun z' =>
    le_trans (hℓle z') (P.stageConsumption_mono k hpt hgmem (by linarith))
  have h1 : (P.stageConsumption (k + 1) z a) ^ (-γ)
      ≤ P.eulerSum γ z (fun z' => P.stageConsumption k z' (P.stagePolicy (k + 1) (a, z))) := by
    unfold eulerSum
    exact P.stage_euler_ge hu hd k z ha hgpos hslackg
  have h2 := P.eulerSum_anti hγ0 z hℓ hmono
  have h3 : (P.stageConsumption (k + 1) z a) ^ (-γ) ≤ cL ^ (-γ) := le_trans h1 (le_trans h2 hcert)
  have hcpos : 0 < P.stageConsumption (k + 1) z a := P.stageConsumption_pos hd _ z ha
  exact absurd (le_of_rpow_neg_le hcpos hcL hγ0 h3) (not_le.2 hcon)

/-- **Upper certification.** If `c_H ≤ m`, `m - c_H` is in the region, and `c_H^{-γ} ≤ E_k(h)` for
numbers `h` above tomorrow's consumption at the saving `m - c_H`, then today's consumption is at
most `c_H`. Should it be more, the household saves less than `m - c_H`, its Euler inequality
under the cap and monotonicity chain into `c_H^{-γ} ≤ c^{-γ}`. -/
theorem stageConsumption_le_of_cert {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hd : P.Unbounded) (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hroom : P.stagePolicy (k + 1) (a, z) < P.maxSaving (a, z))
    {cH : ℝ} (hcH : 0 < cH) (hcHm : cH ≤ P.resources (a, z))
    (hcap : P.resources (a, z) - cH ≤ assetCap) {h : Z → ℝ}
    (hhge : ∀ z', P.stageConsumption k z' (P.resources (a, z) - cH) ≤ h z')
    (hcert : cH ^ (-γ) ≤ P.eulerSum γ z h) :
    P.stageConsumption (k + 1) z a ≤ cH := by
  by_contra hcon
  push Not at hcon
  have hcg : P.stageConsumption (k + 1) z a
      = P.resources (a, z) - P.stagePolicy (k + 1) (a, z) := P.stageConsumption_eq _ _ _
  have hgmem : P.stagePolicy (k + 1) (a, z) ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
  have hpt : P.resources (a, z) - cH ∈ Icc (0 : ℝ) assetCap := ⟨by linarith, hcap⟩
  have hpos : ∀ z', 0 < P.stageConsumption k z' (P.stagePolicy (k + 1) (a, z)) := fun z' =>
    P.stageConsumption_pos hd _ z' hgmem
  have hmono : ∀ z', P.stageConsumption k z' (P.stagePolicy (k + 1) (a, z)) ≤ h z' := fun z' =>
    le_trans (P.stageConsumption_mono k hgmem hpt (by linarith)) (hhge z')
  have h1 : P.eulerSum γ z (fun z' => P.stageConsumption k z' (P.stagePolicy (k + 1) (a, z)))
      ≤ (P.stageConsumption (k + 1) z a) ^ (-γ) := by
    unfold eulerSum
    exact P.stage_euler_le hu hd k z ha hroom
  have h2 := P.eulerSum_anti hγ0 z hpos hmono
  have h3 : cH ^ (-γ) ≤ (P.stageConsumption (k + 1) z a) ^ (-γ) :=
    le_trans hcert (le_trans h2 h1)
  have hcpos : 0 < P.stageConsumption (k + 1) z a := P.stageConsumption_pos hd _ z ha
  exact absurd (le_of_rpow_neg_le hcH hcpos hγ0 h3) (not_le.2 hcon)

/-- **The corner test.** If `E_k(ℓ) ≤ m^{-γ}` for numbers `ℓ` below tomorrow's consumption at zero
saving, the household consumes its cash on hand. -/
theorem stageConsumption_eq_resources_of_cert {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hd : P.Unbounded) (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hslackg : ∀ z' : Z, P.stagePolicy k (P.stagePolicy (k + 1) (a, z), z')
      < P.maxSaving (P.stagePolicy (k + 1) (a, z), z'))
    {ℓ : Z → ℝ} (hℓ : ∀ z', 0 < ℓ z') (hℓle : ∀ z', ℓ z' ≤ P.stageConsumption k z' 0)
    (hcert : P.eulerSum γ z ℓ ≤ (P.resources (a, z)) ^ (-γ)) :
    P.stageConsumption (k + 1) z a = P.resources (a, z) := by
  have hm : 0 < P.resources (a, z) :=
    lt_of_lt_of_le (P.stageConsumption_pos hd (k + 1) z ha) (P.stageConsumption_le_resources _ _ _)
  refine le_antisymm (P.stageConsumption_le_resources _ _ _) ?_
  refine P.le_stageConsumption_of_cert hγ0 hu hd k z ha hslackg hm le_rfl hℓ ?_ hcert
  intro z'
  simpa using hℓle z'

/-! ### The interpolation lemmas, instantiated -/

/-- The chord from below, for stage consumption. -/
theorem stageConsumption_ge_chord {γ : ℝ} (hpc : P.PositiveConsumptionAll) (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ)
    (hslack : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, P.stagePolicy k (a, z) < assetCap)
    (k : ℕ) (z : Z) {a₀ a₁ x ℓ₀ ℓ₁ : ℝ} (ha₀ : a₀ ∈ Icc (0 : ℝ) assetCap)
    (ha₁ : a₁ ∈ Icc (0 : ℝ) assetCap) (h01 : a₀ < a₁) (hx₀ : a₀ ≤ x) (hx₁ : x ≤ a₁)
    (hℓ₀ : ℓ₀ ≤ P.stageConsumption k z a₀) (hℓ₁ : ℓ₁ ≤ P.stageConsumption k z a₁) :
    ((a₁ - x) * ℓ₀ + (x - a₀) * ℓ₁) / (a₁ - a₀) ≤ P.stageConsumption k z x :=
  le_of_chord (P.concaveOn_stageConsumption hpc hγ0 hβ hu hslack k z) ha₀ ha₁ h01 hx₀ hx₁ hℓ₀ hℓ₁

/-- The left secant extended forward, for stage consumption. -/
theorem stageConsumption_le_left_secant {γ : ℝ} (hpc : P.PositiveConsumptionAll) (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ)
    (hslack : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, P.stagePolicy k (a, z) < assetCap)
    (k : ℕ) (z : Z) {am a₀ x ℓm h₀ : ℝ} (ham : am ∈ Icc (0 : ℝ) assetCap)
    (hx : x ∈ Icc (0 : ℝ) assetCap) (hm0 : am < a₀) (hx₀ : a₀ ≤ x)
    (hℓ : ℓm ≤ P.stageConsumption k z am) (hh : P.stageConsumption k z a₀ ≤ h₀) :
    P.stageConsumption k z x ≤ h₀ + (x - a₀) * ((h₀ - ℓm) / (a₀ - am)) :=
  le_of_left_secant (P.concaveOn_stageConsumption hpc hγ0 hβ hu hslack k z) ham hx hm0 hx₀ hℓ hh

/-- The right secant extended backward, for stage consumption. -/
theorem stageConsumption_le_right_secant {γ : ℝ} (hpc : P.PositiveConsumptionAll) (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ)
    (hslack : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, P.stagePolicy k (a, z) < assetCap)
    (k : ℕ) (z : Z) {x a₁ a₂ h₁ ℓ₂ : ℝ} (hx : x ∈ Icc (0 : ℝ) assetCap)
    (ha₁ : a₁ ∈ Icc (0 : ℝ) assetCap) (ha₂ : a₂ ∈ Icc (0 : ℝ) assetCap) (hx₁ : x ≤ a₁)
    (h₁₂ : a₁ < a₂) (hh : P.stageConsumption k z a₁ ≤ h₁) (hℓ : ℓ₂ ≤ P.stageConsumption k z a₂) :
    P.stageConsumption k z x ≤ h₁ - (a₁ - x) * max 0 ((ℓ₂ - h₁) / (a₂ - a₁)) :=
  le_of_right_secant (P.concaveOn_stageConsumption hpc hγ0 hβ hu hslack k z)
    (fun _ ha _ ha' hle => P.stageConsumption_mono k ha ha' hle) hx ha₁ ha₂ hx₁ h₁₂ hh hℓ

end IncomeFluctuation

end LeanEconomics
