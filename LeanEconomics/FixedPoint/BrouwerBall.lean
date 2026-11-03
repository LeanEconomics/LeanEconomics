/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.FixedPoint.BrouwerRetraction

/-!
# The Brouwer fixed-point theorem for the closed unit ball

SLP §17.3 (Theorem 17.3, p. 517) quotes the Brouwer fixed-point theorem without proof. This
module proves it for the closed unit ball of a finite-dimensional real inner product space, on top
of Rogers' lemma `no_C1_retraction` (no C¹ retraction of the ball onto the sphere).

* `C1Restrictions K`: the subalgebra of `C(K, ℝ)` of restrictions of C¹ functions `E → ℝ`.
* `exists_C1_approx_real` (Stone–Weierstrass): a real function continuous on a compact `K` is a
  uniform limit on `K` of C¹ functions.
* `exists_C1_approx`: the same for maps `K → E` with `E` finite-dimensional (approximate each
  coordinate in a basis).
* `brouwer_closedBall`: a map continuous on the closed unit ball of a finite-dimensional real inner
  product space and mapping it into itself has a fixed point.
* `brouwer_ball`: the special case `E = ℝⁿ = EuclideanSpace ℝ (Fin n)`.

Proof of `brouwer_closedBall`. If `f` had no fixed point on the ball `B`, then
`ε = min_B ‖f x − x‖ > 0`. A C¹ approximation `q₀` of `f` to within `η = ε/4`, rescaled to
`q = q₀/(1 + η)`, maps `B` into `B` and has no fixed point on `B`. With `u = x − q x`, the point
`g x = x + λ(x) u` where `λ(x) = (−⟨x, u⟩ + √D(x))/‖u‖²` and
`D(x) = ⟨x, u⟩² − ‖u‖²(‖x‖² − 1)` solves `‖g x‖ = 1`. On `B`, `‖u‖ > 0` and `D > 0` (in the
interior because `‖x‖ < 1`; on the sphere because `2⟨x, u⟩ = 1 − ‖q x‖² + ‖u‖² > 0`), so `g` is
C¹ on the open set `{‖u‖² > 0, D > 0} ⊇ B`; on the sphere `λ = 0` and `g x = x`. This contradicts
`no_C1_retraction`.
-/

namespace LeanEconomics.FixedPoint

open Metric Set Filter Topology Module
open scoped RealInnerProductSpace

/-- The subalgebra of `C(K, ℝ)` consisting of the restrictions to `K` of C¹ functions `E → ℝ`. -/
def C1Restrictions {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) :
    Subalgebra ℝ C(K, ℝ) where
  carrier := {φ | ∃ F : E → ℝ, ContDiff ℝ 1 F ∧ ∀ x : K, φ x = F x}
  mul_mem' := by
    rintro φ ψ ⟨F, hF, hφ⟩ ⟨G, hG, hψ⟩
    exact ⟨fun x => F x * G x, hF.mul hG, fun x => by simp [hφ, hψ]⟩
  add_mem' := by
    rintro φ ψ ⟨F, hF, hφ⟩ ⟨G, hG, hψ⟩
    exact ⟨fun x => F x + G x, hF.add hG, fun x => by simp [hφ, hψ]⟩
  algebraMap_mem' r := ⟨fun _ => r, contDiff_const, fun x => by simp⟩

/-- **Stone–Weierstrass approximation by C¹ functions.** A real function continuous on a compact
subset `K` of a real normed space is uniformly approximable on `K` by C¹ functions. -/
theorem exists_C1_approx_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    (hK : IsCompact K) {f : E → ℝ} (hf : ContinuousOn f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : E → ℝ, ContDiff ℝ 1 F ∧ ∀ x ∈ K, |F x - f x| < ε := by
  have _ : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let φ : C(K, ℝ) := ⟨K.domRestrict f, hf.domRestrict⟩
  have hsep : (C1Restrictions K).SeparatesPoints := by
    intro x y hxy
    obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_separating_of_ne (R := ℝ)
      (Subtype.coe_injective.ne hxy)
    exact ⟨_, ⟨⟨fun z => ℓ z, ℓ.continuous.comp continuous_subtype_val⟩,
      ⟨ℓ, ℓ.contDiff, fun z => rfl⟩, rfl⟩, hℓ⟩
  have hdense := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have hmem : φ ∈ closure (C1Restrictions K : Set C(K, ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe, hdense]
    trivial
  obtain ⟨ψ, ⟨F, hF, hψ⟩, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
  refine ⟨F, hF, fun x hx => ?_⟩
  have h := (ContinuousMap.dist_apply_le_dist (f := φ) (g := ψ) ⟨x, hx⟩).trans_lt hdist
  rw [hψ] at h
  have h' : dist (f x) (F x) < ε := h
  rw [Real.dist_eq, abs_sub_comm] at h'
  exact h'

/-- **C¹ approximation of maps into a finite-dimensional space.** A map `f : E → E`, continuous on
a compact `K ⊆ E` with `E` finite-dimensional, is uniformly approximable on `K` by C¹ maps. -/
theorem exists_C1_approx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) {f : E → E} (hf : ContinuousOn f K)
    {ε : ℝ} (hε : 0 < ε) : ∃ F : E → E, ContDiff ℝ 1 F ∧ ∀ x ∈ K, ‖F x - f x‖ < ε := by
  let b := Module.finBasis ℝ E
  set Cb := ∑ i, ‖b i‖ with hCb
  have hCb0 : 0 ≤ Cb := Finset.sum_nonneg fun i _ => norm_nonneg _
  set η := ε / (Cb + 1) with hη
  have hη0 : 0 < η := by positivity
  have hcoord : ∀ i, ContinuousOn (fun x => b.repr (f x) i) K := fun i =>
    (b.coord i).continuous_of_finiteDimensional.comp_continuousOn hf
  choose F hF happrox using fun i => exists_C1_approx_real hK (hcoord i) hη0
  refine ⟨fun x => ∑ i, F i x • b i, ContDiff.sum fun i _ => (hF i).smul contDiff_const, ?_⟩
  intro x hx
  calc ‖∑ i, F i x • b i - f x‖ = ‖∑ i, (F i x - b.repr (f x) i) • b i‖ := by
        conv_lhs => rw [← b.sum_repr (f x)]
        rw [← Finset.sum_sub_distrib]
        simp only [sub_smul]
    _ ≤ ∑ i, |F i x - b.repr (f x) i| * ‖b i‖ :=
        norm_sum_le_of_le _ fun i _ => by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, η * ‖b i‖ :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (happrox i x hx).le (norm_nonneg _)
    _ = η * Cb := by rw [hCb, Finset.mul_sum]
    _ < ε := by
        rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- **Brouwer fixed-point theorem for the closed unit ball** of a finite-dimensional real inner
product space: a map continuous on the closed unit ball and mapping it into itself has a fixed
point there. -/
theorem brouwer_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : E) 1, f x = x := by
  by_contra hcon
  have hne : ∀ x ∈ closedBall (0 : E) 1, f x ≠ x := fun x hx h => hcon ⟨x, hx, h⟩
  set B := closedBall (0 : E) 1 with hB
  have hBc : IsCompact B := isCompact_closedBall 0 1
  obtain ⟨x0, hx0B, hx0min⟩ := hBc.exists_isMinOn (nonempty_closedBall.2 zero_le_one)
    ((hf.sub continuousOn_id).norm)
  set ε := ‖f x0 - x0‖ with hεdef
  have hε : 0 < ε := norm_pos_iff.2 (sub_ne_zero.2 (hne x0 hx0B))
  have hεle : ∀ x ∈ B, ε ≤ ‖f x - x‖ := fun x hx => hx0min hx
  set η := ε / 4 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨q0, hq0, hq0approx⟩ := exists_C1_approx hBc hf hη0
  set q : E → E := fun x => (1 + η)⁻¹ • q0 x with hqdef
  have hqC : ContDiff ℝ 1 q := contDiff_const.smul hq0
  have hfB : ∀ x ∈ B, ‖f x‖ ≤ 1 := fun x hx => mem_closedBall_zero_iff.1 (hmaps hx)
  have hq0B : ∀ x ∈ B, ‖q0 x‖ ≤ 1 + η := by
    intro x hx
    calc ‖q0 x‖ = ‖(q0 x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖q0 x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ η + 1 := add_le_add (hq0approx x hx).le (hfB x hx)
      _ = 1 + η := add_comm _ _
  have hqB : ∀ x ∈ B, ‖q x‖ ≤ 1 := by
    intro x hx
    rw [hqdef, norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ (by positivity),
      mul_one]
    exact hq0B x hx
  have hqne : ∀ x ∈ B, q x ≠ x := by
    intro x hx hqx
    have h1 : q x - q0 x = (-(η / (1 + η))) • q0 x := by
      have h1η : (1 : ℝ) + η ≠ 0 := by positivity
      have hcoef : (-(η / (1 + η))) = (1 + η)⁻¹ - 1 := by field_simp; ring
      simp only [hqdef]
      rw [hcoef, sub_smul, one_smul]
    have h2 : ‖q x - q0 x‖ ≤ η := by
      rw [h1, norm_smul, norm_neg, Real.norm_of_nonneg (by positivity)]
      calc η / (1 + η) * ‖q0 x‖ ≤ η / (1 + η) * (1 + η) :=
            mul_le_mul_of_nonneg_left (hq0B x hx) (by positivity)
        _ = η := by field_simp
    have h3 : ‖f x - x‖ < ε := by
      calc ‖f x - x‖ = ‖-((q x - q0 x) + (q0 x - f x))‖ := by
            rw [hqx]
            congr 1
            abel
        _ ≤ ‖q x - q0 x‖ + ‖q0 x - f x‖ := by rw [norm_neg]; exact norm_add_le _ _
        _ < η + η := add_lt_add_of_le_of_lt h2 (hq0approx x hx)
        _ < ε := by linarith
    exact absurd (hεle x hx) (not_le.2 h3)
  -- the retraction
  set u : E → E := fun x => x - q x with hudef
  set a : E → ℝ := fun x => ⟪u x, u x⟫ with hadef
  set bb : E → ℝ := fun x => ⟪x, u x⟫ with hbbdef
  set c : E → ℝ := fun x => ⟪x, x⟫ - 1 with hcdef
  set D : E → ℝ := fun x => bb x ^ 2 - a x * c x with hDdef
  set lam : E → ℝ := fun x => (-bb x + Real.sqrt (D x)) / a x with hlamdef
  set g : E → E := fun x => x + lam x • u x with hgdef
  set U : Set E := {x | 0 < a x} ∩ {x | 0 < D x} with hUdef
  have huC : ContDiff ℝ 1 u := contDiff_id.sub hqC
  have haC : ContDiff ℝ 1 a := huC.inner ℝ huC
  have hbbC : ContDiff ℝ 1 bb := contDiff_id.inner ℝ huC
  have hcC : ContDiff ℝ 1 c := (contDiff_id.inner ℝ contDiff_id).sub contDiff_const
  have hDC : ContDiff ℝ 1 D := (hbbC.pow 2).sub (haC.mul hcC)
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const haC.continuous).inter (isOpen_lt continuous_const hDC.continuous)
  -- the identity `2 ⟨x, u⟩ = ‖x‖² − ‖q x‖² + ‖u‖²`
  have hrel : ∀ x, 2 * bb x = ‖x‖ ^ 2 - ‖q x‖ ^ 2 + a x := by
    intro x
    simp only [hbbdef, hadef, hudef, inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm x (q x)]
    ring
  have haB : ∀ x ∈ B, 0 < a x := by
    intro x hx
    simp only [hadef, real_inner_self_eq_norm_sq]
    have : u x ≠ 0 := sub_ne_zero.2 (hqne x hx).symm
    positivity
  have hBU : B ⊆ U := by
    intro x hx
    refine ⟨haB x hx, ?_⟩
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
    have hq1 := hqB x hx
    have ha := haB x hx
    have hr := hrel x
    have hcx : c x = ‖x‖ ^ 2 - 1 := by simp [hcdef]
    change 0 < bb x ^ 2 - a x * c x
    rw [hcx]
    rcases hx1.lt_or_eq with hlt | heq
    · have : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
      nlinarith [sq_nonneg (bb x)]
    · rw [heq] at hr ⊢
      have : 0 < bb x := by nlinarith [norm_nonneg (q x)]
      nlinarith
  have hgC : ContDiffOn ℝ 1 g U := by
    intro x hx
    have hsq : ContDiffAt ℝ 1 (fun y => Real.sqrt (D y)) x := hDC.contDiffAt.sqrt hx.2.ne'
    have hlam : ContDiffAt ℝ 1 lam x :=
      (hbbC.contDiffAt.neg.add hsq).div haC.contDiffAt hx.1.ne'
    exact (contDiffAt_id.add (hlam.smul huC.contDiffAt)).contDiffWithinAt
  have hsph : ∀ x ∈ B, ‖g x‖ = 1 := by
    intro x hx
    have ha := haB x hx
    have hD := (hBU hx).2
    set s := Real.sqrt (D x) with hs
    have hs2 : s ^ 2 = bb x ^ 2 - a x * c x := Real.sq_sqrt hD.le
    have h1 : lam x * a x = s - bb x := by
      simp only [hlamdef]
      field_simp
      ring
    have hinner : ⟪g x, g x⟫ = ⟪x, x⟫ + 2 * lam x * bb x + lam x ^ 2 * a x := by
      simp only [hgdef, hbbdef, hadef, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, real_inner_comm x (u x)]
      simp only [RCLike.conj_to_real]
      ring
    have hkey : a x * (2 * lam x * bb x + lam x ^ 2 * a x + c x) = 0 := by
      linear_combination (lam x * a x + s + bb x) * h1 + hs2
    have hkey' : 2 * lam x * bb x + lam x ^ 2 * a x + c x = 0 :=
      (mul_eq_zero.1 hkey).resolve_left ha.ne'
    have hgg : ⟪g x, g x⟫ = 1 := by
      rw [hinner]
      simp only [hcdef] at hkey'
      linarith
    rw [real_inner_self_eq_norm_sq] at hgg
    have := norm_nonneg (g x)
    nlinarith
  have hid : ∀ x : E, ‖x‖ = 1 → g x = x := by
    intro x hx1
    have hx : x ∈ B := mem_closedBall_zero_iff.2 hx1.le
    have hc0 : c x = 0 := by simp [hcdef, hx1]
    have hbb0 : 0 ≤ bb x := by
      have hr := hrel x
      have hq1 := hqB x hx
      rw [hx1] at hr
      nlinarith [norm_nonneg (q x), haB x hx]
    have hlam0 : lam x = 0 := by
      simp only [hlamdef, hDdef, hc0, mul_zero, sub_zero, Real.sqrt_sq hbb0, neg_add_cancel,
        zero_div]
    simp [hgdef, hlam0]
  exact no_C1_retraction hUo hBU hgC hsph hid

/-- **Brouwer fixed-point theorem for the closed unit ball of `ℝⁿ`.** Every map
`f : ℝⁿ → ℝⁿ` continuous on the closed unit ball and mapping it into itself has a fixed point in
the ball. -/
theorem brouwer_ball (n : ℕ) {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContinuousOn f (closedBall 0 1)) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f x = x :=
  brouwer_closedBall hf hmaps

end LeanEconomics.FixedPoint
