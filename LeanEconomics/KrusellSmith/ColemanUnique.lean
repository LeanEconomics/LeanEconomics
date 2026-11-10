/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ColemanBridge

/-!
# Uniqueness of the Coleman fixed point

Milestone CO6 of `COLEMAN_PLAN.md`, in the classical form (Coleman 1991; Datta–Mirman–Reffett
2002): marginal utility **multiplicatively homogeneous**, `u'(t x) = φ(t) u'(x)` (CRRA:
`φ(t) = t^{-γ}`, `crraData_du_mul`), and the return **strictly decreasing** in capital.

* `euler_of_fixed`: at a fixed point the Euler root holds with consumption the policy;
* `strictAntiOn_cont`: with a strictly decreasing return, the continuation is strictly decreasing;
* **`le_of_fixed`**: of two fixed points `c₁, c₂`, `c₂ ≤ c₁`. The smallest ratio `t = c₁ / c₂` is
  attained (continuous policies on the compact box, finitely many shocks). If `t < 1`, at the
  minimiser `c₁ = t c₂` saves strictly more than `c₂`, and
  `u'(c₁) ≤ B₁(s₁) ≤ φ(t) B₂(s₁) < φ(t) B₂(s₂) ≤ φ(t) u'(c₂) = u'(t c₂) = u'(c₁)`;
* **`fixed_unique`**: the fixed point is unique, so it is the greatest fixed point `gfp T`.

Scope: the clamped Cobb–Douglas return of `crraData` is flat for capital below `capLo > 0`, so the
strictness hypothesis fails there; uniqueness for that instance needs a further argument in the
flat region (open).
-/

open Set Filter Topology

namespace LeanEconomics

namespace KrusellSmith

namespace Coleman

namespace Data

variable {Z : Type*} [Fintype Z] (D : Data Z)

/-- **At a fixed point the Euler root holds with consumption the policy.** -/
theorem euler_of_fixed {c : D.Pol} (hc : D.T c = c) (z : Z) (k : D.Box) :
    IsEulerRoot D.du (D.cont c z) D.cap (D.y z k) (D.y z k - c.1 z k) := by
  have h : c.1 z k = D.y z k - D.saving c z k := by
    conv_lhs => rw [← hc]
    rfl
  rw [h, sub_sub_cancel]
  exact D.saving_spec c z k

theorem ext_mono (c : D.Pol) (z : Z) {a b : ℝ} (hab : a ≤ b) : D.ext c z a ≤ D.ext c z b :=
  c.2.2.2.1 z _ _ (monotone_projIcc D.cap_pos.le hab)

theorem ext_ge_m (c : D.Pol) (z : Z) (s : ℝ) : D.m ≤ D.ext c z s := c.2.1 z _

/-- **With a strictly decreasing return the continuation is strictly decreasing.** -/
theorem strictAntiOn_cont (hR : ∀ z, StrictAntiOn (D.R z) (Icc 0 D.cap)) (c : D.Pol) (z : Z) :
    StrictAntiOn (D.cont c z) (Icc 0 D.cap) := by
  intro a ha b hb hab
  refine mul_lt_mul_of_pos_left ?_ D.β_pos
  have hpos : ∃ z', 0 < D.π z z' := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ z', D.π z z' ≤ 0 := Finset.sum_nonpos fun z' _ => hcon z'
    rw [D.π_sum] at h1
    norm_num at h1
  obtain ⟨z₁, hz₁⟩ := hpos
  have hterm : ∀ z', D.R z' b * D.du (D.ext c z' b) ≤ D.R z' a * D.du (D.ext c z' a) ∧
      (0 < D.π z z' → D.π z z' * D.R z' b * D.du (D.ext c z' b)
        < D.π z z' * D.R z' a * D.du (D.ext c z' a)) := by
    intro z'
    have hm := D.m_pos
    have hea := D.ext_ge_m c z' a
    have heb := D.ext_ge_m c z' b
    have hext := D.ext_mono c z' hab.le
    have hdu : D.du (D.ext c z' b) ≤ D.du (D.ext c z' a) := by
      rcases hext.lt_or_eq with hlt | heq
      · exact (D.du_anti (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith)) hlt).le
      · rw [heq]
    have hdub := D.du_pos _ (show 0 < D.ext c z' b by linarith)
    have hRlt := hR z' ha hb hab
    have hRb := D.R_nonneg z' b
    have hlt : D.R z' b * D.du (D.ext c z' b) < D.R z' a * D.du (D.ext c z' a) :=
      calc D.R z' b * D.du (D.ext c z' b) ≤ D.R z' b * D.du (D.ext c z' a) :=
            mul_le_mul_of_nonneg_left hdu hRb
        _ < D.R z' a * D.du (D.ext c z' a) :=
            mul_lt_mul_of_pos_right hRlt (hdub.trans_le hdu)
    refine ⟨hlt.le, fun hπ => ?_⟩
    rw [mul_assoc, mul_assoc]
    exact mul_lt_mul_of_pos_left hlt hπ
  refine Finset.sum_lt_sum (fun z' _ => ?_) ⟨z₁, Finset.mem_univ _, (hterm z₁).2 hz₁⟩
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hterm z').1 (D.π_nonneg z z')

theorem pol_pos (c : D.Pol) (z : Z) (k : D.Box) : 0 < c.1 z k := D.m_pos.trans_le (c.2.1 z k)

/-- **Of two fixed points, the second is below the first**, for multiplicatively homogeneous
marginal utility and a strictly decreasing return. -/
theorem le_of_fixed [Nonempty Z] {φ : ℝ → ℝ}
    (hφ : ∀ t x, 0 < t → 0 < x → D.du (t * x) = φ t * D.du x)
    (hR : ∀ z, StrictAntiOn (D.R z) (Icc 0 D.cap)) {c₁ c₂ : D.Pol}
    (h₁ : D.T c₁ = c₁) (h₂ : D.T c₂ = c₂) : c₂ ≤ c₁ := by
  -- the smallest ratio `c₁ / c₂` is attained
  have hne : (univ : Set D.Box).Nonempty := ⟨⟨0, le_rfl, D.cap_pos.le⟩, mem_univ _⟩
  have hmin : ∀ z, ∃ k : D.Box, ∀ k' : D.Box, c₁.1 z k / c₂.1 z k ≤ c₁.1 z k' / c₂.1 z k' := by
    intro z
    have hcont : Continuous fun k : D.Box => c₁.1 z k / c₂.1 z k :=
      (D.continuous_pol c₁ z).div (D.continuous_pol c₂ z) fun k => (D.pol_pos c₂ z k).ne'
    obtain ⟨k, -, hk⟩ := isCompact_univ.exists_isMinOn hne hcont.continuousOn
    exact ⟨k, fun k' => hk (mem_univ k')⟩
  choose kmin hkmin using hmin
  obtain ⟨zs, hzs⟩ := Finite.exists_min fun z => c₁.1 z (kmin z) / c₂.1 z (kmin z)
  set ks := kmin zs
  set t := c₁.1 zs ks / c₂.1 zs ks with ht
  have htle : ∀ z k, t * c₂.1 z k ≤ c₁.1 z k := by
    intro z k
    have h1 : t ≤ c₁.1 z k / c₂.1 z k := (hzs z).trans (hkmin z k)
    rwa [le_div_iff₀ (D.pol_pos c₂ z k)] at h1
  have hteq : c₁.1 zs ks = t * c₂.1 zs ks := by
    rw [ht, div_mul_cancel₀ _ (D.pol_pos c₂ zs ks).ne']
  have ht0 : 0 < t := div_pos (D.pol_pos c₁ zs ks) (D.pol_pos c₂ zs ks)
  -- the ratio is at least one
  have ht1 : 1 ≤ t := by
    by_contra hlt
    push_neg at hlt
    set x₁ := c₁.1 zs ks
    set x₂ := c₂.1 zs ks
    set y := D.y zs ks
    have hx₂ := D.pol_pos c₂ zs ks
    obtain ⟨hs₁0, hs₁cap, -, hE₁, -⟩ := D.euler_of_fixed h₁ zs ks
    obtain ⟨hs₂0, -, -, -, hE₂⟩ := D.euler_of_fixed h₂ zs ks
    have hgap : y - x₂ < y - x₁ := by
      have : x₁ < x₂ := by
        rw [hteq]
        nlinarith
      linarith
    -- `u'(c₁) ≤ B₁(s₁)`
    have e1 := hE₁ (by linarith)
    rw [sub_sub_cancel] at e1
    -- `B₁(s₁) ≤ φ(t) B₂(s₁)`
    have e2 : D.cont c₁ zs (y - x₁) ≤ φ t * D.cont c₂ zs (y - x₁) := by
      simp only [cont]
      rw [mul_left_comm (φ t) D.β]
      refine mul_le_mul_of_nonneg_left ?_ D.β_pos.le
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun z' _ => ?_
      have hpos := D.pol_pos c₂ z' (projIcc 0 D.cap D.cap_pos.le (y - x₁))
      have hle := htle z' (projIcc 0 D.cap D.cap_pos.le (y - x₁))
      have hdu : D.du (D.ext c₁ z' (y - x₁)) ≤ D.du (t * D.ext c₂ z' (y - x₁)) := by
        rcases hle.lt_or_eq with hl | he
        · exact (D.du_anti (mem_Ioi.2 (mul_pos ht0 hpos)) (mem_Ioi.2 (by
            have := mul_pos ht0 hpos; linarith)) hl).le
        · exact le_of_eq (congrArg D.du he.symm)
      rw [hφ t (D.ext c₂ z' (y - x₁)) ht0 hpos] at hdu
      have hπR := mul_nonneg (D.π_nonneg zs z') (D.R_nonneg z' (y - x₁))
      calc D.π zs z' * D.R z' (y - x₁) * D.du (D.ext c₁ z' (y - x₁))
          ≤ D.π zs z' * D.R z' (y - x₁) * (φ t * D.du (D.ext c₂ z' (y - x₁))) :=
            mul_le_mul_of_nonneg_left hdu hπR
        _ = φ t * (D.π zs z' * D.R z' (y - x₁) * D.du (D.ext c₂ z' (y - x₁))) := by ring
    -- `φ(t) > 0`
    have hφpos : 0 < φ t := by
      have h := hφ t 1 ht0 one_pos
      rw [mul_one] at h
      have ha := D.du_pos t ht0
      have hb := D.du_pos 1 one_pos
      rw [h] at ha
      exact pos_of_mul_pos_left ha hb.le
    -- `B₂(s₁) < B₂(s₂)`
    have e3 := D.strictAntiOn_cont hR c₂ zs ⟨hs₂0, by linarith⟩ ⟨hs₁0, hs₁cap⟩ hgap
    -- `B₂(s₂) ≤ u'(c₂)`
    have e4 := hE₂ (by linarith)
    rw [sub_sub_cancel] at e4
    have e5 : D.du x₁ = φ t * D.du x₂ := by rw [hteq]; exact hφ t x₂ ht0 hx₂
    have := mul_lt_mul_of_pos_left e3 hφpos
    have := mul_le_mul_of_nonneg_left e4 hφpos.le
    linarith
  intro z k
  have h1 := htle z k
  have h2 := D.pol_pos c₂ z k
  change c₂.1 z k ≤ c₁.1 z k
  nlinarith

/-- **The Coleman fixed point is unique**, for multiplicatively homogeneous marginal utility and a
strictly decreasing return; it is the greatest fixed point. -/
theorem fixed_unique [Nonempty Z] {φ : ℝ → ℝ}
    (hφ : ∀ t x, 0 < t → 0 < x → D.du (t * x) = φ t * D.du x)
    (hR : ∀ z, StrictAntiOn (D.R z) (Icc 0 D.cap)) {c : D.Pol} (hc : D.T c = c) :
    c = OrderHom.gfp D.T :=
  le_antisymm (D.le_of_fixed hφ hR (OrderHom.map_gfp D.T) hc)
    (D.le_of_fixed hφ hR hc (OrderHom.map_gfp D.T))

end Data

/-- **CRRA marginal utility is multiplicatively homogeneous**: `(t x)^{-γ} = t^{-γ} x^{-γ}`. -/
theorem crraData_du_mul {Z E : Type*} [Fintype Z] [Fintype E] [Unique E] (V : KSEnvironment Z E)
    (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)
    (hLbox : T.clampLab (V.efficiency default) = V.efficiency default)
    (hβR : V.discount * T.returnBound ≤ 1) (t x : ℝ) (ht : 0 < t) (hx : 0 < x) :
    (crraData V T hγ hLbox hβR).du (t * x)
      = t ^ (-γ) * (crraData V T hγ hLbox hβR).du x :=
  Real.mul_rpow ht.le hx.le

end Coleman

end KrusellSmith

end LeanEconomics
