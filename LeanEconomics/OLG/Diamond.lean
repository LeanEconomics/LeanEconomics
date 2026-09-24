/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.CRRA
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# Diamond's two-period economy

The classical overlapping-generations model of `Diamond (1965)`: agents live two periods, work
when young and consume out of savings when old, and a representative firm rents capital from the
old. It is the base case of the programme, and everything in it is closed form.

A young household with wage `w` facing gross return `R` solves
`max u(w - s) + β u(R s)`. With CRRA utility the Euler equation `u'(w-s) = β R u'(Rs)` has the
explicit solution `s = σ(R) w` with

  `σ(R) = 1 / (1 + β^{-1/γ} R^{(γ-1)/γ})`   (`saveShare`),

and the saving rate rises with the return exactly when `γ < 1`, the textbook statement that the
substitution effect beats the income effect only above unit intertemporal elasticity. That is why
the two-period model is the right place to start: the household-side comparative static this
programme cannot prove in general is here a one-line calculation, and it goes the *wrong* way for
the risk aversions economists use.

The steady state survives it anyway. With Cobb-Douglas production the wage rises and the return
falls as capital deepens, and the wage channel dominates: capital per worker next period, divided
by capital per worker today, is strictly decreasing whatever `γ` is. So the steady state is unique
for every positive risk aversion and every depreciation rate at most one
(`exists_unique_diamondSteadyState`), with no side condition of the kind textbook treatments
impose on the savings function.
-/

open Set

namespace LeanEconomics

/-! ### The tangent inequality for CRRA -/

/-- The tangent inequality at `c = 1`, which is Bernoulli's inequality in both directions. -/
theorem crra_le_tangent_one {γ : ℝ} (hγ : 0 < γ) (hne : γ ≠ 1) {t : ℝ} (ht : 0 < t) :
    t ^ (1 - γ) / (1 - γ) ≤ 1 / (1 - γ) + (t - 1) := by
  have hs : (-1 : ℝ) ≤ t - 1 := by linarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `0 < γ < 1`: the exponent is in `(0,1)` and Bernoulli goes the concave way
    have hθ0 : (0 : ℝ) < 1 - γ := by linarith
    have hθ1 : (1 : ℝ) - γ ≤ 1 := by linarith
    have hB := rpow_one_add_le_one_add_mul_self hs hθ0.le hθ1
    rw [show (1 : ℝ) + (t - 1) = t from by ring] at hB
    rw [div_le_iff₀ hθ0]
    have hid : (1 / (1 - γ) + (t - 1)) * (1 - γ) = 1 + (1 - γ) * (t - 1) := by
      field_simp
    rw [hid]
    exact hB
  · -- `γ > 1`: the exponent is negative, and Bernoulli at exponent `γ ≥ 1` gives the reverse
    have hθ0 : (1 : ℝ) - γ < 0 := by linarith
    have hu : (0 : ℝ) < t⁻¹ := inv_pos.2 ht
    have hB := one_add_mul_self_le_rpow_one_add
      (show (-1 : ℝ) ≤ t⁻¹ - 1 from by linarith [hu.le]) hgt.le
    rw [show (1 : ℝ) + (t⁻¹ - 1) = t⁻¹ from by ring] at hB
    have hinv : (t⁻¹) ^ γ = t ^ (-γ) := by
      rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    have hkey : t * (t⁻¹) ^ γ = t ^ (1 - γ) := by
      rw [hinv, mul_comm, ← Real.rpow_add_one ht.ne' (-γ),
        show -γ + 1 = 1 - γ from by ring]
    have hmul : t * (1 + γ * (t⁻¹ - 1)) ≤ t * (t⁻¹) ^ γ :=
      mul_le_mul_of_nonneg_left hB ht.le
    rw [hkey] at hmul
    have htt : t * (t⁻¹ - 1) = 1 - t := by field_simp
    have hexp : t * (1 + γ * (t⁻¹ - 1)) = t + γ * (1 - t) := by
      rw [show t * (1 + γ * (t⁻¹ - 1)) = t + γ * (t * (t⁻¹ - 1)) from by ring, htt]
    rw [hexp] at hmul
    rw [div_le_iff_of_neg hθ0]
    have hid : (1 / (1 - γ) + (t - 1)) * (1 - γ) = t + γ * (1 - t) := by
      field_simp
      ring
    rw [hid]
    exact hmul

/-- **CRRA utility lies below its tangent.** The concavity fact the household's optimality needs.
-/
theorem crra_le_tangent {γ : ℝ} (hγ : 0 < γ) {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    crraUtility γ c' ≤ crraUtility γ c + c ^ (-γ) * (c' - c) := by
  rcases eq_or_ne γ 1 with rfl | hne
  · have h := Real.log_le_sub_one_of_pos (div_pos hc' hc)
    rw [Real.log_div hc'.ne' hc.ne'] at h
    have hcinv : c ^ (-(1 : ℝ)) = c⁻¹ := Real.rpow_neg_one c
    simp only [crraUtility_one, hcinv]
    have hid : c' / c - 1 = c⁻¹ * (c' - c) := by field_simp
    rw [hid] at h
    linarith [h]
  · have hcu : crraUtility γ c = c ^ (1 - γ) / (1 - γ) := crraUtility_of_ne hne c
    have hcu' : crraUtility γ c' = c' ^ (1 - γ) / (1 - γ) := crraUtility_of_ne hne c'
    set t : ℝ := c' / c with ht
    have ht0 : 0 < t := div_pos hc' hc
    have hct : c' = c * t := by rw [ht]; field_simp
    have hsplit : c' ^ (1 - γ) = c ^ (1 - γ) * t ^ (1 - γ) := by
      rw [hct, Real.mul_rpow hc.le ht0.le]
    have hcc : c ^ (-γ) * c = c ^ (1 - γ) := by
      have h1 : c ^ (-γ) * c ^ (1 : ℝ) = c ^ (-γ + 1) := (Real.rpow_add hc _ _).symm
      rw [Real.rpow_one] at h1
      rw [h1, show -γ + 1 = 1 - γ from by ring]
    have hpow : c ^ (-γ) * (c' - c) = c ^ (1 - γ) * (t - 1) := by
      rw [hct, show c ^ (-γ) * (c * t - c) = (c ^ (-γ) * c) * (t - 1) from by ring, hcc]
    have hc1 : (0 : ℝ) < c ^ (1 - γ) := Real.rpow_pos_of_pos hc _
    have hnorm := crra_le_tangent_one hγ hne ht0
    have := mul_le_mul_of_nonneg_left hnorm hc1.le
    rw [hcu, hcu', hsplit, hpow]
    calc c ^ (1 - γ) * t ^ (1 - γ) / (1 - γ)
        = c ^ (1 - γ) * (t ^ (1 - γ) / (1 - γ)) := by ring
      _ ≤ c ^ (1 - γ) * (1 / (1 - γ) + (t - 1)) := this
      _ = c ^ (1 - γ) / (1 - γ) + c ^ (1 - γ) * (t - 1) := by ring

/-! ### The two-period household -/

variable {γ β R w : ℝ}

/-- The share of its wage a two-period CRRA household saves,
`σ(R) = 1/(1 + β^{-1/γ} R^{(γ-1)/γ})`. -/
noncomputable def saveShare (γ β R : ℝ) : ℝ := (1 + β ^ (-1/γ) * R ^ ((γ - 1)/γ))⁻¹

theorem one_lt_saveShare_denom (hβ : 0 < β) (hR : 0 < R) :
    1 < 1 + β ^ (-1/γ) * R ^ ((γ - 1)/γ) := by
  have h1 : 0 < β ^ (-1/γ) := Real.rpow_pos_of_pos hβ _
  have h2 : 0 < R ^ ((γ - 1)/γ) := Real.rpow_pos_of_pos hR _
  nlinarith

theorem saveShare_pos (hβ : 0 < β) (hR : 0 < R) : 0 < saveShare γ β R :=
  inv_pos.2 (by linarith [one_lt_saveShare_denom (γ := γ) hβ hR])

theorem saveShare_lt_one (hβ : 0 < β) (hR : 0 < R) : saveShare γ β R < 1 := by
  rw [saveShare, inv_lt_one_iff₀]
  exact Or.inr (one_lt_saveShare_denom hβ hR)

/-- **The Euler equation holds at the closed form**: `u'(w - s) = β R u'(R s)`. -/
theorem saveShare_euler (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (hw : 0 < w) :
    (w - saveShare γ β R * w) ^ (-γ)
      = β * R * (R * (saveShare γ β R * w)) ^ (-γ) := by
  set B : ℝ := β ^ (-1/γ) with hB
  set D : ℝ := 1 + B * R ^ ((γ - 1)/γ) with hD
  have hB0 : 0 < B := Real.rpow_pos_of_pos hβ _
  have hRθ : 0 < R ^ ((γ - 1)/γ) := Real.rpow_pos_of_pos hR _
  have hD1 : 1 < D := by rw [hD]; nlinarith
  have hD0 : 0 < D := by linarith
  have hs : saveShare γ β R * w = w / D := by rw [saveShare, ← hB, ← hD]; field_simp
  have hrest : w - saveShare γ β R * w = w * (B * R ^ ((γ - 1)/γ)) / D := by
    rw [hs, hD]; field_simp; ring
  -- both sides equal `w^{-γ} β R^{1-γ} D^γ`
  have hBγ : B ^ (-γ) = β := by
    rw [hB, ← Real.rpow_mul hβ.le, show (-1/γ) * (-γ) = 1 from by field_simp, Real.rpow_one]
  have hRγ : (R ^ ((γ - 1)/γ)) ^ (-γ) = R ^ (1 - γ) := by
    rw [← Real.rpow_mul hR.le, show ((γ - 1)/γ) * (-γ) = 1 - γ from by field_simp; ring]
  have hleft : (w * (B * R ^ ((γ - 1)/γ)) / D) ^ (-γ)
      = w ^ (-γ) * (β * R ^ (1 - γ)) * (D ^ (-γ))⁻¹ := by
    rw [Real.div_rpow (by positivity) hD0.le, Real.mul_rpow hw.le (by positivity),
      Real.mul_rpow hB0.le hRθ.le, hBγ, hRγ]
    field_simp
  have hright : (R * (w / D)) ^ (-γ) = R ^ (-γ) * w ^ (-γ) * (D ^ (-γ))⁻¹ := by
    rw [Real.mul_rpow hR.le (by positivity), Real.div_rpow hw.le hD0.le]
    field_simp
  rw [hrest, hs, hleft, hright]
  have hRsplit : R * R ^ (-γ) = R ^ (1 - γ) := by
    have h1 : R ^ (-γ) * R ^ (1 : ℝ) = R ^ (-γ + 1) := (Real.rpow_add hR _ _).symm
    rw [Real.rpow_one] at h1
    rw [mul_comm, h1, show -γ + 1 = 1 - γ from by ring]
  have hDγ : (0 : ℝ) < D ^ (-γ) := Real.rpow_pos_of_pos hD0 _
  field_simp
  nlinarith [hRsplit, hDγ]

/-- **The closed form is the household's optimum.** Concavity plus the Euler equation; no
differentiation of the value, only the tangent inequality. -/
theorem saveShare_isOptimal (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (hw : 0 < w)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) w) :
    crraUtility γ (w - s) + β * crraUtility γ (R * s)
      ≤ crraUtility γ (w - saveShare γ β R * w)
        + β * crraUtility γ (R * (saveShare γ β R * w)) := by
  set σ : ℝ := saveShare γ β R with hσ
  have hσ0 : 0 < σ := saveShare_pos hβ hR
  have hσ1 : σ < 1 := saveShare_lt_one hβ hR
  have hc1 : 0 < w - σ * w := by nlinarith
  have hc2 : 0 < R * (σ * w) := by positivity
  have hd1 : 0 < w - s := by linarith [hs.2]
  have hd2 : 0 < R * s := mul_pos hR hs.1
  have t1 := crra_le_tangent hγ hc1 hd1
  have t2 := crra_le_tangent hγ hc2 hd2
  have he := saveShare_euler (γ := γ) hγ hβ hR hw
  have hmul : β * crraUtility γ (R * s)
      ≤ β * (crraUtility γ (R * (σ * w))
        + (R * (σ * w)) ^ (-γ) * (R * s - R * (σ * w))) :=
    mul_le_mul_of_nonneg_left t2 hβ.le
  have hkey : (w - σ * w) ^ (-γ) * ((w - s) - (w - σ * w))
      + β * ((R * (σ * w)) ^ (-γ) * (R * s - R * (σ * w))) ≤ 0 := by
    have hfac : (w - s) - (w - σ * w) = -(s - σ * w) := by ring
    have hfac2 : R * s - R * (σ * w) = R * (s - σ * w) := by ring
    rw [hfac, hfac2, ← hσ] at *
    nlinarith [he]
  linarith [t1, hmul, hkey]

/-- **The textbook comparative static.** The saving rate rises with the gross return exactly when
relative risk aversion is below one: above it the income effect beats the substitution effect and
the household saves a smaller share of a given wage when saving pays better. -/
theorem saveShare_strictMonoOn (hγ0 : 0 < γ) (hγ : γ < 1) (hβ : 0 < β) :
    StrictMonoOn (saveShare γ β) (Ioi (0 : ℝ)) := by
  intro R₁ h₁ R₂ h₂ hlt
  simp only [mem_Ioi] at h₁ h₂
  have hB : (0 : ℝ) < β ^ (-1/γ) := Real.rpow_pos_of_pos hβ _
  have hθ : (γ - 1)/γ < 0 := div_neg_of_neg_of_pos (by linarith) hγ0
  have hpow : R₂ ^ ((γ - 1)/γ) < R₁ ^ ((γ - 1)/γ) :=
    Real.rpow_lt_rpow_of_neg h₁ hlt hθ
  have hd₁ : (0 : ℝ) < 1 + β ^ (-1/γ) * R₁ ^ ((γ - 1)/γ) := by
    linarith [one_lt_saveShare_denom (γ := γ) hβ h₁]
  have hd₂ : (0 : ℝ) < 1 + β ^ (-1/γ) * R₂ ^ ((γ - 1)/γ) := by
    linarith [one_lt_saveShare_denom (γ := γ) hβ h₂]
  simp only [saveShare]
  exact inv_strictAntiOn (mem_Ioi.2 hd₂) (mem_Ioi.2 hd₁) (by nlinarith)

/-- Above unit relative risk aversion the saving rate falls with the return. -/
theorem saveShare_strictAntiOn (hγ : 1 < γ) (hβ : 0 < β) :
    StrictAntiOn (saveShare γ β) (Ioi (0 : ℝ)) := by
  intro R₁ h₁ R₂ h₂ hlt
  simp only [mem_Ioi] at h₁ h₂
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hB : (0 : ℝ) < β ^ (-1/γ) := Real.rpow_pos_of_pos hβ _
  have hθ : (0 : ℝ) < (γ - 1)/γ := div_pos (by linarith) hγ0
  have hpow : R₁ ^ ((γ - 1)/γ) < R₂ ^ ((γ - 1)/γ) :=
    Real.rpow_lt_rpow h₁.le hlt hθ
  have hd₁ : (0 : ℝ) < 1 + β ^ (-1/γ) * R₁ ^ ((γ - 1)/γ) := by
    linarith [one_lt_saveShare_denom (γ := γ) hβ h₁]
  have hd₂ : (0 : ℝ) < 1 + β ^ (-1/γ) * R₂ ^ ((γ - 1)/γ) := by
    linarith [one_lt_saveShare_denom (γ := γ) hβ h₂]
  simp only [saveShare]
  exact inv_strictAntiOn (mem_Ioi.2 hd₁) (mem_Ioi.2 hd₂) (by nlinarith)

/-! ### The firm, and the steady state -/

/-- The key monotonicity. With `R = a + b x` affine and increasing in `x`, and an exponent below
one, `x/(1 + B R^θ)` still rises with `x`: the denominator cannot grow fast enough to reverse it.
-/
theorem div_one_add_rpow_strictMono {B a b θ : ℝ} (hB : 0 < B) (ha : 0 ≤ a) (hb : 0 < b)
    (hθ : θ ≤ 1) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    x / (1 + B * (a + b * x) ^ θ) < y / (1 + B * (a + b * y) ^ θ) := by
  have hy : 0 < y := hx.trans hxy
  have hR1 : 0 < a + b * x := by nlinarith
  have hR2 : 0 < a + b * y := by nlinarith
  have hR12 : a + b * x < a + b * y := by nlinarith
  have hp1 : 0 < (a + b * x) ^ θ := Real.rpow_pos_of_pos hR1 _
  have hp2 : 0 < (a + b * y) ^ θ := Real.rpow_pos_of_pos hR2 _
  have hD1 : 0 < 1 + B * (a + b * x) ^ θ := by positivity
  have hD2 : 0 < 1 + B * (a + b * y) ^ θ := by positivity
  rw [div_lt_div_iff₀ hD1 hD2]
  -- it suffices that `x (a+by)^θ ≤ y (a+bx)^θ`
  have hcross : x * (a + b * y) ^ θ ≤ y * (a + b * x) ^ θ := by
    rcases le_or_gt θ 0 with hθ0 | hθ0
    · have : (a + b * y) ^ θ ≤ (a + b * x) ^ θ :=
        Real.rpow_le_rpow_of_nonpos hR1 hR12.le hθ0
      nlinarith
    · -- `x/y ≤ R₁/R₂ ≤ (R₁/R₂)^θ`
      have hratio : x / y ≤ (a + b * x) / (a + b * y) := by
        rw [div_le_div_iff₀ hy hR2]
        nlinarith
      have hle1 : (a + b * x) / (a + b * y) ≤ 1 := by
        rw [div_le_one hR2]; linarith
      have hpos : 0 < (a + b * x) / (a + b * y) := div_pos hR1 hR2
      have hexp : (a + b * x) / (a + b * y)
          ≤ ((a + b * x) / (a + b * y)) ^ θ := by
        have := Real.rpow_le_rpow_of_exponent_ge hpos hle1 hθ
        simpa using this
      have hchain : x / y ≤ ((a + b * x) / (a + b * y)) ^ θ := le_trans hratio hexp
      rw [Real.div_rpow hR1.le hR2.le, div_le_div_iff₀ hy hp2] at hchain
      linarith [hchain]
  nlinarith [hcross]

variable {α A δ : ℝ}

/-- The competitive wage of a Cobb-Douglas technology. -/
noncomputable def wage (α A k : ℝ) : ℝ := (1 - α) * A * k ^ α

/-- The competitive gross return, net of depreciation. -/
noncomputable def grossReturn (α A δ k : ℝ) : ℝ := 1 - δ + α * A * k ^ (α - 1)

/-- Capital per worker next period, as a function of capital per worker today. -/
noncomputable def diamondMap (γ β α A δ k : ℝ) : ℝ :=
  saveShare γ β (grossReturn α A δ k) * wage α A k

theorem grossReturn_pos (hα : 0 < α) (hA : 0 < A) (hδ : δ ≤ 1) {k : ℝ} (hk : 0 < k) :
    0 < grossReturn α A δ k := by
  have : 0 < k ^ (α - 1) := Real.rpow_pos_of_pos hk _
  have : 0 < α * A * k ^ (α - 1) := by positivity
  simp only [grossReturn]; linarith

/-- **The ratio of tomorrow's capital to today's is strictly decreasing.** This is the whole of
the uniqueness argument, and it holds for every positive risk aversion: the wage channel beats
the return channel whatever the saving rate does. -/
theorem diamondRatio_strictAntiOn (hγ : 0 < γ) (hβ : 0 < β) (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 < A) (hδ : δ ≤ 1) :
    StrictAntiOn (fun k => diamondMap γ β α A δ k / k) (Ioi (0 : ℝ)) := by
  intro k₁ h₁ k₂ h₂ hlt
  simp only [mem_Ioi] at h₁ h₂
  have hB : (0 : ℝ) < β ^ (-1/γ) := Real.rpow_pos_of_pos hβ _
  -- write the ratio in terms of `x = k^{α-1}`, which is strictly decreasing
  have hratio : ∀ k : ℝ, 0 < k → diamondMap γ β α A δ k / k
      = (1 - α) * A * (k ^ (α - 1)
        / (1 + β ^ (-1/γ) * ((1 - δ) + (α * A) * k ^ (α - 1)) ^ ((γ - 1)/γ))) := by
    intro k hk
    have hk1 : k ^ α / k = k ^ (α - 1) := by
      have h := Real.rpow_sub hk α 1
      rw [Real.rpow_one] at h
      rw [h]
    simp only [diamondMap, saveShare, wage, grossReturn]
    rw [show (1 - δ + α * A * k ^ (α - 1)) = ((1 - δ) + (α * A) * k ^ (α - 1)) from by ring]
    generalize (1 + β ^ (-1/γ) * ((1 - δ) + (α * A) * k ^ (α - 1)) ^ ((γ - 1)/γ)) = D
    rw [← hk1]
    ring
  have hx2 : k₂ ^ (α - 1) < k₁ ^ (α - 1) :=
    Real.rpow_lt_rpow_of_neg h₁ hlt (by linarith)
  have hx2pos : (0 : ℝ) < k₂ ^ (α - 1) := Real.rpow_pos_of_pos h₂ _
  have hθ : (γ - 1)/γ ≤ 1 := by
    rw [div_le_one hγ]; linarith
  have hmono := div_one_add_rpow_strictMono (θ := (γ - 1)/γ) (B := β ^ (-1/γ))
    (a := 1 - δ) (b := α * A) hB (by linarith) (by positivity) hθ hx2pos hx2
  change diamondMap γ β α A δ k₂ / k₂ < diamondMap γ β α A δ k₁ / k₁
  rw [hratio k₁ h₁, hratio k₂ h₂]
  have hC : (0 : ℝ) < (1 - α) * A := by nlinarith
  exact mul_lt_mul_of_pos_left hmono hC

/-- **At most one positive steady state.** -/
theorem steadyState_unique (hγ : 0 < γ) (hβ : 0 < β) (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 < A) (hδ : δ ≤ 1) {k₁ k₂ : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (e₁ : diamondMap γ β α A δ k₁ = k₁) (e₂ : diamondMap γ β α A δ k₂ = k₂) : k₁ = k₂ := by
  have hanti := diamondRatio_strictAntiOn (γ := γ) (β := β) hγ hβ hα hα1 hA hδ
  have hr₁ : diamondMap γ β α A δ k₁ / k₁ = 1 := by rw [e₁, div_self h₁.ne']
  have hr₂ : diamondMap γ β α A δ k₂ / k₂ = 1 := by rw [e₂, div_self h₂.ne']
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hcon := hanti (mem_Ioi.2 h₁) (mem_Ioi.2 h₂) h
    simp only [hr₁, hr₂] at hcon
    exact lt_irrefl 1 hcon
  · have hcon := hanti (mem_Ioi.2 h₂) (mem_Ioi.2 h₁) h
    simp only [hr₁, hr₂] at hcon
    exact lt_irrefl 1 hcon

theorem continuousOn_diamondMap (hγ : 0 < γ) (hβ : 0 < β) (hα : 0 < α) (hA : 0 < A)
    (hδ : δ ≤ 1) : ContinuousOn (fun k => diamondMap γ β α A δ k) (Ioi (0 : ℝ)) := by
  have hkα : ContinuousOn (fun k : ℝ => k ^ α) (Ioi (0 : ℝ)) :=
    continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (mem_Ioi.1 hx))
  have hkα1 : ContinuousOn (fun k : ℝ => k ^ (α - 1)) (Ioi (0 : ℝ)) :=
    continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (mem_Ioi.1 hx))
  have hR : ContinuousOn (fun k : ℝ => grossReturn α A δ k) (Ioi (0 : ℝ)) := by
    simp only [grossReturn]
    exact continuousOn_const.add (continuousOn_const.mul hkα1)
  have hRθ : ContinuousOn
      (fun k : ℝ => (grossReturn α A δ k) ^ ((γ - 1)/γ)) (Ioi (0 : ℝ)) :=
    hR.rpow_const fun x hx => Or.inl (grossReturn_pos hα hA hδ (mem_Ioi.1 hx)).ne'
  have hden : ContinuousOn
      (fun k : ℝ => 1 + β ^ (-1/γ) * (grossReturn α A δ k) ^ ((γ - 1)/γ)) (Ioi (0 : ℝ)) :=
    continuousOn_const.add (continuousOn_const.mul hRθ)
  have hne : ∀ k ∈ Ioi (0 : ℝ),
      1 + β ^ (-1/γ) * (grossReturn α A δ k) ^ ((γ - 1)/γ) ≠ 0 := by
    intro k hk
    have := one_lt_saveShare_denom (γ := γ) hβ (grossReturn_pos hα hA hδ (mem_Ioi.1 hk))
    linarith
  simp only [diamondMap, saveShare, wage]
  exact (hden.inv₀ hne).mul (continuousOn_const.mul hkα)

/-- **A steady state exists** once the map crosses the diagonal between two positive levels. -/
theorem exists_steadyState (hγ : 0 < γ) (hβ : 0 < β) (hα : 0 < α) (hA : 0 < A) (hδ : δ ≤ 1)
    {k₀ k₁ : ℝ} (h0 : 0 < k₀) (hk : k₀ ≤ k₁)
    (hlo : k₀ ≤ diamondMap γ β α A δ k₀) (hhi : diamondMap γ β α A δ k₁ ≤ k₁) :
    ∃ k ∈ Icc k₀ k₁, diamondMap γ β α A δ k = k := by
  have hsub : Icc k₀ k₁ ⊆ Ioi (0 : ℝ) := fun x hx => mem_Ioi.2 (lt_of_lt_of_le h0 hx.1)
  have hcont : ContinuousOn (fun k => diamondMap γ β α A δ k - k) (Icc k₀ k₁) :=
    ((continuousOn_diamondMap hγ hβ hα hA hδ).mono hsub).sub continuousOn_id
  have hmem : (0 : ℝ) ∈ Icc (diamondMap γ β α A δ k₁ - k₁) (diamondMap γ β α A δ k₀ - k₀) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨k, hkmem, hkval⟩ := intermediate_value_Icc' hk hcont hmem
  exact ⟨k, hkmem, by linarith [hkval]⟩

/-- **Diamond's steady state exists and is unique.** No condition on the saving function is
needed: the wage channel of a Cobb-Douglas technology dominates for every positive relative risk
aversion, even though the saving rate itself falls with the return whenever risk aversion exceeds
one. -/
theorem exists_unique_steadyState (hγ : 0 < γ) (hβ : 0 < β) (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 < A) (hδ : δ ≤ 1) {k₀ k₁ : ℝ} (h0 : 0 < k₀) (hk : k₀ ≤ k₁)
    (hlo : k₀ ≤ diamondMap γ β α A δ k₀) (hhi : diamondMap γ β α A δ k₁ ≤ k₁) :
    ∃! k : ℝ, 0 < k ∧ diamondMap γ β α A δ k = k := by
  obtain ⟨k, hkmem, hkval⟩ := exists_steadyState hγ hβ hα hA hδ h0 hk hlo hhi
  refine ⟨k, ⟨lt_of_lt_of_le h0 hkmem.1, hkval⟩, ?_⟩
  rintro y ⟨hy0, hyval⟩
  exact steadyState_unique hγ hβ hα hα1 hA hδ hy0 (lt_of_lt_of_le h0 hkmem.1) hyval hkval

end LeanEconomics
