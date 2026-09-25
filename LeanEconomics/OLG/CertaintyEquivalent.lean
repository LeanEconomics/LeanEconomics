/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The certainty-equivalent life cycle, and why Theorem 1 fails for the very risk averse

Theorem 1 --- saving rises with the interest rate --- fails in the life cycle at zero wealth in
the highest earnings state once relative risk aversion passes about `3.4`. It is natural to look
to precautionary saving for the explanation, since that is what makes such a household save. This
file shows the explanation is not precautionary at all: the same reversal happens in the
**certainty-equivalent** household, which faces no risk whatever, and there it has a closed form.

## The closed form

A household with `J` periods, no risk, no borrowing constraint and CRRA utility has
`c_{t+1} = (βR)^{1/γ} c_t` and a lifetime budget, so its initial consumption is
`c₀ = W(R)/D(R)` (`consumption_mul_pathPrice`), where

  `W(R) = ∑_t y_t R^{-t}`                    is human wealth (`humanWealth`),
  `D(R) = ∑_t β^{t/γ} R^{t/γ - t}`           is the price of the optimal path (`pathPrice`).

Saving at zero wealth therefore rises with the rate exactly when `c₀` falls, that is when

  `W(R₂) · D(R₁) ≤ W(R₁) · D(R₂)`

(`consumption_antitone_iff`). Both `W` and `D` fall as the rate rises --- future income is
discounted harder, and the optimal path is cheaper --- and the comparison is between the two
elasticities. Differentiating, `c₀` falls with `R` exactly when

  `T_y > (1 - 1/γ) · T_c`,

with `T_y` and `T_c` the durations of the two streams: the income stream must be longer than the
consumption weights, discounted by the strength of the intertemporal tilt. A more risk averse
household will not tilt its path, so the second term grows with `γ` and the inequality eventually
reverses. That is the whole mechanism, and there is no risk in it.

## What is proved here

`saving_mono_of_le_one`: for `γ ≤ 1` the comparison holds term by term, so the certainty-equivalent
household always saves more at a higher rate, whatever the income profile. For `γ > 1` it is the
duration comparison above, and at Aiyagari's numbers it reverses at `γ ≈ 4.33`, against `γ ≈ 3.39`
in the economy with risk (`WriteUps/WriteUpOLG/numerics/precaut2.m`, `durcheck.m`). So risk moves the
threshold by about one unit of risk aversion; it does not create the effect. A precautionary
argument near zero wealth would therefore be aimed at the wrong target.
-/

open Finset

namespace LeanEconomics

namespace CertaintyEquivalent

variable {J : ℕ} {y : ℕ → ℝ} {β γ R R₁ R₂ : ℝ}

/-- **Human wealth**: the present value of the income stream. -/
noncomputable def humanWealth (J : ℕ) (y : ℕ → ℝ) (R : ℝ) : ℝ :=
  ∑ t ∈ range J, y t * R ^ (-(t : ℝ))

/-- **The price of the optimal path**, per unit of initial consumption. -/
noncomputable def pathPrice (J : ℕ) (β γ R : ℝ) : ℝ :=
  ∑ t ∈ range J, β ^ ((t : ℝ) / γ) * R ^ ((t : ℝ) / γ - (t : ℝ))

theorem humanWealth_nonneg (hy : ∀ t, 0 ≤ y t) (hR : 0 < R) : 0 ≤ humanWealth J y R :=
  sum_nonneg fun t _ => mul_nonneg (hy t) (Real.rpow_nonneg hR.le _)

theorem pathPrice_pos (hJ : 0 < J) (hβ : 0 < β) (hR : 0 < R) : 0 < pathPrice J β γ R := by
  refine sum_pos' (fun t _ => mul_nonneg (Real.rpow_nonneg hβ.le _) (Real.rpow_nonneg hR.le _))
    ⟨0, mem_range.mpr hJ, ?_⟩
  exact mul_pos (Real.rpow_pos_of_pos hβ _) (Real.rpow_pos_of_pos hR _)

/-- The Euler path, in closed form: `c_t = c_0 (βR)^{t/γ}`. -/
theorem consumption_eq_of_euler {c : ℕ → ℝ} (hβ : 0 < β) (hR : 0 < R)
    (heuler : ∀ t, c (t + 1) = (β * R) ^ (1 / γ) * c t) (t : ℕ) :
    c t = c 0 * (β * R) ^ ((t : ℝ) / γ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [heuler t, ih]
    have hpos : (0 : ℝ) < β * R := mul_pos hβ hR
    have hc : ((t + 1 : ℕ) : ℝ) / γ = (t : ℝ) / γ + 1 / γ := by push_cast; ring
    rw [hc, Real.rpow_add hpos]
    ring

/-- **The closed form**: with the Euler equations and the lifetime budget, initial consumption
times the price of the path is human wealth. -/
theorem consumption_mul_pathPrice {c : ℕ → ℝ} (hγ0 : 0 < γ) (hβ : 0 < β) (hR : 0 < R)
    (heuler : ∀ t, c (t + 1) = (β * R) ^ (1 / γ) * c t)
    (hbudget : ∑ t ∈ range J, c t * R ^ (-(t : ℝ)) = humanWealth J y R) :
    c 0 * pathPrice J β γ R = humanWealth J y R := by
  rw [← hbudget, pathPrice, mul_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [consumption_eq_of_euler hβ hR heuler t, Real.mul_rpow hβ.le hR.le]
  rw [show (t : ℝ) / γ - (t : ℝ) = (t : ℝ) / γ + -(t : ℝ) by ring, Real.rpow_add hR]
  ring

/-- A negative power reverses the order of the bases. -/
theorem rpow_le_rpow_of_nonpos {x z : ℝ} (hx : 0 < x) (hxy : x ≤ z) {e : ℝ} (he : e ≤ 0) :
    z ^ e ≤ x ^ e := by
  have hz : (0 : ℝ) < z := lt_of_lt_of_le hx hxy
  rw [show e = -(-e) by ring, Real.rpow_neg hx.le, Real.rpow_neg hz.le,
    inv_le_inv₀ (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hx _)]
  exact Real.rpow_le_rpow hx.le hxy (by linarith)

/-- **Initial consumption falls with the rate exactly when the cross product does.** -/
theorem consumption_antitone_iff (hJ : 0 < J) (hβ : 0 < β) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    {c₁ c₂ : ℝ} (h₁ : c₁ * pathPrice J β γ R₁ = humanWealth J y R₁)
    (h₂ : c₂ * pathPrice J β γ R₂ = humanWealth J y R₂) :
    c₂ ≤ c₁ ↔ humanWealth J y R₂ * pathPrice J β γ R₁
      ≤ humanWealth J y R₁ * pathPrice J β γ R₂ := by
  have hD₁ := pathPrice_pos (γ := γ) hJ hβ hR₁
  have hD₂ := pathPrice_pos (γ := γ) hJ hβ hR₂
  have e₁ : c₂ * (pathPrice J β γ R₂ * pathPrice J β γ R₁)
      = humanWealth J y R₂ * pathPrice J β γ R₁ := by rw [← h₂]; ring
  have e₂ : c₁ * (pathPrice J β γ R₂ * pathPrice J β γ R₁)
      = humanWealth J y R₁ * pathPrice J β γ R₂ := by rw [← h₁]; ring
  rw [← e₁, ← e₂]
  constructor
  · intro h
    exact mul_le_mul_of_nonneg_right h (mul_pos hD₂ hD₁).le
  · intro h
    exact le_of_mul_le_mul_right h (mul_pos hD₂ hD₁)

/-- **For relative risk aversion at most one the comparison holds term by term.** Whatever the
income profile, the certainty-equivalent household saves more at a higher rate. -/
theorem humanWealth_mul_pathPrice_le_of_le_one (hy : ∀ t, 0 ≤ y t) (hβ : 0 < β) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hR₁ : 0 < R₁) (hR : R₁ ≤ R₂) :
    humanWealth J y R₂ * pathPrice J β γ R₁ ≤ humanWealth J y R₁ * pathPrice J β γ R₂ := by
  have hR₂ : (0 : ℝ) < R₂ := lt_of_lt_of_le hR₁ hR
  simp only [humanWealth, pathPrice]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  refine sum_le_sum fun s _ => sum_le_sum fun t _ => ?_
  -- the term is `y s * β^{t/γ}` times a ratio of powers of the two rates
  have hρpos : (0 : ℝ) < R₂ / R₁ := div_pos hR₂ hR₁
  have hsplit : ∀ e : ℝ, R₂ ^ e = R₁ ^ e * (R₂ / R₁) ^ e := by
    intro e
    rw [← Real.mul_rpow hR₁.le hρpos.le]
    congr 1
    field_simp
  have hρ : (1 : ℝ) ≤ R₂ / R₁ := (one_le_div hR₁).mpr hR
  have hkey : R₂ ^ (-(s : ℝ)) * R₁ ^ ((t : ℝ) / γ - (t : ℝ))
      ≤ R₁ ^ (-(s : ℝ)) * R₂ ^ ((t : ℝ) / γ - (t : ℝ)) := by
    have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    have hs : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    have hθ : (0 : ℝ) ≤ (t : ℝ) / γ - (t : ℝ) := by
      rcases eq_or_lt_of_le ht with h | h
      · rw [← h]; simp
      · have : (t : ℝ) ≤ (t : ℝ) / γ := by rw [le_div_iff₀ hγ0]; nlinarith
        linarith
    have hpow : (R₂ / R₁) ^ (-(s : ℝ)) ≤ (R₂ / R₁) ^ ((t : ℝ) / γ - (t : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hρ (by linarith)
    rw [hsplit (-(s : ℝ)), hsplit ((t : ℝ) / γ - (t : ℝ))]
    calc R₁ ^ (-(s : ℝ)) * (R₂ / R₁) ^ (-(s : ℝ)) * R₁ ^ ((t : ℝ) / γ - (t : ℝ))
        = R₁ ^ (-(s : ℝ)) * R₁ ^ ((t : ℝ) / γ - (t : ℝ)) * (R₂ / R₁) ^ (-(s : ℝ)) := by ring
      _ ≤ R₁ ^ (-(s : ℝ)) * R₁ ^ ((t : ℝ) / γ - (t : ℝ))
            * (R₂ / R₁) ^ ((t : ℝ) / γ - (t : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = R₁ ^ (-(s : ℝ))
            * (R₁ ^ ((t : ℝ) / γ - (t : ℝ)) * (R₂ / R₁) ^ ((t : ℝ) / γ - (t : ℝ))) := by ring
  have hcoef : (0 : ℝ) ≤ y s * β ^ ((t : ℝ) / γ) :=
    mul_nonneg (hy s) (Real.rpow_nonneg hβ.le _)
  calc y s * R₂ ^ (-(s : ℝ)) * (β ^ ((t : ℝ) / γ) * R₁ ^ ((t : ℝ) / γ - (t : ℝ)))
      = y s * β ^ ((t : ℝ) / γ) * (R₂ ^ (-(s : ℝ)) * R₁ ^ ((t : ℝ) / γ - (t : ℝ))) := by ring
    _ ≤ y s * β ^ ((t : ℝ) / γ) * (R₁ ^ (-(s : ℝ)) * R₂ ^ ((t : ℝ) / γ - (t : ℝ))) :=
        mul_le_mul_of_nonneg_left hkey hcoef
    _ = y s * R₁ ^ (-(s : ℝ)) * (β ^ ((t : ℝ) / γ) * R₂ ^ ((t : ℝ) / γ - (t : ℝ))) := by ring

/-- **Theorem 1 at zero wealth, without risk, for `γ ≤ 1`.** -/
theorem consumption_antitone_of_le_one (hJ : 0 < J) (hy : ∀ t, 0 ≤ y t) (hβ : 0 < β)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hR₁ : 0 < R₁) (hR : R₁ ≤ R₂)
    {c₁ c₂ : ℝ} (h₁ : c₁ * pathPrice J β γ R₁ = humanWealth J y R₁)
    (h₂ : c₂ * pathPrice J β γ R₂ = humanWealth J y R₂) : c₂ ≤ c₁ :=
  (consumption_antitone_iff hJ hβ hR₁ (lt_of_lt_of_le hR₁ hR) h₁ h₂).mpr
    (humanWealth_mul_pathPrice_le_of_le_one hy hβ hγ0 hγ1 hR₁ hR)

/-! ### A criterion for every risk aversion

`humanWealth_mul_pathPrice_le_of_le_one` settles `γ ≤ 1` term by term, because there the exponent
`θ = 1 - 1/γ` is nonpositive and every factor moves the right way. Above one the two elasticities
genuinely compete, and the comparison is the duration criterion. Writing `λ = R₁/R₂ < 1`,

  `W(R₂) = ∑ y_t R₁^{-t} λ^t`,   `D(R₂) = ∑ β^{t/γ} R₁^{t/γ-t} (λ^t)^θ`,

so the criterion asks how the same weights respond to `λ^t` against `(λ^t)^θ`. Every `λ^t` lies in
`[λ^{J-1}, 1]`, and on that interval the concave `x ↦ x^θ` lies above its chord, which is affine.
Replacing the power by its chord therefore gives a sufficient condition in terms of two sums that
are linear in `λ^t`, and it is first-order exact: as `R₂ → R₁` it reproduces the duration criterion
`T_y ≥ (1 - 1/γ) T_c` exactly. At Aiyagari's numbers the chord threshold is `4.3263` against the
exact `4.3267` (`WriteUps/WriteUpOLG/numerics/chord.m`).
-/

/-- The chord of `x ↦ x^θ` across `[m, 1]`, as an affine function of `x`. -/
noncomputable def chordSlope (θ m : ℝ) : ℝ := (1 - m ^ θ) / (1 - m)

/-- The intercept of that chord. -/
noncomputable def chordInt (θ m : ℝ) : ℝ := m ^ θ - chordSlope θ m * m

/-- **A concave power lies above its chord.** -/
theorem chord_le_rpow {θ m x : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hm0 : 0 < m) (hm1 : m < 1)
    (hx : x ∈ Set.Icc m 1) : chordInt θ m + chordSlope θ m * x ≤ x ^ θ := by
  have hd : (0 : ℝ) < 1 - m := by linarith
  set b : ℝ := (x - m) / (1 - m) with hb
  have hb0 : 0 ≤ b := div_nonneg (by linarith [hx.1]) hd.le
  have hb1 : b ≤ 1 := by rw [hb, div_le_one hd]; linarith [hx.2]
  have hcomb : (1 - b) * m + b * 1 = x := by
    rw [hb]; field_simp; ring
  have hconc := (Real.strictConcaveOn_rpow hθ0 hθ1).concaveOn.2
    (Set.mem_Ici.2 hm0.le) (Set.mem_Ici.2 zero_le_one) (by linarith : (0:ℝ) ≤ 1 - b) hb0
    (by ring)
  simp only [smul_eq_mul, hcomb, Real.one_rpow] at hconc
  have hid : chordInt θ m + chordSlope θ m * x = (1 - b) * m ^ θ + b * 1 := by
    rw [chordInt, chordSlope, hb]; field_simp; ring
  rw [hid]
  simpa using hconc

/-- The path price with each term discounted once more, by `λ^t`. -/
noncomputable def pathPriceTilt (J : ℕ) (β γ R lam : ℝ) : ℝ :=
  ∑ t ∈ range J, β ^ ((t : ℝ) / γ) * R ^ ((t : ℝ) / γ - (t : ℝ)) * lam ^ (t : ℝ)

theorem humanWealth_eq_tilt (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) :
    humanWealth J y R₂ = ∑ t ∈ range J, y t * R₁ ^ (-(t : ℝ)) * (R₁ / R₂) ^ (t : ℝ) := by
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Real.div_rpow hR₁.le hR₂.le, Real.rpow_neg hR₁.le, Real.rpow_neg hR₂.le]
  field_simp

/-- **The chord bound on the path price at the higher rate.** -/
theorem chord_le_pathPrice (hβ : 0 < β) (hγ : 1 < γ) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hR : R₁ < R₂) (hJ : 1 < J) :
    chordInt (1 - 1/γ) ((R₁/R₂) ^ ((J : ℝ) - 1)) * pathPrice J β γ R₁
        + chordSlope (1 - 1/γ) ((R₁/R₂) ^ ((J : ℝ) - 1)) * pathPriceTilt J β γ R₁ (R₁/R₂)
      ≤ pathPrice J β γ R₂ := by
  set lam : ℝ := R₁ / R₂ with hlam
  set θ : ℝ := 1 - 1/γ with hθ
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hlam0 : 0 < lam := div_pos hR₁ hR₂
  have hlam1 : lam < 1 := by rw [hlam, div_lt_one hR₂]; exact hR
  have hθ0 : 0 < θ := by rw [hθ]; have : 1/γ < 1 := by rw [div_lt_one hγ0]; exact hγ
                         linarith
  have hθ1 : θ < 1 := by rw [hθ]; have : 0 < 1/γ := by positivity
                         linarith
  set m : ℝ := lam ^ ((J : ℝ) - 1) with hm
  have hm0 : 0 < m := Real.rpow_pos_of_pos hlam0 _
  have hm1 : m < 1 := by
    rw [hm]
    exact Real.rpow_lt_one hlam0.le hlam1 (by
      have h2 : (2 : ℕ) ≤ J := hJ
      have : (2 : ℝ) ≤ (J : ℝ) := by exact_mod_cast h2
      linarith)
  -- each term of the higher-rate price is the lower-rate term times `(λ^t)^θ`
  have hterm : ∀ t ∈ range J, β ^ ((t : ℝ)/γ) * R₂ ^ ((t : ℝ)/γ - (t : ℝ))
      = β ^ ((t : ℝ)/γ) * R₁ ^ ((t : ℝ)/γ - (t : ℝ)) * (lam ^ (t : ℝ)) ^ θ := by
    intro t _
    have hpow : (lam ^ (t : ℝ)) ^ θ = lam ^ ((t : ℝ) * θ) := by
      rw [← Real.rpow_mul hlam0.le]
    have hexp : (t : ℝ) * θ = (t : ℝ) - (t : ℝ)/γ := by rw [hθ]; field_simp
    rw [hpow, hexp, hlam, Real.div_rpow hR₁.le hR₂.le]
    rw [show ((t : ℝ)/γ - (t : ℝ)) = -((t : ℝ) - (t : ℝ)/γ) from by ring,
      Real.rpow_neg hR₁.le, Real.rpow_neg hR₂.le]
    field_simp
  -- the chord bounds each `(λ^t)^θ` from below
  have hbound : ∀ t ∈ range J,
      (β ^ ((t : ℝ)/γ) * R₁ ^ ((t : ℝ)/γ - (t : ℝ)))
          * (chordInt θ m + chordSlope θ m * lam ^ (t : ℝ))
        ≤ β ^ ((t : ℝ)/γ) * R₂ ^ ((t : ℝ)/γ - (t : ℝ)) := by
    intro t ht
    rw [hterm t ht]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine chord_le_rpow hθ0 hθ1 hm0 hm1 ⟨?_, ?_⟩
    · rw [hm]
      refine Real.rpow_le_rpow_of_exponent_ge hlam0 hlam1.le ?_
      have : (t : ℝ) ≤ (J : ℝ) - 1 := by
        have := Finset.mem_range.1 ht
        have h2 : (t : ℝ) + 1 ≤ (J : ℝ) := by exact_mod_cast this
        linarith
      linarith
    · exact Real.rpow_le_one hlam0.le hlam1.le (by positivity)
  have hsum := Finset.sum_le_sum hbound
  have hlhs : chordInt θ m * pathPrice J β γ R₁
      + chordSlope θ m * pathPriceTilt J β γ R₁ lam
      = ∑ t ∈ range J, (β ^ ((t : ℝ)/γ) * R₁ ^ ((t : ℝ)/γ - (t : ℝ)))
          * (chordInt θ m + chordSlope θ m * lam ^ (t : ℝ)) := by
    simp only [pathPrice, pathPriceTilt, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hlhs]
  simpa [pathPrice] using hsum

/-- **Theorem 1 at zero wealth for every risk aversion above one**, given the chord criterion.
Together with `consumption_antitone_of_le_one` this covers all `γ > 0`: below one the criterion is
automatic, above one it is this inequality, which is first-order equivalent to the duration
comparison. -/
theorem consumption_antitone_of_chord (hJ : 1 < J) (hγ : 1 < γ) (hβ : 0 < β)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hR : R₁ < R₂) (hW : 0 ≤ humanWealth J y R₁)
    (hchord : humanWealth J y R₂ * pathPrice J β γ R₁
      ≤ humanWealth J y R₁
        * (chordInt (1 - 1/γ) ((R₁/R₂) ^ ((J : ℝ) - 1)) * pathPrice J β γ R₁
          + chordSlope (1 - 1/γ) ((R₁/R₂) ^ ((J : ℝ) - 1)) * pathPriceTilt J β γ R₁ (R₁/R₂)))
    {c₁ c₂ : ℝ} (h₁ : c₁ * pathPrice J β γ R₁ = humanWealth J y R₁)
    (h₂ : c₂ * pathPrice J β γ R₂ = humanWealth J y R₂) : c₂ ≤ c₁ := by
  rw [consumption_antitone_iff (by omega) hβ hR₁ hR₂ h₁ h₂]
  exact le_trans hchord
    (mul_le_mul_of_nonneg_left (chord_le_pathPrice hβ hγ hR₁ hR₂ hR hJ) hW)

/-! ### The risk correction, and how much slack a bound on it has -/

/-- **Theorem 1 from the certainty-equivalent criterion and an allowance for risk.** The
certainty-equivalent household's saving response has a closed form and is proved antitone for
`γ ≤ 1` (`consumption_antitone_of_le_one`) and by the chord above it
(`consumption_antitone_of_chord`). The risky household's response differs from it by a correction.
Any bound on that correction which the certainty-equivalent response exceeds certifies Theorem 1 at
the state.

The arithmetic is trivial; what matters is how much room it leaves, and the room is the finding.
Measured at Aiyagari's numbers at zero wealth in the top earnings state, the correction is stable —
between `1.15` and `3.89` across `γ ∈ [1,5]`, and DECREASING in `γ` — while the
certainty-equivalent response falls steeply, from `20.98` at `γ = 1` to `2.73` at `γ = 3` and
through zero at `γ ≈ 4.33`. So a bound on the correction may be loose by a factor of `5.4` at
`γ = 1`, `3.0`
at `γ = 2` and `1.5` at `γ = 3` and still deliver Theorem 1 there
(`WriteUps/WriteUpOLG/numerics/riskgap.m`).

That is a far weaker demand than the routes of `Increment`, where the remaining estimate needs an
absolute error below `0.03` on a quantity of size about one. Here a crude precautionary bound would
do. -/
theorem saving_nonneg_of_correction_le {gCE gRisk corr B : ℝ}
    (hsplit : gCE - corr ≤ gRisk) (hcorr : corr ≤ B) (hCE : B ≤ gCE) : 0 ≤ gRisk := by
  linarith

/-! ### The precautionary split, in secant form -/

/-- **The secant reduction.** Write the risky household's saving at the state as the
certainty-equivalent saving plus precautionary saving, `g = g_CE + P` with `P ≥ 0`. Theorem 1 across
an interval of rates is then exactly a bound on how far precautionary saving FALLS across it. No
derivative appears, and nothing is assumed about the sign of that fall. -/
theorem saving_le_of_precautionary_fall {gCE₁ gCE₂ P₁ P₂ : ℝ}
    (hfall : P₁ - P₂ ≤ gCE₂ - gCE₁) : gCE₁ + P₁ ≤ gCE₂ + P₂ := by linarith

/-- **The level route.** Discarding `P₂ ≥ 0` altogether, a bound on the LEVEL of precautionary
saving at the lower rate suffices. At Aiyagari's numbers over `r ∈ [4%, 6%]` this route closes at
`γ = 1`, where the margin `g_CE(R₂) - g_CE(R₁) = 0.329` exceeds `P(R₁) = 0.109` threefold, and it
closes nowhere above: at `γ = 2` the margin is `0.107` against `P(R₁) = 0.154`. -/
theorem saving_le_of_precautionary_level {gCE₁ gCE₂ P₁ P₂ : ℝ} (hP₂ : 0 ≤ P₂)
    (hlevel : P₁ ≤ gCE₂ - gCE₁) : gCE₁ + P₁ ≤ gCE₂ + P₂ := by linarith

/-- **The multiplicative route.** Keeping a fraction `θ` of precautionary saving at the higher rate
turns the requirement into `(1 - θ) P₁ ≤ margin`. At `γ = 2` the admissible `θ` is `0.305` against a
true ratio of `0.793` --- a crude bound would do. At `γ = 3` it is `0.842` against `0.872`, a margin
of three per cent, and above `γ ≈ 3.1` there is none: Theorem 1 itself fails across that
interval. -/
theorem saving_le_of_precautionary_ratio {gCE₁ gCE₂ P₁ P₂ θ : ℝ}
    (hratio : θ * P₁ ≤ P₂) (hmargin : (1 - θ) * P₁ ≤ gCE₂ - gCE₁) :
    gCE₁ + P₁ ≤ gCE₂ + P₂ := by nlinarith

/-- **The level route, discharged by a consumption floor.** Precautionary saving is
`P₁ = c₀^CE - c₀`, so any proved FLOOR `F ≤ c₀` bounds it above by `c₀^CE - F`, and the level route
closes on the single numerical inequality `c₀^CE - F ≤ margin`. Nothing else is needed: no bound on
how precautionary saving moves with the rate, and no estimate at the higher rate.

At Aiyagari's numbers with logarithmic utility, at zero wealth in the top earnings state across
`r ∈ [4%, 6%]`, the floor of `Incidence.riskHumanWealth_le_stageConsumption` gives
`κ_{J-1}(y_max + H^risk_{J-1}) = 1.3184` against a true `c₀ = 1.4373`, the closed form gives
`c₀^CE = 1.5463`, and the margin is `0.3287`. So `c₀^CE - F = 0.2280 ≤ 0.3287` and the route closes,
with the floor at ninety-two per cent of the truth where eighty-five was required
(`WriteUps/WriteUpOLG/numerics/logfloor.m`). -/
theorem precautionary_level_of_floor {c0CE c0 F gCE₁ gCE₂ P₂ : ℝ}
    (hfloor : F ≤ c0) (hnum : c0CE - F ≤ gCE₂ - gCE₁) (hP₂ : 0 ≤ P₂) :
    gCE₁ + (c0CE - c0) ≤ gCE₂ + P₂ := by linarith

/-- **Theorem 1 at a state, from two sandwiches and one comparison.** If the CEILING on consumption
at the higher rate lies below the FLOOR at the lower rate, then consumption falls with the rate at
that state, which is Theorem 1 there. No certainty-equivalent machinery is involved at all.

This supersedes the level route above rather than complementing it: the quantity that route required
a floor to beat, `c₀^CE - margin`, IS the certainty-equivalent consumption at the higher rate, and
that in turn IS the arithmetic upper sandwich `κ_k(m + H_k)` — the deterministic household's
propensity times its resources plus the present value of its own expected earnings. So the
`γ = 1` result is exactly this lemma with `C` the arithmetic ceiling at `R₂` and `F` the
constraint-incidence floor at `R₁`.

Measured at zero wealth in the top earnings state across `r ∈ [4%, 6%]`: at `γ = 1`,
`C = 1.2176 ≤ 1.3184 = F`, and Theorem 1 follows. At `γ = 2` it does not: `C = 1.4168` against
`F = 1.2250`. The reason is structural. The width of the sandwich at a rate is the precautionary
wedge — the arithmetic human wealth gives the ceiling, the risk-adjusted one the floor, and they
cannot both be tight — so the route works exactly while the consumption response to the rate exceeds
that wedge. Measured, the response is `0.285` against a wedge of `0.184` at `γ = 1`, and `0.075`
against `0.267` at `γ = 2` (`WriteUps/WriteUpOLG/numerics/g2.m`). -/
theorem le_of_ceiling_le_floor {c₁ c₂ F C : ℝ} (hfloor : F ≤ c₁) (hceil : c₂ ≤ C) (hnum : C ≤ F) :
    c₂ ≤ c₁ :=
  le_trans hceil (le_trans hnum hfloor)

/-! ### Chaining the two rates through the certainty equivalent -/

/-- **The certainty-equivalent chaining step.** Two Euler relations at two rates, one an upper bound
and one a lower, divide into a bound on the RATIO of today's consumptions in terms of the
ratio of the
two certainty equivalents:

`c₂^{-γ} ≥ K₂ M₂^{-γ}` and `c₁^{-γ} ≤ K₁ M₁^{-γ}` give `c₂/c₁ ≤ (K₁/K₂)^{1/γ} (M₂/M₁)`.

The point is what is ABSENT. The earlier quantitative step bounded the expectation below by its
smallest term, which charged every stage's error against next period's consumption in the WORST
earnings state and amplified it by a factor measured at `4.2` to `5.8` per stage — hopeless
over sixty
of them. Chaining through the certainty equivalent instead leaves the multiplier equal to the power
mean's gradient sum `A = ∑ π (C/M)^{-γ-1}`, which is `1` exactly when next period's consumption is
riskless, and is measured at `1.04` at `γ = 1` rising to `1.19` at `γ = 8`: a fivefold reduction.

It is not yet a contraction. With `q = (R₁/R₂)^{1/γ}` the product `qA` is `1.022` at `γ = 1` and
`1.127` at `γ = 5`, so the recursion still grows, by `(qA)^{59} = 3.6` at `γ = 1` against `1180` at
`γ = 5`. The per-stage criterion it yields, `b₁ ≤ (Þ/qA)(a + c₁/(γR))` — the `StageSlack` of
`RateMonotone` with the risk penalty `A` made explicit — fails by fourteen per cent at zero
wealth in
the top earnings state at `γ = 1` (`WriteUps/WriteUpOLG/numerics/cestep.m`). -/
theorem mul_le_mul_of_euler_pair {γ c₁ c₂ M₁ M₂ K₁ K₂ : ℝ} (hγ : 0 < γ) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (h₂ : K₂ * M₂ ^ (-γ) ≤ c₂ ^ (-γ)) (h₁ : c₁ ^ (-γ) ≤ K₁ * M₁ ^ (-γ)) :
    c₂ * M₁ * K₂ ^ (1 / γ) ≤ c₁ * M₂ * K₁ ^ (1 / γ) := by
  have hexp : ∀ c M K : ℝ, 0 < c → 0 < M → 0 < K →
      (c * M * K ^ (1 / γ)) ^ (-γ) = c ^ (-γ) * M ^ (-γ) * K⁻¹ := by
    intro c M K hc hM hK
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hc.le hM.le,
      ← Real.rpow_mul hK.le, show (1 / γ) * (-γ) = -1 from by field_simp, Real.rpow_neg_one]
  have a₁ : c₁ ^ (-γ) / K₁ ≤ M₁ ^ (-γ) := by
    rw [div_le_iff₀ hK₁]
    calc c₁ ^ (-γ) ≤ K₁ * M₁ ^ (-γ) := h₁
      _ = M₁ ^ (-γ) * K₁ := by ring
  have a₂ : M₂ ^ (-γ) ≤ c₂ ^ (-γ) / K₂ := by
    rw [le_div_iff₀ hK₂]
    calc M₂ ^ (-γ) * K₂ = K₂ * M₂ ^ (-γ) := by ring
      _ ≤ c₂ ^ (-γ) := h₂
  have hmul := mul_le_mul a₁ a₂ (by positivity : (0 : ℝ) ≤ M₂ ^ (-γ))
    (by positivity : (0 : ℝ) ≤ M₁ ^ (-γ))
  have hXY : (c₁ * M₂ * K₁ ^ (1 / γ)) ^ (-γ) ≤ (c₂ * M₁ * K₂ ^ (1 / γ)) ^ (-γ) := by
    rw [hexp c₁ M₂ K₁ hc₁ hM₂ hK₁, hexp c₂ M₁ K₂ hc₂ hM₁ hK₂]
    calc c₁ ^ (-γ) * M₂ ^ (-γ) * K₁⁻¹ = c₁ ^ (-γ) / K₁ * M₂ ^ (-γ) := by ring
      _ ≤ M₁ ^ (-γ) * (c₂ ^ (-γ) / K₂) := hmul
      _ = c₂ ^ (-γ) * M₁ ^ (-γ) * K₂⁻¹ := by ring
  -- invert the negative power: `t ↦ t ^ (-1/γ)` is antitone on the positives
  have hinv : ∀ Z : ℝ, 0 < Z → (Z ^ (-γ)) ^ (-1 / γ) = Z := by
    intro Z hZ
    rw [← Real.rpow_mul hZ.le, show (-γ) * (-1 / γ) = 1 from by field_simp, Real.rpow_one]
  have hne : (-1 / γ : ℝ) ≤ 0 := by
    rw [neg_div]
    exact neg_nonpos.2 (by positivity)
  have hstep := rpow_le_rpow_of_nonpos (x := (c₁ * M₂ * K₁ ^ (1 / γ)) ^ (-γ))
    (z := (c₂ * M₁ * K₂ ^ (1 / γ)) ^ (-γ)) (e := -1 / γ) (by positivity) hXY hne
  rw [hinv _ (by positivity : (0:ℝ) < c₂ * M₁ * K₂ ^ (1 / γ)),
    hinv _ (by positivity : (0:ℝ) < c₁ * M₂ * K₁ ^ (1 / γ))] at hstep
  exact hstep

end CertaintyEquivalent

end LeanEconomics
