/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.HistoryMarginals
import LeanEconomics.KrusellSmith.MinMPCSmallShare

/-!
# Matched expectations converge in the CRRA Cobb–Douglas economy, whatever the marginals

`HistoryMarginals.lean` gives fading memory and a matching bound for every sequence-state
equilibrium when the employment chain is bounded below and prices are Lipschitz in labour. Clamped
Cobb–Douglas prices are (`CobbDouglas.labLip`, `abs_grossReturn_sub_le_lab`,
`abs_wage_sub_le_lab`), so for small capital shares (`SmallShare.lean`, `MinMPCSmallShare.lean`):

* **`minMPC_smallShare_matching`**: for CRRA, clamped Cobb–Douglas with `0 ≤ δ < 1` and
  `(β (1 − δ))^{1/γ} < 1 − δ`, and transition probabilities bounded below, there is a share
  `α₀ > 0` below which, for some `r < 1` and `C₀`, in **every** sequence-state equilibrium, at
  histories agreeing over their last `T + 1` shocks saving differs by at most `C₀ r ^ T` at every
  household state — the employment marginals may depend on the whole history;
* **`smallShare_matching`**: the same with `δ > 0` and the slope bound `R̄` (no condition on
  `γ`).
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace CobbDouglas

variable {Z : Type*} (T : CobbDouglas Z)

theorem abs_clampLab_sub_le (L L' : ℝ) : |T.clampLab L - T.clampLab L'| ≤ |L - L'| := by
  simp only [clampLab]
  rw [max_comm T.labLo, max_comm T.labLo]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

theorem abs_rpow_clampLab_sub_le {p : ℝ} (hp : p ≤ 1) (L L' : ℝ) :
    |T.clampLab L ^ p - T.clampLab L' ^ p| ≤ |p| * T.labLo ^ (p - 1) * |L - L'| :=
  (abs_rpow_sub_le hp T.labLo_pos (T.clampLab_mem L).1 (T.clampLab_mem L').1).trans
    (mul_le_mul_of_nonneg_left (T.abs_clampLab_sub_le L L')
      (mul_nonneg (abs_nonneg p) (Real.rpow_nonneg T.labLo_pos.le _)))

/-- The Lipschitz constant of clamped Cobb–Douglas prices in labour. -/
noncomputable def labLip : ℝ :=
  max (T.share * T.tfpHi * T.capLo ^ (T.share - 1) * ((1 - T.share) * T.labLo ^ (-T.share)))
    ((1 - T.share) * T.tfpHi * T.capHi ^ T.share * (T.share * T.labLo ^ (-T.share - 1)))

theorem labLip_nonneg [Nonempty Z] : 0 ≤ T.labLip := by
  have z : Z := Classical.arbitrary Z
  have hs := T.share_pos
  have hs1 : 0 ≤ 1 - T.share := by linarith [T.share_lt_one]
  refine le_trans ?_ (le_max_left _ _)
  exact mul_nonneg (mul_nonneg (mul_nonneg hs.le (T.tfpHi_nonneg z))
    (Real.rpow_nonneg T.capLo_pos.le _)) (mul_nonneg hs1 (Real.rpow_nonneg T.labLo_pos.le _))

theorem abs_grossReturn_sub_le_lab (z : Z) (K L L' : ℝ) :
    |T.grossReturn z K L - T.grossReturn z K L'| ≤ T.labLip * |L - L'| := by
  have hs := T.share_pos
  have hs1 : 0 ≤ 1 - T.share := by linarith [T.share_lt_one]
  have e : T.grossReturn z K L - T.grossReturn z K L'
      = (T.share * T.tfp z * T.clampCap K ^ (T.share - 1))
        * (T.clampLab L ^ (1 - T.share) - T.clampLab L' ^ (1 - T.share)) := by
    simp only [grossReturn]
    ring
  have hK := Real.rpow_nonneg (T.clampCap_pos K).le (T.share - 1)
  have hcoef : 0 ≤ T.share * T.tfp z * T.clampCap K ^ (T.share - 1) :=
    mul_nonneg (mul_nonneg hs.le (T.tfp_pos z).le) hK
  have hcoefle : T.share * T.tfp z * T.clampCap K ^ (T.share - 1)
      ≤ T.share * T.tfpHi * T.capLo ^ (T.share - 1) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (T.tfp_le z) hs.le)
      (Real.rpow_le_rpow_of_nonpos T.capLo_pos (T.clampCap_mem K).1 (by linarith [T.share_lt_one]))
      hK (mul_nonneg hs.le (T.tfpHi_nonneg z))
  have hp := T.abs_rpow_clampLab_sub_le (p := 1 - T.share) (by linarith) L L'
  rw [abs_of_nonneg hs1, show 1 - T.share - 1 = -T.share by ring] at hp
  rw [e, abs_mul, abs_of_nonneg hcoef]
  calc _ ≤ (T.share * T.tfpHi * T.capLo ^ (T.share - 1))
          * ((1 - T.share) * T.labLo ^ (-T.share) * |L - L'|) :=
        mul_le_mul hcoefle hp (abs_nonneg _) (hcoef.trans hcoefle)
    _ = (T.share * T.tfpHi * T.capLo ^ (T.share - 1) * ((1 - T.share) * T.labLo ^ (-T.share)))
        * |L - L'| := by ring
    _ ≤ T.labLip * |L - L'| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)

theorem abs_wage_sub_le_lab (z : Z) (K L L' : ℝ) :
    |T.wage z K L - T.wage z K L'| ≤ T.labLip * |L - L'| := by
  have hs := T.share_pos
  have hs1 : 0 ≤ 1 - T.share := by linarith [T.share_lt_one]
  have e : T.wage z K L - T.wage z K L'
      = ((1 - T.share) * T.tfp z * T.clampCap K ^ T.share)
        * (T.clampLab L ^ (-T.share) - T.clampLab L' ^ (-T.share)) := by
    simp only [wage]
    ring
  have hK := Real.rpow_nonneg (T.clampCap_pos K).le T.share
  have hcoef : 0 ≤ (1 - T.share) * T.tfp z * T.clampCap K ^ T.share :=
    mul_nonneg (mul_nonneg hs1 (T.tfp_pos z).le) hK
  have hcoefle : (1 - T.share) * T.tfp z * T.clampCap K ^ T.share
      ≤ (1 - T.share) * T.tfpHi * T.capHi ^ T.share :=
    mul_le_mul (mul_le_mul_of_nonneg_left (T.tfp_le z) hs1)
      (Real.rpow_le_rpow (T.clampCap_pos K).le (T.clampCap_mem K).2 hs.le)
      hK (mul_nonneg hs1 (T.tfpHi_nonneg z))
  have hp := T.abs_rpow_clampLab_sub_le (p := -T.share) (by linarith) L L'
  rw [abs_neg, abs_of_pos hs] at hp
  rw [e, abs_mul, abs_of_nonneg hcoef]
  calc _ ≤ ((1 - T.share) * T.tfpHi * T.capHi ^ T.share)
          * (T.share * T.labLo ^ (-T.share - 1) * |L - L'|) :=
        mul_le_mul hcoefle hp (abs_nonneg _) (hcoef.trans hcoefle)
    _ = ((1 - T.share) * T.tfpHi * T.capHi ^ T.share * (T.share * T.labLo ^ (-T.share - 1)))
        * |L - L'| := by ring
    _ ≤ T.labLip * |L - L'| := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)

end CobbDouglas

namespace KSModel

variable {M : KSModel Z E}

/-- The contraction hypotheses with the slope bound `R̄` as a `SlopeContraction`. -/
noncomputable def ContractionHyp.toSlope (H : M.ContractionHyp) [Nonempty Z] :
    M.SlopeContraction where
  B := H.toContractionBase
  θ := M.returnBound
  θ_nonneg := M.returnBound_nonneg
  slope z₀ K a b l := M.abs_policy_sub_le z₀ K a b l
  lam_slope_lt := H.lam_return_lt

theorem ContractionHyp.toSlope_κ (H : M.ContractionHyp) [Nonempty Z] : H.toSlope.κ = H.κ := rfl

theorem ContractionHyp.toSlope_rate (H : M.ContractionHyp) [Nonempty Z] :
    H.toSlope.rate = H.lawRate := rfl

end KSModel

variable [Nonempty Z] [Nonempty E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ}
  (hγ : 0 < γ) {ε : ℝ} (hε : 0 < ε) (hminor : ∀ z z' e e', ε ≤ V.idioProb z z' e e')
include hε hminor

/-- The matching bound from a `SlopeContraction` of the CRRA model with `κ_θ < 1`, `r_θ < 1`. -/
theorem crra_matching_of_slope {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (S : (crraModel V (T.withShare α h0 h1) hγ).SlopeContraction) (hκ : S.κ < 1)
    (hr : S.rate < 1) :
    ∃ r < 1, ∃ C₀ : ℝ, ∀ μ : History Z → ProbabilityMeasure
        (crraModel V (T.withShare α h0 h1) hγ).AState,
      (crraModel V (T.withShare α h0 h1) hγ).IsSeqStateEquilibrium μ →
      ∀ (n : ℕ) (ω ω' : History Z), (∀ k ≤ n, ω k = ω' k) →
      ∀ (a : ↥(Icc (0 : ℝ) (crraModel V (T.withShare α h0 h1) hγ).assetCap)) (e : E),
        |((crraModel V (T.withShare α h0 h1) hγ).seqPolicy μ ω a e : ℝ)
          - (crraModel V (T.withShare α h0 h1) hγ).seqPolicy μ ω' a e| ≤ C₀ * r ^ n := by
  have hminor' : ∀ z z' e e', ε ≤ (crraModel V (T.withShare α h0 h1) hγ).idioProb z z' e e' :=
    hminor
  have hℓL := (T.withShare α h0 h1).labLip_nonneg
  refine ⟨S.histRate ε, S.histRate_lt_one hε hr, S.B.G₁ * ((S.B.ℓ * S.histWeight
    (T.withShare α h0 h1).labLip ε + S.labourGap (T.withShare α h0 h1).labLip) / (1 - S.κ)),
    fun μ hμ n ω ω' hag a e => ?_⟩
  have := S.seqPolicy_gap_of_agree' hminor' hℓL
    (T.withShare α h0 h1).abs_grossReturn_sub_le_lab (T.withShare α h0 h1).abs_wage_sub_le_lab
    hε hκ hμ n hag a e
  refine this.trans (le_of_eq ?_)
  ring

/-- **Matched expectations converge geometrically, whatever the employment marginals** (minimal-MPC
version): for CRRA and clamped Cobb–Douglas with `0 ≤ δ < 1`, `(β (1 − δ))^{1/γ} < 1 − δ` and
transition probabilities bounded below, below some capital share `α₀ > 0` there are `r < 1` and
`C₀` such that in every sequence-state equilibrium, at histories agreeing over their last `n + 1`
shocks, saving differs by at most `C₀ r ^ n`. -/
theorem minMPC_smallShare_matching (hδ1 : T.depreciation < 1)
    (hgap : (V.discount * (1 - T.depreciation)) ^ (1 / γ) < 1 - T.depreciation) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃ r < 1, ∃ C₀ : ℝ, ∀ μ : History Z → ProbabilityMeasure
          (crraModel V (T.withShare α h0 hα) hγ).AState,
        (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ →
        ∀ (n : ℕ) (ω ω' : History Z), (∀ k ≤ n, ω k = ω' k) →
        ∀ (a : ↥(Icc (0 : ℝ) (crraModel V (T.withShare α h0 hα) hγ).assetCap)) (e : E),
          |((crraModel V (T.withShare α h0 hα) hγ).seqPolicy μ ω a e : ℝ)
            - (crraModel V (T.withShare α h0 hα) hγ).seqPolicy μ ω' a e| ≤ C₀ * r ^ n := by
  obtain ⟨α₀, hα₀, h⟩ := minMPC_smallShare V T hγ hδ1 hgap
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, S, hκ, hr⟩ := h α h0 hα
  exact ⟨h1, crra_matching_of_slope V T hγ hε hminor h0 h1 S hκ hr⟩

/-- **Matched expectations converge geometrically, whatever the employment marginals**
(`δ > 0`, slope bound `R̄`). -/
theorem smallShare_matching (hδ : 0 < T.depreciation) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃ r < 1, ∃ C₀ : ℝ, ∀ μ : History Z → ProbabilityMeasure
          (crraModel V (T.withShare α h0 hα) hγ).AState,
        (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ →
        ∀ (n : ℕ) (ω ω' : History Z), (∀ k ≤ n, ω k = ω' k) →
        ∀ (a : ↥(Icc (0 : ℝ) (crraModel V (T.withShare α h0 hα) hγ).assetCap)) (e : E),
          |((crraModel V (T.withShare α h0 hα) hγ).seqPolicy μ ω a e : ℝ)
            - (crraModel V (T.withShare α h0 hα) hγ).seqPolicy μ ω' a e| ≤ C₀ * r ^ n := by
  obtain ⟨α₀, hα₀, h⟩ := smallShare_contraction V T hγ hδ
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, -, H, hκ, hr⟩ := h α h0 hα
  exact ⟨h1, crra_matching_of_slope V T hγ hε hminor h0 h1 H.toSlope hκ hr⟩

end KrusellSmith

end LeanEconomics
