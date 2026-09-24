/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.MPCBound
import LeanEconomics.OLG.Existence

/-!
# The propensity to consume is at least `κ_k`

`MPCBound` bounds the secant slope of the consumption function from ABOVE. The increment argument
of `Increment` needs the other side: saving Lipschitz in assets with constant `(1 - κ_k) R`, which
is the same as the propensity to consume being at least `κ_k`.

The terminal condition is an identity: in the last period consumption is cash on hand, so the
propensity is exactly `1 = κ₀` (`stageConsumption_sub_zero`). The step is the two-point Euler
comparison. With `b_i` the saving at `a_i` and `t = κ_k R (b₂ - b₁)`, the induction hypothesis
shifts next period's consumption up by `t` in EVERY state, and the Euler equation at `a₂` gives

  `c₂^{-γ} ≤ βR ∑ π (C'(z') + t)^{-γ} = βR M(C' + t)^{-γ} ≤ βR (M(C') + t)^{-γ}`,

where `M` is the certainty equivalent — the power mean of exponent `-γ`. The last step is
`powerMean_add_const_le`, superadditivity under a common shift. The Euler equation at `a₁` gives
`M(C') ≥ Þ c₁`, and `βR = Þ^γ` turns the chain into `c₂ ≥ c₁ + t/Þ`, which is the claim at stage
`k+1` after clearing denominators.

Superadditivity is why this side goes through and the matching upper bound does not. A certainty
equivalent of a negative power obeys `M(x + t) ≥ M(x) + t`, and several arguments in this
programme wanted the reverse, which is false.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **The propensity to consume is at least `κ_k`.** Equivalently, saving is Lipschitz in assets
with constant `(1 - κ_k)(1 + r)`, which is the constant the increment argument uses. -/
theorem stageMPC_mul_le_stageConsumption_sub {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      P.stagePolicy j (b, w) < P.maxSaving (b, w))
    (k : ℕ) : ∀ (z : Z) (a₁ a₂ : ℝ), a₁ ∈ Icc (0 : ℝ) assetCap → a₂ ∈ Icc (0 : ℝ) assetCap →
      a₁ ≤ a₂ → P.stageMPC γ k * ((1 + P.interest) * (a₂ - a₁))
        ≤ P.stageConsumption k z a₂ - P.stageConsumption k z a₁ := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hT0 : 0 < P.patience γ := P.patience_pos' hγ0 hβ
  have hTneg : (P.patience γ) ^ (-γ) = ((P.discount : ℝ) * (1 + P.interest))⁻¹ := by
    rw [patience, ← Real.rpow_mul hβR0.le,
      show (1 / γ) * (-γ) = -1 from by field_simp, Real.rpow_neg_one]
  have hTpow : (P.patience γ) ^ γ = (P.discount : ℝ) * (1 + P.interest) := by
    have h := hTneg
    rw [Real.rpow_neg hT0.le] at h
    have := congrArg (·⁻¹) h
    simpa [inv_inv] using this
  induction k with
  | zero =>
    intro z a₁ a₂ ha₁ ha₂ hle
    rw [P.stageConsumption_sub_zero ha₁ ha₂ z]
    have : P.stageMPC γ 0 = 1 := rfl
    rw [this, one_mul]
  | succ k ih =>
    intro z a₁ a₂ ha₁ ha₂ hle
    set b₁ : ℝ := P.stagePolicy (k + 1) (a₁, z) with hb₁def
    set b₂ : ℝ := P.stagePolicy (k + 1) (a₂, z) with hb₂def
    have hb₁mem : b₁ ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
    have hb₂mem : b₂ ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
    have hble : b₁ ≤ b₂ := P.stagePolicy_mono (k + 1) ha₁ ha₂ hle
    set c₁ : ℝ := P.stageConsumption (k + 1) z a₁ with hc₁def
    set c₂ : ℝ := P.stageConsumption (k + 1) z a₂ with hc₂def
    have hc₁0 : 0 < c₁ := P.stageConsumption_pos hd _ z ha₁
    have hκ : 0 < P.stageMPC γ k := P.stageMPC_pos hγ0 hβ k
    set t : ℝ := P.stageMPC γ k * ((1 + P.interest) * (b₂ - b₁)) with htdef
    have ht0 : 0 ≤ t :=
      mul_nonneg hκ.le (mul_nonneg hR.le (sub_nonneg.2 hble))
    have hcb₁ : c₁ = P.resources (a₁, z) - b₁ := rfl
    have hcb₂ : c₂ = P.resources (a₂, z) - b₂ := rfl
    have hres : P.resources (a₂, z) - P.resources (a₁, z) = (1 + P.interest) * (a₂ - a₁) := by
      rw [P.resources_eq_of_mem ha₁ z, P.resources_eq_of_mem ha₂ z]; ring
    -- the key step: `c₁ + t / Þ ≤ c₂`
    have hkey : c₁ + t / P.patience γ ≤ c₂ := by
      rcases eq_or_lt_of_le hb₂mem.1 with hb0 | hb0
      · have hb₁0 : b₁ = 0 := le_antisymm (hb0 ▸ hble) hb₁mem.1
        have ht : t = 0 := by rw [htdef, ← hb0, hb₁0]; ring
        rw [ht, zero_div, add_zero]
        exact P.stageConsumption_mono (k + 1) ha₁ ha₂ hle
      · set C : Z → ℝ := fun z' => P.stageConsumption k z' b₁ with hCdef
        have hC0 : ∀ z', 0 < C z' := fun z' => P.stageConsumption_pos hd k z' hb₁mem
        have hw : ∀ z', 0 ≤ P.transitionMatrix z z' := P.transitionMatrix_nonneg z
        have hw1 : ∑ z', P.transitionMatrix z z' = 1 := P.transitionMatrix_sum z
        have hγne : (-γ) ≠ 0 := by intro h; linarith [neg_eq_zero.1 h]
        set M : ℝ := powerMean (P.transitionMatrix z) (-γ) C with hMdef
        have hM0 : 0 < M := powerMean_pos hw hw1 hC0
        have hMrpow : M ^ (-γ) = ∑ z', P.transitionMatrix z z' * (C z') ^ (-γ) :=
          powerMean_rpow hγne hw hw1 hC0
        -- from the Euler equation under the cap at `a₁`
        have heul₁ := P.stage_euler_le hu hd k z ha₁ (hslack (k + 1) a₁ ha₁ z)
        have hTc₁ : P.patience γ * c₁ ≤ M := by
          have h2 : M ^ (-γ) ≤ (P.patience γ * c₁) ^ (-γ) := by
            rw [Real.mul_rpow hT0.le hc₁0.le, hTneg, hMrpow]
            rw [inv_mul_eq_div, le_div_iff₀ hβR0]
            nlinarith [heul₁]
          exact le_of_rpow_neg_le hM0 (by positivity) hγ0 h2
        -- from the induction hypothesis and the Euler equation above the floor at `a₂`
        have hIH : ∀ z', C z' + t ≤ P.stageConsumption k z' b₂ := by
          intro z'
          have h := ih z' b₁ b₂ hb₁mem hb₂mem hble
          rw [hCdef, htdef]; linarith [h]
        have heul₂ := P.stage_euler_ge hu hd k z ha₂ hb0 (fun z' => hslack k b₂ hb₂mem z')
        have hsum : ∑ z', P.transitionMatrix z z' * (P.stageConsumption k z' b₂) ^ (-γ)
            ≤ ∑ z', P.transitionMatrix z z' * (C z' + t) ^ (-γ) :=
          Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left
            (rpow_neg_antitone hγ0 (by have := hC0 z'; linarith) (hIH z')) (hw z')
        have hsuper : M + t ≤ powerMean (P.transitionMatrix z) (-γ) (fun z' => C z' + t) :=
          powerMean_add_const_le (by linarith) hw hw1 hC0 ht0
        have hMt : ∑ z', P.transitionMatrix z z' * (C z' + t) ^ (-γ) ≤ (M + t) ^ (-γ) := by
          rw [← powerMean_rpow hγne hw hw1 (fun z' => by have := hC0 z'; linarith)]
          exact rpow_neg_antitone hγ0 (by positivity) hsuper
        have hTt : (M + t) ^ (-γ) ≤ (P.patience γ * c₁ + t) ^ (-γ) :=
          rpow_neg_antitone hγ0 (by positivity) (by linarith)
        have hchain : c₂ ^ (-γ)
            ≤ ((P.discount : ℝ) * (1 + P.interest)) * (P.patience γ * c₁ + t) ^ (-γ) := by
          have h := heul₂
          nlinarith [hsum, hMt, hTt, hβR0, hR]
        have hrew : ((P.discount : ℝ) * (1 + P.interest)) * (P.patience γ * c₁ + t) ^ (-γ)
            = (c₁ + t / P.patience γ) ^ (-γ) := by
          have hsplit : c₁ + t / P.patience γ = (P.patience γ * c₁ + t) / P.patience γ := by
            field_simp
          rw [hsplit, Real.div_rpow (by positivity) hT0.le, hTneg, ← hTpow]
          field_simp
        have hc₂0 : 0 < c₂ := P.stageConsumption_pos hd _ z ha₂
        have hpos : 0 < c₁ + t / P.patience γ :=
          add_pos_of_pos_of_nonneg hc₁0 (div_nonneg ht0 hT0.le)
        have hfin : c₂ ^ (-γ) ≤ (c₁ + t / P.patience γ) ^ (-γ) := by rw [← hrew]; exact hchain
        exact le_of_rpow_neg_le hc₂0 hpos hγ0 hfin
    -- clear denominators
    have hden : 0 < P.patience γ + P.stageMPC γ k * (1 + P.interest) := by positivity
    rw [P.stageMPC_succ, div_mul_eq_mul_div, div_le_iff₀ hden]
    have hb : b₂ - b₁ = (1 + P.interest) * (a₂ - a₁) - (c₂ - c₁) := by
      rw [hcb₁, hcb₂] at *; linarith [hres]
    have hk2 : t / P.patience γ ≤ c₂ - c₁ := by linarith [hkey]
    rw [htdef, hb] at hk2
    rw [div_le_iff₀ hT0] at hk2
    nlinarith [hk2, hT0, hκ, hR]

/-- **`cohortAssets` is Lipschitz in assets, with constant `cohortSlope`.** The same constant the
affine ceiling of `Existence` carries, now as a bound on DIFFERENCES rather than on levels, which is
what the increment argument accumulates. -/
theorem cohortAssets_sub_le_cohortSlope {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      P.stagePolicy j (b, w) < P.maxSaving (b, w))
    (k : ℕ) : ∀ (z : Z) (a₁ a₂ : ℝ), a₁ ∈ Icc (0 : ℝ) assetCap → a₂ ∈ Icc (0 : ℝ) assetCap →
      a₁ ≤ a₂ → P.cohortAssets k (a₂, z) - P.cohortAssets k (a₁, z)
        ≤ P.cohortSlope γ k * (a₂ - a₁) := by
  induction k with
  | zero =>
    intro z a₁ a₂ _ _ _
    have h₁ : P.cohortAssets 0 (a₁, z) = a₁ := P.cohortAssets_zero _
    have h₂ : P.cohortAssets 0 (a₂, z) = a₂ := P.cohortAssets_zero _
    rw [h₁, h₂, P.cohortSlope_zero, one_mul]
  | succ k ih =>
    intro z a₁ a₂ ha₁ ha₂ hle
    have hG : 0 < P.cohortSlope γ k := P.cohortSlope_pos hγ0 hβ k
    set b₁ : ℝ := P.stagePolicy (k + 1) (a₁, z) with hb₁def
    set b₂ : ℝ := P.stagePolicy (k + 1) (a₂, z) with hb₂def
    have hb₁mem : b₁ ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
    have hb₂mem : b₂ ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
    have hble : b₁ ≤ b₂ := P.stagePolicy_mono (k + 1) ha₁ ha₂ hle
    -- the propensity floor caps the saving increment
    have hb : b₂ - b₁ ≤ (1 - P.stageMPC γ (k + 1)) * ((1 + P.interest) * (a₂ - a₁)) := by
      have hc := P.stageMPC_mul_le_stageConsumption_sub hγ0 hu hβ hd hslack (k + 1) z a₁ a₂
        ha₁ ha₂ hle
      have hres : P.resources (a₂, z) - P.resources (a₁, z) = (1 + P.interest) * (a₂ - a₁) := by
        rw [P.resources_eq_of_mem ha₁ z, P.resources_eq_of_mem ha₂ z]; ring
      have e₁ : P.stageConsumption (k + 1) z a₁ = P.resources (a₁, z) - b₁ := rfl
      have e₂ : P.stageConsumption (k + 1) z a₂ = P.resources (a₂, z) - b₂ := rfl
      rw [e₁, e₂] at hc
      nlinarith [hres]
    -- the cohort step, against the induction hypothesis
    have hdiff : (∑ z', P.transitionMatrix z z' * P.cohortAssets k (b₂, z'))
        - (∑ z', P.transitionMatrix z z' * P.cohortAssets k (b₁, z'))
        ≤ P.cohortSlope γ k * (b₂ - b₁) := by
      rw [← Finset.sum_sub_distrib]
      calc ∑ z', (P.transitionMatrix z z' * P.cohortAssets k (b₂, z')
              - P.transitionMatrix z z' * P.cohortAssets k (b₁, z'))
          ≤ ∑ z', P.transitionMatrix z z' * (P.cohortSlope γ k * (b₂ - b₁)) := by
            refine Finset.sum_le_sum fun z' _ => ?_
            have := mul_le_mul_of_nonneg_left (ih z' b₁ b₂ hb₁mem hb₂mem hble)
              (P.transitionMatrix_nonneg z z')
            linarith [this]
        _ = P.cohortSlope γ k * (b₂ - b₁) := by
            rw [← Finset.sum_mul, P.transitionMatrix_sum z, one_mul]
    rw [P.cohortAssets_succ, P.cohortAssets_succ, P.cohortSlope_succ]
    simp only [stageStep]
    have hmul : P.cohortSlope γ k * (b₂ - b₁)
        ≤ P.cohortSlope γ k * ((1 - P.stageMPC γ (k + 1)) * ((1 + P.interest) * (a₂ - a₁))) :=
      mul_le_mul_of_nonneg_left hb hG.le
    nlinarith [hdiff, hmul]

end IncomeFluctuation

end LeanEconomics
