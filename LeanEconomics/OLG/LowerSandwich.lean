/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.LifeCycle

/-!
# The lower half of the sandwich, with human wealth

Everything in this programme has reduced to one quantitative fact: a bound on consumption that is
tight to a few per cent rather than to a factor of ten. The upper half of the sandwich,
`c_k ≤ κ_k (m + H_k)`, is already good --- at Aiyagari's calibration it is about twenty per cent
above the truth --- because it carries the expected present value of future earnings. The lower
half, `κ_k m ≤ c_k`, is the weak one: it ignores future earnings entirely and is a factor of ten
below the truth. This file repairs it by the same device, carrying earnings forward across all
remaining ages rather than one step at a time.

## The bound

Let `H_k` be the present value of `k` periods of the *minimum* earnings, `H_0 = 0` and
`R H_{k+1} = y_min + H_k` (`minHumanWealth`). Then

  `Þ^k κ_k (m + H_k) ≤ c_k(m)`   (`minHumanWealth_le_stageConsumption`),

against the old `κ_k m`. The extra term is the household's guaranteed human wealth, and at
Aiyagari's numbers it raises the bound by a factor of about four.

## Why the patience factor is there, and why it is small

The induction alone would give `κ_k (m + H_k)`, with the same propensity as the upper bound, but
that is false: at the borrowing constraint the household consumes exactly its cash on hand, and
`κ_k (m + H_k)` exceeds it, because `H_k` discounts earnings at `R` while `1/κ_k` discounts at
`R/Þ`. Discounting `H_k` at `R/Þ` instead repairs the corner and breaks the induction. The factor
`Þ^k` repairs both at once (`stageMPC_mul_minHumanWealth_le`), and it costs almost nothing: at
`β = 0.96`, `r = 4%` and `μ = 3` it is `Þ^{59} ≈ 0.97`.

## What it is worth

At the state where the life cycle binds, zero wealth in the highest earnings state, the household
enters the next period with cash on hand about `2.0` and consumes about `0.88`. The old bound gives
`0.086`; this one gives `0.33`. Through `MPCBound` that improves the bound on the propensity to
consume from about `0.94` to about `0.75`, against a true propensity of `0.04`. So the gap is a
factor of four smaller and the conclusion is unchanged: what the argument needs is a lower bound
that carries the *expected* human wealth, not the minimum, and no Euler chain we have found
delivers that, because a household that draws the minimum forever really does consume this little.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **Guaranteed human wealth**: the present value of `k` periods of the minimum earnings. -/
noncomputable def minHumanWealth : ℕ → ℝ
  | 0 => 0
  | k + 1 => (P.minIncome + minHumanWealth k) / (1 + P.interest)

theorem minHumanWealth_succ (k : ℕ) :
    P.minHumanWealth (k + 1) = (P.minIncome + P.minHumanWealth k) / (1 + P.interest) := rfl

theorem minHumanWealth_nonneg (k : ℕ) : 0 ≤ P.minHumanWealth k := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [minHumanWealth_succ]
    exact div_nonneg (by linarith [P.minIncome_pos]) hR.le

/-- The propensity that goes with the lower bound: the finite-horizon propensity of `LifeCycle`
discounted once more by patience at each step, which is what makes the bound respect the
borrowing constraint. -/
noncomputable def lowMPC (γ : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => P.patience γ * lowMPC γ k * (1 + P.interest)
      / (P.patience γ + lowMPC γ k * (1 + P.interest))

theorem lowMPC_succ (γ : ℝ) (k : ℕ) : P.lowMPC γ (k + 1)
    = P.patience γ * P.lowMPC γ k * (1 + P.interest)
      / (P.patience γ + P.lowMPC γ k * (1 + P.interest)) := rfl

theorem lowMPC_pos {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    0 < P.lowMPC γ k := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hT := P.patience_pos' hγ0 hβ
  induction k with
  | zero => exact one_pos
  | succ k ih =>
    rw [lowMPC_succ]
    exact div_pos (by positivity) (by positivity)

/-- **The corner is respected**: the bound never exceeds what a household pinned at the borrowing
limit with the worst earnings can afford. This is what the extra patience factor buys. -/
theorem lowMPC_mul_minHumanWealth_le {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) ≤ 1) (k : ℕ) :
    P.lowMPC γ k * (P.minIncome + P.minHumanWealth k) ≤ P.minIncome := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hT0 : 0 < P.patience γ := P.patience_pos' hγ0 hβ
  have hT1 : P.patience γ ≤ 1 := by
    rw [patience]; exact Real.rpow_le_one (by positivity) hβR (by positivity)
  have hy : 0 < P.minIncome := P.minIncome_pos
  induction k with
  | zero => simp [minHumanWealth, lowMPC]
  | succ k ih =>
    have hμ := P.lowMPC_pos hγ0 hβ k
    have hH := P.minHumanWealth_nonneg k
    have hD : 0 < P.patience γ + P.lowMPC γ k * (1 + P.interest) := by positivity
    have hform : P.lowMPC γ (k + 1) * (P.minIncome + P.minHumanWealth (k + 1))
        = P.patience γ * P.lowMPC γ k
            * ((1 + P.interest) * P.minIncome + P.minIncome + P.minHumanWealth k)
          / (P.patience γ + P.lowMPC γ k * (1 + P.interest)) := by
      rw [lowMPC_succ, minHumanWealth_succ]
      field_simp
      ring
    rw [hform, div_le_iff₀ hD]
    nlinarith [ih, hT0, hT1, hμ, hH, hy, hR,
      mul_le_mul_of_nonneg_right hT1 (mul_nonneg (mul_nonneg hμ.le hR.le) hy.le),
      mul_le_mul_of_nonneg_left ih hT0.le]

/-- **The lower half of the sandwich, with human wealth.** Consumption is at least a fixed
propensity times cash on hand plus the present value of the minimum earnings still to come. The
old bound is the case `H = 0`. -/
theorem minHumanWealth_le_stageConsumption {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hβR : (P.discount : ℝ) * (1 + P.interest) ≤ 1) (hd : P.Unbounded)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, P.stagePolicy j (b, w) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.lowMPC γ k * (P.resources (a, z) + P.minHumanWealth k) ≤ P.stageConsumption k z a := by
  classical
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hT0 : 0 < P.patience γ := P.patience_pos' hγ0 hβ
  have hT1 : P.patience γ ≤ 1 := by
    rw [patience]; exact Real.rpow_le_one (by positivity) hβR (by positivity)
  have hTneg : P.patience γ ^ (-γ) = ((P.discount : ℝ) * (1 + P.interest))⁻¹ := by
    rw [patience, ← Real.rpow_mul (by positivity),
      show (1 / γ) * (-γ) = -1 from by field_simp, Real.rpow_neg_one]
  induction k generalizing a z with
  | zero =>
    rw [P.stageConsumption_zero ha z]
    simp [minHumanWealth, lowMPC]
  | succ k ih =>
    have hμ := P.lowMPC_pos hγ0 hβ k
    have hD : 0 < P.patience γ + P.lowMPC γ k * (1 + P.interest) := by positivity
    have hHk : 0 ≤ P.minHumanWealth (k + 1) := P.minHumanWealth_nonneg (k + 1)
    set A : ℝ := P.stagePolicy (k + 1) (a, z) with hA
    have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
    set c : ℝ := P.stageConsumption (k + 1) z a with hc
    have hc0 : 0 < c := P.stageConsumption_pos hd _ z ha
    have hcA : c = P.resources (a, z) - A := rfl
    have hm : P.minIncome ≤ P.resources (a, z) := by
      rw [P.resources_eq_of_mem ha z]
      have h1 := P.minIncome_le z
      have h2 : 0 ≤ (1 + P.interest) * a := mul_nonneg hR.le ha.1
      linarith
    rcases eq_or_lt_of_le hAmem.1 with hA0 | hA0
    · -- the corner
      have hcm : c = P.resources (a, z) := by rw [hcA, ← hA0, sub_zero]
      have hcorner := P.lowMPC_mul_minHumanWealth_le hγ0 hβ hβR (k + 1)
      have hμ1 : P.lowMPC γ (k + 1) ≤ 1 := by
        by_contra hcon
        rw [not_le] at hcon
        nlinarith [hcorner, hHk, P.minIncome_pos]
      rw [hcm]
      nlinarith [hcorner, hm, hμ1, hHk, P.lowMPC_pos hγ0 hβ (k + 1)]
    · -- interior
      have hslackA : ∀ w : Z, P.stagePolicy k (A, w) < P.maxSaving (A, w) := by
        intro w
        rw [maxSaving_eq]
        refine lt_min (hslack k A hAmem w) ?_
        have h0 : 0 < P.resources (A, w) - P.stagePolicy k (A, w) :=
          P.stageConsumption_pos hd k w hAmem
        linarith
      have hE := P.stage_euler_ge hu hd k z ha hA0 hslackA
      set X : ℝ := P.lowMPC γ k * ((1 + P.interest) * (A + P.minHumanWealth (k + 1))) with hX
      have hX0 : 0 < X := by
        rw [hX]
        have : 0 < A + P.minHumanWealth (k + 1) := by linarith
        positivity
      have hlow : ∀ w : Z, X ≤ P.stageConsumption k w A := by
        intro w
        refine le_trans ?_ (ih w hAmem)
        rw [hX, P.resources_eq_of_mem hAmem w, minHumanWealth_succ]
        have hy : P.minIncome ≤ P.income w := P.minIncome_le w
        have hfield : (1 + P.interest) * (A + (P.minIncome + P.minHumanWealth k)
            / (1 + P.interest)) = (1 + P.interest) * A + P.minIncome + P.minHumanWealth k := by
          field_simp
          ring
        rw [hfield]
        exact mul_le_mul_of_nonneg_left (by linarith) hμ.le
      have hsum : ∑ w, P.transitionMatrix z w * (P.stageConsumption k w A) ^ (-γ)
          ≤ X ^ (-γ) := by
        calc ∑ w, P.transitionMatrix z w * (P.stageConsumption k w A) ^ (-γ)
            ≤ ∑ w, P.transitionMatrix z w * X ^ (-γ) :=
              Finset.sum_le_sum fun w _ =>
                mul_le_mul_of_nonneg_left (rpow_neg_antitone hγ0 hX0 (hlow w))
                  (P.transitionMatrix_nonneg z w)
          _ = X ^ (-γ) := by rw [← Finset.sum_mul, P.transitionMatrix_sum z, one_mul]
      have hchain : c ^ (-γ) ≤ (P.discount : ℝ) * (1 + P.interest) * X ^ (-γ) := by
        have := le_trans hE (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsum hR.le) hβ.le)
        linarith [this]
      have hTc : (P.patience γ * c) ^ (-γ) ≤ X ^ (-γ) := by
        rw [Real.mul_rpow hT0.le hc0.le, hTneg, inv_mul_le_iff₀ (by positivity)]
        linarith [hchain]
      have hXTc : X ≤ P.patience γ * c := le_of_rpow_neg_le (by positivity) hX0 hγ0 hTc
      rw [hX, hcA] at hXTc
      have hstep2 : P.lowMPC γ k * (1 + P.interest)
          * (P.resources (a, z) + P.minHumanWealth (k + 1))
          ≤ c * (P.patience γ + P.lowMPC γ k * (1 + P.interest)) := by nlinarith [hXTc]
      have hL : 0 ≤ P.lowMPC γ k * (1 + P.interest)
          * (P.resources (a, z) + P.minHumanWealth (k + 1)) := by
        have hpos : 0 < P.resources (a, z) + P.minHumanWealth (k + 1) := by
          linarith [hm, hHk, P.minIncome_pos]
        positivity
      rw [lowMPC_succ, div_mul_eq_mul_div, div_le_iff₀ hD]
      nlinarith [hstep2, mul_nonneg (sub_nonneg.2 hT1) hL]

end IncomeFluctuation

end LeanEconomics
