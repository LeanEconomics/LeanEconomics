/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.LowerSandwich
import LeanEconomics.Analysis.PowerMean

/-!
# The constraint-incidence bound

`LowerSandwich` carries the *minimum* earnings across all remaining ages and reaches about thirty
per cent of the truth. The reason it stops there is visible in its statement: a household that
drew the minimum forever really would consume that little. What is wanted is a bound carrying the
earnings the household actually expects, and the obstruction is the borrowing constraint, since a
constrained household consumes its cash on hand and commands none of its future earnings.

This file carries both at once. Human wealth is accumulated by the **risk-adjusted** expectation,
the power mean with exponent `-μ` that the Euler equation itself produces, and then **capped**
state by state at the level the borrowing constraint permits:

  `H_0 = 0`,
  `H_{k+1}(z) = min ( M^z_{-μ}(y_w + H_k(w)) / R , (1/κ_{k+1} - 1) y_z )`

(`riskHumanWealth`), with `κ` the finite-horizon propensity of `LifeCycle`. The bound is then

  `κ_k (m + H_k(z)) ≤ c_k(a, z)`   (`riskHumanWealth_le_stageConsumption`),

and the cap is exactly the constraint's incidence: it binds in the low-earnings states, where a
household at zero assets is against the limit, and is slack everywhere else.

## What it is worth

At Aiyagari's calibration, in the first period of a sixty-period life
(\texttt{numerics/incidence.m}): the cap binds at the two lowest earnings states and nowhere else,
and the bound reaches

* `1.000` of the truth at the constrained corner, where it is exact;
* `0.877` of the truth at zero wealth in the highest earnings state, against `0.295` for the
  minimum-earnings bound;
* `0.83`--`0.89` across the middle and high earnings states.

So the consumption bound is now within about twelve per cent where it matters, against a factor of
three before, and it never exceeds the truth anywhere on the grid. It is the sharpest bound in the
development, and the mechanism is the one the numerical sections identified: the constraint acts
through where it binds, and bounding its incidence is what carries expected earnings into the
bound.

The propensity bound of `MPCBound` is not improved by it, because that bound is driven by the
worst earnings state next period, which is exactly where the cap binds.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

/-! ### Two facts about the power mean -/

variable {ι : Type*} [Fintype ι] {w : ι → ℝ} {p : ℝ}

theorem powerMean_const (hp : p ≠ 0) (hw1 : ∑ i, w i = 1) {a : ℝ}
    (ha : 0 < a) : powerMean w p (fun _ => a) = a := by
  have hrw : ∑ i, w i * a ^ p = a ^ p := by
    rw [← Finset.sum_mul, hw1, one_mul]
  simp only [powerMean, hrw]
  rw [← Real.rpow_mul ha.le, mul_one_div_cancel hp, Real.rpow_one]

/-- **Shifting every coordinate by a constant raises the mean by at least that constant.** The
power mean with a negative exponent is concave and homogeneous of degree one, hence
superadditive, and the mean of a constant is that constant. -/
theorem powerMean_add_const_le (hp : p < 0) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) {c : ℝ} (hc : 0 ≤ c) :
    powerMean w p x + c ≤ powerMean w p (fun i => x i + c) := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · simp
  have hp0 : p ≠ 0 := ne_of_lt hp
  have h2x : ∀ i, 0 < 2 * x i := fun i => by linarith [hx i]
  have hcst : ∀ _ : ι, (0 : ℝ) < 2 * c := fun _ => by linarith
  have hconc := powerMean_concave (w := w) (p := p) hp hw hw1 h2x hcst
    (θ := 1 / 2) (φ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have h1 : powerMean w p (fun i => 2 * x i) = 2 * powerMean w p x :=
    powerMean_smul hp0 (by norm_num) hw hw1 hx
  have h2 : powerMean w p (fun _ : ι => 2 * c) = 2 * c := by
    have := powerMean_const (w := w) (p := p) hp0 hw1 (a := 2 * c) (by linarith)
    simpa using this
  have h3 : (fun i => 1 / 2 * (2 * x i) + 1 / 2 * (2 * c)) = fun i => x i + c := by
    funext i; ring
  rw [h1, h2, h3] at hconc
  linarith

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **Risk-adjusted human wealth, capped by the constraint's incidence.** -/
noncomputable def riskHumanWealth (γ : ℝ) : ℕ → Z → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun z => min
      (powerMean (P.transitionMatrix z) (-γ)
        (fun w => P.income w + riskHumanWealth γ k w) / (1 + P.interest))
      ((1 / P.stageMPC γ (k + 1) - 1) * P.income z)

theorem riskHumanWealth_succ (γ : ℝ) (k : ℕ) (z : Z) :
    P.riskHumanWealth γ (k + 1) z = min
      (powerMean (P.transitionMatrix z) (-γ)
        (fun w => P.income w + P.riskHumanWealth γ k w) / (1 + P.interest))
      ((1 / P.stageMPC γ (k + 1) - 1) * P.income z) := rfl

theorem riskHumanWealth_nonneg {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ)
    (z : Z) : 0 ≤ P.riskHumanWealth γ k z := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  induction k generalizing z with
  | zero => exact le_rfl
  | succ k ih =>
    rw [riskHumanWealth_succ]
    refine le_min ?_ ?_
    · refine div_nonneg ?_ hR.le
      refine (powerMean_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) ?_).le
      intro v
      have h1 : 0 < P.income v := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le v)
      have h2 := ih v
      linarith
    · have hκ1 := P.stageMPC_le_one hγ0 hβ (k + 1)
      have hκ0 := P.stageMPC_pos hγ0 hβ (k + 1)
      have hy : 0 < P.income z := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z)
      have hinv : 1 ≤ 1 / P.stageMPC γ (k + 1) := by
        rw [le_div_iff₀ hκ0]; linarith
      nlinarith

/-- **The constraint-incidence bound.** Consumption is at least the finite-horizon propensity
times cash on hand plus risk-adjusted human wealth, capped where the borrowing constraint bites.
-/
theorem riskHumanWealth_le_stageConsumption {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, P.stagePolicy j (b, w) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.stageMPC γ k * (P.resources (a, z) + P.riskHumanWealth γ k z)
      ≤ P.stageConsumption k z a := by
  classical
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hT0 : 0 < P.patience γ := P.patience_pos' hγ0 hβ
  have hTneg : P.patience γ ^ (-γ) = ((P.discount : ℝ) * (1 + P.interest))⁻¹ := by
    rw [patience, ← Real.rpow_mul (by positivity),
      show (1 / γ) * (-γ) = -1 from by field_simp, Real.rpow_neg_one]
  induction k generalizing a z with
  | zero =>
    rw [P.stageConsumption_zero ha z]
    simp [riskHumanWealth, stageMPC]
  | succ k ih =>
    have hκ := P.stageMPC_pos hγ0 hβ k
    have hκ1 := P.stageMPC_pos hγ0 hβ (k + 1)
    have hκle := P.stageMPC_le_one hγ0 hβ (k + 1)
    have hD : 0 < P.patience γ + P.stageMPC γ k * (1 + P.interest) := by positivity
    have hHk : 0 ≤ P.riskHumanWealth γ (k + 1) z := P.riskHumanWealth_nonneg hγ0 hβ (k + 1) z
    set A : ℝ := P.stagePolicy (k + 1) (a, z) with hA
    have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
    set c : ℝ := P.stageConsumption (k + 1) z a with hc
    have hc0 : 0 < c := P.stageConsumption_pos hd _ z ha
    have hcA : c = P.resources (a, z) - A := rfl
    have hyz : 0 < P.income z := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z)
    have hm : P.income z ≤ P.resources (a, z) := by
      rw [P.resources_eq_of_mem ha z]
      have : 0 ≤ (1 + P.interest) * a := mul_nonneg hR.le ha.1
      linarith
    rcases eq_or_lt_of_le hAmem.1 with hA0 | hA0
    · -- the corner: the cap is exactly what makes the bound affordable
      have hcm : c = P.resources (a, z) := by rw [hcA, ← hA0, sub_zero]
      have hcap : P.riskHumanWealth γ (k + 1) z
          ≤ (1 / P.stageMPC γ (k + 1) - 1) * P.income z := by
        rw [riskHumanWealth_succ]; exact min_le_right _ _
      have hkey : P.stageMPC γ (k + 1) * ((1 / P.stageMPC γ (k + 1) - 1) * P.income z)
          = (1 - P.stageMPC γ (k + 1)) * P.income z := by field_simp
      rw [hcm]
      nlinarith [hcap, hkey, hm, hκ1, hκle]
    · -- interior: one Euler step against the risk-adjusted mean
      have hpos : ∀ v : Z, 0 < P.income v + P.riskHumanWealth γ k v := by
        intro v
        have h1 : 0 < P.income v := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le v)
        have h2 := P.riskHumanWealth_nonneg hγ0 hβ k v
        linarith
      set N : ℝ := powerMean (P.transitionMatrix z) (-γ)
        (fun v => P.income v + P.riskHumanWealth γ k v) with hN
      have hN0 : 0 < N :=
        powerMean_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hpos
      have hRA : 0 ≤ (1 + P.interest) * A := mul_nonneg hR.le hAmem.1
      have hshift : N + (1 + P.interest) * A
          ≤ powerMean (P.transitionMatrix z) (-γ)
            (fun v => P.income v + P.riskHumanWealth γ k v + (1 + P.interest) * A) :=
        powerMean_add_const_le (by linarith) (P.transitionMatrix_nonneg z)
          (P.transitionMatrix_sum z) hpos hRA
      have hslackA : ∀ v : Z, P.stagePolicy k (A, v) < P.maxSaving (A, v) := by
        intro v
        rw [maxSaving_eq]
        refine lt_min (hslack k A hAmem v) ?_
        have h0 : 0 < P.resources (A, v) - P.stagePolicy k (A, v) :=
          P.stageConsumption_pos hd k v hAmem
        linarith
      have hE := P.stage_euler_ge hu hd k z ha hA0 hslackA
      set X : ℝ := P.stageMPC γ k * (N + (1 + P.interest) * A) with hX
      have hX0 : 0 < X := by rw [hX]; positivity
      -- the Euler sum, bounded by the power mean
      have hlow : ∀ v : Z, P.stageMPC γ k
            * (P.income v + P.riskHumanWealth γ k v + (1 + P.interest) * A)
          ≤ P.stageConsumption k v A := by
        intro v
        have := ih v hAmem
        rw [P.resources_eq_of_mem hAmem v] at this
        calc P.stageMPC γ k * (P.income v + P.riskHumanWealth γ k v + (1 + P.interest) * A)
            = P.stageMPC γ k * (P.income v + (1 + P.interest) * A
              + P.riskHumanWealth γ k v) := by ring
          _ ≤ P.stageConsumption k v A := this
      have hsum : ∑ v, P.transitionMatrix z v * (P.stageConsumption k v A) ^ (-γ)
          ≤ X ^ (-γ) := by
        have hstep : ∀ v : Z, (P.stageConsumption k v A) ^ (-γ)
            ≤ (P.stageMPC γ k * (P.income v + P.riskHumanWealth γ k v
              + (1 + P.interest) * A)) ^ (-γ) :=
          fun v => rpow_neg_antitone hγ0
            (by have := hpos v; have := hRA; positivity) (hlow v)
        have h1 : ∑ v, P.transitionMatrix z v * (P.stageConsumption k v A) ^ (-γ)
            ≤ ∑ v, P.transitionMatrix z v
              * (P.stageMPC γ k * (P.income v + P.riskHumanWealth γ k v
                + (1 + P.interest) * A)) ^ (-γ) :=
          Finset.sum_le_sum fun v _ =>
            mul_le_mul_of_nonneg_left (hstep v) (P.transitionMatrix_nonneg z v)
        refine h1.trans ?_
        -- pull out the propensity and recognise the power mean
        have h2 : ∀ v : Z, P.transitionMatrix z v
              * (P.stageMPC γ k * (P.income v + P.riskHumanWealth γ k v
                + (1 + P.interest) * A)) ^ (-γ)
            = P.stageMPC γ k ^ (-γ) * (P.transitionMatrix z v
              * (P.income v + P.riskHumanWealth γ k v + (1 + P.interest) * A) ^ (-γ)) := by
          intro v
          rw [Real.mul_rpow hκ.le (by have := hpos v; have := hRA; positivity)]; ring
        rw [Finset.sum_congr rfl fun v _ => h2 v, ← Finset.mul_sum]
        have h3 : ∑ v, P.transitionMatrix z v
              * (P.income v + P.riskHumanWealth γ k v + (1 + P.interest) * A) ^ (-γ)
            = (powerMean (P.transitionMatrix z) (-γ)
              (fun v => P.income v + P.riskHumanWealth γ k v + (1 + P.interest) * A)) ^ (-γ) :=
          (powerMean_rpow (by linarith) (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z)
            (fun v => by have := hpos v; linarith)).symm
        rw [h3, hX, Real.mul_rpow hκ.le (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hκ.le _)
        exact rpow_neg_antitone hγ0 (by positivity) hshift
      have hchain : c ^ (-γ) ≤ (P.discount : ℝ) * (1 + P.interest) * X ^ (-γ) := by
        have := le_trans hE (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsum hR.le) hβ.le)
        linarith [this]
      have hTc : (P.patience γ * c) ^ (-γ) ≤ X ^ (-γ) := by
        rw [Real.mul_rpow hT0.le hc0.le, hTneg, inv_mul_le_iff₀ (by positivity)]
        linarith [hchain]
      have hXTc : X ≤ P.patience γ * c := le_of_rpow_neg_le (by positivity) hX0 hγ0 hTc
      -- the cap only lowers the target
      have hcapN : (1 + P.interest) * P.riskHumanWealth γ (k + 1) z ≤ N := by
        have h := min_le_left (powerMean (P.transitionMatrix z) (-γ)
          (fun v => P.income v + P.riskHumanWealth γ k v) / (1 + P.interest))
          ((1 / P.stageMPC γ (k + 1) - 1) * P.income z)
        rw [← riskHumanWealth_succ] at h
        rw [← hN] at h
        rw [le_div_iff₀ hR] at h
        linarith [h]
      rw [hX, hcA] at hXTc
      rw [stageMPC_succ, div_mul_eq_mul_div, div_le_iff₀ hD]
      nlinarith [hXTc, hcapN, hκ, hR, hT0, hc0]

end IncomeFluctuation

end LeanEconomics
