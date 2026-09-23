/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.Incidence
import LeanEconomics.OLG.Equilibrium

/-!
# The constraint-incidence bound, made asset-dependent

`Incidence` caps human wealth state by state at `(1/κ_k - 1) y_z`, the level a household at **zero
assets** can claim without the bound exceeding its cash on hand. `cap_necessary_of_corner` shows
that cap cannot be raised inside the affine class: at a state where a household with nothing is
against the borrowing limit, no bound of that shape may claim more. It also says what a sharper
bound needs, namely that human wealth depend on the assets held, and a lower bound on the
household's own asset path to support it.

That lower bound is now available. `le_stagePolicy_state_on` reads the saving floor at the
household's own earnings state rather than the worst, and at the states where the cap bites hardest
it is positive: a household in a high earnings state saves, so a period later it is no longer at
the corner, and the cap that applies to it then is the one for a household with assets.

So this file carries assets through the recursion. Writing `Φ_k(z, a)` for the saving floor,
clamped at zero,

  `G_0(z, a) = 0`,
  `G_{k+1}(z, a) = min ( M^z_{-γ}(y_w + G_k(w, Φ_{k+1}(z, a))) / R ,
                         (1/κ_{k+1} - 1)(y_z + R a) )`

(`assetHumanWealth`), and the bound is `κ_k (m + G_k(z, a)) ≤ c_k(a, z)`
(`assetHumanWealth_le_stageConsumption`). Both changes matter: the cap now grows with assets, and
the recursion evaluates tomorrow's human wealth at the assets the household will actually hold
rather than at zero.

## What it is worth

At Aiyagari's calibration (`numerics/assetdep.m`, `numerics/worstgrid.m`), against the truth over
the whole grid at three ages, the worst ratio of bound to truth improves from

* `0.606` to `0.746` at `r = 4%`,
* `0.237` to `0.350` at `r = -7%`,
* `0.760` to `0.857` at `r = 10%`,

and the new bound never exceeds the truth anywhere. The gain is largest exactly where the old
bound was weakest, at positive assets in low earnings states, where the zero-asset cap is most
conservative: at `r = 4%`, five units of assets and the lowest earnings, the ratio rises from
`0.621` to `0.835`.

What it does not improve is the ceiling on aggregate capital, where the binding state is the
highest earnings one and the cap was never active: the implied ceiling at `r = -7%` is `22.15`
against `22.17` for the old bound. That ceiling is still far better than the `39.66` feasibility
alone gives.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### The asset path the household is guaranteed -/

/-- The saving floor at the household's own earnings state, clamped at zero. -/
noncomputable def assetFloor (γ : ℝ) (k : ℕ) (z : Z) (a : ℝ) : ℝ :=
  max 0 ((1 - P.stageMPC γ k) * (P.income z + (1 + P.interest) * a)
    - P.stageMPC γ k * P.stageHumanWealth k z)

theorem assetFloor_nonneg (γ : ℝ) (k : ℕ) (z : Z) (a : ℝ) : 0 ≤ P.assetFloor γ k z a :=
  le_max_left _ _

theorem assetFloor_mono {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) (z : Z)
    {a b : ℝ} (hab : a ≤ b) : P.assetFloor γ k z a ≤ P.assetFloor γ k z b := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  refine max_le_max le_rfl ?_
  have h1 : (1 + P.interest) * a ≤ (1 + P.interest) * b :=
    mul_le_mul_of_nonneg_left hab hR.le
  have hκle := P.stageMPC_le_one hγ0 hβ k
  nlinarith

/-- **The floor is below the policy.** -/
theorem assetFloor_le_stagePolicy {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, P.stagePolicy j (b, w) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.assetFloor γ k z a ≤ P.stagePolicy k (a, z) := by
  refine max_le (P.stagePolicy_mem_region k (a, z)).1 ?_
  exact P.le_stagePolicy_state_on hγ0 hu hβ hd (P.allRegions hslack) k z ha

/-! ### Human wealth that knows the assets -/

/-- **Risk-adjusted human wealth, capped by the constraint's incidence at the assets held.** -/
noncomputable def assetHumanWealth (γ : ℝ) : ℕ → Z → ℝ → ℝ
  | 0 => fun _ _ => 0
  | k + 1 => fun z a => min
      (powerMean (P.transitionMatrix z) (-γ)
        (fun w => P.income w + assetHumanWealth γ k w (P.assetFloor γ (k + 1) z a))
        / (1 + P.interest))
      ((1 / P.stageMPC γ (k + 1) - 1) * (P.income z + (1 + P.interest) * a))

theorem assetHumanWealth_succ (γ : ℝ) (k : ℕ) (z : Z) (a : ℝ) :
    P.assetHumanWealth γ (k + 1) z a = min
      (powerMean (P.transitionMatrix z) (-γ)
        (fun w => P.income w + P.assetHumanWealth γ k w (P.assetFloor γ (k + 1) z a))
        / (1 + P.interest))
      ((1 / P.stageMPC γ (k + 1) - 1) * (P.income z + (1 + P.interest) * a)) := rfl

theorem assetHumanWealth_nonneg {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ)
    (z : Z) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ P.assetHumanWealth γ k z a := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  induction k generalizing z a with
  | zero => exact le_rfl
  | succ k ih =>
    rw [P.assetHumanWealth_succ]
    refine le_min ?_ ?_
    · refine div_nonneg ?_ hR.le
      refine (powerMean_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) ?_).le
      intro v
      have h1 : 0 < P.income v := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le v)
      have h2 := ih v (P.assetFloor_nonneg γ (k + 1) z a)
      linarith
    · have hκ1 := P.stageMPC_le_one hγ0 hβ (k + 1)
      have hκ0 := P.stageMPC_pos hγ0 hβ (k + 1)
      have hy : 0 < P.income z := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z)
      have hRa : 0 ≤ (1 + P.interest) * a := mul_nonneg hR.le ha
      have hinv : 1 ≤ 1 / P.stageMPC γ (k + 1) := by
        rw [le_div_iff₀ hκ0]; linarith
      nlinarith

/-- **More assets, more claimable human wealth.** -/
theorem assetHumanWealth_mono {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ)
    (z : Z) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    P.assetHumanWealth γ k z a ≤ P.assetHumanWealth γ k z b := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  induction k generalizing z a b with
  | zero => exact le_rfl
  | succ k ih =>
    rw [P.assetHumanWealth_succ, P.assetHumanWealth_succ]
    refine min_le_min ?_ ?_
    · refine div_le_div_of_nonneg_right ?_ hR.le
      refine powerMean_mono (by linarith) (P.transitionMatrix_nonneg z)
        (P.transitionMatrix_sum z) (fun v => ?_) (fun v => ?_) (fun v => ?_)
      · have h1 : 0 < P.income v := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le v)
        have := P.assetHumanWealth_nonneg hγ0 hβ k v (P.assetFloor_nonneg γ (k + 1) z a)
        linarith
      · have h1 : 0 < P.income v := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le v)
        have := P.assetHumanWealth_nonneg hγ0 hβ k v (P.assetFloor_nonneg γ (k + 1) z b)
        linarith
      · have := ih v (P.assetFloor_nonneg γ (k + 1) z a)
          (P.assetFloor_mono hγ0 hβ (k + 1) z hab)
        linarith
    · have hκ0 := P.stageMPC_pos hγ0 hβ (k + 1)
      have hκ1 := P.stageMPC_le_one hγ0 hβ (k + 1)
      have hinv : 1 ≤ 1 / P.stageMPC γ (k + 1) := by rw [le_div_iff₀ hκ0]; linarith
      have h1 : (1 + P.interest) * a ≤ (1 + P.interest) * b :=
        mul_le_mul_of_nonneg_left hab hR.le
      nlinarith

/-- The recursion read at any point above the floor. -/
theorem assetHumanWealth_le_powerMean {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (k : ℕ) (z : Z) {a A : ℝ} (hA : 0 ≤ A) (hfloor : P.assetFloor γ (k + 1) z a ≤ A) :
    P.assetHumanWealth γ (k + 1) z a
      ≤ powerMean (P.transitionMatrix z) (-γ)
          (fun v => P.income v + P.assetHumanWealth γ k v A) / (1 + P.interest) := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  rw [P.assetHumanWealth_succ]
  refine le_trans (min_le_left _ _) ?_
  refine div_le_div_of_nonneg_right ?_ hR.le
  refine powerMean_mono (by linarith) (P.transitionMatrix_nonneg z)
    (P.transitionMatrix_sum z) (fun v => ?_) (fun v => ?_) (fun v => ?_)
  · have h1 : 0 < P.income v := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le v)
    have := P.assetHumanWealth_nonneg hγ0 hβ k v (P.assetFloor_nonneg γ (k + 1) z a)
    linarith
  · have h1 : 0 < P.income v := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le v)
    have := P.assetHumanWealth_nonneg hγ0 hβ k v hA
    linarith
  · have := P.assetHumanWealth_mono hγ0 hβ k v (P.assetFloor_nonneg γ (k + 1) z a) hfloor
    linarith

/-- **The asset-dependent bound is never worse than the asset-free one.** Both changes push the
same way: the cap grows with assets, and tomorrow's human wealth is read at the assets the
household will hold rather than at zero. -/
theorem riskHumanWealth_le_assetHumanWealth {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (k : ℕ) (z : Z) {a : ℝ} (ha : 0 ≤ a) :
    P.riskHumanWealth γ k z ≤ P.assetHumanWealth γ k z a := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  induction k generalizing z a with
  | zero => exact le_rfl
  | succ k ih =>
    rw [P.riskHumanWealth_succ, P.assetHumanWealth_succ]
    refine min_le_min ?_ ?_
    · refine div_le_div_of_nonneg_right ?_ hR.le
      refine powerMean_mono (by linarith) (P.transitionMatrix_nonneg z)
        (P.transitionMatrix_sum z) (fun v => ?_) (fun v => ?_) (fun v => ?_)
      · have h1 : 0 < P.income v := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le v)
        have := P.riskHumanWealth_nonneg hγ0 hβ k v
        linarith
      · have h1 : 0 < P.income v := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le v)
        have := P.assetHumanWealth_nonneg hγ0 hβ k v (P.assetFloor_nonneg γ (k + 1) z a)
        linarith
      · have := ih v (P.assetFloor_nonneg γ (k + 1) z a)
        linarith
    · have hκ0 := P.stageMPC_pos hγ0 hβ (k + 1)
      have hκ1 := P.stageMPC_le_one hγ0 hβ (k + 1)
      have hinv : 1 ≤ 1 / P.stageMPC γ (k + 1) := by rw [le_div_iff₀ hκ0]; linarith
      have hRa : 0 ≤ (1 + P.interest) * a := mul_nonneg hR.le ha
      nlinarith

/-! ### The bound -/

/-- **The asset-dependent constraint-incidence bound.** -/
theorem assetHumanWealth_le_stageConsumption {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, P.stagePolicy j (b, w) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.stageMPC γ k * (P.resources (a, z) + P.assetHumanWealth γ k z a)
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
    simp [assetHumanWealth, stageMPC]
  | succ k ih =>
    have hκ := P.stageMPC_pos hγ0 hβ k
    have hκ1 := P.stageMPC_pos hγ0 hβ (k + 1)
    have hκle := P.stageMPC_le_one hγ0 hβ (k + 1)
    have hD : 0 < P.patience γ + P.stageMPC γ k * (1 + P.interest) := by positivity
    have hHk : 0 ≤ P.assetHumanWealth γ (k + 1) z a :=
      P.assetHumanWealth_nonneg hγ0 hβ (k + 1) z ha.1
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
      have hcap : P.assetHumanWealth γ (k + 1) z a
          ≤ (1 / P.stageMPC γ (k + 1) - 1) * P.resources (a, z) := by
        rw [P.assetHumanWealth_succ]
        refine le_trans (min_le_right _ _) (le_of_eq ?_)
        rw [P.resources_eq_of_mem ha z]
      have hkey : P.stageMPC γ (k + 1) * ((1 / P.stageMPC γ (k + 1) - 1) * P.resources (a, z))
          = (1 - P.stageMPC γ (k + 1)) * P.resources (a, z) := by field_simp
      rw [hcm]
      nlinarith [hcap, hkey, hκ1, hκle]
    · -- interior: one Euler step against the risk-adjusted mean
      have hpos : ∀ v : Z, 0 < P.income v + P.assetHumanWealth γ k v A := by
        intro v
        have h1 : 0 < P.income v := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le v)
        have h2 := P.assetHumanWealth_nonneg hγ0 hβ k v hAmem.1
        linarith
      set N : ℝ := powerMean (P.transitionMatrix z) (-γ)
        (fun v => P.income v + P.assetHumanWealth γ k v A) with hN
      have hN0 : 0 < N :=
        powerMean_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hpos
      have hRA : 0 ≤ (1 + P.interest) * A := mul_nonneg hR.le hAmem.1
      have hshift : N + (1 + P.interest) * A
          ≤ powerMean (P.transitionMatrix z) (-γ)
            (fun v => P.income v + P.assetHumanWealth γ k v A + (1 + P.interest) * A) :=
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
            * (P.income v + P.assetHumanWealth γ k v A + (1 + P.interest) * A)
          ≤ P.stageConsumption k v A := by
        intro v
        have := ih v hAmem
        rw [P.resources_eq_of_mem hAmem v] at this
        calc P.stageMPC γ k * (P.income v + P.assetHumanWealth γ k v A + (1 + P.interest) * A)
            = P.stageMPC γ k * (P.income v + (1 + P.interest) * A
              + P.assetHumanWealth γ k v A) := by ring
          _ ≤ P.stageConsumption k v A := this
      have hsum : ∑ v, P.transitionMatrix z v * (P.stageConsumption k v A) ^ (-γ)
          ≤ X ^ (-γ) := by
        have hstep : ∀ v : Z, (P.stageConsumption k v A) ^ (-γ)
            ≤ (P.stageMPC γ k * (P.income v + P.assetHumanWealth γ k v A
              + (1 + P.interest) * A)) ^ (-γ) :=
          fun v => rpow_neg_antitone hγ0
            (by have := hpos v; have := hRA; positivity) (hlow v)
        have h1 : ∑ v, P.transitionMatrix z v * (P.stageConsumption k v A) ^ (-γ)
            ≤ ∑ v, P.transitionMatrix z v
              * (P.stageMPC γ k * (P.income v + P.assetHumanWealth γ k v A
                + (1 + P.interest) * A)) ^ (-γ) :=
          Finset.sum_le_sum fun v _ =>
            mul_le_mul_of_nonneg_left (hstep v) (P.transitionMatrix_nonneg z v)
        refine h1.trans ?_
        -- pull out the propensity and recognise the power mean
        have h2 : ∀ v : Z, P.transitionMatrix z v
              * (P.stageMPC γ k * (P.income v + P.assetHumanWealth γ k v A
                + (1 + P.interest) * A)) ^ (-γ)
            = P.stageMPC γ k ^ (-γ) * (P.transitionMatrix z v
              * (P.income v + P.assetHumanWealth γ k v A + (1 + P.interest) * A) ^ (-γ)) := by
          intro v
          rw [Real.mul_rpow hκ.le (by have := hpos v; have := hRA; positivity)]; ring
        rw [Finset.sum_congr rfl fun v _ => h2 v, ← Finset.mul_sum]
        have h3 : ∑ v, P.transitionMatrix z v
              * (P.income v + P.assetHumanWealth γ k v A + (1 + P.interest) * A) ^ (-γ)
            = (powerMean (P.transitionMatrix z) (-γ)
              (fun v => P.income v + P.assetHumanWealth γ k v A + (1 + P.interest) * A)) ^ (-γ) :=
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
      have hfloorA : P.assetFloor γ (k + 1) z a ≤ A :=
        P.assetFloor_le_stagePolicy hγ0 hu hβ hd hslack (k + 1) z ha
      have hcapN : (1 + P.interest) * P.assetHumanWealth γ (k + 1) z a ≤ N := by
        have h := P.assetHumanWealth_le_powerMean hγ0 hβ k z hAmem.1 hfloorA
        rw [← hN, le_div_iff₀ hR] at h
        linarith [h]
      rw [hX, hcA] at hXTc
      rw [stageMPC_succ, div_mul_eq_mul_div, div_le_iff₀ hD]
      nlinarith [hXTc, hcapN, hκ, hR, hT0, hc0]

end IncomeFluctuation

end LeanEconomics
