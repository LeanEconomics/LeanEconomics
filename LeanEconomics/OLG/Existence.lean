/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.Continuity
import LeanEconomics.OLG.Incidence

/-!
# Both ends of the rate interval

`OLG.Continuity` proves that a stationary life-cycle equilibrium exists once capital supply is
known to lie below demand at the bottom of the rate interval and above it at the top. This file
proves those two inequalities.

The ceiling at the bottom uses feasibility alone. If an asset level `B` satisfies `R B + y_max ≤ B`
then a household starting below `B` stays below it, so over `K + 1` periods it accumulates at most
`(K + 1) B` and capital per head is at most `B`. No optimality, no sandwich, no slackness. Such a
`B` exists whenever `R < 1`, which is where a capital demand curve of the Cobb-Douglas kind is
large.

The floor at the top is an affine lower bound on a cohort's accumulated assets,
`F_k(z) + G_k a ≤ A_k(a, z)`, with a slope `G` common to all earnings states and an intercept `F`
that carries one value per state. The recursion is driven by the saving floor of `OLG.Equilibrium`,
read at the household's own earnings state rather than at the worst one. Reading it at the worst
state instead gives a floor that is identically zero in the calibration of the write-up, so the
state dependence is not a refinement but the whole content.

Because the intercept carries a vector rather than a scalar, aggregating needs nothing more than
one multiplication by the cohort's earnings weights. No stationary distribution over assets
appears anywhere, which is what makes the finite horizon so much cheaper than the stationary case.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### The ceiling, from feasibility alone -/

/-- **A forward-invariant asset level bounds a cohort's holdings.** If `R B + y_max ≤ B` then a
household that starts below `B` never leaves `[0, B]`, so the assets it holds over `k + 1` periods
sum to at most `(k + 1) B`. Only the budget is used. -/
theorem cohortAssets_le_of_invariant {B : ℝ} (hBcap : B ≤ assetCap)
    (hinv : (1 + P.interest) * B + P.maxIncome ≤ B) (k : ℕ) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) B) :
    P.cohortAssets k (a, z) ≤ ((k : ℝ) + 1) * B := by
  induction k generalizing z a with
  | zero => simpa [cohortAssets_zero] using ha.2
  | succ k ih =>
    have hmem : a ∈ Icc (0 : ℝ) assetCap := ⟨ha.1, le_trans ha.2 hBcap⟩
    have hR := P.interest_gt_neg_one
    have hgmem : P.stagePolicy (k + 1) (a, z) ∈ Icc (0 : ℝ) B := by
      refine ⟨(P.stagePolicy_mem_region _ _).1, ?_⟩
      have h1 : P.stagePolicy (k + 1) (a, z) ≤ P.resources (a, z) :=
        le_trans (P.policyOf_mem _ (a, z)).2 (P.maxSaving_le_resources (a, z))
      rw [P.resources_eq_of_mem hmem z] at h1
      have hy := P.le_maxIncome z
      nlinarith [ha.2]
    have hB0 : 0 ≤ B := le_trans hgmem.1 hgmem.2
    have hsum : ∑ z', P.transitionMatrix z z'
          * P.cohortAssets k (P.stagePolicy (k + 1) (a, z), z')
        ≤ ((k : ℝ) + 1) * B := by
      calc ∑ z', P.transitionMatrix z z'
              * P.cohortAssets k (P.stagePolicy (k + 1) (a, z), z')
          ≤ ∑ z', P.transitionMatrix z z' * (((k : ℝ) + 1) * B) :=
            Finset.sum_le_sum fun z' _ =>
              mul_le_mul_of_nonneg_left (ih z' hgmem) (P.transitionMatrix_nonneg z z')
        _ = ((k : ℝ) + 1) * B := by
            rw [← Finset.sum_mul, P.transitionMatrix_sum z, one_mul]
    rw [cohortAssets_succ, stageStep]
    push_cast
    linarith [ha.2, hsum]

/-- **A ceiling on aggregate capital.** Capital per head never exceeds a forward-invariant asset
level, whatever the household does. -/
theorem olgCapital_le_of_invariant {B : ℝ} (hB0 : 0 ≤ B) (hBcap : B ≤ assetCap)
    (hinv : (1 + P.interest) * B + P.maxIncome ≤ B) (K : ℕ) {ν : Z → ℝ}
    (hν : ∀ z, 0 ≤ ν z) (hν1 : ∑ z, ν z = 1) : P.olgCapital K ν ≤ B := by
  rw [olgCapital, div_le_iff₀ (by positivity)]
  calc ∑ z, ν z * P.cohortAssets K (0, z)
      ≤ ∑ z, ν z * (((K : ℝ) + 1) * B) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
          (P.cohortAssets_le_of_invariant hBcap hinv K z ⟨le_rfl, hB0⟩) (hν z)
    _ = ((K : ℝ) + 1) * B := by rw [← Finset.sum_mul, hν1, one_mul]
    _ = B * ((K : ℝ) + 1) := by ring

/-! ### A sharper ceiling, from the incidence bound

Feasibility says a household cannot carry forward more than its cash on hand. The
constraint-incidence bound of `OLG.Incidence` says it will not want to: it consumes at least
`κ_k(m + H_k(z))`, so it saves at most `(1 - κ_k)(y_z + Ra) - κ_k H_k(z)`. The forward-invariant
level that follows is roughly half the one feasibility gives, which widens the margin at the
bottom of the rate interval and lets that endpoint be taken closer to zero.

At Aiyagari's calibration (`numerics/ceiling.m`): at `r = -7%` feasibility gives `42.52` and the
incidence bound `22.17`, against a capital demand of `56.25`; and the highest low endpoint for
which the ceiling stays under demand rises from `-6.73%` to `-5.85%`.
-/

/-- **A forward-invariant level for the incidence bound.** The condition is that no household, at
any age or earnings state, saves past `B` when it starts there. -/
theorem cohortAssets_le_of_incidence {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, P.stagePolicy j (b, w) < assetCap)
    {B : ℝ} (hBcap : B ≤ assetCap)
    (hinv : ∀ j : ℕ, ∀ w : Z, (1 - P.stageMPC γ j) * (P.income w + (1 + P.interest) * B)
      - P.stageMPC γ j * P.riskHumanWealth γ j w ≤ B)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) B) :
    P.cohortAssets k (a, z) ≤ ((k : ℝ) + 1) * B := by
  induction k generalizing z a with
  | zero => simpa [cohortAssets_zero] using ha.2
  | succ k ih =>
    have hmem : a ∈ Icc (0 : ℝ) assetCap := ⟨ha.1, le_trans ha.2 hBcap⟩
    have hR := P.interest_gt_neg_one
    have hκle := P.stageMPC_le_one hγ0 hβ (k + 1)
    have hgmem : P.stagePolicy (k + 1) (a, z) ∈ Icc (0 : ℝ) B := by
      refine ⟨(P.stagePolicy_mem_region _ _).1, ?_⟩
      have hb := P.riskHumanWealth_le_stageConsumption hγ0 hu hβ hd hslack (k + 1) z hmem
      rw [P.stageConsumption_eq, P.resources_eq_of_mem hmem z] at hb
      have hstep : P.stagePolicy (k + 1) (a, z)
          ≤ (1 - P.stageMPC γ (k + 1)) * (P.income z + (1 + P.interest) * a)
            - P.stageMPC γ (k + 1) * P.riskHumanWealth γ (k + 1) z := by nlinarith [hb]
      have hmono : (1 - P.stageMPC γ (k + 1)) * (P.income z + (1 + P.interest) * a)
          ≤ (1 - P.stageMPC γ (k + 1)) * (P.income z + (1 + P.interest) * B) :=
        mul_le_mul_of_nonneg_left
          (by nlinarith [ha.2, hR]) (sub_nonneg.2 hκle)
      linarith [hstep, hmono, hinv (k + 1) z]
    have hB0 : 0 ≤ B := le_trans hgmem.1 hgmem.2
    have hsum : ∑ z', P.transitionMatrix z z'
          * P.cohortAssets k (P.stagePolicy (k + 1) (a, z), z')
        ≤ ((k : ℝ) + 1) * B := by
      calc ∑ z', P.transitionMatrix z z'
              * P.cohortAssets k (P.stagePolicy (k + 1) (a, z), z')
          ≤ ∑ z', P.transitionMatrix z z' * (((k : ℝ) + 1) * B) :=
            Finset.sum_le_sum fun z' _ =>
              mul_le_mul_of_nonneg_left (ih z' hgmem) (P.transitionMatrix_nonneg z z')
        _ = ((k : ℝ) + 1) * B := by
            rw [← Finset.sum_mul, P.transitionMatrix_sum z, one_mul]
    rw [cohortAssets_succ, stageStep]
    push_cast
    linarith [ha.2, hsum]

/-- **The sharper ceiling on aggregate capital.** -/
theorem olgCapital_le_of_incidence {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, P.stagePolicy j (b, w) < assetCap)
    {B : ℝ} (hB0 : 0 ≤ B) (hBcap : B ≤ assetCap)
    (hinv : ∀ j : ℕ, ∀ w : Z, (1 - P.stageMPC γ j) * (P.income w + (1 + P.interest) * B)
      - P.stageMPC γ j * P.riskHumanWealth γ j w ≤ B)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) (hν1 : ∑ z, ν z = 1) : P.olgCapital K ν ≤ B := by
  rw [olgCapital, div_le_iff₀ (by positivity)]
  calc ∑ z, ν z * P.cohortAssets K (0, z)
      ≤ ∑ z, ν z * (((K : ℝ) + 1) * B) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
          (P.cohortAssets_le_of_incidence hγ0 hu hβ hd hslack hBcap hinv K z ⟨le_rfl, hB0⟩) (hν z)
    _ = ((K : ℝ) + 1) * B := by rw [← Finset.sum_mul, hν1, one_mul]
    _ = B * ((K : ℝ) + 1) := by ring

/-! ### The floor: an affine lower bound on accumulated assets -/

/-- The slope of the affine floor on a cohort's accumulated assets: how much an extra unit of
assets held now adds to everything the household holds from here on. -/
noncomputable def cohortSlope (γ : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => 1 + cohortSlope γ k * (1 - P.stageMPC γ (k + 1)) * (1 + P.interest)

@[simp] theorem cohortSlope_zero (γ : ℝ) : P.cohortSlope γ 0 = 1 := rfl

theorem cohortSlope_succ (γ : ℝ) (k : ℕ) :
    P.cohortSlope γ (k + 1)
      = 1 + P.cohortSlope γ k * (1 - P.stageMPC γ (k + 1)) * (1 + P.interest) := rfl

/-- The intercept of the affine floor, one value per earnings state. It is the state dependence
here that makes the bound useful: collapsed to the worst state it is vacuous. -/
noncomputable def cohortFloor (γ : ℝ) : ℕ → Z → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun z => (∑ z', P.transitionMatrix z z' * cohortFloor γ k z')
      + P.cohortSlope γ k * ((1 - P.stageMPC γ (k + 1)) * P.income z
        - P.stageMPC γ (k + 1) * P.stageHumanWealth (k + 1) z)

@[simp] theorem cohortFloor_zero (γ : ℝ) (z : Z) : P.cohortFloor γ 0 z = 0 := rfl

theorem cohortFloor_succ (γ : ℝ) (k : ℕ) (z : Z) :
    P.cohortFloor γ (k + 1) z
      = (∑ z', P.transitionMatrix z z' * P.cohortFloor γ k z')
        + P.cohortSlope γ k * ((1 - P.stageMPC γ (k + 1)) * P.income z
          - P.stageMPC γ (k + 1) * P.stageHumanWealth (k + 1) z) := rfl

theorem cohortSlope_pos {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    0 < P.cohortSlope γ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [P.cohortSlope_succ]
    have h1 : 0 ≤ 1 - P.stageMPC γ (k + 1) := sub_nonneg.2 (P.stageMPC_le_one hγ0 hβ (k + 1))
    have hR := P.interest_gt_neg_one
    nlinarith [mul_nonneg (mul_nonneg ih.le h1) hR.le]

/-- **The affine floor on accumulated assets.** At every stage, and at every asset level the
reachable family admits, a cohort holds at least `F_k(z) + G_k a` over the rest of its life. -/
theorem cohortFloor_add_mul_le_cohortAssets {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) (Rg : P.StageRegions)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Rg.region k) :
    P.cohortFloor γ k z + P.cohortSlope γ k * a ≤ P.cohortAssets k (a, z) := by
  induction k generalizing z a with
  | zero => simp [cohortAssets_zero]
  | succ k ih =>
    have hgmem : P.stagePolicy (k + 1) (a, z) ∈ Rg.region k := Rg.maps k a ha z
    have hsum : (∑ z', P.transitionMatrix z z' * P.cohortFloor γ k z')
          + P.cohortSlope γ k * P.stagePolicy (k + 1) (a, z)
        ≤ ∑ z', P.transitionMatrix z z'
            * P.cohortAssets k (P.stagePolicy (k + 1) (a, z), z') := by
      have hle : ∑ z', P.transitionMatrix z z'
            * (P.cohortFloor γ k z' + P.cohortSlope γ k * P.stagePolicy (k + 1) (a, z))
          ≤ ∑ z', P.transitionMatrix z z'
            * P.cohortAssets k (P.stagePolicy (k + 1) (a, z), z') :=
        Finset.sum_le_sum fun z' _ =>
          mul_le_mul_of_nonneg_left (ih z' hgmem) (P.transitionMatrix_nonneg z z')
      have hexp : ∑ z', P.transitionMatrix z z'
            * (P.cohortFloor γ k z' + P.cohortSlope γ k * P.stagePolicy (k + 1) (a, z))
          = (∑ z', P.transitionMatrix z z' * P.cohortFloor γ k z')
            + P.cohortSlope γ k * P.stagePolicy (k + 1) (a, z) := by
        rw [Finset.sum_congr rfl fun z' _ => mul_add (P.transitionMatrix z z')
            (P.cohortFloor γ k z') (P.cohortSlope γ k * P.stagePolicy (k + 1) (a, z)),
          Finset.sum_add_distrib, ← Finset.sum_mul, P.transitionMatrix_sum z, one_mul]
      linarith [hle, hexp.symm.le, hexp.le]
    have hfloor := P.le_stagePolicy_state_on hγ0 hu hβ hd Rg (k + 1) z ha
    have hslope := P.cohortSlope_pos hγ0 hβ k
    have hprod := mul_le_mul_of_nonneg_left hfloor hslope.le
    rw [cohortAssets_succ, stageStep, P.cohortFloor_succ, P.cohortSlope_succ]
    nlinarith [hsum, hprod]

/-- **A floor on aggregate capital**, in the primitives: the discount factor, the rate, the
earnings process and the horizon. -/
theorem le_olgCapital {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) (Rg : P.StageRegions) (K : ℕ)
    (h0 : (0 : ℝ) ∈ Rg.region K) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) :
    (∑ z, ν z * P.cohortFloor γ K z) / (K + 1) ≤ P.olgCapital K ν := by
  rw [olgCapital]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hν z)
  have h := P.cohortFloor_add_mul_le_cohortAssets hγ0 hu hβ hd Rg K z h0
  simpa using h

/-! ### A closed form for the slope

The slope `G` obeys `G_{k+1} = 1 + G_k(1-κ_{k+1})R`, whose coefficient depends on the age through
`κ`. Multiplying by the geometric sum `S_k = ∑_{i ≤ k} (Þ/R)^i` removes that dependence entirely:
since `κ_k S_k = 1` and `S_{k+1} = (Þ/R)S_k + 1`, the product `W_k = G_k S_k` satisfies
`W_{k+1} = S_{k+1} + Þ W_k`, a recursion with a constant coefficient. Then `S_{k+1} ≥ 1` gives
`W_k ≥ ∑_{j ≤ k} Þ^j`, and `(1 - Þ/R)S_k ≤ 1` turns that into a lower bound on `G_k` itself.

This is where the closed form for `κ_k` pays. Using only `κ_k ≥ 1 - Þ/R` and `G_k ≥ 1` the
resulting floor first exceeds Cobb-Douglas demand at an interest rate of about six hundred per
cent; using the bound below it does so at about eighteen.
-/

/-- Multiplying the slope by the geometric sum turns its recursion into one with a constant
coefficient, `W_{k+1} = S_{k+1} + Þ W_k`. -/
theorem cohortSlope_mul_mpcSum_succ {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    P.cohortSlope γ (k + 1) * P.mpcSum γ (k + 1)
      = P.mpcSum γ (k + 1) + P.patience γ * (P.cohortSlope γ k * P.mpcSum γ k) := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hκ := P.stageMPC_mul_mpcSum hγ0 hβ (k + 1)
  have hS := P.mpcSum_succ γ k
  have hqR : P.patience γ / (1 + P.interest) * (1 + P.interest) = P.patience γ :=
    div_mul_cancel₀ _ hR.ne'
  rw [P.cohortSlope_succ]
  linear_combination (-(P.cohortSlope γ k) * (1 + P.interest)) * hκ
    + (P.cohortSlope γ k * (1 + P.interest)) * hS
    + (P.cohortSlope γ k * P.mpcSum γ k) * hqR

/-- The constant-coefficient recursion is bounded below by the plain geometric sum in `Þ`. -/
theorem geomSum_le_cohortSlope_mul_mpcSum {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), P.patience γ ^ j) ≤ P.cohortSlope γ k * P.mpcSum γ k := by
  induction k with
  | zero => simp [cohortSlope, mpcSum]
  | succ k ih =>
    rw [P.cohortSlope_mul_mpcSum_succ hγ0 hβ k, geom_sum_succ]
    have h1 := P.one_le_mpcSum hγ0 hβ (k + 1)
    have hT := (P.patience_pos' hγ0 hβ).le
    nlinarith [mul_le_mul_of_nonneg_left ih hT]

/-- **A closed-form lower bound on the slope**, `G_k ≥ (1 - Þ/R) ∑_{j ≤ k} Þ^j`. It is the rate at
which `κ_k` settles that makes this available: the bound grows geometrically in `Þ`, where the
crude `G_k ≥ 1` does not grow at all. -/
theorem mul_geomSum_le_cohortSlope {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    (1 - P.patience γ / (1 + P.interest)) * (∑ j ∈ Finset.range (k + 1), P.patience γ ^ j)
      ≤ P.cohortSlope γ k := by
  have hG := P.cohortSlope_pos hγ0 hβ k
  have hT0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range (k + 1), P.patience γ ^ j :=
    Finset.sum_nonneg fun j _ => pow_nonneg (P.patience_pos' hγ0 hβ).le j
  have hTW := P.geomSum_le_cohortSlope_mul_mpcSum hγ0 hβ k
  have hcS := P.sub_mul_mpcSum_le_one hγ0 hβ k
  rcases le_or_gt (1 - P.patience γ / (1 + P.interest)) 0 with hc | hc
  · nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hTW hc.le
    have h2 := mul_le_mul_of_nonneg_left hcS hG.le
    nlinarith [h1, h2]

/-! ### The ceiling as an affine bound too

`olgCapital_le_of_incidence` bounds every age's assets by one forward-invariant level and so pays
`(K+1)B` for a cohort that is at zero when it is born, near zero when it dies, and near `B` only in
between. The floor does not make that mistake: it carries an affine bound with a slope common to
all states and an intercept per state, and aggregates once at the end. The ceiling can be built the
same way, from the same slope, with the saving *ceiling* in place of the saving floor.

The gain is large, because it replaces a worst case over ages by an average over them. At
`r = -7%` the invariant level is `22.17` and the affine ceiling `1.54`, against a true capital
supply of `0.64`. The bottom of the rate interval then rises from `-5.85%` to `+2.78%`, against an
absolute limit of `5.09%`, where capital supply meets demand.
-/

/-- The intercept of the affine ceiling on a cohort's accumulated assets, one value per earnings
state. The slope is the same `cohortSlope` the floor uses; only the per-age term differs, taking
the saving ceiling that the constraint-incidence bound gives rather than the saving floor. -/
noncomputable def cohortCeil (γ : ℝ) : ℕ → Z → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun z => (∑ z', P.transitionMatrix z z' * cohortCeil γ k z')
      + P.cohortSlope γ k * ((1 - P.stageMPC γ (k + 1)) * P.income z
        - P.stageMPC γ (k + 1) * P.riskHumanWealth γ (k + 1) z)

@[simp] theorem cohortCeil_zero (γ : ℝ) (z : Z) : P.cohortCeil γ 0 z = 0 := rfl

theorem cohortCeil_succ (γ : ℝ) (k : ℕ) (z : Z) :
    P.cohortCeil γ (k + 1) z
      = (∑ z', P.transitionMatrix z z' * P.cohortCeil γ k z')
        + P.cohortSlope γ k * ((1 - P.stageMPC γ (k + 1)) * P.income z
          - P.stageMPC γ (k + 1) * P.riskHumanWealth γ (k + 1) z) := rfl

/-- **The affine ceiling on accumulated assets.** -/
theorem cohortAssets_le_cohortCeil {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, P.stagePolicy j (b, w) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.cohortAssets k (a, z) ≤ P.cohortCeil γ k z + P.cohortSlope γ k * a := by
  induction k generalizing z a with
  | zero => simp [cohortAssets_zero]
  | succ k ih =>
    set A : ℝ := P.stagePolicy (k + 1) (a, z) with hA
    have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
    have hslope := P.cohortSlope_pos hγ0 hβ k
    have hsum : (∑ z', P.transitionMatrix z z' * P.cohortAssets k (A, z'))
        ≤ (∑ z', P.transitionMatrix z z' * P.cohortCeil γ k z') + P.cohortSlope γ k * A := by
      have hle : (∑ z', P.transitionMatrix z z' * P.cohortAssets k (A, z'))
          ≤ ∑ z', P.transitionMatrix z z' * (P.cohortCeil γ k z' + P.cohortSlope γ k * A) :=
        Finset.sum_le_sum fun z' _ =>
          mul_le_mul_of_nonneg_left (ih z' hAmem) (P.transitionMatrix_nonneg z z')
      have hexp : ∑ z', P.transitionMatrix z z'
            * (P.cohortCeil γ k z' + P.cohortSlope γ k * A)
          = (∑ z', P.transitionMatrix z z' * P.cohortCeil γ k z')
            + P.cohortSlope γ k * A := by
        rw [Finset.sum_congr rfl fun z' _ => mul_add (P.transitionMatrix z z')
            (P.cohortCeil γ k z') (P.cohortSlope γ k * A),
          Finset.sum_add_distrib, ← Finset.sum_mul, P.transitionMatrix_sum z, one_mul]
      linarith [hle, hexp.le, hexp.symm.le]
    have hceil : A ≤ (1 - P.stageMPC γ (k + 1)) * (P.income z + (1 + P.interest) * a)
        - P.stageMPC γ (k + 1) * P.riskHumanWealth γ (k + 1) z := by
      have hb := P.riskHumanWealth_le_stageConsumption hγ0 hu hβ hd hslack (k + 1) z ha
      rw [P.stageConsumption_eq, P.resources_eq_of_mem ha z] at hb
      nlinarith [hb]
    have hprod := mul_le_mul_of_nonneg_left hceil hslope.le
    rw [cohortAssets_succ, stageStep, P.cohortCeil_succ, P.cohortSlope_succ]
    nlinarith [hsum, hprod]

/-- **A ceiling on aggregate capital, averaged over ages rather than worst-cased.** -/
theorem olgCapital_le_cohortCeil {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, P.stagePolicy j (b, w) < assetCap)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) :
    P.olgCapital K ν ≤ (∑ z, ν z * P.cohortCeil γ K z) / (K + 1) := by
  rw [olgCapital]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hν z)
  have h := P.cohortAssets_le_cohortCeil hγ0 hu hβ hd hslack K z
    (⟨le_rfl, P.assetCap_nonneg⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) assetCap)
  simpa using h

/-! ### Why the floor needs a patient household

Aggregating the floor against earnings weights that the chain leaves alone turns the vector
recursion into a scalar one, and then the sign of each increment has an exact answer: the floor
rises if and only if the household is patient at that rate. That is why the provable floor of the
write-up is flat below `1/β - 1` and rises above it, and why the upper end of the rate interval
has to be taken above the rate of time preference.
-/

variable {ν : Z → ℝ}

/-- Averaging human wealth against stationary weights turns the vector recursion into the scalar
one, `R H̄_{k+1} = ȳ + H̄_k`. -/
theorem sum_mul_stageHumanWealth_succ
    (hst : ∀ z', ∑ z, ν z * P.transitionMatrix z z' = ν z') (k : ℕ) :
    (1 + P.interest) * ∑ z, ν z * P.stageHumanWealth (k + 1) z
      = (∑ z, ν z * P.income z) + ∑ z, ν z * P.stageHumanWealth k z := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have h1 : ∑ z, ν z * P.stageHumanWealth (k + 1) z
      = (∑ z', ν z' * (P.income z' + P.stageHumanWealth k z')) / (1 + P.interest) := by
    have h2 : ∀ z : Z, ν z * P.stageHumanWealth (k + 1) z
        = (∑ z', ν z * (P.transitionMatrix z z' * (P.income z' + P.stageHumanWealth k z')))
          / (1 + P.interest) := by
      intro z
      rw [stageHumanWealth_succ, mul_div_assoc', Finset.mul_sum]
    rw [Finset.sum_congr rfl fun z _ => h2 z, ← Finset.sum_div]
    refine congrArg (fun y => y / (1 + P.interest)) ?_
    calc ∑ z, ∑ z', ν z * (P.transitionMatrix z z' * (P.income z' + P.stageHumanWealth k z'))
        = ∑ z', ∑ z, (ν z * P.transitionMatrix z z')
            * (P.income z' + P.stageHumanWealth k z') := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun z' _ => Finset.sum_congr rfl fun z _ => by ring
      _ = ∑ z', (∑ z, ν z * P.transitionMatrix z z')
            * (P.income z' + P.stageHumanWealth k z') :=
          Finset.sum_congr rfl fun z' _ => (Finset.sum_mul _ _ _).symm
      _ = ∑ z', ν z' * (P.income z' + P.stageHumanWealth k z') :=
          Finset.sum_congr rfl fun z' _ => by rw [hst z']
  rw [h1, mul_div_cancel₀ _ (ne_of_gt hR)]
  rw [Finset.sum_congr rfl fun z _ => mul_add (ν z) (P.income z) (P.stageHumanWealth k z),
    Finset.sum_add_distrib]

/-- **The floor rises exactly when the household is patient.** With `ȳ` the average earnings and
`H̄_k` the average human wealth, `κ_k H̄_k ≤ (1 - κ_k) ȳ` as soon as `Þ ≥ 1`, that is as soon as
`β R ≥ 1`. The increment of the aggregate floor at each age is the slack in this inequality, so
below the rate of time preference the floor does not move and above it the floor climbs. -/
theorem stageMPC_mul_sum_stageHumanWealth_le {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hT : 1 ≤ P.patience γ) (hν : ∀ z, 0 ≤ ν z)
    (hst : ∀ z', ∑ z, ν z * P.transitionMatrix z z' = ν z') (k : ℕ) :
    P.stageMPC γ k * (∑ z, ν z * P.stageHumanWealth k z)
      ≤ (1 - P.stageMPC γ k) * (∑ z, ν z * P.income z) := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hY : 0 ≤ ∑ z, ν z * P.income z :=
    Finset.sum_nonneg fun z _ =>
      mul_nonneg (hν z) (lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z)).le
  induction k with
  | zero =>
    have h0 : P.stageMPC γ 0 = 1 := rfl
    have h1 : ∀ z : Z, P.stageHumanWealth 0 z = 0 := fun _ => rfl
    simp [h0, h1]
  | succ k ih =>
    have hκ := P.stageMPC_pos hγ0 hβ k
    have hden : 0 < P.patience γ + P.stageMPC γ k * (1 + P.interest) := by
      have := P.patience_pos' hγ0 hβ; positivity
    have hH := P.sum_mul_stageHumanWealth_succ hst k
    have hstep : P.stageMPC γ (k + 1) * (P.patience γ + P.stageMPC γ k * (1 + P.interest))
        = P.stageMPC γ k * (1 + P.interest) := by
      rw [stageMPC_succ]; field_simp
    have e1 : P.stageMPC γ (k + 1) * (∑ z, ν z * P.stageHumanWealth (k + 1) z)
          * (P.patience γ + P.stageMPC γ k * (1 + P.interest))
        = P.stageMPC γ k
          * ((∑ z, ν z * P.income z) + ∑ z, ν z * P.stageHumanWealth k z) := by
      rw [show P.stageMPC γ (k + 1) * (∑ z, ν z * P.stageHumanWealth (k + 1) z)
            * (P.patience γ + P.stageMPC γ k * (1 + P.interest))
          = (P.stageMPC γ (k + 1) * (P.patience γ + P.stageMPC γ k * (1 + P.interest)))
            * (∑ z, ν z * P.stageHumanWealth (k + 1) z) from by ring, hstep,
        show P.stageMPC γ k * (1 + P.interest) * (∑ z, ν z * P.stageHumanWealth (k + 1) z)
          = P.stageMPC γ k
            * ((1 + P.interest) * ∑ z, ν z * P.stageHumanWealth (k + 1) z) from by ring, hH]
    have e2 : (1 - P.stageMPC γ (k + 1)) * (∑ z, ν z * P.income z)
          * (P.patience γ + P.stageMPC γ k * (1 + P.interest))
        = (∑ z, ν z * P.income z) * P.patience γ := by
      rw [show (1 - P.stageMPC γ (k + 1)) * (∑ z, ν z * P.income z)
            * (P.patience γ + P.stageMPC γ k * (1 + P.interest))
          = (∑ z, ν z * P.income z)
            * ((P.patience γ + P.stageMPC γ k * (1 + P.interest))
              - P.stageMPC γ (k + 1)
                * (P.patience γ + P.stageMPC γ k * (1 + P.interest))) from by ring, hstep]
      ring
    refine le_of_mul_le_mul_right ?_ hden
    rw [e1, e2]
    nlinarith [ih, hY, hT, mul_le_mul_of_nonneg_left hT hY]

/-- The aggregate floor, averaged against stationary weights, never falls with age once the
household is patient. -/
theorem sum_mul_cohortFloor_succ
    (hst : ∀ z', ∑ z, ν z * P.transitionMatrix z z' = ν z') (γ : ℝ) (k : ℕ) :
    (∑ z, ν z * P.cohortFloor γ (k + 1) z)
      = (∑ z, ν z * P.cohortFloor γ k z)
        + P.cohortSlope γ k * ((1 - P.stageMPC γ (k + 1)) * (∑ z, ν z * P.income z)
          - P.stageMPC γ (k + 1) * (∑ z, ν z * P.stageHumanWealth (k + 1) z)) := by
  have hsplit : ∀ z : Z, ν z * P.cohortFloor γ (k + 1) z
      = (∑ z', ν z * (P.transitionMatrix z z' * P.cohortFloor γ k z'))
        + P.cohortSlope γ k * ((1 - P.stageMPC γ (k + 1)) * (ν z * P.income z)
          - P.stageMPC γ (k + 1) * (ν z * P.stageHumanWealth (k + 1) z)) := by
    intro z
    rw [P.cohortFloor_succ, mul_add, Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl fun z _ => hsplit z, Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) ?_ ?_
  · calc ∑ z, ∑ z', ν z * (P.transitionMatrix z z' * P.cohortFloor γ k z')
        = ∑ z', ∑ z, (ν z * P.transitionMatrix z z') * P.cohortFloor γ k z' := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun z' _ => Finset.sum_congr rfl fun z _ => by ring
      _ = ∑ z', (∑ z, ν z * P.transitionMatrix z z') * P.cohortFloor γ k z' :=
          Finset.sum_congr rfl fun z' _ => (Finset.sum_mul _ _ _).symm
      _ = ∑ z', ν z' * P.cohortFloor γ k z' :=
          Finset.sum_congr rfl fun z' _ => by rw [hst z']
  · rw [← Finset.mul_sum]
    refine congrArg (fun x => P.cohortSlope γ k * x) ?_
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **The aggregate floor climbs with age when the household is patient.** -/
theorem sum_mul_cohortFloor_mono {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hT : 1 ≤ P.patience γ) (hν : ∀ z, 0 ≤ ν z)
    (hst : ∀ z', ∑ z, ν z * P.transitionMatrix z z' = ν z') (k : ℕ) :
    (∑ z, ν z * P.cohortFloor γ k z) ≤ ∑ z, ν z * P.cohortFloor γ (k + 1) z := by
  rw [P.sum_mul_cohortFloor_succ hst γ k]
  have hslope := P.cohortSlope_pos hγ0 hβ k
  have h := P.stageMPC_mul_sum_stageHumanWealth_le hγ0 hβ hT hν hst (k + 1)
  nlinarith [hslope, h]

/-- The aggregate floor is nonnegative at every age when the household is patient, so the floor
never works against the existence argument. -/
theorem sum_mul_cohortFloor_nonneg {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hT : 1 ≤ P.patience γ) (hν : ∀ z, 0 ≤ ν z)
    (hst : ∀ z', ∑ z, ν z * P.transitionMatrix z z' = ν z') (k : ℕ) :
    0 ≤ ∑ z, ν z * P.cohortFloor γ k z := by
  induction k with
  | zero => simp
  | succ k ih => exact le_trans ih (P.sum_mul_cohortFloor_mono hγ0 hβ hT hν hst k)

/-! ### The floor in closed form

Everything in the increment now has a closed form. Average human wealth is `ȳ` times a geometric
sum in `R^{-1}`, the propensity is the reciprocal of a geometric sum in `Þ/R`, and the slope is
bounded below by a geometric sum in `Þ`. Putting them together turns the aggregate floor into an
explicit expression in the discount factor, the interest rate, average earnings and the horizon,
with no reference to the household's decisions and no recursion left to run.
-/

/-- The geometric sum in the gross return, `∑_{i ≤ k} R^{-i}`. -/
noncomputable def rateSum (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), (1 + P.interest)⁻¹ ^ i

/-- **Average human wealth in closed form**: `H̄_{k+1} = ȳ R^{-1} ∑_{i ≤ k} R^{-i}`. -/
theorem sum_mul_stageHumanWealth_eq
    (hst : ∀ z', ∑ z, ν z * P.transitionMatrix z z' = ν z') (k : ℕ) :
    (∑ z, ν z * P.stageHumanWealth (k + 1) z)
      = (∑ z, ν z * P.income z) * ((1 + P.interest)⁻¹ * P.rateSum k) := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  induction k with
  | zero =>
    have h := P.sum_mul_stageHumanWealth_succ hst 0
    have h0 : (∑ z, ν z * P.stageHumanWealth 0 z) = 0 :=
      Finset.sum_eq_zero fun z _ => mul_zero (ν z)
    rw [h0, add_zero] at h
    have hr : P.rateSum 0 = 1 := by simp [rateSum]
    rw [hr, mul_one]
    field_simp
    linear_combination h
  | succ k ih =>
    have h := P.sum_mul_stageHumanWealth_succ hst (k + 1)
    rw [ih] at h
    have hgs : P.rateSum (k + 1) = (1 + P.interest)⁻¹ * P.rateSum k + 1 := by
      simp only [rateSum]; exact geom_sum_succ
    rw [hgs]
    field_simp at h ⊢
    linarith [h]

/-- The increment of the aggregate floor, with the propensity and human wealth eliminated:
`(1-κ_{k+1})ȳ - κ_{k+1}H̄_{k+1} = κ_{k+1} ȳ ((Þ/R)S_k - R^{-1}U_k)`. -/
theorem floorStep_eq {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hst : ∀ z', ∑ z, ν z * P.transitionMatrix z z' = ν z') (k : ℕ) :
    (1 - P.stageMPC γ (k + 1)) * (∑ z, ν z * P.income z)
        - P.stageMPC γ (k + 1) * (∑ z, ν z * P.stageHumanWealth (k + 1) z)
      = P.stageMPC γ (k + 1) * (∑ z, ν z * P.income z)
        * (P.patience γ / (1 + P.interest) * P.mpcSum γ k
          - (1 + P.interest)⁻¹ * P.rateSum k) := by
  have hκ := P.stageMPC_mul_mpcSum hγ0 hβ (k + 1)
  have hS := P.mpcSum_succ γ k
  rw [P.sum_mul_stageHumanWealth_eq hst k]
  linear_combination (-(∑ z, ν z * P.income z)) * hκ
    + ((∑ z, ν z * P.income z) * P.stageMPC γ (k + 1)) * hS

/-- The two geometric sums are ordered when the household is patient, so the increment is
nonnegative and can be bounded below term by term. -/
theorem rateSum_le_mpcSum {γ : ℝ} (hT : 1 ≤ P.patience γ) (k : ℕ) :
    P.rateSum k ≤ P.mpcSum γ k := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (by positivity) ?_ i
  rw [div_eq_mul_inv]
  nlinarith [inv_pos.2 hR]

/-- **The aggregate floor in closed form.** Every factor is explicit in the primitives: the
geometric sum in `Þ` from the slope, the limiting propensity `1 - Þ/R`, average earnings, and the
gap between the two geometric sums. -/
theorem geomFloor_le_sum_mul_cohortFloor {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hT : 1 ≤ P.patience γ) (hq : P.patience γ ≤ 1 + P.interest) (hν : ∀ z, 0 ≤ ν z)
    (hst : ∀ z', ∑ z, ν z * P.transitionMatrix z z' = ν z') (K : ℕ) :
    (1 - P.patience γ / (1 + P.interest)) ^ 2 * (∑ z, ν z * P.income z)
        * (∑ k ∈ Finset.range K, (∑ j ∈ Finset.range (k + 1), P.patience γ ^ j)
            * (P.patience γ / (1 + P.interest) * P.mpcSum γ k
              - (1 + P.interest)⁻¹ * P.rateSum k))
      ≤ ∑ z, ν z * P.cohortFloor γ K z := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hY : 0 ≤ ∑ z, ν z * P.income z :=
    Finset.sum_nonneg fun z _ =>
      mul_nonneg (hν z) (lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z)).le
  induction K with
  | zero => simp
  | succ K ih =>
    have hgap : 0 ≤ P.patience γ / (1 + P.interest) * P.mpcSum γ K
        - (1 + P.interest)⁻¹ * P.rateSum K := by
      have h1 := P.rateSum_le_mpcSum hT K
      have h2 : (1 + P.interest)⁻¹ ≤ P.patience γ / (1 + P.interest) := by
        rw [div_eq_mul_inv]; nlinarith [inv_pos.2 hR]
      have h3 : (0 : ℝ) ≤ P.rateSum K :=
        Finset.sum_nonneg fun i _ => pow_nonneg (by positivity) i
      nlinarith [h1, h2, h3, inv_pos.2 hR]
    have hslope := P.mul_geomSum_le_cohortSlope hγ0 hβ K
    have hκ := P.minMPC_le_stageMPC hγ0 hβ (K + 1)
    have hmin : P.minMPC γ = 1 - P.patience γ / (1 + P.interest) := by
      have h : (1 - P.minMPC γ) * (1 + P.interest) = P.patience γ :=
        one_sub_minMPC_mul (P := P)
      rw [eq_sub_iff_add_eq, ← h]
      field_simp
      ring
    have hstep := P.floorStep_eq hγ0 hβ hst K
    have hT0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range (K + 1), P.patience γ ^ j :=
      Finset.sum_nonneg fun j _ => pow_nonneg (P.patience_pos' hγ0 hβ).le j
    rw [P.sum_mul_cohortFloor_succ hst γ K, hstep, Finset.sum_range_succ, mul_add]
    refine add_le_add ih ?_
    rw [hmin] at hκ
    have hc : (0 : ℝ) ≤ 1 - P.patience γ / (1 + P.interest) := by
      have := (div_le_one hR).2 hq
      linarith
    calc (1 - P.patience γ / (1 + P.interest)) ^ 2 * (∑ z, ν z * P.income z)
            * ((∑ j ∈ Finset.range (K + 1), P.patience γ ^ j)
              * (P.patience γ / (1 + P.interest) * P.mpcSum γ K
                - (1 + P.interest)⁻¹ * P.rateSum K))
        = ((1 - P.patience γ / (1 + P.interest))
              * (∑ j ∈ Finset.range (K + 1), P.patience γ ^ j))
            * ((1 - P.patience γ / (1 + P.interest)) * (∑ z, ν z * P.income z)
              * (P.patience γ / (1 + P.interest) * P.mpcSum γ K
                - (1 + P.interest)⁻¹ * P.rateSum K)) := by ring
      _ ≤ P.cohortSlope γ K
            * (P.stageMPC γ (K + 1) * (∑ z, ν z * P.income z)
              * (P.patience γ / (1 + P.interest) * P.mpcSum γ K
                - (1 + P.interest)⁻¹ * P.rateSum K)) := by
          refine mul_le_mul hslope ?_ (mul_nonneg (mul_nonneg hc hY) hgap)
            (P.cohortSlope_pos hγ0 hβ K).le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hκ hY) hgap

/-! ### Both ends at once -/

/-- **A stationary life-cycle equilibrium exists**, with both boundary inequalities discharged
rather than assumed.

At the bottom of the rate interval a forward-invariant asset level `B` caps capital supply, and
`B` need only be below capital demand there. At the top, the affine floor on accumulated assets
puts capital supply above demand, and the artefactual cap need only exceed what a lifetime of
feasible saving could reach. Neither hypothesis mentions the household's policy: both are
inequalities among the discount factor, the interest rate, the earnings process and the horizon.

The rate this produces generally lies above the rate of time preference, which is why the floor
has to be read on a reachable family (see `OLG.Reachable`) rather than on the whole capped
interval, where it would be vacuous. -/
theorem exists_olgEquilibrium_of_bounds {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) {rlo rhi : ℝ}
    (hlo : P.RateOK rlo) (hhi : P.RateOK rhi) (hle : rlo ≤ rhi)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) (hν1 : ∑ z, ν z = 1)
    {D : ℝ → ℝ} (hD : ContinuousOn D (Icc rlo rhi))
    {B : ℝ} (hB0 : 0 ≤ B) (hBcap : B ≤ assetCap)
    (hinv : (1 + rlo) * B + P.maxIncome ≤ B) (hBD : B ≤ D rlo)
    (hcap : (P.withRate rhi hhi).reach (K + 1) < assetCap)
    (hDfloor : D rhi ≤ (∑ z, ν z * (P.withRate rhi hhi).cohortFloor γ K z) / (K + 1)) :
    ∃ r ∈ Icc rlo rhi,
      (∑ z, ν z * P.augCohortAssets hlo.one_add_pos hle K ((0, r), z)) / (K + 1) = D r := by
  refine P.exists_olgEquilibrium hlo.one_add_pos hle K ν hD ?_ ?_
  · rw [P.olgSupply_eq hlo.one_add_pos hle (left_mem_Icc.2 hle) hlo K ν]
    exact le_trans ((P.withRate rlo hlo).olgCapital_le_of_invariant hB0 hBcap hinv K hν hν1) hBD
  · rw [P.olgSupply_eq hlo.one_add_pos hle (right_mem_Icc.2 hle) hhi K ν]
    refine le_trans hDfloor ?_
    refine (P.withRate rhi hhi).le_olgCapital hγ0 hu hβ hd
      ((P.withRate rhi hhi).reachRegions K hcap) K ?_ hν
    exact (P.withRate rhi hhi).mem_reachRegion (le_refl K) (by simp)

/-- The same statement read as an equilibrium of the economy at the rate found: at that rate the
capital the cohorts accumulate is the capital the firm demands. -/
theorem exists_olgEquilibrium_rate {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) {rlo rhi : ℝ}
    (hlo : P.RateOK rlo) (hhi : P.RateOK rhi) (hle : rlo ≤ rhi)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) (hν1 : ∑ z, ν z = 1)
    {D : ℝ → ℝ} (hD : ContinuousOn D (Icc rlo rhi))
    {B : ℝ} (hB0 : 0 ≤ B) (hBcap : B ≤ assetCap)
    (hinv : (1 + rlo) * B + P.maxIncome ≤ B) (hBD : B ≤ D rlo)
    (hcap : (P.withRate rhi hhi).reach (K + 1) < assetCap)
    (hDfloor : D rhi ≤ (∑ z, ν z * (P.withRate rhi hhi).cohortFloor γ K z) / (K + 1)) :
    ∃ r, ∃ hr : r ∈ Icc rlo rhi,
      (P.withRate r (P.rateOK_of_mem_Icc hlo hhi hr)).olgCapital K ν = D r := by
  obtain ⟨r, hr, heq⟩ := P.exists_olgEquilibrium_of_bounds hγ0 hu hβ hd hlo hhi hle K hν hν1 hD
    hB0 hBcap hinv hBD hcap hDfloor
  refine ⟨r, hr, ?_⟩
  rw [← P.olgSupply_eq hlo.one_add_pos hle hr (P.rateOK_of_mem_Icc hlo hhi hr) K ν]
  exact heq

/-- **Existence with both ends in closed form.** The floor hypothesis is now an inequality between
the demand curve and an explicit expression in the discount factor, the interest rate, average
earnings and the horizon: no recursion in the model is left to run, and nothing refers to the
household's decisions.

The two conditions on the patience factor at the top of the interval, `1 ≤ Þ ≤ R`, say that the
household is patient enough for the floor to climb and impatient enough for its propensity to
settle. Both hold on the interval any calibration of interest puts the equilibrium in. -/
theorem exists_olgEquilibrium_of_geomBounds {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) {rlo rhi : ℝ}
    (hlo : P.RateOK rlo) (hhi : P.RateOK rhi) (hle : rlo ≤ rhi)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) (hν1 : ∑ z, ν z = 1)
    (hst : ∀ z', ∑ z, ν z * P.transitionMatrix z z' = ν z')
    {D : ℝ → ℝ} (hD : ContinuousOn D (Icc rlo rhi))
    {B : ℝ} (hB0 : 0 ≤ B) (hBcap : B ≤ assetCap)
    (hinv : (1 + rlo) * B + P.maxIncome ≤ B) (hBD : B ≤ D rlo)
    (hcap : (P.withRate rhi hhi).reach (K + 1) < assetCap)
    (hT : 1 ≤ (P.withRate rhi hhi).patience γ)
    (hq : (P.withRate rhi hhi).patience γ ≤ 1 + rhi)
    (hDgeom : D rhi
      ≤ (1 - (P.withRate rhi hhi).patience γ / (1 + rhi)) ^ 2 * (∑ z, ν z * P.income z)
        * (∑ k ∈ Finset.range K,
            (∑ j ∈ Finset.range (k + 1), (P.withRate rhi hhi).patience γ ^ j)
              * ((P.withRate rhi hhi).patience γ / (1 + rhi)
                  * (P.withRate rhi hhi).mpcSum γ k
                - (1 + rhi)⁻¹ * (P.withRate rhi hhi).rateSum k)) / (K + 1)) :
    ∃ r, ∃ hr : r ∈ Icc rlo rhi,
      (P.withRate r (P.rateOK_of_mem_Icc hlo hhi hr)).olgCapital K ν = D r := by
  refine P.exists_olgEquilibrium_rate hγ0 hu hβ hd hlo hhi hle K hν hν1 hD hB0 hBcap hinv hBD
    hcap ?_
  refine le_trans hDgeom ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact (P.withRate rhi hhi).geomFloor_le_sum_mul_cohortFloor hγ0 hβ hT hq hν hst K

/-- **Existence with the sharper ceiling.** The same statement as
`exists_olgEquilibrium_of_bounds`, with the bottom of the interval handled by the
constraint-incidence bound rather than by feasibility. The household's behaviour enters only
through `κ` and `H`, both explicit recursions in the primitives, and the reward is a
forward-invariant level about half the size, which is what lets the low endpoint be taken closer
to zero.

The extra hypothesis is that the artefactual cap is slack at the low rate. Unlike at the top of
the interval that is not a vacuous demand: below the rate of time preference the capped interval
is forward invariant, which is exactly the case `OLG.Reachable` describes. -/
theorem exists_olgEquilibrium_of_sharpBounds {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) {rlo rhi : ℝ}
    (hlo : P.RateOK rlo) (hhi : P.RateOK rhi) (hle : rlo ≤ rhi)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) (hν1 : ∑ z, ν z = 1)
    {D : ℝ → ℝ} (hD : ContinuousOn D (Icc rlo rhi))
    (hslo : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate rlo hlo).stagePolicy j (b, w) < assetCap)
    {B : ℝ} (hB0 : 0 ≤ B) (hBcap : B ≤ assetCap)
    (hinv : ∀ j : ℕ, ∀ w : Z, (1 - (P.withRate rlo hlo).stageMPC γ j)
        * (P.income w + (1 + rlo) * B)
      - (P.withRate rlo hlo).stageMPC γ j * (P.withRate rlo hlo).riskHumanWealth γ j w ≤ B)
    (hBD : B ≤ D rlo)
    (hcap : (P.withRate rhi hhi).reach (K + 1) < assetCap)
    (hDfloor : D rhi ≤ (∑ z, ν z * (P.withRate rhi hhi).cohortFloor γ K z) / (K + 1)) :
    ∃ r, ∃ hr : r ∈ Icc rlo rhi,
      (P.withRate r (P.rateOK_of_mem_Icc hlo hhi hr)).olgCapital K ν = D r := by
  have hmain : ∃ r ∈ Icc rlo rhi,
      (∑ z, ν z * P.augCohortAssets hlo.one_add_pos hle K ((0, r), z)) / (K + 1) = D r := by
    refine P.exists_olgEquilibrium hlo.one_add_pos hle K ν hD ?_ ?_
    · rw [P.olgSupply_eq hlo.one_add_pos hle (left_mem_Icc.2 hle) hlo K ν]
      exact le_trans ((P.withRate rlo hlo).olgCapital_le_of_incidence hγ0 hu hβ hd hslo hB0
        hBcap hinv K hν hν1) hBD
    · rw [P.olgSupply_eq hlo.one_add_pos hle (right_mem_Icc.2 hle) hhi K ν]
      refine le_trans hDfloor ?_
      refine (P.withRate rhi hhi).le_olgCapital hγ0 hu hβ hd
        ((P.withRate rhi hhi).reachRegions K hcap) K ?_ hν
      exact (P.withRate rhi hhi).mem_reachRegion (le_refl K) (by simp)
  obtain ⟨r, hr, heq⟩ := hmain
  refine ⟨r, hr, ?_⟩
  rw [← P.olgSupply_eq hlo.one_add_pos hle hr (P.rateOK_of_mem_Icc hlo hhi hr) K ν]
  exact heq

/-- **Existence with both ends read the same way.** The two boundary conditions are now the same
shape: a weighted average over earnings states of an affine bound on a cohort's accumulated
assets, one built from the saving ceiling and one from the saving floor, sharing a slope. Nothing
refers to the household's decisions; `κ`, `H` and the two intercepts are explicit finite
recursions in the discount factor, the interest rate, the earnings process and the horizon.

Each half asks for what it can have. At the bottom the artefactual cap is slack, which holds below
the rate of time preference; at the top it cannot be, and the reachable family of `OLG.Reachable`
stands in. -/
theorem exists_olgEquilibrium_affine {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) {rlo rhi : ℝ}
    (hlo : P.RateOK rlo) (hhi : P.RateOK rhi) (hle : rlo ≤ rhi)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z)
    {D : ℝ → ℝ} (hD : ContinuousOn D (Icc rlo rhi))
    (hslo : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate rlo hlo).stagePolicy j (b, w) < assetCap)
    (hceil : (∑ z, ν z * (P.withRate rlo hlo).cohortCeil γ K z) / (K + 1) ≤ D rlo)
    (hcap : (P.withRate rhi hhi).reach (K + 1) < assetCap)
    (hfloor : D rhi ≤ (∑ z, ν z * (P.withRate rhi hhi).cohortFloor γ K z) / (K + 1)) :
    ∃ r, ∃ hr : r ∈ Icc rlo rhi,
      (P.withRate r (P.rateOK_of_mem_Icc hlo hhi hr)).olgCapital K ν = D r := by
  have hmain : ∃ r ∈ Icc rlo rhi,
      (∑ z, ν z * P.augCohortAssets hlo.one_add_pos hle K ((0, r), z)) / (K + 1) = D r := by
    refine P.exists_olgEquilibrium hlo.one_add_pos hle K ν hD ?_ ?_
    · rw [P.olgSupply_eq hlo.one_add_pos hle (left_mem_Icc.2 hle) hlo K ν]
      exact le_trans ((P.withRate rlo hlo).olgCapital_le_cohortCeil hγ0 hu hβ hd hslo K hν) hceil
    · rw [P.olgSupply_eq hlo.one_add_pos hle (right_mem_Icc.2 hle) hhi K ν]
      refine le_trans hfloor ?_
      refine (P.withRate rhi hhi).le_olgCapital hγ0 hu hβ hd
        ((P.withRate rhi hhi).reachRegions K hcap) K ?_ hν
      exact (P.withRate rhi hhi).mem_reachRegion (le_refl K) (by simp)
  obtain ⟨r, hr, heq⟩ := hmain
  refine ⟨r, hr, ?_⟩
  rw [← P.olgSupply_eq hlo.one_add_pos hle hr (P.rateOK_of_mem_Icc hlo hhi hr) K ν]
  exact heq

end IncomeFluctuation

end LeanEconomics
