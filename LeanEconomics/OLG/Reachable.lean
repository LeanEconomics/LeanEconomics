/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.LifeCycle

/-!
# What a cohort can reach

The finite-horizon sandwich of `OLG.LifeCycle` needs the artefactual asset cap to be slack where
the household is, and the convenient way to ask for that is slack on the whole capped interval
`Icc 0 assetCap`. That hypothesis is not innocent. The one-step bound gives
`a' ≤ (1 - κ_k)(R a + y_max)`, so `Icc 0 assetCap` is carried into itself only when
`(1 - κ_k) R < 1`, which is to say only below the rate of time preference. Above that rate a
household sitting at the cap wants to save past it, the cap binds, and the Euler inequality under
it is gone. There is then no cap at all for which the hypothesis is true, so any theorem carrying
it is vacuous at those rates. Stationary overlapping-generations equilibria in life-cycle
economies sit above the rate of time preference, which is exactly where the hypothesis is needed.

A cohort that begins life with nothing never goes near the top of the capped interval. This file
builds the family of regions it does visit and shows it is a `StageRegions`, so the sandwich
applies along a cohort's own path with no slackness assumption beyond one inequality on the cap.

The bound used is deliberately crude: only feasibility, `a' ≤ R a + y_max`, with none of the
damping that optimal saving supplies. That keeps it free of the sandwich it is used to prove,
which is what breaks the circularity. Its cost is a larger cap: at `r = 10%` over sixty periods
the crude bound reaches about `9044` where the optimal path reaches about `82`. Since the cap is
an artefact of the state space rather than an economic object, that is a fair trade.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### The crude reachable bound -/

/-- The most a household can hold after `j` periods of life, having started with nothing. Only
feasibility is used: whatever the household would like, it cannot carry forward more than its
cash on hand, so `a' ≤ R a + y_max`. -/
noncomputable def reach : ℕ → ℝ
  | 0 => 0
  | j + 1 => (1 + P.interest) * reach j + P.maxIncome

@[simp] theorem reach_zero : P.reach 0 = 0 := rfl

theorem reach_succ (j : ℕ) :
    P.reach (j + 1) = (1 + P.interest) * P.reach j + P.maxIncome := rfl

theorem reach_nonneg (j : ℕ) : 0 ≤ P.reach j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [P.reach_succ]
    have hR := P.interest_gt_neg_one
    have hy := P.maxIncome_pos
    nlinarith

theorem reach_mono : Monotone P.reach := by
  refine monotone_nat_of_le_succ fun j => ?_
  induction j with
  | zero => simpa [P.reach_succ] using P.maxIncome_pos.le
  | succ j ih =>
    have h1 := P.reach_succ (j + 1)
    have h2 := P.reach_succ j
    have h3 : (1 + P.interest) * P.reach j ≤ (1 + P.interest) * P.reach (j + 1) :=
      mul_le_mul_of_nonneg_left ih P.interest_gt_neg_one.le
    linarith

/-- **Feasibility caps saving by cash on hand.** The household with `k` periods left, holding no
more than the cohort can have reached, saves no more than the cohort can reach one period on. -/
theorem stagePolicy_le_reach_succ {j : ℕ} {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hab : a ≤ P.reach j) (k : ℕ) (z : Z) :
    P.stagePolicy k (a, z) ≤ P.reach (j + 1) := by
  have h1 : P.stagePolicy k (a, z) ≤ P.resources (a, z) :=
    le_trans (P.policyOf_mem _ (a, z)).2 (P.maxSaving_le_resources (a, z))
  rw [P.resources_eq_of_mem ha z] at h1
  have hy := P.le_maxIncome z
  have hR := P.interest_gt_neg_one
  rw [P.reach_succ]
  nlinarith

/-! ### The family a cohort visits -/

/-- The asset levels a cohort of length `K + 1` that started life with nothing can occupy at the
stage with `k` periods still to come: it has been alive `K - k` periods. Stages before the start
of life are empty. -/
noncomputable def reachRegion (K k : ℕ) : Set ℝ :=
  if k ≤ K then Icc (0 : ℝ) (P.reach (K - k)) else ∅

theorem reachRegion_of_le {K k : ℕ} (hk : k ≤ K) :
    P.reachRegion K k = Icc (0 : ℝ) (P.reach (K - k)) := by
  simp [reachRegion, hk]

theorem mem_reachRegion {K k : ℕ} (hk : k ≤ K) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (P.reach (K - k))) :
    a ∈ P.reachRegion K k := by rw [P.reachRegion_of_le hk]; exact ha

theorem reachRegion_subset {K k : ℕ} (hcap : P.reach (K + 1) < assetCap) :
    P.reachRegion K k ⊆ Icc (0 : ℝ) assetCap := by
  unfold reachRegion
  split_ifs with hk
  · exact Icc_subset_Icc_right (le_trans (P.reach_mono (by omega)) hcap.le)
  · exact empty_subset _

/-- **The regions a cohort visits form a reachable family.** The only hypothesis is that the
artefactual cap exceeds what a lifetime of feasible saving could reach. -/
noncomputable def reachRegions (K : ℕ) (hcap : P.reach (K + 1) < assetCap) : P.StageRegions where
  region := P.reachRegion K
  subset := fun _ => P.reachRegion_subset hcap
  maps := by
    intro k a ha z
    by_cases hk : k + 1 ≤ K
    · have hmem : a ∈ Icc (0 : ℝ) assetCap := P.reachRegion_subset hcap ha
      rw [P.reachRegion_of_le hk] at ha
      refine P.mem_reachRegion (by omega) ⟨(P.stagePolicy_mem_region _ _).1, ?_⟩
      have h := P.stagePolicy_le_reach_succ hmem ha.2 (k + 1) z
      have he : K - (k + 1) + 1 = K - k := by omega
      rwa [he] at h
    · simp [reachRegion, hk] at ha
  slack := by
    intro k a ha z
    by_cases hk : k ≤ K
    · have hmem : a ∈ Icc (0 : ℝ) assetCap := P.reachRegion_subset hcap ha
      rw [P.reachRegion_of_le hk] at ha
      exact lt_of_le_of_lt (le_trans (P.stagePolicy_le_reach_succ hmem ha.2 k z)
        (P.reach_mono (by omega))) hcap
    · simp [reachRegion, hk] at ha

@[simp] theorem reachRegions_region (K : ℕ) (hcap : P.reach (K + 1) < assetCap) (k : ℕ) :
    (P.reachRegions K hcap).region k = P.reachRegion K k := rfl

/-! ### The sandwich along a cohort's own path -/

variable {γ : ℝ}

/-- **The minimal-MPC bound along a cohort's path**: `κ_k · m ≤ c_k(a, z)`, assuming nothing
about the artefactual cap beyond `reach (K + 1) < assetCap`. -/
theorem stageMPC_mul_le_stageConsumption_reach (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) {K : ℕ}
    (hcap : P.reach (K + 1) < assetCap) {k : ℕ} (hk : k ≤ K) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) (P.reach (K - k))) :
    P.stageMPC γ k * P.resources (a, z) ≤ P.stageConsumption k z a :=
  P.stageMPC_mul_le_stageConsumption_on hγ0 hu hβ hd (P.reachRegions K hcap) k z
    (P.mem_reachRegion hk ha)

/-- **The upper sandwich along a cohort's path**: `c_k(a, z) ≤ κ_k · (m + H_k(z))`, assuming
nothing about the artefactual cap beyond `reach (K + 1) < assetCap`. This is the bound the
equilibrium saving floor is built from, and the one that used to be unavailable above the rate of
time preference. -/
theorem stageConsumption_le_stageHumanWealth_reach (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) {K : ℕ}
    (hcap : P.reach (K + 1) < assetCap) {k : ℕ} (hk : k ≤ K) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) (P.reach (K - k))) :
    P.stageConsumption k z a
      ≤ P.stageMPC γ k * (P.resources (a, z) + P.stageHumanWealth k z) :=
  P.stageConsumption_le_stageHumanWealth_on hγ0 hu hβ hd (P.reachRegions K hcap) k z
    (P.mem_reachRegion hk ha)

/-- **The one-step saving bound along a cohort's path**: `a' ≤ (1 - κ_k)(R a + y_max)`. -/
theorem stagePolicy_le_reach (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) {K : ℕ}
    (hcap : P.reach (K + 1) < assetCap) {k : ℕ} (hk : k ≤ K) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) (P.reach (K - k))) :
    P.stagePolicy k (a, z) ≤ (1 - P.stageMPC γ k) * ((1 + P.interest) * a + P.maxIncome) :=
  P.stagePolicy_le_on hγ0 hu hβ hd (P.reachRegions K hcap) k z (P.mem_reachRegion hk ha)

end IncomeFluctuation

end LeanEconomics
