/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.PropensityFloor
import LeanEconomics.OLG.MassWeighted

/-!
# The increment of capital supply from a bound on the failure of Theorem 1

`Increment` bounds an abstract sequence; this file runs the same argument on the life-cycle
objects of `Equilibrium`, in the coordinate the mass weighting is exact in. Two economies `P`
(the lower rate) and `Q` (the higher rate) share the earnings process. Write `D_k(s)` for the
difference in a cohort's remaining life-cycle assets, `Q.cohortAssets k s - P.cohortAssets k s`.
One step of the recursion splits at the lower-rate saving:

  `D_{k+1}(a,z) = ∑_{z'} π(z,z') [A_Q(g_Q, z') - A_Q(g_P, z')] + ∑_{z'} π(z,z') D_k(g_P, z')`,

with `A_Q = Q.cohortAssets k`. The first bracket is at least `-G_k (g_P - g_Q)^+` by monotonicity
and the Lipschitz bound of `PropensityFloor`, and `(g_P - g_Q)^+ ≤ V_{k+1}(z)`, the failure of
Theorem 1 at stage `k+1` in earnings state `z`, worst case over the assets a cohort can hold
there. So with

  `F_0 = 0,  F_{k+1}(z) = G_k V_{k+1}(z) + ∑_{z'} π(z,z') F_k(z')`

we get `D_k(a,z) ≥ -F_k(z)` on the reachable regions (`cohortAssets_sub_ge_of_failure`), and
with `ν` invariant the `ν`-average of `F_K` telescopes to `∑_{k<K} G_k ∑_z ν_z V_{k+1}(z)`
(`sum_mul_failAccum`). Aggregate capital per head is the `ν`-average of `cohortAssets K (0, ·)`
over `K + 1` cohorts, so

  `Q.olgCapital - P.olgCapital ≥ -(∑_{k<K} G_k ∑_z ν_z V_{k+1}(z)) / (K + 1)`

(`olgCapital_sub_ge_of_failure`). This is the quantity the enclosure certificate computes; with
`lt_of_increment_bound` it gives single crossing.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- The accumulated failure bound in the earnings coordinate. -/
noncomputable def failAccum (G : ℕ → ℝ) (V : ℕ → Z → ℝ) : ℕ → Z → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun z => G k * V (k + 1) z + ∑ z', P.transitionMatrix z z' * failAccum G V k z'

@[simp] theorem failAccum_zero (G : ℕ → ℝ) (V : ℕ → Z → ℝ) (z : Z) :
    P.failAccum G V 0 z = 0 := rfl

theorem failAccum_succ (G : ℕ → ℝ) (V : ℕ → Z → ℝ) (k : ℕ) (z : Z) :
    P.failAccum G V (k + 1) z
      = G k * V (k + 1) z + ∑ z', P.transitionMatrix z z' * P.failAccum G V k z' := rfl

/-- **Life-cycle assets at the higher rate fall short by at most the accumulated failure.** The
regions are those of the lower-rate economy, which is the one whose saving the split is taken
at; `V` bounds the failure of Theorem 1 on them; `G` is a Lipschitz constant for the higher-rate
economy's remaining life-cycle assets. -/
theorem cohortAssets_sub_ge_of_failure {Q : IncomeFluctuation Z 0 assetCap}
    (hπ : Q.transitionMatrix = P.transitionMatrix) (R : P.StageRegions)
    {G : ℕ → ℝ} (hG : ∀ k, 0 ≤ G k)
    (K : ℕ) (hLip : ∀ k < K, ∀ (z : Z) (a₁ a₂ : ℝ), a₁ ∈ Icc (0 : ℝ) assetCap →
      a₂ ∈ Icc (0 : ℝ) assetCap → a₁ ≤ a₂ →
      Q.cohortAssets k (a₂, z) - Q.cohortAssets k (a₁, z) ≤ G k * (a₂ - a₁))
    {V : ℕ → Z → ℝ} (hV0 : ∀ k z, 0 ≤ V k z)
    (hV : ∀ k : ℕ, ∀ a ∈ R.region (k + 1), ∀ z : Z,
      P.stagePolicy (k + 1) (a, z) - Q.stagePolicy (k + 1) (a, z) ≤ V (k + 1) z)
    (k : ℕ) (hk : k ≤ K) : ∀ a ∈ R.region k, ∀ z : Z,
      -(P.failAccum G V k z) ≤ Q.cohortAssets k (a, z) - P.cohortAssets k (a, z) := by
  induction k with
  | zero => intro a _ z; simp [cohortAssets_zero]
  | succ k ih =>
    have ih := ih (Nat.le_of_succ_le hk)
    intro a ha z
    have haI : a ∈ Icc (0 : ℝ) assetCap := R.subset _ ha
    set gP := P.stagePolicy (k + 1) (a, z) with hgP
    set gQ := Q.stagePolicy (k + 1) (a, z) with hgQ
    have hgPreg : gP ∈ R.region k := R.maps k a ha z
    have hgPI : gP ∈ Icc (0 : ℝ) assetCap := R.subset _ hgPreg
    have hgQI : gQ ∈ Icc (0 : ℝ) assetCap := Q.stagePolicy_mem_region _ _
    -- the split of the one-step difference
    have hsplit : Q.cohortAssets (k + 1) (a, z) - P.cohortAssets (k + 1) (a, z)
        = ∑ z', P.transitionMatrix z z'
            * ((Q.cohortAssets k (gQ, z') - Q.cohortAssets k (gP, z'))
              + (Q.cohortAssets k (gP, z') - P.cohortAssets k (gP, z'))) := by
      simp only [cohortAssets_succ, stageStep, hπ, ← hgP, ← hgQ]
      have hterm : ∀ z', P.transitionMatrix z z'
            * ((Q.cohortAssets k (gQ, z') - Q.cohortAssets k (gP, z'))
              + (Q.cohortAssets k (gP, z') - P.cohortAssets k (gP, z')))
          = P.transitionMatrix z z' * Q.cohortAssets k (gQ, z')
            - P.transitionMatrix z z' * P.cohortAssets k (gP, z') := fun z' => by ring
      simp only [hterm, Finset.sum_sub_distrib]
      ring
    -- the first bracket, term by term
    have hterm1 : ∀ z', -(G k * V (k + 1) z)
        ≤ Q.cohortAssets k (gQ, z') - Q.cohortAssets k (gP, z') := by
      intro z'
      rcases le_or_gt gP gQ with hle | hlt
      · have := Q.monoRegion_cohortAssets k z' gP hgPI gQ hgQI hle
        have := mul_nonneg (hG k) (hV0 (k + 1) z)
        linarith
      · have h1 := hLip k (by omega) z' gQ gP hgQI hgPI hlt.le
        have h2 : gP - gQ ≤ V (k + 1) z := hV k a ha z
        have h3 := mul_le_mul_of_nonneg_left h2 (hG k)
        linarith
    have hterm2 : ∀ z', -(P.failAccum G V k z')
        ≤ Q.cohortAssets k (gP, z') - P.cohortAssets k (gP, z') :=
      fun z' => ih gP hgPreg z'
    have hsum : ∑ z', P.transitionMatrix z z'
          * (-(G k * V (k + 1) z) + -(P.failAccum G V k z'))
        ≤ ∑ z', P.transitionMatrix z z'
            * ((Q.cohortAssets k (gQ, z') - Q.cohortAssets k (gP, z'))
              + (Q.cohortAssets k (gP, z') - P.cohortAssets k (gP, z'))) :=
      Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left
        (add_le_add (hterm1 z') (hterm2 z')) (P.transitionMatrix_nonneg z z')
    have hlhs : ∑ z', P.transitionMatrix z z'
          * (-(G k * V (k + 1) z) + -(P.failAccum G V k z'))
        = -(P.failAccum G V (k + 1) z) := by
      rw [failAccum_succ]
      simp only [mul_add, Finset.sum_add_distrib, mul_neg, Finset.sum_neg_distrib,
        ← Finset.sum_mul, P.transitionMatrix_sum z]
      ring
    rw [hsplit, ← hlhs]
    exact hsum

/-- **The `ν`-average of the accumulated failure telescopes** when `ν` is invariant. -/
theorem sum_mul_failAccum {ν : Z → ℝ}
    (hinv : ∀ z' : Z, ∑ z, ν z * P.transitionMatrix z z' = ν z') (G : ℕ → ℝ) (V : ℕ → Z → ℝ) :
    ∀ K : ℕ, ∑ z, ν z * P.failAccum G V K z
      = ∑ k ∈ Finset.range K, G k * ∑ z, ν z * V (k + 1) z := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [failAccum_succ, mul_add, Finset.sum_add_distrib]
    have h := P.sum_mul_incomeStep hinv (P.failAccum G V K)
    simp only [incomeStep] at h
    rw [h, Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun z _ => by ring

/-- **Aggregate capital at the higher rate falls short by at most the accumulated failure.**
The newborn state `(0, z)` must lie in the region for the whole life. -/
theorem olgCapital_sub_ge_of_failure {Q : IncomeFluctuation Z 0 assetCap}
    (hπ : Q.transitionMatrix = P.transitionMatrix) (R : P.StageRegions)
    {G : ℕ → ℝ} (hG : ∀ k, 0 ≤ G k) (K : ℕ)
    (hLip : ∀ k < K, ∀ (z : Z) (a₁ a₂ : ℝ), a₁ ∈ Icc (0 : ℝ) assetCap →
      a₂ ∈ Icc (0 : ℝ) assetCap → a₁ ≤ a₂ →
      Q.cohortAssets k (a₂, z) - Q.cohortAssets k (a₁, z) ≤ G k * (a₂ - a₁))
    {V : ℕ → Z → ℝ} (hV0 : ∀ k z, 0 ≤ V k z)
    (hV : ∀ k : ℕ, ∀ a ∈ R.region (k + 1), ∀ z : Z,
      P.stagePolicy (k + 1) (a, z) - Q.stagePolicy (k + 1) (a, z) ≤ V (k + 1) z)
    (h0 : (0 : ℝ) ∈ R.region K) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z)
    (hinv : ∀ z' : Z, ∑ z, ν z * P.transitionMatrix z z' = ν z') :
    -((∑ k ∈ Finset.range K, G k * ∑ z, ν z * V (k + 1) z) / (K + 1))
      ≤ Q.olgCapital K ν - P.olgCapital K ν := by
  have hK : (0 : ℝ) < K + 1 := by positivity
  unfold olgCapital
  rw [← sub_div, ← P.sum_mul_failAccum hinv G V K, ← neg_div,
    div_le_div_iff_of_pos_right hK, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  have h := P.cohortAssets_sub_ge_of_failure hπ R hG K hLip hV0 hV K le_rfl 0 h0 z
  have := mul_le_mul_of_nonneg_left h (hν z)
  linarith

end IncomeFluctuation

end LeanEconomics
