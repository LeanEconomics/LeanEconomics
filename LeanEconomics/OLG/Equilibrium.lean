/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.MeansTest
import LeanEconomics.OLG.Reachable
import LeanEconomics.Equilibrium.Bisection

/-!
# Stationary equilibrium of the life-cycle economy

Every cohort is born with no assets and an earnings state drawn from a fixed law `ν`, lives `J`
periods, and is replaced. The distribution of the youngest cohort is therefore **the same at
every interest rate**, which is what the infinite horizon could not offer, and the distribution
of every older cohort is that law pushed forward by the policies of the ages in between.

## No measure theory is needed

Because assets at birth are degenerate at zero, the whole aggregate is a finite composition. Let

  `(stageStep k h)(a, z) = ∑_{z'} π(z, z') · h(g_k(a, z), z')`

be the expectation of `h` next period for a household with `k` periods still to come
(`stageStep`). Then the assets a household holds over its whole life, summed across ages and
seen from its birth state, satisfy the backward recursion

  `A_0(a, z) = a`,   `A_{k+1}(a, z) = a + (stageStep (k+1) A_k)(a, z)`

(`cohortAssets`), and aggregate capital per head is `∑_z ν(z) A_{J-1}(0, z) / J`
(`olgCapital`). No pushforward measures, no Feller property, no stationary distribution and no
Doeblin condition: the equilibrium object is a finite sum of finite sums.

## The chain

Light's Theorem 2 is then an induction on age with two ingredients, and both are already proved.
Next period's assets rise with this period's, at each earnings state and for any continuation
(`policyOf_mono_of_lt`), so the class of functions increasing in assets is preserved by
`stageStep` (`monoRegion_stageStep`). And if the policies of two economies are ordered at every
stage, ordered functions stay ordered (`stageStep_le_stageStep`). Hence
`cohortAssets` is ordered (`cohortAssets_le`) and so is aggregate capital
(`olgCapital_le_of_stagePolicy_le`). Theorem 3 is then the usual single crossing against a
strictly decreasing demand (`olgEquilibriumRate_unique`).

What is assumed is exactly Light's Theorem 1, that saving rises with the rate at every age. The
numerical section of the write-up reports where that holds: at Aiyagari's calibration it does
for relative risk aversion up to about `3.4`, so this chain delivers his `μ = 3`.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### The expectation operator of one age -/

/-- The expected value of `h` next period, for a household with `k` periods still to come. -/
noncomputable def stageStep (k : ℕ) (h : ℝ × Z → ℝ) : ℝ × Z → ℝ :=
  fun s => ∑ z', P.transitionMatrix s.2 z' * h (P.stagePolicy k s, z')

/-- Functions increasing in assets at each earnings state, on the asset region. -/
def MonoRegion (assetCap : ℝ) (h : ℝ × Z → ℝ) : Prop :=
  ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ b ∈ Icc (0 : ℝ) assetCap, a ≤ b → h (a, z) ≤ h (b, z)

omit [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z] in
theorem monoRegion_fst : MonoRegion (Z := Z) assetCap (fun s => s.1) := fun _ _ _ _ _ h => h

omit [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z] in
theorem monoRegion_add {h h' : ℝ × Z → ℝ} (hh : MonoRegion assetCap h)
    (hh' : MonoRegion assetCap h') : MonoRegion assetCap (fun s => h s + h' s) :=
  fun z a ha b hb hab => add_le_add (hh z a ha b hb hab) (hh' z a ha b hb hab)

/-- **The operator preserves the monotone class.** Saving rises with assets, whatever the
continuation (`policyOf_mono_of_lt`), so an expectation of an increasing function is increasing.
-/
theorem monoRegion_stageStep {h : ℝ × Z → ℝ} (hh : MonoRegion assetCap h) (k : ℕ) :
    MonoRegion assetCap (P.stageStep k h) := by
  intro z a ha b hb hab
  refine Finset.sum_le_sum fun z' _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (P.transitionMatrix_nonneg z z')
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact hh z' _ (P.stagePolicy_mem_region k (a, z)) _ (P.stagePolicy_mem_region k (b, z))
      (P.policyOf_mono_of_lt (v := P.stageValue k) ha hb hlt)

/-- **Ordered policies keep ordered functions ordered.** -/
theorem stageStep_le_stageStep {Q : IncomeFluctuation Z 0 assetCap}
    (hπ : Q.transitionMatrix = P.transitionMatrix) {h h' : ℝ × Z → ℝ}
    (hh' : MonoRegion assetCap h') (hle : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → h s ≤ h' s)
    {k : ℕ} (hg : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap →
      P.stagePolicy k s ≤ Q.stagePolicy k s)
    (s : ℝ × Z) (hs : s.1 ∈ Icc (0 : ℝ) assetCap) :
    P.stageStep k h s ≤ Q.stageStep k h' s := by
  simp only [stageStep, hπ]
  refine Finset.sum_le_sum fun z' _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (P.transitionMatrix_nonneg s.2 z')
  calc h (P.stagePolicy k s, z') ≤ h' (P.stagePolicy k s, z') :=
        hle _ (P.stagePolicy_mem_region k s)
    _ ≤ h' (Q.stagePolicy k s, z') :=
        hh' z' _ (P.stagePolicy_mem_region k s) _ (Q.stagePolicy_mem_region k s) (hg s hs)

/-! ### The assets of a cohort over its life -/

/-- **The assets a household holds over the rest of its life**, summed across ages and seen from
its current state, when `k` periods are still to come. -/
noncomputable def cohortAssets : ℕ → (ℝ × Z → ℝ)
  | 0 => fun s => s.1
  | k + 1 => fun s => s.1 + P.stageStep (k + 1) (cohortAssets k) s

theorem cohortAssets_zero (s : ℝ × Z) : P.cohortAssets 0 s = s.1 := rfl

theorem cohortAssets_succ (k : ℕ) (s : ℝ × Z) :
    P.cohortAssets (k + 1) s = s.1 + P.stageStep (k + 1) (P.cohortAssets k) s := rfl

theorem monoRegion_cohortAssets (k : ℕ) : MonoRegion assetCap (P.cohortAssets k) := by
  induction k with
  | zero => exact monoRegion_fst
  | succ k ih =>
    exact monoRegion_add monoRegion_fst (P.monoRegion_stageStep ih (k + 1))

/-- **Ordered policies give ordered life-cycle assets.** -/
theorem cohortAssets_le {Q : IncomeFluctuation Z 0 assetCap}
    (hπ : Q.transitionMatrix = P.transitionMatrix)
    (hg : ∀ k : ℕ, ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap →
      P.stagePolicy k s ≤ Q.stagePolicy k s)
    (k : ℕ) (s : ℝ × Z) (hs : s.1 ∈ Icc (0 : ℝ) assetCap) :
    P.cohortAssets k s ≤ Q.cohortAssets k s := by
  induction k generalizing s with
  | zero => exact le_rfl
  | succ k ih =>
    rw [cohortAssets_succ, cohortAssets_succ]
    refine add_le_add le_rfl ?_
    exact P.stageStep_le_stageStep hπ (Q.monoRegion_cohortAssets k) (fun t ht => ih t ht)
      (fun t ht => hg (k + 1) t ht) s hs

/-! ### Aggregate capital -/

/-- **Aggregate capital per head** in a stationary life-cycle economy: every cohort is born with
no assets and an earnings state drawn from `ν`, lives `J = K + 1` periods, and cohorts have equal
weight. -/
noncomputable def olgCapital (K : ℕ) (ν : Z → ℝ) : ℝ :=
  (∑ z, ν z * P.cohortAssets K (0, z)) / (K + 1)

/-- **Light's Theorem 2 for the life cycle.** If saving rises with the rate at every age, so does
aggregate capital. The proof is an induction on age: no stationary distribution, no Doeblin
condition and no monotone transitions are needed, because the youngest cohort's distribution does
not depend on the rate. -/
theorem olgCapital_le_of_stagePolicy_le {Q : IncomeFluctuation Z 0 assetCap}
    (hπ : Q.transitionMatrix = P.transitionMatrix)
    (hg : ∀ k : ℕ, ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap →
      P.stagePolicy k s ≤ Q.stagePolicy k s)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) :
    P.olgCapital K ν ≤ Q.olgCapital K ν := by
  have hcap : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine Finset.sum_le_sum fun z _ => ?_
  exact mul_le_mul_of_nonneg_left (P.cohortAssets_le hπ hg K (0, z) ⟨le_rfl, hcap⟩) (hν z)

/-! ### A floor on saving, from primitives

In the infinite horizon the only floor on capital supply came from an ergodic identity that
loses a factor `‖u'‖²/Var`. The life cycle needs nothing of the kind: the upper sandwich of
`LifeCycle` bounds consumption above at every age, and what is not consumed is saved. -/

/-- **An affine floor on saving at every age, on a reachable family.** From `c_k ≤ κ_k (m + H_k)`
and `m ≥ y_min + R a`, what the household carries forward is at least
`(1 - κ_k)(y_min + R a) - κ_k H_k`. Iterated from zero assets at birth this is an explicit floor
on the assets of every cohort.

The floor is what the equilibrium argument needs at a high interest rate, and a high interest rate
is exactly where the artefactual cap cannot be slack everywhere. Stating it on a `StageRegions` is
what keeps it from being vacuous there. -/
theorem le_stagePolicy_on {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) (G : P.StageRegions)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ G.region k) :
    (1 - P.stageMPC γ k) * (P.minIncome + (1 + P.interest) * a)
        - P.stageMPC γ k * P.stageHumanWealth k z
      ≤ P.stagePolicy k (a, z) := by
  have hup := P.stageConsumption_le_stageHumanWealth_on hγ0 hu hβ hd G k z ha
  have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a :=
    P.resources_eq_of_mem (G.subset k ha) z
  have hy : P.minIncome ≤ P.income z := P.minIncome_le z
  have hκ1 : P.stageMPC γ k ≤ 1 := P.stageMPC_le_one hγ0 hβ k
  have hc : P.stageConsumption k z a = P.resources (a, z) - P.stagePolicy k (a, z) :=
    P.stageConsumption_eq k z a
  rw [hres] at hup hc
  nlinarith [mul_le_mul_of_nonneg_left hy (sub_nonneg.2 hκ1)]

/-- **The affine floor on saving when the cap is slack everywhere.** -/
theorem le_stagePolicy {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, P.stagePolicy k (a, z) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (1 - P.stageMPC γ k) * (P.minIncome + (1 + P.interest) * a)
        - P.stageMPC γ k * P.stageHumanWealth k z
      ≤ P.stagePolicy k (a, z) :=
  P.le_stagePolicy_on hγ0 hu hβ hd (P.allRegions hslack) k z ha

/-- **The affine floor on saving along a cohort's own path.** A cohort that starts life with
nothing satisfies the floor at every age it reaches, assuming only that the artefactual cap
exceeds what a lifetime of feasible saving could reach. Unlike `le_stagePolicy` this says
something at interest rates above the rate of time preference, where no cap is slack everywhere
and `le_stagePolicy`'s hypothesis cannot be met. -/
theorem le_stagePolicy_reach {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) {K : ℕ}
    (hcap : P.reach (K + 1) < assetCap) {k : ℕ} (hk : k ≤ K) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) (P.reach (K - k))) :
    (1 - P.stageMPC γ k) * (P.minIncome + (1 + P.interest) * a)
        - P.stageMPC γ k * P.stageHumanWealth k z
      ≤ P.stagePolicy k (a, z) :=
  P.le_stagePolicy_on hγ0 hu hβ hd (P.reachRegions K hcap) k z (P.mem_reachRegion hk ha)

/-! ### Uniqueness -/

/-- **Theorem 3: single crossing.** A capital supply that never falls with the rate meets a
strictly falling demand at most once. -/
theorem olgEquilibriumRate_unique {S D : ℝ → ℝ} {s : Set ℝ} (hS : MonotoneOn S s)
    (hD : StrictAntiOn D s) {r₁ r₂ : ℝ} (hr₁ : r₁ ∈ s) (hr₂ : r₂ ∈ s)
    (h₁ : S r₁ = D r₁) (h₂ : S r₂ = D r₂) : r₁ = r₂ := by
  have hmono := strictMonoOn_sub_of_monotoneOn_of_strictAntiOn hS hD
  have he₁ : (fun r => S r - D r) r₁ = 0 := by simp [h₁]
  have he₂ : (fun r => S r - D r) r₂ = 0 := by simp [h₂]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (hmono hr₁ hr₂ h) (by rw [he₁, he₂]; exact lt_irrefl 0)
  · exact absurd (hmono hr₂ hr₁ h) (by rw [he₁, he₂]; exact lt_irrefl 0)

end IncomeFluctuation

end LeanEconomics
