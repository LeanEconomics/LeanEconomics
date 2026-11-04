/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Monotone
import LeanEconomics.KrusellSmith.Distribution

/-!
# Stochastic dominance in assets along the tree

Milestone MR2 of `MINIMAL_STATE_PLAN.md`. A distribution `ν'` **dominates** `ν` in assets
(`ν ≼ ν'`, `AssetDominates`) if every bounded continuous function that is nondecreasing in assets
for each idiosyncratic state (`AssetMono`) has a larger integral under `ν'`.

* `assetMono_expectedNext`: the expected next value of an asset-monotone function is
  asset-monotone, because saving is nondecreasing in assets (`policy_mono`) and the idiosyncratic
  transition does not depend on assets.
* `expectedNext_le`: it is larger along a path of prices at which every household saves more.
* **`nodeDist_dominates`**: if `ν ≼ ν'` and every household saves at least as much along `K'` as
  along `K`, then at every node the distribution from `ν'` along `K'` dominates the one from `ν`
  along `K`; so mean capital is larger at every node (`meanCapital_le`).

Both comparisons MR3 needs are cases: the same initial distribution with savings ordered by the
path, and the same path with ordered initial distributions.
-/

open Set MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- A function of the household's state that is nondecreasing in assets for each idiosyncratic
state. -/
def AssetMono (f : M.AState → ℝ) : Prop :=
  ∀ x y : M.AState, x.2 = y.2 → (x.1 : ℝ) ≤ y.1 → f x ≤ f y

/-- **Dominance in assets**: every bounded continuous asset-monotone function has a larger
integral. -/
def AssetDominates (ν ν' : Measure M.AState) : Prop :=
  ∀ f : M.AState →ᵇ ℝ, M.AssetMono f → ∫ x, f x ∂ν ≤ ∫ x, f x ∂ν'

theorem assetMono_assets : M.AssetMono M.assets := fun _ _ _ h => h

variable {M}

/-- Saving is nondecreasing in assets, at states with assets in range. -/
theorem policy_mono_assets (z₀ : Z) (K : List Z → ℝ × ℝ) {a b : ↥(Icc (0 : ℝ) M.assetCap)}
    (hab : (a : ℝ) ≤ b) (l : Label Z E) : M.policy z₀ K (a, l) ≤ M.policy z₀ K (b, l) := by
  have h := M.policy_mono z₀ K a.2 b.2 hab l
  simpa only [stateAt, M.clampAssets_of_mem a.2, M.clampAssets_of_mem b.2] using h

/-- **The expected next value of an asset-monotone function is asset-monotone.** -/
theorem assetMono_expectedNext (z₀ : Z) (K : List Z → ℝ × ℝ) (h : List Z) (z' : Z)
    {f : M.AState →ᵇ ℝ} (hf : M.AssetMono f) : M.AssetMono (M.expectedNext z₀ K h z' f) := by
  intro x y hxy hle
  change ∑ e', M.nextProb z₀ h z' e' x * f (M.nextA z₀ K h e' x)
    ≤ ∑ e', M.nextProb z₀ h z' e' y * f (M.nextA z₀ K h e' y)
  refine Finset.sum_le_sum fun e' _ => ?_
  have hp : M.nextProb z₀ h z' e' x = M.nextProb z₀ h z' e' y := by
    simp only [nextProb, hxy]
  rw [hp]
  refine mul_le_mul_of_nonneg_left (hf _ _ rfl ?_) (M.nextProb_nonneg z₀ h z' e' y)
  change (M.clampAssets (M.policy z₀ K (x.1, ⟨x.2.idio, h⟩)) : ℝ)
    ≤ M.clampAssets (M.policy z₀ K (y.1, ⟨y.2.idio, h⟩))
  rw [hxy]
  exact Subtype.coe_le_coe.2 (monotone_projIcc M.assetCap_pos.le (policy_mono_assets z₀ K hle _))

/-- **The expected next value is larger when every household saves more.** -/
theorem expectedNext_le (z₀ : Z) {K K' : List Z → ℝ × ℝ}
    (hpol : ∀ s, M.policy z₀ K s ≤ M.policy z₀ K' s) (h : List Z) (z' : Z)
    {f : M.AState →ᵇ ℝ} (hf : M.AssetMono f) (x : M.AState) :
    M.expectedNext z₀ K h z' f x ≤ M.expectedNext z₀ K' h z' f x := by
  change ∑ e', M.nextProb z₀ h z' e' x * f (M.nextA z₀ K h e' x)
    ≤ ∑ e', M.nextProb z₀ h z' e' x * f (M.nextA z₀ K' h e' x)
  refine Finset.sum_le_sum fun e' _ => mul_le_mul_of_nonneg_left (hf _ _ rfl ?_)
    (M.nextProb_nonneg z₀ h z' e' x)
  change (M.clampAssets (M.policy z₀ K (x.1, ⟨x.2.idio, h⟩)) : ℝ)
    ≤ M.clampAssets (M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩))
  exact Subtype.coe_le_coe.2 (monotone_projIcc M.assetCap_pos.le (hpol _))

/-- **Dominance propagates down the tree.** -/
theorem nodeDist_dominates (z₀ : Z) {ν ν' : Measure M.AState} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {K K' : List Z → ℝ × ℝ}
    (hpol : ∀ s, M.policy z₀ K s ≤ M.policy z₀ K' s) (hν : M.AssetDominates ν ν') :
    ∀ h, M.AssetDominates (M.nodeDist z₀ ν K h) (M.nodeDist z₀ ν' K' h)
  | [] => hν
  | z' :: h => by
    intro f hf
    have := M.isProbabilityMeasure_nodeDist z₀ ν K h
    have := M.isProbabilityMeasure_nodeDist z₀ ν' K' h
    change ∫ x, f x ∂(M.pushNode z₀ K h z' (M.nodeDist z₀ ν K h))
      ≤ ∫ x, f x ∂(M.pushNode z₀ K' h z' (M.nodeDist z₀ ν' K' h))
    rw [M.integral_pushNode z₀ K h z' _ f, M.integral_pushNode z₀ K' h z' _ f]
    calc ∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ ν K h)
        ≤ ∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ ν' K' h) :=
          nodeDist_dominates z₀ hpol hν h _ (assetMono_expectedNext z₀ K h z' hf)
      _ ≤ ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ ν' K' h) :=
          integral_mono ((M.expectedNext z₀ K h z' f).integrable _)
            ((M.expectedNext z₀ K' h z' f).integrable _) (expectedNext_le z₀ hpol h z' hf)

/-- **Mean capital is larger at every node** under dominance and higher saving. -/
theorem meanCapital_le (z₀ : Z) {ν ν' : Measure M.AState} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {K K' : List Z → ℝ × ℝ}
    (hpol : ∀ s, M.policy z₀ K s ≤ M.policy z₀ K' s) (hν : M.AssetDominates ν ν') (h : List Z) :
    M.meanCapital z₀ ν K h ≤ M.meanCapital z₀ ν' K' h :=
  nodeDist_dominates z₀ hpol hν h M.assets M.assetMono_assets

theorem AssetDominates.refl (ν : Measure M.AState) : M.AssetDominates ν ν := fun _ _ => le_rfl

end KSModel

end KrusellSmith

end LeanEconomics
