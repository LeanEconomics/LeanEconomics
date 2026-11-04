/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Sensitivity
import LeanEconomics.KrusellSmith.Distribution

/-!
# How far the distributions drift apart down the tree

Milestone M3 of the uniqueness argument (`UNIQUENESS_PLAN.md`). Two paths of capital and labour
`K, K'` from the same initial distribution give two trees of distributions. Test them against
functions that are `L`-Lipschitz in assets for each idiosyncratic state (`AssetLip`): the
distributions at node `h` differ by at most `L · D_h` (`integral_nodeDist_sub_le`), where

  `D_root = 0`,   `D_{z' :: h} = R̄ · D_h + P_h`,

and `P_h` bounds the difference between the two saving policies at `h` (`gapPath`). The induction
step is the duality of `integral_pushNode`: the pushed-forward test function is `R̄ L`-Lipschitz
(saving rises with assets at most at the gross return, `policy_sub_le`), and the two pushed-forward
functions differ by at most `L P_h`.

Mean assets is the test function with `L = 1`, so mean capital at `h` differs by at most `D_h`.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (z₀ : Z)

/-- A bounded continuous function on assets and idiosyncratic states that is `L`-Lipschitz in
assets for each idiosyncratic state. -/
def AssetLip (L : ℝ) (f : M.AState →ᵇ ℝ) : Prop :=
  ∀ (a b : ↥(Icc (0 : ℝ) M.assetCap)) (i : Idio E), |f (a, i) - f (b, i)| ≤ L * |(a : ℝ) - b|

theorem assetLip_assets : AssetLip 1 (M.assets : M.AState →ᵇ ℝ) := by
  intro a b i
  rw [one_mul]
  exact le_rfl

/-- Saving at a node moves with assets at most at the bound on the gross return. -/
theorem abs_policy_sub_le (K : List Z → ℝ × ℝ) (a b : ↥(Icc (0 : ℝ) M.assetCap))
    (l : Label Z E) :
    |M.policy z₀ K (a, l) - M.policy z₀ K (b, l)| ≤ M.returnBound * |(a : ℝ) - b| := by
  have ha : M.stateAt (a : ℝ) l = (a, l) := by
    simp only [stateAt, M.clampAssets_of_mem a.2]
  have hb : M.stateAt (b : ℝ) l = (b, l) := by
    simp only [stateAt, M.clampAssets_of_mem b.2]
  have hR := M.grossReturn_le (shockAt z₀ l.node) (K l.node).1 (K l.node).2
  have hR0 := M.grossReturn_nonneg (shockAt z₀ l.node) (K l.node).1 (K l.node).2
  rcases le_total (a : ℝ) b with hab | hab
  · have h1 := M.policy_mono z₀ K a.2 b.2 hab l
    have h2 := M.policy_sub_le z₀ K a.2 b.2 hab l
    rw [ha, hb] at h1 h2
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h1), abs_sub_comm, abs_of_nonneg (by linarith)]
    have : M.returnAt z₀ K l.node * ((b : ℝ) - a) ≤ M.returnBound * ((b : ℝ) - a) :=
      mul_le_mul_of_nonneg_right hR (by linarith)
    exact h2.trans this
  · have h1 := M.policy_mono z₀ K b.2 a.2 hab l
    have h2 := M.policy_sub_le z₀ K b.2 a.2 hab l
    rw [ha, hb] at h1 h2
    rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (by linarith)]
    have : M.returnAt z₀ K l.node * ((a : ℝ) - b) ≤ M.returnBound * ((a : ℝ) - b) :=
      mul_le_mul_of_nonneg_right hR (by linarith)
    exact h2.trans this

theorem sum_nextProb' (h : List Z) (z' : Z) (x : M.AState) :
    ∑ e', M.nextProb z₀ h z' e' x = 1 := M.sum_nextProb z₀ h z' x

/-- **The pushed-forward test function is Lipschitz in assets**, with the constant multiplied by
the bound on the gross return. -/
theorem assetLip_expectedNext (K : List Z → ℝ × ℝ) (h : List Z) (z' : Z) {L : ℝ} (hL : 0 ≤ L)
    {f : M.AState →ᵇ ℝ} (hf : AssetLip L f) :
    AssetLip (M.returnBound * L) (M.expectedNext z₀ K h z' f) := by
  intro a b i
  change |∑ e', M.nextProb z₀ h z' e' (a, i) * f (M.nextA z₀ K h e' (a, i))
      - ∑ e', M.nextProb z₀ h z' e' (b, i) * f (M.nextA z₀ K h e' (b, i))| ≤ _
  rw [← Finset.sum_sub_distrib]
  have hpol := M.abs_policy_sub_le z₀ K a b ⟨i.idio, h⟩
  calc |∑ e', (M.nextProb z₀ h z' e' (a, i) * f (M.nextA z₀ K h e' (a, i))
          - M.nextProb z₀ h z' e' (b, i) * f (M.nextA z₀ K h e' (b, i)))|
      ≤ ∑ e', |M.nextProb z₀ h z' e' (a, i) * f (M.nextA z₀ K h e' (a, i))
          - M.nextProb z₀ h z' e' (b, i) * f (M.nextA z₀ K h e' (b, i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e', M.nextProb z₀ h z' e' (a, i) * (L * (M.returnBound * |(a : ℝ) - b|)) := by
        refine Finset.sum_le_sum fun e' _ => ?_
        have hp : 0 ≤ M.nextProb z₀ h z' e' (a, i) := M.nextProb_nonneg z₀ h z' e' _
        have hpe : M.nextProb z₀ h z' e' (b, i) = M.nextProb z₀ h z' e' (a, i) := rfl
        rw [hpe, ← mul_sub, abs_mul, abs_of_nonneg hp]
        refine mul_le_mul_of_nonneg_left ?_ hp
        have hfa := hf (M.clampAssets (M.policy z₀ K ((a, i).1, ⟨(a, i).2.idio, h⟩)))
          (M.clampAssets (M.policy z₀ K ((b, i).1, ⟨(b, i).2.idio, h⟩))) ⟨e'⟩
        have hca : ((M.clampAssets (M.policy z₀ K (a, ⟨i.idio, h⟩)) : ↥(Icc (0 : ℝ) M.assetCap))
            : ℝ) = M.policy z₀ K (a, ⟨i.idio, h⟩) := by
          rw [M.clampAssets_of_mem (M.policy_mem_Icc z₀ K _)]
        have hcb : ((M.clampAssets (M.policy z₀ K (b, ⟨i.idio, h⟩)) : ↥(Icc (0 : ℝ) M.assetCap))
            : ℝ) = M.policy z₀ K (b, ⟨i.idio, h⟩) := by
          rw [M.clampAssets_of_mem (M.policy_mem_Icc z₀ K _)]
        change |f (M.clampAssets (M.policy z₀ K (a, ⟨i.idio, h⟩)), ⟨e'⟩)
            - f (M.clampAssets (M.policy z₀ K (b, ⟨i.idio, h⟩)), ⟨e'⟩)| ≤ _
        refine (hfa.trans ?_)
        change L * |((M.clampAssets (M.policy z₀ K (a, ⟨i.idio, h⟩)) : ↥(Icc (0 : ℝ) M.assetCap))
            : ℝ) - ((M.clampAssets (M.policy z₀ K (b, ⟨i.idio, h⟩)) : ↥(Icc (0 : ℝ) M.assetCap))
            : ℝ)| ≤ _
        rw [hca, hcb]
        exact mul_le_mul_of_nonneg_left hpol hL
    _ = M.returnBound * L * |(a : ℝ) - b| := by
        rw [← Finset.sum_mul, M.sum_nextProb' z₀ h z' (a, i), one_mul]
        ring

/-- **The two pushed-forward test functions differ by at most `L` times the policy gap.** -/
theorem abs_expectedNext_sub_le (K K' : List Z → ℝ × ℝ) (h : List Z) (z' : Z) {L : ℝ}
    {f : M.AState →ᵇ ℝ} (hf : AssetLip L f) (x : M.AState) :
    |M.expectedNext z₀ K h z' f x - M.expectedNext z₀ K' h z' f x|
      ≤ L * |M.policy z₀ K (x.1, ⟨x.2.idio, h⟩) - M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩)| := by
  change |∑ e', M.nextProb z₀ h z' e' x * f (M.nextA z₀ K h e' x)
      - ∑ e', M.nextProb z₀ h z' e' x * f (M.nextA z₀ K' h e' x)| ≤ _
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ e', |M.nextProb z₀ h z' e' x * f (M.nextA z₀ K h e' x)
          - M.nextProb z₀ h z' e' x * f (M.nextA z₀ K' h e' x)|
      ≤ ∑ e', M.nextProb z₀ h z' e' x * (L * |M.policy z₀ K (x.1, ⟨x.2.idio, h⟩)
          - M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩)|) := by
        refine Finset.sum_le_sum fun e' _ => ?_
        have hp : 0 ≤ M.nextProb z₀ h z' e' x := M.nextProb_nonneg z₀ h z' e' _
        rw [← mul_sub, abs_mul, abs_of_nonneg hp]
        refine mul_le_mul_of_nonneg_left ?_ hp
        have hfa := hf (M.clampAssets (M.policy z₀ K (x.1, ⟨x.2.idio, h⟩)))
          (M.clampAssets (M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩))) ⟨e'⟩
        have hca : ((M.clampAssets (M.policy z₀ K (x.1, ⟨x.2.idio, h⟩))
            : ↥(Icc (0 : ℝ) M.assetCap)) : ℝ) = M.policy z₀ K (x.1, ⟨x.2.idio, h⟩) := by
          rw [M.clampAssets_of_mem (M.policy_mem_Icc z₀ K _)]
        have hcb : ((M.clampAssets (M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩))
            : ↥(Icc (0 : ℝ) M.assetCap)) : ℝ) = M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩) := by
          rw [M.clampAssets_of_mem (M.policy_mem_Icc z₀ K' _)]
        change |f (M.clampAssets (M.policy z₀ K (x.1, ⟨x.2.idio, h⟩)), ⟨e'⟩)
            - f (M.clampAssets (M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩)), ⟨e'⟩)| ≤ _
        refine hfa.trans ?_
        rw [hca, hcb]
    _ = L * |M.policy z₀ K (x.1, ⟨x.2.idio, h⟩) - M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩)| := by
        rw [← Finset.sum_mul, M.sum_nextProb' z₀ h z' x, one_mul]

/-- The distribution gap down the tree, from a bound `P` on the policy gap at each node. -/
def gapPath (θ : ℝ) (P : List Z → ℝ) : List Z → ℝ
  | [] => 0
  | _ :: h => θ * gapPath θ P h + P h

omit [Fintype Z] in
theorem gapPath_nonneg {θ : ℝ} (hθ : 0 ≤ θ) {P : List Z → ℝ} (hP : ∀ h, 0 ≤ P h) :
    ∀ h, 0 ≤ gapPath θ P h
  | [] => le_rfl
  | _ :: h => add_nonneg (mul_nonneg hθ (gapPath_nonneg hθ hP h)) (hP h)

variable (μ₀ : Measure M.AState) [IsProbabilityMeasure μ₀]

/-- **Distributions drift apart by at most the gap path.** If `P h` bounds the saving-policy gap
at every state of node `h`, then every `L`-Lipschitz test function integrates against the two
distributions at `h` to within `L · gapPath R̄ P h`. -/
theorem integral_nodeDist_sub_le (K K' : List Z → ℝ × ℝ) (P : List Z → ℝ)
    (hP : ∀ h (x : M.AState),
      |M.policy z₀ K (x.1, ⟨x.2.idio, h⟩) - M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩)| ≤ P h) :
    ∀ (h : List Z) {L : ℝ}, 0 ≤ L → ∀ {f : M.AState →ᵇ ℝ}, AssetLip L f →
      |∫ x, f x ∂(M.nodeDist z₀ μ₀ K h) - ∫ x, f x ∂(M.nodeDist z₀ μ₀ K' h)|
        ≤ L * gapPath M.returnBound P h
  | [], L, hL, f, _ => by simp [nodeDist, gapPath]
  | z' :: h, L, hL, f, hf => by
    have := M.isProbabilityMeasure_nodeDist z₀ μ₀ K h
    have := M.isProbabilityMeasure_nodeDist z₀ μ₀ K' h
    have hR0 : 0 ≤ M.returnBound :=
      (M.grossReturn_nonneg z₀ 0 0).trans (M.grossReturn_le z₀ 0 0)
    have hd : ∫ x, f x ∂(M.nodeDist z₀ μ₀ K (z' :: h))
        = ∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K h) :=
      M.integral_pushNode z₀ K h z' _ f
    have hd' : ∫ x, f x ∂(M.nodeDist z₀ μ₀ K' (z' :: h))
        = ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₀ K' h) :=
      M.integral_pushNode z₀ K' h z' _ f
    rw [hd, hd']
    -- same integrand, different distributions
    have h1 := integral_nodeDist_sub_le K K' P hP h (mul_nonneg hR0 hL)
      (M.assetLip_expectedNext z₀ K h z' hL hf)
    -- same distribution, different integrands
    have h2 : |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K' h)
        - ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₀ K' h)| ≤ L * P h := by
      rw [← integral_sub ((M.expectedNext z₀ K h z' f).integrable _)
        ((M.expectedNext z₀ K' h z' f).integrable _)]
      have := norm_integral_le_of_norm_le_const (μ := M.nodeDist z₀ μ₀ K' h)
        (f := fun x => M.expectedNext z₀ K h z' f x - M.expectedNext z₀ K' h z' f x)
        (C := L * P h) (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          exact (M.abs_expectedNext_sub_le z₀ K K' h z' hf x).trans
            (mul_le_mul_of_nonneg_left (hP h x) hL))
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    calc |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K h)
          - ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₀ K' h)|
        ≤ |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K h)
            - ∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K' h)|
          + |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K' h)
            - ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₀ K' h)| :=
          abs_sub_le _ _ _
      _ ≤ M.returnBound * L * gapPath M.returnBound P h + L * P h := add_le_add h1 h2
      _ = L * gapPath M.returnBound P (z' :: h) := by simp only [gapPath]; ring

/-- **Mean capital differs by at most the gap path.** -/
theorem meanCapital_sub_le (K K' : List Z → ℝ × ℝ) (P : List Z → ℝ)
    (hP : ∀ h (x : M.AState),
      |M.policy z₀ K (x.1, ⟨x.2.idio, h⟩) - M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩)| ≤ P h)
    (h : List Z) :
    |M.meanCapital z₀ μ₀ K h - M.meanCapital z₀ μ₀ K' h| ≤ gapPath M.returnBound P h := by
  have := M.integral_nodeDist_sub_le z₀ μ₀ K K' P hP h zero_le_one assetLip_assets
  rwa [one_mul] at this

end KSModel

end KrusellSmith

end LeanEconomics
