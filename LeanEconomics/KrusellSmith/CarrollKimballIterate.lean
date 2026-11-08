/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CarrollKimballTree

/-!
# Carroll–Kimball on the tree: every Bellman iterate

Milestone MR4b, step b5, of `MINIMAL_STATE_PLAN.md`. Along the Bellman iterates
`vₙ = Tⁿ 0` of the Krusell–Smith household, the consumption function is concave in assets at
every label (`concaveOn_consumptionOf_iterate`), for CRRA marginal utility, positive returns,
and the consumption floor and asset cap slack along the iteration.

* **Base** (`policyOf_zero`, `concaveOn_consumptionOf_zero`): with no future the household saves
  nothing (utility is strictly increasing: strictly concave and nondecreasing), so it consumes its
  cash `R_h a + w_h e`, affine in assets.
* **Step**: `concaveOn_consumptionOf_bellman` (b4), with the iterate's concave slices
  (`concaveSlices_iterate`) giving monotone children's consumption.

The slackness hypotheses are explicit; they are the calibration conditions of the
income-fluctuation development (`crra_policyOf_lt_assetCap`) and of `KSInada`
(`floorLevel_le_consumption`), to be discharged for a concrete economy in MR4d. The fixed point
is not needed: Light's step (MR4c) runs along the iterates too.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (U : M.SmoothUtility) (z₀ : Z) (K : List Z → ℝ × ℝ)

/-- Utility is strictly increasing above the floor: strictly concave and nondecreasing. -/
theorem utility_lt_utility {x y : ℝ} (hx : M.consFloor ≤ x) (hxy : x < y) :
    M.utility x < M.utility y := by
  have hle := M.monotoneOn_utility (mem_Ici.2 hx) (mem_Ici.2 (hx.trans hxy.le)) hxy.le
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    -- the midpoint lies strictly above the chord, hence above `u y`: contradicts monotonicity
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    have hsum : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
    have hs := M.strictConcaveOn_utility.2 (mem_Ici.2 hx) (mem_Ici.2 (hx.trans hxy.le))
      hxy.ne hhalf hhalf hsum
    simp only [smul_eq_mul] at hs
    have hmid : (1 / 2 : ℝ) * x + 1 / 2 * y ≤ y := by linarith
    have hmono := M.monotoneOn_utility
      (mem_Ici.2 (show M.consFloor ≤ (1 / 2 : ℝ) * x + 1 / 2 * y by linarith))
      (mem_Ici.2 (hx.trans hxy.le)) hmid
    linarith

theorem contOf_zero (s : M.State) (a : ℝ) : M.contOf z₀ (0 : M.State →ᵇ ℝ) s a = 0 := by
  simp [contOf]

/-- **With no future the household saves nothing.** -/
theorem policyOf_zero (s : M.State) : M.policyOf z₀ K (0 : M.State →ᵇ ℝ) s = 0 := by
  have h0 : (0 : ℝ) ∈ (M.household z₀ K).feasible s := ⟨le_rfl, M.maxSaving_nonneg z₀ K s⟩
  have hfl : M.consFloor ≤ M.cash z₀ K s := M.consFloor_le_cash z₀ K s
  refine (M.eq_policyOf_of_objective z₀ K M.concaveSlices_zero h0 (le_antisymm ?_ ?_)).symm
  · exact M.le_bellman_contOf z₀ K 0 h0
  · change (M.household z₀ K).bellmanFn 0 s ≤ _
    refine (M.household z₀ K).bellmanFn_le 0 fun a ha => ?_
    rw [M.objective_eq_contOf z₀ K 0 ha]
    simp only [contOf_zero, mul_zero, add_zero, sub_zero]
    have hca : M.consFloor ≤ M.cash z₀ K s - a := le_sub_comm.1 (ha.2.trans (min_le_right _ _))
    exact M.monotoneOn_utility (mem_Ici.2 hca) (mem_Ici.2 hfl) (by linarith [ha.1])

/-- **With no future, consumption is cash on hand, affine in assets, hence concave.** -/
theorem concaveOn_consumptionOf_zero (l : Label Z E) :
    ConcaveOn ℝ (Icc 0 M.assetCap)
      fun A => M.consumptionOf z₀ K (0 : M.State →ᵇ ℝ) (M.stateAt A l) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => le_of_eq ?_⟩
  have hm : a • x + b • y ∈ Icc 0 M.assetCap := convex_Icc 0 M.assetCap hx hy ha hb hab
  simp only [consumptionOf, policyOf_zero, sub_zero, smul_eq_mul] at hm ⊢
  rw [M.cash_stateAt z₀ K hx, M.cash_stateAt z₀ K hy, M.cash_stateAt z₀ K hm]
  linear_combination (M.wageAt z₀ K l.node * M.efficiency l.idio
    - M.returnAt z₀ K l.node * M.borrowLimit) * hab

/-- **Carroll and Kimball on the tree, along every Bellman iterate**, for CRRA marginal utility:
the consumption function against `Tⁿ 0` is concave in assets at every label, provided returns
are positive and the consumption floor and asset cap are slack along the iteration. -/
theorem concaveOn_consumptionOf_iterate {γ : ℝ} (hγ : 0 < γ)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) (hR : ∀ h, 0 < M.returnAt z₀ K h)
    (hsl : ∀ n : ℕ, M.SlackOf z₀ K (((M.household z₀ K).bellman)^[n] 0))
    (hcap : ∀ (n : ℕ) (s : M.State),
      M.policyOf z₀ K (((M.household z₀ K).bellman)^[n] 0) s < M.assetCap) :
    ∀ (n : ℕ) (l : Label Z E), ConcaveOn ℝ (Icc 0 M.assetCap)
      fun A => M.consumptionOf z₀ K (((M.household z₀ K).bellman)^[n] 0) (M.stateAt A l)
  | 0, l => M.concaveOn_consumptionOf_zero z₀ K l
  | n + 1, l => by
    have IH := concaveOn_consumptionOf_iterate hγ hdu hR hsl hcap n
    have hsl' := hsl (n + 1)
    have hcap' := hcap (n + 1)
    rw [Function.iterate_succ_apply'] at hsl' hcap' ⊢
    exact M.concaveOn_consumptionOf_bellman U z₀ K hγ hdu hR (M.concaveSlices_iterate z₀ K n)
      (hsl n) IH l (fun a _ => hsl' _) (fun a _ => hcap' _)

end KSModel

end KrusellSmith

end LeanEconomics
