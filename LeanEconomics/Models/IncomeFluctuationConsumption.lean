/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationMonotone
import LeanEconomics.Analysis.RelativeRiskAversion

/-!
# The consumption function

`consumptionFn z a` is what the household actually eats at assets `a`: cash on hand less the
optimal saving. Light (2018) Theorem 1 needs three things from it — positivity, monotonicity,
and CONCAVITY in assets (his Lemma 4). The first two are proved here. The third is not, and
this file says exactly why.

## Consumption rises with assets

`consumptionFn_mono` is the theorem of this file, and it is the mirror image of `policy_mono`.
That one swapped the two households' savings and used increasing differences of `u`; this one
swaps them by the SAME resource gap, `b ↦ b + Δ` and `b' ↦ b' - Δ`, which leaves every
consumption level untouched and moves only the continuation. So the roles are exchanged: the
argument runs on increasing differences of the CONTINUATION, and it is again
`ConcaveOn.sub_le_sub_of_shift` — applied to `cont` rather than to `u`.

Together the two say the marginal propensities are both non-negative:

  `0 ≤ c(a') - c(a) ≤ resources(a') - resources(a)`   for `a ≤ a'`,

which is `sub_le_sub_of_le_resources`. Neither half needs a derivative.

## Concavity is NOT free, and this file does not prove it

It would be pleasant if concavity of `c` followed from concavity of `u` and of the value
function, the way monotonicity does. It does not. With CRRA `u` and a continuation of constant
absolute risk tolerance, the marginal propensity to consume is `T_u(c) / (T_u(c) + T_W(b))`
with `T_u(c) = c/γ` and `T_W` constant, which RISES with consumption — so the consumption
function is CONVEX. Concavity therefore cannot follow from concavity of the two primitives; it
needs the continuation to inherit the curvature of `u`, which is what makes it a statement
about the FIXED POINT rather than about one application of the operator.

That is the Carroll and Kimball (1996) theorem — the Bellman operator preserves concavity of
the consumption function when utility is HARA — and it is the shape of the closed-class
arguments already used here for monotonicity, concavity, Lipschitz bounds and increasing
differences. Light states it as his Lemma 4 and cites Jensen (2017) rather than proving it.
It is left as a hypothesis: `mul_marginal_le_of_scale` takes it as an argument, and everything
else that theorem needs about the consumption function is discharged here.
-/

open Set Filter Topology

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ}
variable (P : IncomeFluctuation Z assetCap)

/-- **The continuation value is concave in savings**, being a non-negative combination of the
value function's concave slices. -/
theorem concaveOn_cont (z : Z) : ConcaveOn ℝ (Icc 0 assetCap) (P.cont z) := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  simp only [cont, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z' _ => ?_
  have hvz := (P.concaveOn_valueFunction z').2 hx hy hθ hφ hθφ
  simp only [smul_eq_mul] at hvz
  nlinarith [P.transitionMatrix_nonneg z z']

/-- Consumption at the optimum, as a function of assets. -/
noncomputable def consumptionFn (z : Z) (a : ℝ) : ℝ :=
  P.consumption (a, z) (P.policy (a, z))

theorem consumptionFn_pos {a : ℝ} (ha : a ∈ Icc 0 assetCap) (z : Z) :
    0 < P.consumptionFn z a :=
  P.consumption_policy_pos (s := (a, z)) ha

/-- The saving cap cannot grow by more than resources do. -/
theorem maxSaving_le_add_sub {a a' : ℝ} {z : Z} (hle : a ≤ a') :
    P.maxSaving (a', z)
      ≤ P.maxSaving (a, z) + (P.resources (a', z) - P.resources (a, z)) := by
  have hΔ : 0 ≤ P.resources (a', z) - P.resources (a, z) := by
    linarith [P.resources_mono (z := z) hle]
  have hmin : min assetCap (P.resources (a', z))
      ≤ min assetCap (P.resources (a, z)) + (P.resources (a', z) - P.resources (a, z)) := by
    rcases le_total assetCap (P.resources (a, z)) with h | h
    · rw [min_eq_left h]
      exact le_trans (min_le_left _ _) (by linarith)
    · rw [min_eq_right h]
      exact le_trans (min_le_right _ _) (by linarith)
  rw [P.maxSaving_eq, P.maxSaving_eq]
  linarith

/-- **Consumption rises with assets.** The two households swap savings plans shifted by their
resource gap, which leaves consumption alone and moves only the continuation — so the
comparison is increasing differences of the continuation, exactly as `policy_mono` is
increasing differences of `u`. -/
theorem consumptionFn_mono {a a' : ℝ} {z : Z} (ha : a ∈ Icc 0 assetCap)
    (ha' : a' ∈ Icc 0 assetCap) (hle : a ≤ a') :
    P.consumptionFn z a ≤ P.consumptionFn z a' := by
  set Δ : ℝ := P.resources (a', z) - P.resources (a, z) with hΔdef
  have hΔ : 0 ≤ Δ := by
    rw [hΔdef]; linarith [P.resources_mono (z := z) hle]
  set b : ℝ := P.policy (a, z) with hbdef
  set b' : ℝ := P.policy (a', z) with hb'def
  -- the goal is `b' ≤ b + Δ`
  by_contra hcon
  rw [not_le] at hcon
  have hgap : b + Δ < b' := by
    simp only [consumptionFn, consumption] at hcon
    rw [hΔdef]; linarith
  have hbmem : b ∈ P.toExtended.feasible (a, z) := P.policy_mem _
  have hb'mem : b' ∈ P.toExtended.feasible (a', z) := P.policy_mem _
  rw [P.feasible_eq] at hbmem hb'mem
  -- both shifted plans are feasible
  have hshiftup : b + Δ ∈ P.toExtended.feasible (a', z) := by
    rw [P.feasible_eq]
    exact ⟨by linarith [hbmem.1], by linarith [hb'mem.2]⟩
  have hshiftdown : b' - Δ ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq]
    refine ⟨by linarith [hbmem.1], ?_⟩
    have := P.maxSaving_le_add_sub (z := z) hle
    rw [← hΔdef] at this
    linarith [hb'mem.2]
  -- the shift is consumption-neutral, so only two consumption levels appear
  have hc1 : 0 < P.consumption (a, z) b := P.consumption_policy_pos (s := (a, z)) ha
  have hc2 : 0 < P.consumption (a', z) b' := P.consumption_policy_pos (s := (a', z)) ha'
  have he1 : P.consumption (a', z) (b + Δ) = P.consumption (a, z) b := by
    simp only [consumption, hΔdef]; ring
  have he2 : P.consumption (a, z) (b' - Δ) = P.consumption (a', z) b' := by
    simp only [consumption, hΔdef]; ring
  -- optimality at each state, against the other's shifted plan
  have hI := P.objR_le_of_mem ha hshiftdown (by rw [he2]; exact hc2)
  have hII := P.objR_le_of_mem ha' hshiftup (by rw [he1]; exact hc1)
  -- increasing differences of the continuation
  have hbreg : b ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region _
  have hb'reg : b' ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region _
  have hshift := (P.concaveOn_cont z).sub_le_sub_of_shift (c₁ := b) (c₂ := b' - Δ) (Δ := Δ)
    hbreg (by simpa using hb'reg) (by linarith) hΔ
  rw [sub_add_cancel] at hshift
  -- the two optimality inequalities therefore hold with equality
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hshift hβ
  simp only [objR, he1, he2] at hI hII
  have hIIeq : P.objR (a', z) (b + Δ) = P.objR (a', z) b' := by
    simp only [objR, he1]
    nlinarith [hI, hII, hscaled]
  -- so the shifted plan attains the optimum at the richer state, and uniqueness closes it
  have hbell : P.toExtended.objectiveE P.toExtended.valueFunction (a', z) (b + Δ)
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction (a', z) : ℝ) : EReal) := by
    rw [P.objectiveE_eq_coe ha' hshiftup (by rw [he1]; exact hc1), hIIeq,
      ← P.objectiveE_eq_coe ha' (P.policy_mem _) hc2]
    exact P.policy_optimal _
  exact absurd (P.eq_policy_of_optimal ha' hshiftup hbell) (by rw [← hb'def]; linarith)

/-- **The marginal propensities are both non-negative.** Consumption rises with assets, and by
no more than resources do — the second half is `policy_mono`. -/
theorem sub_le_sub_of_le_resources {a a' : ℝ} {z : Z} (ha : a ∈ Icc 0 assetCap)
    (ha' : a' ∈ Icc 0 assetCap) (hle : a ≤ a') :
    0 ≤ P.consumptionFn z a' - P.consumptionFn z a ∧
      P.consumptionFn z a' - P.consumptionFn z a
        ≤ P.resources (a', z) - P.resources (a, z) := by
  refine ⟨by linarith [P.consumptionFn_mono (z := z) ha ha' hle], ?_⟩
  have := P.policy_mono (z := z) ha ha' hle
  simp only [consumptionFn, consumption]
  linarith

theorem monotoneOn_consumptionFn (z : Z) :
    MonotoneOn (P.consumptionFn z) (Icc 0 assetCap) :=
  fun _ ha _ ha' h => P.consumptionFn_mono ha ha' h

end IncomeFluctuation

end LeanEconomics
