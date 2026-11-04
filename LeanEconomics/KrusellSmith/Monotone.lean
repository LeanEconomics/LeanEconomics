/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Euler

/-!
# Saving and consumption rise with assets

At every node, along every path of capital and labour, both optimal saving and optimal
consumption are nondecreasing in assets (`policy_mono`, `consumption_mono`). With the budget
constraint this bounds both slopes by the gross return (`policy_sub_le`, `consumption_sub_le`):
a household richer by `Δ` in assets has `R Δ` more cash and splits it between saving and
consumption, neither falling.

The proofs are swap arguments (Topkis) that use **uniqueness of the optimal saving** for
strictness:

* saving: utility is concave, so the gain from saving less is larger for the poorer household
  (`concave_increment_le`); if the richer household saved less, the two optimal choices
  would tie at the poorer state, contradicting uniqueness;
* consumption: the same with the continuation value, which is concave in saving, in place of
  utility.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

/-- **Increments of a concave function shrink to the right**: for `x ≤ y` and a step `d ≥ 0`,
`f (y + d) - f y ≤ f (x + d) - f x`, all points in the domain. -/
theorem concave_increment_le {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f)
    {x y d : ℝ} (hxy : x ≤ y) (hd : 0 ≤ d) (hx : x ∈ S) (hyd : y + d ∈ S) :
    f (y + d) - f y ≤ f (x + d) - f x := by
  rcases hd.lt_or_eq with hd' | rfl
  · have hpos : 0 < y + d - x := by linarith
    set t := d / (y + d - x) with ht
    have ht0 : 0 ≤ t := div_nonneg hd hpos.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hpos]; linarith
    have h1 := hf.2 hx hyd (sub_nonneg.2 ht1) ht0 (by ring)
    have h2 := hf.2 hx hyd ht0 (sub_nonneg.2 ht1) (by ring)
    have e1 : (1 - t) • x + t • (y + d) = x + d := by
      simp only [smul_eq_mul, ht]
      field_simp
      ring
    have e2 : t • x + (1 - t) • (y + d) = y := by
      simp only [smul_eq_mul, ht]
      field_simp
      ring
    rw [e1] at h1
    rw [e2] at h2
    simp only [smul_eq_mul] at h1 h2
    have h3 := add_le_add h1 h2
    ring_nf at h3 ⊢
    linarith
  · simp

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z) (K : List Z → ℝ × ℝ)

/-- The continuation value of saving `a'` at the state `s`. -/
noncomputable def cont (s : M.State) (a' : ℝ) : ℝ :=
  ∑ ze : Z × E, M.shockProb z₀ ze (s, a')
    * (M.household z₀ K).valueFunction (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)

theorem concaveOn_cont (s : M.State) : ConcaveOn ℝ (Icc 0 M.assetCap) (M.cont z₀ K s) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [cont, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ze _ => ?_
  have hvz := (M.concaveOn_valueFunction z₀ K ⟨ze.2, ze.1 :: s.2.node⟩).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hvz
  have hp := M.shockProb_nonneg' z₀ ze (s, x)
  change a * (M.shockProb z₀ ze (s, x) * _) + b * (M.shockProb z₀ ze (s, x) * _)
    ≤ M.shockProb z₀ ze (s, x) * _
  simp only [stateAt]
  nlinarith

/-- The objective of saving `a` at `s`, through the continuation. -/
theorem objective_eq_cont (s : M.State) {a : ℝ} (ha : a ∈ (M.household z₀ K).feasible s) :
    (M.household z₀ K).objective (M.household z₀ K).valueFunction s a
      = M.utility (M.cash z₀ K s - a) + M.discount * M.cont z₀ K s a :=
  M.objective_eq z₀ K _ ha

theorem bellmanFn_eq_valueFunction (s : M.State) :
    (M.household z₀ K).bellmanFn (M.household z₀ K).valueFunction s
      = (M.household z₀ K).valueFunction s := by
  change (M.household z₀ K).bellman _ s = _
  rw [(M.household z₀ K).bellman_valueFunction]

/-- The value is the objective of the optimal saving. -/
theorem valueFunction_eq_cont (s : M.State) :
    (M.household z₀ K).valueFunction s
      = M.utility (M.consumption z₀ K s) + M.discount * M.cont z₀ K s (M.policy z₀ K s) := by
  rw [← M.bellmanFn_eq_valueFunction z₀ K s]
  change (M.household z₀ K).bellman _ s = _
  rw [M.policy_optimal z₀ K s, M.objective_eq_cont z₀ K s (M.policy_mem z₀ K s)]
  rfl

/-- A feasible saving whose objective reaches the value is the policy. -/
theorem eq_policy_of_objective {s : M.State} {a : ℝ} (ha : a ∈ (M.household z₀ K).feasible s)
    (hval : M.utility (M.cash z₀ K s - a) + M.discount * M.cont z₀ K s a
      = (M.household z₀ K).valueFunction s) :
    a = M.policy z₀ K s := by
  refine M.optimal_saving_unique z₀ K ha (M.policy_mem z₀ K s) ?_ ?_
  · rw [M.objective_eq_cont z₀ K s ha, hval, M.bellmanFn_eq_valueFunction]
  · rw [M.bellmanFn_eq_valueFunction, M.valueFunction_eq_cont,
      M.objective_eq_cont z₀ K s (M.policy_mem z₀ K s)]
    rfl

theorem le_valueFunction {s : M.State} {a : ℝ} (ha : a ∈ (M.household z₀ K).feasible s) :
    M.utility (M.cash z₀ K s - a) + M.discount * M.cont z₀ K s a
      ≤ (M.household z₀ K).valueFunction s := by
  rw [← M.objective_eq_cont z₀ K s ha, ← M.bellmanFn_eq_valueFunction]
  exact (M.household z₀ K).le_bellmanFn _ ha

/-- The continuation does not depend on the assets of the state, only on its label. -/
theorem cont_stateAt (a b : ℝ) (l : Label Z E) :
    M.cont z₀ K (M.stateAt a l) = M.cont z₀ K (M.stateAt b l) := rfl

theorem cash_mono {a b : ℝ} (ha : a ∈ Icc 0 M.assetCap) (hb : b ∈ Icc 0 M.assetCap)
    (hab : a ≤ b) (l : Label Z E) :
    M.cash z₀ K (M.stateAt a l) ≤ M.cash z₀ K (M.stateAt b l) := by
  rw [M.cash_stateAt z₀ K ha, M.cash_stateAt z₀ K hb]
  nlinarith [M.returnAt_nonneg z₀ K l.node]

/-- **Optimal saving is nondecreasing in assets.** -/
theorem policy_mono {a b : ℝ} (ha : a ∈ Icc 0 M.assetCap) (hb : b ∈ Icc 0 M.assetCap)
    (hab : a ≤ b) (l : Label Z E) :
    M.policy z₀ K (M.stateAt a l) ≤ M.policy z₀ K (M.stateAt b l) := by
  set sa := M.stateAt a l
  set sb := M.stateAt b l
  set pa := M.policy z₀ K sa
  set pb := M.policy z₀ K sb
  by_contra hlt
  rw [not_le] at hlt
  have hxa := M.cash_mono z₀ K ha hb hab l
  have hpa := M.policy_mem z₀ K sa
  have hpb := M.policy_mem z₀ K sb
  -- each household could have chosen the other's saving
  have hfa : pb ∈ (M.household z₀ K).feasible sa := ⟨hpb.1, hlt.le.trans hpa.2⟩
  have hfb : pa ∈ (M.household z₀ K).feasible sb := by
    refine ⟨hpa.1, le_min (hpa.2.trans (min_le_left _ _)) ?_⟩
    linarith [hpa.2.trans (min_le_right _ _)]
  have h1 := M.le_valueFunction z₀ K hfa
  have h2 := M.le_valueFunction z₀ K hfb
  have v1 := M.valueFunction_eq_cont z₀ K sa
  have v2 := M.valueFunction_eq_cont z₀ K sb
  have hcont := M.cont_stateAt z₀ K a b l
  -- increasing differences, from concavity of utility
  have hca : M.consFloor ≤ M.cash z₀ K sa - pa := le_sub_comm.1 (hpa.2.trans (min_le_right _ _))
  have hid := concave_increment_le M.strictConcaveOn_utility.concaveOn
    (x := M.cash z₀ K sa - pa) (y := M.cash z₀ K sa - pb) (d := M.cash z₀ K sb - M.cash z₀ K sa)
    (by linarith) (by linarith) (mem_Ici.2 hca) (mem_Ici.2 (by linarith))
  have e1 : M.cash z₀ K sa - pb + (M.cash z₀ K sb - M.cash z₀ K sa) = M.cash z₀ K sb - pb := by
    ring
  have e2 : M.cash z₀ K sa - pa + (M.cash z₀ K sb - M.cash z₀ K sa) = M.cash z₀ K sb - pa := by
    ring
  rw [e1, e2] at hid
  have hcb : M.cont z₀ K sb = M.cont z₀ K sa := hcont.symm
  rw [hcb] at h2 v2
  -- the poorer household is indifferent to the richer one's saving
  have htie : M.utility (M.cash z₀ K sa - pb) + M.discount * M.cont z₀ K sa pb
      = (M.household z₀ K).valueFunction sa := by
    have v1' : (M.household z₀ K).valueFunction sa
        = M.utility (M.cash z₀ K sa - pa) + M.discount * M.cont z₀ K sa pa :=
      M.valueFunction_eq_cont z₀ K sa
    have v2' : (M.household z₀ K).valueFunction sb
        = M.utility (M.cash z₀ K sb - pb) + M.discount * M.cont z₀ K sa pb := by
      rw [M.valueFunction_eq_cont z₀ K sb, hcb]
      rfl
    linarith
  have := M.eq_policy_of_objective z₀ K hfa htie
  exact absurd this hlt.ne

/-- **Optimal consumption is nondecreasing in assets.** -/
theorem consumption_mono {a b : ℝ} (ha : a ∈ Icc 0 M.assetCap) (hb : b ∈ Icc 0 M.assetCap)
    (hab : a ≤ b) (l : Label Z E) :
    M.consumption z₀ K (M.stateAt a l) ≤ M.consumption z₀ K (M.stateAt b l) := by
  set sa := M.stateAt a l
  set sb := M.stateAt b l
  set pa := M.policy z₀ K sa
  set pb := M.policy z₀ K sb
  set xa := M.cash z₀ K sa
  set xb := M.cash z₀ K sb
  by_contra hlt
  rw [not_le] at hlt
  have hca : M.consumption z₀ K sa = xa - pa := rfl
  have hcb : M.consumption z₀ K sb = xb - pb := rfl
  rw [hca, hcb] at hlt
  have hxa : xa ≤ xb := M.cash_mono z₀ K ha hb hab l
  have hpa := M.policy_mem z₀ K sa
  have hpb := M.policy_mem z₀ K sb
  set δ := (xa - pa) - (xb - pb) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  -- swapped consumption levels: the poorer consumes `xb - pb`, the richer `xa - pa`
  have hfa : pa + δ ∈ (M.household z₀ K).feasible sa := by
    refine ⟨by linarith [hpa.1], le_min ?_ ?_⟩
    · linarith [hpb.2.trans (min_le_left _ _)]
    · linarith [hpb.2.trans (min_le_right _ _)]
  have hfb : pb - δ ∈ (M.household z₀ K).feasible sb := by
    refine ⟨by linarith [hpa.1], le_min ?_ ?_⟩
    · linarith [hpb.2.trans (min_le_left _ _)]
    · linarith [hpa.2.trans (min_le_right _ _)]
  have h1 := M.le_valueFunction z₀ K hfa
  have h2 := M.le_valueFunction z₀ K hfb
  have v1 : (M.household z₀ K).valueFunction sa
      = M.utility (xa - pa) + M.discount * M.cont z₀ K sa pa := M.valueFunction_eq_cont z₀ K sa
  have v2 : (M.household z₀ K).valueFunction sb
      = M.utility (xb - pb) + M.discount * M.cont z₀ K sb pb := M.valueFunction_eq_cont z₀ K sb
  have hcont : M.cont z₀ K sb = M.cont z₀ K sa := M.cont_stateAt z₀ K b a l
  rw [hcont] at h2 v2
  have e1 : xa - (pa + δ) = xb - pb := by rw [hδ]; ring
  have e2 : xb - (pb - δ) = xa - pa := by rw [hδ]; ring
  rw [e1] at h1
  rw [e2] at h2
  -- concavity of the continuation: saving `δ` more pays less at the higher level
  have hpaI : pa ∈ Icc 0 M.assetCap := M.mem_Icc_of_mem_feasible z₀ K hpa
  have hpbI : pb ∈ Icc 0 M.assetCap := M.mem_Icc_of_mem_feasible z₀ K hpb
  have hle : pa ≤ pb - δ := by rw [hδ]; linarith
  have hid := concave_increment_le (M.concaveOn_cont z₀ K sa) (x := pa) (y := pb - δ) (d := δ) hle
    hδ0.le hpaI (by rw [sub_add_cancel]; exact hpbI)
  rw [sub_add_cancel] at hid
  have hβ := M.discount_pos
  have hscaled := mul_le_mul_of_nonneg_left hid hβ.le
  -- so both swaps tie, and the poorer household's tie contradicts uniqueness
  have htie : M.utility (xa - (pa + δ)) + M.discount * M.cont z₀ K sa (pa + δ)
      = (M.household z₀ K).valueFunction sa := by
    rw [e1]
    nlinarith
  have := M.eq_policy_of_objective z₀ K hfa htie
  linarith

/-- **Saving rises by at most the extra cash.** -/
theorem policy_sub_le {a b : ℝ} (ha : a ∈ Icc 0 M.assetCap) (hb : b ∈ Icc 0 M.assetCap)
    (hab : a ≤ b) (l : Label Z E) :
    M.policy z₀ K (M.stateAt b l) - M.policy z₀ K (M.stateAt a l)
      ≤ M.returnAt z₀ K l.node * (b - a) := by
  have h := M.consumption_mono z₀ K ha hb hab l
  have hca : M.consumption z₀ K (M.stateAt a l)
      = M.cash z₀ K (M.stateAt a l) - M.policy z₀ K (M.stateAt a l) := rfl
  have hcb : M.consumption z₀ K (M.stateAt b l)
      = M.cash z₀ K (M.stateAt b l) - M.policy z₀ K (M.stateAt b l) := rfl
  rw [hca, hcb, M.cash_stateAt z₀ K ha, M.cash_stateAt z₀ K hb] at h
  linarith

/-- **Consumption rises by at most the extra cash.** -/
theorem consumption_sub_le {a b : ℝ} (ha : a ∈ Icc 0 M.assetCap) (hb : b ∈ Icc 0 M.assetCap)
    (hab : a ≤ b) (l : Label Z E) :
    M.consumption z₀ K (M.stateAt b l) - M.consumption z₀ K (M.stateAt a l)
      ≤ M.returnAt z₀ K l.node * (b - a) := by
  have h := M.policy_mono z₀ K ha hb hab l
  have hca : M.consumption z₀ K (M.stateAt a l)
      = M.cash z₀ K (M.stateAt a l) - M.policy z₀ K (M.stateAt a l) := rfl
  have hcb : M.consumption z₀ K (M.stateAt b l)
      = M.cash z₀ K (M.stateAt b l) - M.policy z₀ K (M.stateAt b l) := rfl
  rw [hca, hcb, M.cash_stateAt z₀ K ha, M.cash_stateAt z₀ K hb]
  linarith

end KSModel

end KrusellSmith

end LeanEconomics
