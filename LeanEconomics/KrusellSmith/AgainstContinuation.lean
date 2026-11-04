/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Monotone

/-!
# The household against an arbitrary continuation value

Milestone MR4b, step b2, of `MINIMAL_STATE_PLAN.md`. Carroll–Kimball concavity is proved along
the Bellman iterates, so the household's problem is needed against an arbitrary continuation
value `v`, not only against its own value function. This module restates the single-period
facts of `Policy.lean` and `Monotone.lean` for an arbitrary `v` with concave slices, as
`Models/IncomeFluctuationIterate.lean` does for the income-fluctuation problem.

* `ConcaveSlices v`: `v` is concave in assets at every label; preserved by the Bellman operator
  (`concaveSlices_bellman`) and so by every iterate from `0` (`concaveSlices_iterate`).
* `contOf v s a'`: the continuation value of saving `a'`; concave under concave slices
  (`concaveOn_contOf`).
* `policyOf v s`, `consumptionOf v s`: an optimal saving against `v` and the consumption it
  leaves; `policyOf` against the value function is `policy` (`policyOf_valueFunction`).
* `eq_policyOf_of_objective`: under concave slices **the optimal saving is unique**.
* `policyOf_mono`, `consumptionOf_mono`: **saving and consumption are nondecreasing in assets**
  (the swap arguments of `policy_mono`, `consumption_mono`).
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z) (K : List Z → ℝ × ℝ)

/-- A continuation value concave in assets at every label. -/
def ConcaveSlices (v : M.State →ᵇ ℝ) : Prop :=
  ∀ l : Label Z E, ConcaveOn ℝ (Icc 0 M.assetCap) fun a => v (M.clampAssets a, l)

theorem concaveSlices_zero : M.ConcaveSlices (0 : M.State →ᵇ ℝ) := fun _ => by
  simpa using (concaveOn_const (c := (0 : ℝ)) (convex_Icc 0 M.assetCap))

theorem concaveSlices_bellman {v : M.State →ᵇ ℝ} (hv : M.ConcaveSlices v) :
    M.ConcaveSlices ((M.household z₀ K).bellman v) :=
  M.concaveOn_bellman z₀ K v hv

theorem concaveSlices_iterate (n : ℕ) :
    M.ConcaveSlices (((M.household z₀ K).bellman)^[n] 0) := by
  induction n with
  | zero => exact M.concaveSlices_zero
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact M.concaveSlices_bellman z₀ K ih

/-- The continuation value of saving `a'` at `s`, against `v`. -/
noncomputable def contOf (v : M.State →ᵇ ℝ) (s : M.State) (a' : ℝ) : ℝ :=
  ∑ ze : Z × E, M.shockProb z₀ ze (s, a') * v (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)

theorem contOf_label (v : M.State →ᵇ ℝ) (a b : ℝ) (l : Label Z E) :
    M.contOf z₀ v (M.stateAt a l) = M.contOf z₀ v (M.stateAt b l) := rfl

theorem concaveOn_contOf {v : M.State →ᵇ ℝ} (hv : M.ConcaveSlices v) (s : M.State) :
    ConcaveOn ℝ (Icc 0 M.assetCap) (M.contOf z₀ v s) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [contOf, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ze _ => ?_
  have hvz := (hv ⟨ze.2, ze.1 :: s.2.node⟩).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hvz
  have hp := M.shockProb_nonneg' z₀ ze (s, x)
  change a * (M.shockProb z₀ ze (s, x) * _) + b * (M.shockProb z₀ ze (s, x) * _)
    ≤ M.shockProb z₀ ze (s, x) * _
  simp only [stateAt]
  nlinarith

theorem objective_eq_contOf (v : M.State →ᵇ ℝ) {s : M.State} {a : ℝ}
    (ha : a ∈ (M.household z₀ K).feasible s) :
    (M.household z₀ K).objective v s a
      = M.utility (M.cash z₀ K s - a) + M.discount * M.contOf z₀ v s a :=
  M.objective_eq z₀ K v ha

/-- **An optimal saving against `v`.** -/
noncomputable def policyOf (v : M.State →ᵇ ℝ) (s : M.State) : ℝ :=
  Classical.choose ((M.household z₀ K).exists_optimal_action v s)

theorem policyOf_mem (v : M.State →ᵇ ℝ) (s : M.State) :
    M.policyOf z₀ K v s ∈ (M.household z₀ K).feasible s :=
  (Classical.choose_spec ((M.household z₀ K).exists_optimal_action v s)).1

theorem bellman_eq_policyOf (v : M.State →ᵇ ℝ) (s : M.State) :
    (M.household z₀ K).bellman v s
      = (M.household z₀ K).objective v s (M.policyOf z₀ K v s) :=
  (Classical.choose_spec ((M.household z₀ K).exists_optimal_action v s)).2.1

theorem policyOf_valueFunction :
    M.policyOf z₀ K (M.household z₀ K).valueFunction = M.policy z₀ K := rfl

/-- The consumption optimal saving against `v` leaves. -/
noncomputable def consumptionOf (v : M.State →ᵇ ℝ) (s : M.State) : ℝ :=
  M.cash z₀ K s - M.policyOf z₀ K v s

theorem bellman_eq_contOf (v : M.State →ᵇ ℝ) (s : M.State) :
    (M.household z₀ K).bellman v s
      = M.utility (M.consumptionOf z₀ K v s) + M.discount * M.contOf z₀ v s (M.policyOf z₀ K v s) :=
  (M.bellman_eq_policyOf z₀ K v s).trans (M.objective_eq_contOf z₀ K v (M.policyOf_mem z₀ K v s))

theorem le_bellman_contOf (v : M.State →ᵇ ℝ) {s : M.State} {a : ℝ}
    (ha : a ∈ (M.household z₀ K).feasible s) :
    M.utility (M.cash z₀ K s - a) + M.discount * M.contOf z₀ v s a
      ≤ (M.household z₀ K).bellman v s := by
  rw [← M.objective_eq_contOf z₀ K v ha]
  exact (M.household z₀ K).le_bellmanFn v ha

/-- **Under concave slices the optimal saving is unique.** -/
theorem eq_policyOf_of_objective {v : M.State →ᵇ ℝ} (hv : M.ConcaveSlices v) {s : M.State}
    {a : ℝ} (ha : a ∈ (M.household z₀ K).feasible s)
    (hval : M.utility (M.cash z₀ K s - a) + M.discount * M.contOf z₀ v s a
      = (M.household z₀ K).bellman v s) :
    a = M.policyOf z₀ K v s := by
  set p := M.policyOf z₀ K v s
  have hp := M.policyOf_mem z₀ K v s
  by_contra hne
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hsum : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
  have hmid : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * p ∈ (M.household z₀ K).feasible s := by
    have h := convex_Icc (0 : ℝ) (M.maxSaving z₀ K s) ha hp hhalf.le hhalf.le hsum
    simp only [smul_eq_mul] at h
    exact h
  have haI := M.mem_Icc_of_mem_feasible z₀ K ha
  have hpI := M.mem_Icc_of_mem_feasible z₀ K hp
  have hca : M.consFloor ≤ M.cash z₀ K s - a := le_sub_comm.1 (ha.2.trans (min_le_right _ _))
  have hcp : M.consFloor ≤ M.cash z₀ K s - p := le_sub_comm.1 (hp.2.trans (min_le_right _ _))
  have hcne : M.cash z₀ K s - a ≠ M.cash z₀ K s - p := fun h => hne (by linarith)
  have hu := M.strictConcaveOn_utility.2 (mem_Ici.2 hca) (mem_Ici.2 hcp) hcne hhalf hhalf hsum
  simp only [smul_eq_mul] at hu
  have hcmid : M.cash z₀ K s - ((1 / 2 : ℝ) * a + (1 / 2 : ℝ) * p)
      = (1 / 2 : ℝ) * (M.cash z₀ K s - a) + (1 / 2 : ℝ) * (M.cash z₀ K s - p) := by ring
  have hc := (M.concaveOn_contOf z₀ hv s).2 haI hpI hhalf.le hhalf.le hsum
  simp only [smul_eq_mul] at hc
  have hβ := mul_le_mul_of_nonneg_left hc M.discount_pos.le
  have hle := M.le_bellman_contOf z₀ K v hmid
  rw [hcmid] at hle
  have hopt : (M.household z₀ K).bellman v s
      = M.utility (M.cash z₀ K s - p) + M.discount * M.contOf z₀ v s p :=
    M.bellman_eq_contOf z₀ K v s
  nlinarith

/-- **Saving against `v` is nondecreasing in assets.** -/
theorem policyOf_mono {v : M.State →ᵇ ℝ} (hv : M.ConcaveSlices v) {a b : ℝ}
    (ha : a ∈ Icc 0 M.assetCap) (hb : b ∈ Icc 0 M.assetCap) (hab : a ≤ b) (l : Label Z E) :
    M.policyOf z₀ K v (M.stateAt a l) ≤ M.policyOf z₀ K v (M.stateAt b l) := by
  set sa := M.stateAt a l
  set sb := M.stateAt b l
  set pa := M.policyOf z₀ K v sa
  set pb := M.policyOf z₀ K v sb
  by_contra hlt
  rw [not_le] at hlt
  have hxa := M.cash_mono z₀ K ha hb hab l
  have hpa := M.policyOf_mem z₀ K v sa
  have hpb := M.policyOf_mem z₀ K v sb
  have hfa : pb ∈ (M.household z₀ K).feasible sa := ⟨hpb.1, hlt.le.trans hpa.2⟩
  have hfb : pa ∈ (M.household z₀ K).feasible sb := by
    refine ⟨hpa.1, le_min (hpa.2.trans (min_le_left _ _)) ?_⟩
    linarith [hpa.2.trans (min_le_right _ _)]
  have h2 := M.le_bellman_contOf z₀ K v hfb
  have hcont : M.contOf z₀ v sb = M.contOf z₀ v sa := M.contOf_label z₀ v b a l
  have hca : M.consFloor ≤ M.cash z₀ K sa - pa := le_sub_comm.1 (hpa.2.trans (min_le_right _ _))
  have hid := concave_increment_le M.strictConcaveOn_utility.concaveOn
    (x := M.cash z₀ K sa - pa) (y := M.cash z₀ K sa - pb) (d := M.cash z₀ K sb - M.cash z₀ K sa)
    (by linarith) (by linarith) (mem_Ici.2 hca) (mem_Ici.2 (by linarith))
  have e1 : M.cash z₀ K sa - pb + (M.cash z₀ K sb - M.cash z₀ K sa) = M.cash z₀ K sb - pb := by
    ring
  have e2 : M.cash z₀ K sa - pa + (M.cash z₀ K sb - M.cash z₀ K sa) = M.cash z₀ K sb - pa := by
    ring
  rw [e1, e2] at hid
  rw [hcont] at h2
  have htie : M.utility (M.cash z₀ K sa - pb) + M.discount * M.contOf z₀ v sa pb
      = (M.household z₀ K).bellman v sa := by
    have v1 : (M.household z₀ K).bellman v sa
        = M.utility (M.cash z₀ K sa - pa) + M.discount * M.contOf z₀ v sa pa :=
      M.bellman_eq_contOf z₀ K v sa
    have v2 : (M.household z₀ K).bellman v sb
        = M.utility (M.cash z₀ K sb - pb) + M.discount * M.contOf z₀ v sa pb := by
      rw [M.bellman_eq_contOf z₀ K v sb, hcont]
      rfl
    have h1 := M.le_bellman_contOf z₀ K v hfa
    linarith
  exact absurd (M.eq_policyOf_of_objective z₀ K hv hfa htie) hlt.ne

/-- **Consumption against `v` is nondecreasing in assets.** -/
theorem consumptionOf_mono {v : M.State →ᵇ ℝ} (hv : M.ConcaveSlices v) {a b : ℝ}
    (ha : a ∈ Icc 0 M.assetCap) (hb : b ∈ Icc 0 M.assetCap) (hab : a ≤ b) (l : Label Z E) :
    M.consumptionOf z₀ K v (M.stateAt a l) ≤ M.consumptionOf z₀ K v (M.stateAt b l) := by
  set sa := M.stateAt a l
  set sb := M.stateAt b l
  set pa := M.policyOf z₀ K v sa
  set pb := M.policyOf z₀ K v sb
  set xa := M.cash z₀ K sa
  set xb := M.cash z₀ K sb
  by_contra hlt
  rw [not_le] at hlt
  have hca : M.consumptionOf z₀ K v sa = xa - pa := rfl
  have hcb : M.consumptionOf z₀ K v sb = xb - pb := rfl
  rw [hca, hcb] at hlt
  have hxa : xa ≤ xb := M.cash_mono z₀ K ha hb hab l
  have hpa := M.policyOf_mem z₀ K v sa
  have hpb := M.policyOf_mem z₀ K v sb
  set δ := (xa - pa) - (xb - pb) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hfa : pa + δ ∈ (M.household z₀ K).feasible sa := by
    refine ⟨by linarith [hpa.1], le_min ?_ ?_⟩
    · linarith [hpb.2.trans (min_le_left _ _)]
    · linarith [hpb.2.trans (min_le_right _ _)]
  have hfb : pb - δ ∈ (M.household z₀ K).feasible sb := by
    refine ⟨by linarith [hpa.1], le_min ?_ ?_⟩
    · linarith [hpb.2.trans (min_le_left _ _)]
    · linarith [hpa.2.trans (min_le_right _ _)]
  have h1 := M.le_bellman_contOf z₀ K v hfa
  have h2 := M.le_bellman_contOf z₀ K v hfb
  have v1 : (M.household z₀ K).bellman v sa
      = M.utility (xa - pa) + M.discount * M.contOf z₀ v sa pa := M.bellman_eq_contOf z₀ K v sa
  have v2 : (M.household z₀ K).bellman v sb
      = M.utility (xb - pb) + M.discount * M.contOf z₀ v sb pb := M.bellman_eq_contOf z₀ K v sb
  have hcont : M.contOf z₀ v sb = M.contOf z₀ v sa := M.contOf_label z₀ v b a l
  rw [hcont] at h2 v2
  have e1 : xa - (pa + δ) = xb - pb := by rw [hδ]; ring
  have e2 : xb - (pb - δ) = xa - pa := by rw [hδ]; ring
  rw [e1] at h1
  rw [e2] at h2
  have hpaI : pa ∈ Icc 0 M.assetCap := M.mem_Icc_of_mem_feasible z₀ K hpa
  have hpbI : pb ∈ Icc 0 M.assetCap := M.mem_Icc_of_mem_feasible z₀ K hpb
  have hle : pa ≤ pb - δ := by rw [hδ]; linarith
  have hid := concave_increment_le (M.concaveOn_contOf z₀ hv sa) (x := pa) (y := pb - δ) (d := δ)
    hle hδ0.le hpaI (by rw [sub_add_cancel]; exact hpbI)
  rw [sub_add_cancel] at hid
  have hscaled := mul_le_mul_of_nonneg_left hid M.discount_pos.le
  have htie : M.utility (xa - (pa + δ)) + M.discount * M.contOf z₀ v sa (pa + δ)
      = (M.household z₀ K).bellman v sa := by
    rw [e1]
    nlinarith
  have := M.eq_policyOf_of_objective z₀ K hv hfa htie
  linarith

end KSModel

end KrusellSmith

end LeanEconomics
