/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationCrossRate

/-!
# The contraction, run on the compact region alone

The value function is a bounded continuous function on all of `ℝ × Z`, but the model only
ever lives on `[0, assetCap] × Z`, which is forward invariant: every feasible choice lands
back in it (`feasible_subset_region`). So the Bellman operator evaluated at a state of the
region never consults the continuation value anywhere else.

That has a consequence worth exploiting. The whole contraction estimate can be run with
suprema taken over the REGION rather than globally:

  sup_region |V_P - V_Q| ≤ (1 - β)⁻¹ * sup_region |bellman_P V_Q - V_Q|

so comparative statics in the interest rate never needs a global sup-norm estimate. Since
the agent distribution also lives on the region, this is all the equilibrium argument
requires. It needs no second programme on the subtype, and no transport: it is a direct
estimate on the objects already built.

The mechanism is that the reward cancels. Two continuation values fed to the same programme
give objectives differing only in the discounted expectation, and the expectation samples
the next asset level, which feasibility confines to the region.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z assetCap)

/-- The region the model lives on. -/
def region (_P : IncomeFluctuation Z assetCap) : Set (ℝ × Z) := {s | s.1 ∈ Icc 0 assetCap}

theorem isCompact_region : IsCompact P.region := by
  have himg : P.region = (Icc 0 assetCap) ×ˢ (univ : Set Z) := by
    ext s; simp [region, Set.mem_prod]
  rw [himg]
  exact isCompact_Icc.prod isCompact_univ

theorem region_nonempty : P.region.Nonempty :=
  ⟨(0, Classical.ofNonempty), by simp [region, P.assetCap_nonneg]⟩

/-- **The expectation only samples the region.** This is forward invariance in the form the
estimate needs. -/
theorem abs_expect_sub_le {v w : (ℝ × Z) →ᵇ ℝ} {c : ℝ}
    (hvw : ∀ t : ℝ × Z, t ∈ P.region → |v t - w t| ≤ c) {s : ℝ × Z} {a : ℝ}
    (ha : a ∈ P.toExtended.feasible s) :
    |P.toExtended.expect v (s, a) - P.toExtended.expect w (s, a)| ≤ c := by
  have htr : ∀ z' : Z, P.toExtended.transition z' (s, a) = (a, z') := fun _ => rfl
  have hreg : ∀ z' : Z, P.toExtended.transition z' (s, a) ∈ P.region := fun z' => by
    rw [htr z']; exact P.feasible_subset_region ha
  simp only [ExtendedStochasticProgram.expect, ← Finset.sum_sub_distrib, ← mul_sub]
  calc |∑ z', P.toExtended.prob z' (s, a)
          * (v (P.toExtended.transition z' (s, a)) - w (P.toExtended.transition z' (s, a)))|
      ≤ ∑ z', |P.toExtended.prob z' (s, a)
          * (v (P.toExtended.transition z' (s, a)) - w (P.toExtended.transition z' (s, a)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z' : Z, P.toExtended.prob z' (s, a) * c := by
        refine Finset.sum_le_sum fun z' _ => ?_
        rw [abs_mul, abs_of_nonneg (P.toExtended.prob_nonneg z' _)]
        exact mul_le_mul_of_nonneg_left (hvw _ (hreg z')) (P.toExtended.prob_nonneg z' _)
    _ = c := by rw [← Finset.sum_mul, P.toExtended.prob_sum, one_mul]

/-- **The operator contracts, measured on the region alone.** The reward cancels, so the two
objectives differ only in the discounted expectation, and the expectation samples the next
asset level, which feasibility confines to the region. -/
theorem abs_bellmanFn_sub_le_region {v w : (ℝ × Z) →ᵇ ℝ} {c : ℝ}
    (hvw : ∀ t : ℝ × Z, t ∈ P.region → |v t - w t| ≤ c) (s : ℝ × Z) :
    |P.toExtended.bellmanFn v s - P.toExtended.bellmanFn w s| ≤ P.discount * c := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have key : ∀ v w : (ℝ × Z) →ᵇ ℝ, (∀ t : ℝ × Z, t ∈ P.region → |v t - w t| ≤ c) →
      P.toExtended.bellmanFn v s ≤ P.toExtended.bellmanFn w s + P.discount * c := by
    intro v w hvw
    refine P.toExtended.bellmanFn_le v fun a ha => ?_
    have hstep : P.toExtended.objectiveE v s a
        ≤ P.toExtended.objectiveE w s a + ((P.discount * c : ℝ) : EReal) := by
      simp only [ExtendedStochasticProgram.objectiveE]
      rw [add_assoc, ← EReal.coe_add]
      refine add_le_add (le_refl _) ?_
      rw [EReal.coe_le_coe_iff]
      have hexp := P.abs_expect_sub_le hvw ha
      rw [abs_le] at hexp
      -- `toExtended.discount` and `discount` are defeq but distinct atoms to `linarith`
      rw [show (P.toExtended.discount : ℝ) = (P.discount : ℝ) from rfl]
      nlinarith [hexp.2, hβ]
    refine le_trans hstep ?_
    rw [EReal.coe_add]
    exact add_le_add (P.toExtended.le_bellmanFn w ha) (le_refl _)
  have hc : 0 ≤ c :=
    le_trans (abs_nonneg _) (hvw (0, Classical.ofNonempty) (by simp [region, P.assetCap_nonneg]))
  have k1 := key v w hvw
  have k2 := key w v fun t ht => by rw [abs_sub_comm]; exact hvw t ht
  rw [abs_le]
  constructor <;> linarith

/-- **The bridge.** Two value functions differ on the region by at most the operator gap on
the region, amplified by `(1 - β)⁻¹`. Every norm here is taken over the COMPACT REGION, so
comparative statics in the interest rate never needs a global sup-norm estimate.

Since the agent distribution also lives on the region, this is all the equilibrium argument
requires. Note it needs no second programme on the compact state space and no transport --
it is a direct estimate on the objects already built. -/
theorem abs_valueFunction_sub_le_region {P Q : IncomeFluctuation Z assetCap} {D : ℝ}
    (hD : ∀ t : ℝ × Z, t ∈ P.region →
      |P.toExtended.bellmanFn Q.toExtended.valueFunction t
        - Q.toExtended.valueFunction t| ≤ D)
    {s : ℝ × Z} (hs : s ∈ P.region) :
    |P.toExtended.valueFunction s - Q.toExtended.valueFunction s|
      ≤ D / (1 - P.discount) := by
  have hβ1 : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
  have hβ0 : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  set f : ℝ × Z → ℝ :=
    fun t => |P.toExtended.valueFunction t - Q.toExtended.valueFunction t| with hf
  have hcont : ContinuousOn f P.region :=
    ((P.toExtended.valueFunction.continuous.sub
      Q.toExtended.valueFunction.continuous).abs).continuousOn
  obtain ⟨t, htmem, htmax⟩ :=
    P.isCompact_region.exists_isMaxOn P.region_nonempty hcont
  have hCle : ∀ u : ℝ × Z, u ∈ P.region → f u ≤ f t := fun u hu => htmax hu
  -- the contraction, measured on the region
  have hstep : f t ≤ P.discount * f t + D := by
    have h1 : P.toExtended.valueFunction t
        = P.toExtended.bellmanFn P.toExtended.valueFunction t := by
      rw [← P.toExtended.bellman_apply, P.toExtended.bellman_valueFunction]
    have h2 := P.abs_bellmanFn_sub_le_region
      (v := P.toExtended.valueFunction) (w := Q.toExtended.valueFunction) (c := f t)
      (fun u hu => hCle u hu) t
    have h3 := hD t htmem
    have htri : |P.toExtended.bellmanFn P.toExtended.valueFunction t
          - Q.toExtended.valueFunction t|
        ≤ |P.toExtended.bellmanFn P.toExtended.valueFunction t
            - P.toExtended.bellmanFn Q.toExtended.valueFunction t|
          + |P.toExtended.bellmanFn Q.toExtended.valueFunction t
            - Q.toExtended.valueFunction t| := abs_sub_le _ _ _
    have h4 : f t = |P.toExtended.bellmanFn P.toExtended.valueFunction t
        - Q.toExtended.valueFunction t| := by rw [hf]; simp only [← h1]
    calc f t = |P.toExtended.bellmanFn P.toExtended.valueFunction t
          - Q.toExtended.valueFunction t| := h4
      _ ≤ |P.toExtended.bellmanFn P.toExtended.valueFunction t
            - P.toExtended.bellmanFn Q.toExtended.valueFunction t|
          + |P.toExtended.bellmanFn Q.toExtended.valueFunction t
            - Q.toExtended.valueFunction t| := htri
      _ ≤ P.discount * f t + D := add_le_add h2 h3
  have hC : f t ≤ D / (1 - P.discount) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hstep]
  exact le_trans (hCle s hs) hC

end IncomeFluctuation

end LeanEconomics
