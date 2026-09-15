/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationRegion

/-!
# Varying the interest rate

The cross-rate estimates so far take two programmes plus a hypothesis for each field they
must share -- income, maximum income, minimum income, the transition matrix, the discount
factor, the utility function. Six hypotheses is a signal that the wrong object is being
quantified over: in the comparative statics only the INTEREST RATE varies.

`withRate` makes that structural. Every field except `interest` is inherited, so every
sharing hypothesis becomes `rfl` and disappears from the statements, and
`fun r => P.withRate r _` is the family the equilibrium theorem wants.

The other content here is the step that turns the two argument gaps -- in consumption and in
the continuation value -- into a comparison of objectives. It is stated with the gaps as
hypotheses, so the analytic work (uniform continuity) and the arithmetic (extended reals)
stay separate.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z assetCap)

/-- The same household problem at a different interest rate. -/
def withRate (r : ℝ) (hr : 0 < 1 + r) : IncomeFluctuation Z assetCap :=
  { P with interest := r, interest_gt_neg_one := hr }

@[simp] theorem withRate_interest (r : ℝ) (hr : 0 < 1 + r) :
    (P.withRate r hr).interest = r := rfl
@[simp] theorem withRate_income (r : ℝ) (hr : 0 < 1 + r) :
    (P.withRate r hr).income = P.income := rfl
@[simp] theorem withRate_maxIncome (r : ℝ) (hr : 0 < 1 + r) :
    (P.withRate r hr).maxIncome = P.maxIncome := rfl
@[simp] theorem withRate_minIncome (r : ℝ) (hr : 0 < 1 + r) :
    (P.withRate r hr).minIncome = P.minIncome := rfl
@[simp] theorem withRate_u (r : ℝ) (hr : 0 < 1 + r) :
    (P.withRate r hr).u = P.u := rfl
@[simp] theorem withRate_discount (r : ℝ) (hr : 0 < 1 + r) :
    (P.withRate r hr).discount = P.discount := rfl
@[simp] theorem withRate_transitionMatrix (r : ℝ) (hr : 0 < 1 + r) :
    (P.withRate r hr).transitionMatrix = P.transitionMatrix := rfl
@[simp] theorem withRate_region (r : ℝ) (hr : 0 < 1 + r) :
    (P.withRate r hr).region = P.region := rfl
@[simp] theorem withRate_loBound (r : ℝ) (hr : 0 < 1 + r) (v : (ℝ × Z) →ᵇ ℝ) :
    (P.withRate r hr).toExtended.loBound v = P.toExtended.loBound v := rfl

/-- **From argument gaps to an objective comparison.**

The reward is real at both actions because consumption is positive at both -- which is what
the cutoff delivers -- so the extended-real objective collapses to a real one and the
comparison is ordinary arithmetic. Keeping the two gaps as hypotheses separates the analytic
work from the arithmetic. -/
theorem objectiveE_le_of_gaps (v : (ℝ × Z) →ᵇ ℝ) {r r' : ℝ} (hr : 0 < 1 + r) (hr' : 0 < 1 + r')
    {s : ℝ × Z} (hs : s ∈ P.region) {a a' : ℝ}
    (ha : a ∈ (P.withRate r hr).toExtended.feasible s)
    (ha' : a' ∈ (P.withRate r' hr').toExtended.feasible s)
    (hcA : 0 < (P.withRate r hr).consumption s a)
    (hcB : 0 < (P.withRate r' hr').consumption s a')
    {e₁ e₂ : ℝ}
    (hu : P.u ((P.withRate r hr).consumption s a)
        - P.u ((P.withRate r' hr').consumption s a') ≤ e₁)
    (hv : (P.withRate r hr).toExtended.expect v (s, a)
        - (P.withRate r' hr').toExtended.expect v (s, a') ≤ e₂) :
    (P.withRate r hr).toExtended.objectiveE v s a
      ≤ (P.withRate r' hr').toExtended.objectiveE v s a'
        + ((e₁ + P.discount * e₂ : ℝ) : EReal) := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hrwA := (P.withRate r hr).reward_eq_coe hs ha hcA
  have hrwB := (P.withRate r' hr').reward_eq_coe hs ha' hcB
  have hdA : ((P.withRate r hr).toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  have hdB : ((P.withRate r' hr').toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  simp only [ExtendedStochasticProgram.objectiveE, hrwA, hrwB, hdA, hdB]
  rw [← EReal.coe_add, add_assoc, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hu' : (P.withRate r hr).u = P.u := rfl
  have hu'' : (P.withRate r' hr').u = P.u := rfl
  rw [hu', hu''] at *
  nlinarith [hu, hv, hβ]

end IncomeFluctuation

end LeanEconomics
