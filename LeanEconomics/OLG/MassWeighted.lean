/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.Equilibrium

/-!
# The earnings marginal of a cohort, and the mass-weighted failure of Theorem 1

The increment argument of `Increment` needs, at each age, the MASS-WEIGHTED failure of Theorem 1

  `ē_j = 𝔼[(g¹_j - g²_j)^+]`,

the expectation taken under the lower-rate economy's own age-`j` distribution. Bounding an
expectation against a distribution one does not control looks like the hard part, and it would be
if the failure were spread over assets. Measured, it is not: at the calibration the failure is
confined to the HIGH-EARNINGS states, and within those it reaches down to zero assets. It is an
earnings-state phenomenon.

That is the coordinate in which no estimate is needed. Earnings are exogenous and the cohort is born
with its state drawn from the invariant law, so the earnings marginal is `ν` at EVERY age, exactly.
Hence

  `ē_j ≤ ∑_z ν z * V_j z`,   `V_j z = sup over assets of the failure at earnings state z`,

which is exact in earnings and worst-case only in assets. At the calibration that is the difference
between a bound of `0.98` and one of `0.032` against a budget of `0.67`: the violating states at
`γ = 5` are the top two, carrying `ν` mass `0.095`.

What remains is a primitive bound on `V_j z`, a statement about the household at one earnings state
with no distribution in it — the `StageSlack` object of `RateMonotone`, read quantitatively.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- The one-step transform of a function of the earnings state. -/
noncomputable def incomeStep (g : Z → ℝ) : Z → ℝ :=
  fun z => ∑ z', P.transitionMatrix z z' * g z'

/-- A `stageStep` applied to a function of the earnings state alone forgets the assets: the policy
enters only through the asset coordinate, which the function ignores. -/
theorem stageStep_of_incomeFn (k : ℕ) (g : Z → ℝ) (s : ℝ × Z) :
    P.stageStep k (fun t => g t.2) s = P.incomeStep g s.2 := rfl

/-- **One step preserves an invariant earnings law.** -/
theorem sum_mul_incomeStep {ν : Z → ℝ}
    (hinv : ∀ z' : Z, ∑ z, ν z * P.transitionMatrix z z' = ν z') (g : Z → ℝ) :
    ∑ z, ν z * P.incomeStep g z = ∑ z, ν z * g z := by
  unfold incomeStep
  calc ∑ z, ν z * ∑ z', P.transitionMatrix z z' * g z'
      = ∑ z, ∑ z', ν z * P.transitionMatrix z z' * g z' := by
        exact Finset.sum_congr rfl fun z _ => by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z' _ => by ring
    _ = ∑ z', ∑ z, ν z * P.transitionMatrix z z' * g z' := Finset.sum_comm
    _ = ∑ z', (∑ z, ν z * P.transitionMatrix z z') * g z' := by
        exact Finset.sum_congr rfl fun z' _ => by rw [Finset.sum_mul]
    _ = ∑ z', ν z' * g z' := by
        exact Finset.sum_congr rfl fun z' _ => by rw [hinv z']

/-- **The earnings marginal of a cohort is `ν` at every age.** Iterating the transform leaves the
`ν`-weighted expectation of any function of the earnings state unchanged. No estimate of the joint
distribution is involved: earnings are exogenous and the cohort is born from the invariant law. -/
theorem sum_mul_incomeStep_iterate {ν : Z → ℝ}
    (hinv : ∀ z' : Z, ∑ z, ν z * P.transitionMatrix z z' = ν z') (g : Z → ℝ) (j : ℕ) :
    ∑ z, ν z * (P.incomeStep^[j] g) z = ∑ z, ν z * g z := by
  induction j generalizing g with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    rw [ih (P.incomeStep g)]
    exact P.sum_mul_incomeStep hinv g

omit [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z] in
/-- **The mass-weighted failure is bounded by its `ν`-weighted, asset-worst-case value.** With the
earnings marginal exactly `ν` at every age, a bound on the failure that is uniform in assets at each
earnings state gives a bound on the expectation, with the earnings weights carried exactly. -/
theorem sum_mul_le_of_le {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) {v V : Z → ℝ} (h : ∀ z, v z ≤ V z) :
    ∑ z, ν z * v z ≤ ∑ z, ν z * V z :=
  Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (h z) (hν z)

end IncomeFluctuation

end LeanEconomics
