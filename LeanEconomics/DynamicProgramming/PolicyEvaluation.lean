/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Stochastic

/-!
# Policy evaluation and verification for stochastic dynamic programs

For a continuous policy `σ : S → A`:

* `policyOp hσ v s = objective v s (σ s)`: the operator of following `σ` today and receiving
  `v` tomorrow; it satisfies Blackwell's conditions (`blackwell_policyOp`), so it has a unique
  fixed point, **the value of following `σ`**, `policyValue hσ` (`policyValue_eq`);
* **verification** (`policyValue_eq_valueFunction`): if `σ` is feasible and, against its own
  value, attains the maximum of the objective at every state, then its value is the value
  function; `bellman_eq_objective_policy`: `σ` then attains the Bellman value.
-/

open scoped NNReal
open Filter Topology BoundedContinuousFunction

namespace LeanEconomics

variable {S A Z : Type*} [TopologicalSpace S] [TopologicalSpace A] [Fintype Z]

namespace StochasticDynamicProgram

variable (D : StochasticDynamicProgram S A Z) {σ : S → A} (hσ : Continuous σ)

/-- **Following the policy `σ` today**, with continuation value `v`. -/
noncomputable def policyOp (v : S →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun s => D.objective v s (σ s))
    (by
      have h := (D.continuous_uncurry_objective v).comp (continuous_id.prodMk hσ)
      exact h)
    (‖D.reward‖ + D.discount * ‖v‖)
    fun s => by simpa [Real.norm_eq_abs] using D.abs_objective_le v s (σ s)

@[simp]
theorem policyOp_apply (v : S →ᵇ ℝ) (s : S) : D.policyOp hσ v s = D.objective v s (σ s) := rfl

/-- **Blackwell's conditions** for the policy operator. -/
theorem blackwell_policyOp : Blackwell D.discount (D.policyOp hσ) where
  monotone := by
    intro v w hvw s
    have hβ : (0 : ℝ) ≤ D.discount := D.discount.coe_nonneg
    have hsum : D.expectation v (s, σ s) ≤ D.expectation w (s, σ s) := by
      refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (D.prob_nonneg z _)
      simpa using hvw (D.transition z (s, σ s))
    change D.objective v s (σ s) ≤ D.objective w s (σ s)
    simp only [objective]
    nlinarith
  discounting := by
    intro v c _ s
    have hterm : ∀ z : Z, D.prob z (s, σ s) * (v + const S c) (D.transition z (s, σ s))
        = D.prob z (s, σ s) * v (D.transition z (s, σ s)) + D.prob z (s, σ s) * c := fun z => by
      simp only [coe_add, const_apply, Pi.add_apply]; ring
    have hsum : D.expectation (v + const S c) (s, σ s) = D.expectation v (s, σ s) + c := by
      simp only [expectation]
      rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_add_distrib,
        ← Finset.sum_mul, D.prob_sum, one_mul]
    change D.objective (v + const S c) s (σ s) ≤ D.objective v s (σ s) + D.discount * c
    simp only [objective, hsum]
    nlinarith [D.discount.coe_nonneg]

/-- **The value of following `σ`.** -/
noncomputable def policyValue : S →ᵇ ℝ :=
  (D.blackwell_policyOp hσ).valueFunction D.discount_lt_one

/-- The value of following `σ` solves its own Bellman equation. -/
theorem policyValue_eq (s : S) :
    D.policyValue hσ s = D.objective (D.policyValue hσ) s (σ s) := by
  have h := (D.blackwell_policyOp hσ).isFixedPt_valueFunction D.discount_lt_one
  exact (congrArg (fun v : S →ᵇ ℝ => v s) h).symm

variable {D hσ}

/-- **Verification**: a feasible policy that attains the maximum against its own value has the
value function as its value. -/
theorem policyValue_eq_valueFunction (hfeas : ∀ s, σ s ∈ D.feasible s)
    (hopt : ∀ s, ∀ a ∈ D.feasible s,
      D.objective (D.policyValue hσ) s a ≤ D.objective (D.policyValue hσ) s (σ s)) :
    D.policyValue hσ = D.valueFunction := by
  refine D.eq_valueFunction (BoundedContinuousFunction.ext fun s => ?_)
  rw [bellman_apply, maxValue_eq (D.continuous_uncurry_objective _) (D.isCompact_feasible s)
    ⟨hfeas s, isMaxOn_iff.2 (hopt s)⟩, ← D.policyValue_eq hσ s]

/-- Under verification, **`σ` attains the Bellman value** of the value function. -/
theorem bellman_eq_objective_policy (hfeas : ∀ s, σ s ∈ D.feasible s)
    (hopt : ∀ s, ∀ a ∈ D.feasible s,
      D.objective (D.policyValue hσ) s a ≤ D.objective (D.policyValue hσ) s (σ s)) (s : S) :
    D.objective D.valueFunction s (σ s) = D.bellmanFn D.valueFunction s := by
  have hV := policyValue_eq_valueFunction hfeas hopt
  have h := maxValue_eq (D.continuous_uncurry_objective (D.policyValue hσ))
    (D.isCompact_feasible s) ⟨hfeas s, isMaxOn_iff.2 (hopt s)⟩
  rw [hV] at h
  exact h.symm

end StochasticDynamicProgram

end LeanEconomics
