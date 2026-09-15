/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuation
import LeanEconomics.Analysis.DifferentiableSandwich

/-!
# The lazy agent's value, and the envelope condition

Clausen and Strub's construction: to show the value function is differentiable in assets,
exhibit a differentiable LOWER bound touching it. Freeze the optimal saving and vary the
state — the "lazy" agent, who meets an unfamiliar state by making the choice that was optimal
at a familiar one.

The point is structural. Once the saving is frozen, current assets enter the objective ONLY
through the reward, because the continuation value depends on the saving chosen and on the
current income state, never on current assets. So the lazy value is `u` composed with an
affine map plus a constant, and is differentiable wherever `u` is.

Concavity of the value function, already proved, then supplies the upper half of the sandwich
via `ConcaveOn.hasDerivAt_of_lowerBound`, and the derivative is the envelope condition

  V'(a) = (1 + r) · u'(c),

which is the expression Light (2018) Theorem 1 is built on.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z assetCap)

/-- **The lazy agent's value.** The saving `a'` is frozen; only current assets vary. -/
noncomputable def lazyValue (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (a' a : ℝ) : ℝ :=
  P.u (P.resources (a, z) - a')
    + P.discount * ∑ z' : Z, P.transitionMatrix z z' * v (a', z')

/-- Resources are affine in assets above the borrowing constraint. -/
theorem hasDerivAt_resources {z : Z} {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun x => P.resources (x, z)) (1 + P.interest) a := by
  have heq : (fun x => P.resources (x, z)) =ᶠ[𝓝 a] fun x => P.income z + (1 + P.interest) * x := by
    filter_upwards [lt_mem_nhds ha] with x hx
    simp only [resources, max_eq_right hx.le]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  simpa using ((hasDerivAt_id a).const_mul (1 + P.interest)).const_add (P.income z)

/-- **The lazy value is differentiable**, because current assets enter only through the
reward once the saving is frozen. -/
theorem hasDerivAt_lazyValue (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (a' : ℝ) {a du : ℝ} (ha : 0 < a)
    (hu : HasDerivAt P.u du (P.resources (a, z) - a')) :
    HasDerivAt (P.lazyValue v z a') ((1 + P.interest) * du) a := by
  have hinner : HasDerivAt (fun x => P.resources (x, z) - a') (1 + P.interest) a :=
    (P.hasDerivAt_resources ha).sub_const a'
  have hcomp : HasDerivAt (fun x => P.u (P.resources (x, z) - a'))
      (du * (1 + P.interest)) a := hu.comp a hinner
  have hsum := hcomp.add_const
    ((P.discount : ℝ) * ∑ z' : Z, P.transitionMatrix z z' * v (a', z'))
  rw [mul_comm du (1 + P.interest)] at hsum
  exact hsum

/-- **The lazy value is a lower bound**: freezing a feasible saving can only do worse than
optimising. -/
theorem lazyValue_le (v : (ℝ × Z) →ᵇ ℝ) (z : Z) {a' a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hmem : a' ∈ P.toExtended.feasible (a, z)) (hc : 0 < P.consumption (a, z) a') :
    P.lazyValue v z a' a ≤ P.toExtended.bellmanFn v (a, z) := by
  have hobj := P.toExtended.le_bellmanFn v hmem
  have hrw := P.reward_eq_coe (s := (a, z)) ha hmem hc
  have hdx : (P.toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  rw [ExtendedStochasticProgram.objectiveE, hrw, hdx, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at hobj
  exact hobj

/-- At the optimum the lazy value touches the Bellman value. -/
theorem lazyValue_eq (v : (ℝ × Z) →ᵇ ℝ) (z : Z) {a' a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hmem : a' ∈ P.toExtended.feasible (a, z)) (hc : 0 < P.consumption (a, z) a')
    (hopt : P.toExtended.objectiveE v (a, z) a'
      = ((P.toExtended.bellmanFn v (a, z) : ℝ) : EReal)) :
    P.lazyValue v z a' a = P.toExtended.bellmanFn v (a, z) := by
  have hrw := P.reward_eq_coe (s := (a, z)) ha hmem hc
  have hdx : (P.toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  rw [ExtendedStochasticProgram.objectiveE, hrw, hdx, ← EReal.coe_add,
    EReal.coe_eq_coe_iff] at hopt
  exact hopt

end IncomeFluctuation

end LeanEconomics
