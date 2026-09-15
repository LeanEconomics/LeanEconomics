/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuation

/-!
# The agent distribution: state space and Markov operator

Step one towards a stationary agent distribution for the income fluctuation problem.

## The compact state space

The model is posed with state space `ℝ × Z`, but a distribution has to live somewhere
compact -- Prokhorov's theorem, which supplies the compactness of the space of probability
measures, needs a compact underlying space. The household never leaves
`[0, assetCap] × Z`, so that is where the distribution lives, and `State` is that region as
a space in its own right rather than as a subset of a larger one.

Taking it as a subtype is forced. A *subset* of `ℝ × Z` would not be a compact space, and
the earlier concavity work could not use a subtype because it is not a module over `ℝ`.
Both choices are right in their own place: concavity needs the linear structure of the
ambient space, the distribution needs compactness of the region.

## The Markov operator

`markovOp h s` is the expected value of `h` at next period's state, given that the household
is at `s` today and follows its optimal policy. The content of the definition is that it
lands in the *bounded continuous* functions again:

* continuity is the **Feller property**, and comes from continuity of the optimal policy,
  which is what the whole concavity and uniqueness development was for;
* boundedness is immediate from `∑ prob = 1`.

Feller is what will make the induced map on probability measures continuous, and continuity
of that map is what a fixed point argument needs.

## What is not here

The operator on measures itself. Mathlib has `Measure.bind` and `lintegral_bind` but no
Bochner `integral_bind`, so the measure side is better built from `Measure.map` and
`Measure.withDensity`, whose Bochner lemmas do exist. That is the other half of this step.
-/

open scoped NNReal
open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable (P : IncomeFluctuation Z)

/-- The compact region the agent distribution lives on: assets in `[0, assetCap]` paired
with an income state. -/
def State : Type _ := ↥(Icc (0 : ℝ) P.assetCap) × Z

noncomputable instance : TopologicalSpace P.State := inferInstanceAs (TopologicalSpace (_ × _))

instance : CompactSpace P.State :=
  haveI : CompactSpace ↥(Icc (0 : ℝ) P.assetCap) := isCompact_iff_compactSpace.mp isCompact_Icc
  inferInstanceAs (CompactSpace (_ × _))

/-- The region, read back as a state of the original model. -/
def incl (s : P.State) : ℝ × Z := ((s.1 : ℝ), s.2)

theorem continuous_incl : Continuous P.incl :=
  (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd

theorem incl_mem (s : P.State) : (P.incl s).1 ∈ Icc 0 P.assetCap := s.1.2

/-- Next period's assets under the optimal policy, as a point of the region. -/
noncomputable def nextAssets (s : P.State) : ↥(Icc (0 : ℝ) P.assetCap) :=
  ⟨P.policy (P.incl s), P.policy_mem_region _⟩

/-- Next period's state if the income shock `z'` occurs. -/
noncomputable def nextState (s : P.State) (z' : Z) : P.State := (P.nextAssets s, z')

/-- **The policy moves the household continuously within the region.** This is the Feller
input, and it is exactly what the concavity and uniqueness development bought. -/
theorem continuous_nextAssets : Continuous P.nextAssets :=
  (P.continuousOn_policy.comp_continuous P.continuous_incl P.incl_mem).subtype_mk _

theorem continuous_nextState (z' : Z) : Continuous fun s => P.nextState s z' :=
  P.continuous_nextAssets.prodMk continuous_const

/-- The probability of moving to income state `z'`, as a function of today's state. -/
noncomputable def prob (s : P.State) (z' : Z) : ℝ := P.transitionMatrix s.2 z'

theorem prob_nonneg (s : P.State) (z' : Z) : 0 ≤ P.prob s z' := P.transitionMatrix_nonneg _ _

theorem prob_sum (s : P.State) : ∑ z', P.prob s z' = 1 := P.transitionMatrix_sum _

theorem continuous_prob (z' : Z) : Continuous fun s => P.prob s z' :=
  (continuous_of_discreteTopology (f := fun z => P.transitionMatrix z z')).comp continuous_snd

/-- The expected value of `h` next period, as a bare function. -/
noncomputable def markovFn (h : P.State →ᵇ ℝ) (s : P.State) : ℝ :=
  ∑ z', P.prob s z' * h (P.nextState s z')

theorem continuous_markovFn (h : P.State →ᵇ ℝ) : Continuous (P.markovFn h) :=
  continuous_finsetSum _ fun z' _ =>
    (P.continuous_prob z').mul (h.continuous.comp (P.continuous_nextState z'))

theorem abs_markovFn_le (h : P.State →ᵇ ℝ) (s : P.State) : |P.markovFn h s| ≤ ‖h‖ := by
  calc |P.markovFn h s| ≤ ∑ z', |P.prob s z' * h (P.nextState s z')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z', P.prob s z' * |h (P.nextState s z')| := by
        refine Finset.sum_congr rfl fun z' _ => ?_
        rw [abs_mul, abs_of_nonneg (P.prob_nonneg s z')]
    _ ≤ ∑ z', P.prob s z' * ‖h‖ := by
        refine Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left ?_ (P.prob_nonneg s z')
        simpa [Real.norm_eq_abs] using h.norm_coe_le_norm (P.nextState s z')
    _ = ‖h‖ := by rw [← Finset.sum_mul, P.prob_sum, one_mul]

/-- **The Markov operator.** `markovOp h` is the expected value of `h` next period. That it
is again bounded and *continuous* is the Feller property. -/
noncomputable def markovOp (h : P.State →ᵇ ℝ) : P.State →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (P.markovFn h) (P.continuous_markovFn h) ‖h‖
    fun s => by simpa [Real.norm_eq_abs] using P.abs_markovFn_le h s

@[simp]
theorem markovOp_apply (h : P.State →ᵇ ℝ) (s : P.State) :
    P.markovOp h s = ∑ z', P.prob s z' * h (P.nextState s z') := rfl

theorem norm_markovOp_le (h : P.State →ᵇ ℝ) : ‖P.markovOp h‖ ≤ ‖h‖ :=
  (norm_le (norm_nonneg h)).2 fun s => by
    rw [Real.norm_eq_abs]
    exact P.abs_markovFn_le h s

/-- The operator is monotone: a larger payoff tomorrow is worth more today. -/
theorem markovOp_mono {h k : P.State →ᵇ ℝ} (hk : ⇑h ≤ ⇑k) : ⇑(P.markovOp h) ≤ ⇑(P.markovOp k) := by
  intro s
  refine Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left ?_ (P.prob_nonneg s z')
  exact hk _

/-- The operator is unital: a constant payoff is worth its own value. This is `∑ prob = 1`,
and it is what will make the induced map send probability measures to probability
measures. -/
theorem markovOp_const (c : ℝ) : P.markovOp (const P.State c) = const P.State c := by
  ext s
  simp only [markovOp_apply, const_apply, ← Finset.sum_mul, P.prob_sum, one_mul]

end IncomeFluctuation

end LeanEconomics
