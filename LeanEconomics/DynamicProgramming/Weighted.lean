/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Stochastic

/-!
# Weighted supremum norms: dynamic programs with unbounded rewards

Every model so far has capped the state space, because the reward had to be bounded. This
file removes that requirement. The reward may grow without bound, provided it grows no
faster than a chosen **weight** `w ≥ 1`, and provided the weight grows slowly enough along
the law of motion.

## The reduction

The textbook route (Boyd 1990) builds the Banach space
`B_w = {v | sup |v s| / w s < ∞}` and redoes the fixed point theory there. That is
unnecessary. The map `v ↦ v / w` is a bijection from `B_w` onto the bounded continuous
functions carrying the weighted norm to the supremum norm, so conjugating the Bellman
operator by it,

  `T̃ u = T (u * w) / w`,

gives an operator on `S →ᵇ ℝ` that is a contraction exactly when `T` is one on `B_w`. No new
space, no new fixed point theorem: `LeanEconomics.Blackwell` applies to `T̃` as it stands.
Working with `T̃` is what this file does, and `valueFunction` multiplies the weight back in
at the end.

Under the conjugation, Blackwell's two conditions become conditions on the coefficients
`β * p z * w (g z) / w`, which are what multiply the continuation value in `T̃`:

* they are nonnegative, giving **monotonicity**;
* they sum to at most `modulus < 1`, giving **discounting**.

## The drift condition

That second requirement is the field `drift`:

  `β * ∑ z, p z (s,a) * w (g z (s,a)) ≤ modulus * w s`.

In words: the discounted expected weight of tomorrow's state is a fraction `modulus < 1` of
today's. It is the price of dropping the cap, and it is a genuine economic restriction, not
a technical one. In a savings problem with weight growing like assets it amounts to
`β * (1 + r) < 1`: a household that is not impatient relative to the interest rate
accumulates without bound, and then no weight makes the value finite.

## Main results

* `LeanEconomics.WeightedDynamicProgram.blackwell` : the conjugated operator is a
  contraction of modulus `modulus`.
* `LeanEconomics.WeightedDynamicProgram.exists_optimal_policy` : the value function,
  weight multiplied back in, satisfies the Bellman equation of the original unbounded
  problem.
* `LeanEconomics.StochasticDynamicProgram.toWeighted` : a bounded-reward program is the
  special case `w = 1`, so this genuinely generalises the previous file.
-/

open scoped NNReal
open Filter Topology BoundedContinuousFunction

namespace LeanEconomics

variable {S A Z : Type*} [TopologicalSpace S] [TopologicalSpace A] [Fintype Z]

/-- A dynamic program whose reward is bounded only relative to a weight `w`. -/
structure WeightedDynamicProgram (S A Z : Type*) [TopologicalSpace S] [TopologicalSpace A]
    [Fintype Z] where
  /-- The actions available at each state. -/
  feasible : S → Set A
  isCompact_feasible : ∀ s, IsCompact (feasible s)
  feasible_nonempty : ∀ s, (feasible s).Nonempty
  upperHemicontinuous_feasible : UpperHemicontinuous feasible
  lowerHemicontinuous_feasible : LowerHemicontinuous feasible
  /-- The weight, against which the reward is measured. -/
  w : C(S, ℝ)
  one_le_w : ∀ s, 1 ≤ w s
  /-- The reward divided by the weight. That this is bounded is exactly the statement that
  the reward grows no faster than `w`. -/
  rewardOverWeight : (S × A) →ᵇ ℝ
  /-- The state reached when shock `z` occurs. -/
  transition : Z → C(S × A, S)
  /-- The probability that shock `z` occurs. -/
  prob : Z → C(S × A, ℝ)
  prob_nonneg : ∀ z p, 0 ≤ prob z p
  discount : ℝ≥0
  /-- The contraction modulus, which the drift condition delivers. -/
  modulus : ℝ≥0
  modulus_lt_one : modulus < 1
  /-- **The drift condition.** Discounted expected weight tomorrow is at most `modulus`
  times the weight today. It is required only at *feasible* actions, which matters: an
  infeasible action can send the state anywhere, and no weight could survive that. -/
  drift : ∀ s, ∀ a ∈ feasible s,
    discount * ∑ z, prob z (s, a) * w (transition z (s, a)) ≤ modulus * w s

namespace WeightedDynamicProgram

variable (D : WeightedDynamicProgram S A Z)

theorem w_pos (s : S) : 0 < D.w s := lt_of_lt_of_le zero_lt_one (D.one_le_w s)

theorem w_ne_zero (s : S) : D.w s ≠ 0 := ne_of_gt (D.w_pos s)

/-- The discounted expected continuation value, divided by the weight at the current
state. -/
noncomputable def expectation (u : S →ᵇ ℝ) (p : S × A) : ℝ :=
  (D.discount * ∑ z, D.prob z p * D.w (D.transition z p) * u (D.transition z p)) / D.w p.1

/-- The objective of the conjugated operator. -/
noncomputable def objective (u : S →ᵇ ℝ) (s : S) (a : A) : ℝ :=
  D.rewardOverWeight (s, a) + D.expectation u (s, a)

theorem continuous_expectation (u : S →ᵇ ℝ) : Continuous (D.expectation u) := by
  refine Continuous.div ?_ (D.w.continuous.comp continuous_fst) fun p => D.w_ne_zero p.1
  refine continuous_const.mul (continuous_finsetSum _ fun z _ => ?_)
  exact ((D.prob z).continuous.mul (D.w.continuous.comp (D.transition z).continuous)).mul
    (u.continuous.comp (D.transition z).continuous)

theorem continuous_uncurry_objective (u : S →ᵇ ℝ) : Continuous ↿(D.objective u) :=
  D.rewardOverWeight.continuous.add (D.continuous_expectation u)

/-- The drift condition bounds the expectation operator by `modulus * ‖u‖`. This is the one
place the condition does real work. -/
theorem abs_expectation_le (u : S →ᵇ ℝ) {s : S} {a : A} (ha : a ∈ D.feasible s) :
    |D.expectation u (s, a)| ≤ D.modulus * ‖u‖ := by
  set p : S × A := (s, a) with hp
  have hw := D.w_pos p.1
  have hβ : (0 : ℝ) ≤ D.discount := D.discount.coe_nonneg
  have hterm : ∀ z : Z, |D.prob z p * D.w (D.transition z p) * u (D.transition z p)|
      ≤ D.prob z p * D.w (D.transition z p) * ‖u‖ := by
    intro z
    rw [abs_mul, abs_of_nonneg (mul_nonneg (D.prob_nonneg z p) (D.w_pos _).le)]
    exact mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs] using u.norm_coe_le_norm (D.transition z p))
      (mul_nonneg (D.prob_nonneg z p) (D.w_pos _).le)
  have hsum : |∑ z, D.prob z p * D.w (D.transition z p) * u (D.transition z p)|
      ≤ (∑ z, D.prob z p * D.w (D.transition z p)) * ‖u‖ := by
    calc |∑ z, D.prob z p * D.w (D.transition z p) * u (D.transition z p)|
        ≤ ∑ z, |D.prob z p * D.w (D.transition z p) * u (D.transition z p)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z, D.prob z p * D.w (D.transition z p) * ‖u‖ := Finset.sum_le_sum fun z _ => hterm z
      _ = _ := by rw [← Finset.sum_mul]
  rw [expectation, abs_div, abs_of_pos hw, div_le_iff₀ hw, abs_mul,
    abs_of_nonneg hβ]
  have hdrift := D.drift s a ha
  have hnorm : (0 : ℝ) ≤ ‖u‖ := norm_nonneg _
  calc (D.discount : ℝ) * |∑ z, D.prob z p * D.w (D.transition z p) * u (D.transition z p)|
      ≤ D.discount * ((∑ z, D.prob z p * D.w (D.transition z p)) * ‖u‖) := by
        exact mul_le_mul_of_nonneg_left hsum hβ
    _ = (D.discount * ∑ z, D.prob z p * D.w (D.transition z p)) * ‖u‖ := by ring
    _ ≤ (D.modulus * D.w p.1) * ‖u‖ := mul_le_mul_of_nonneg_right hdrift hnorm
    _ = D.modulus * ‖u‖ * D.w p.1 := by ring

theorem abs_objective_le (u : S →ᵇ ℝ) {s : S} {a : A} (ha : a ∈ D.feasible s) :
    |D.objective u s a| ≤ ‖D.rewardOverWeight‖ + D.modulus * ‖u‖ := by
  have h₁ : |D.rewardOverWeight (s, a)| ≤ ‖D.rewardOverWeight‖ := by
    simpa [Real.norm_eq_abs] using D.rewardOverWeight.norm_coe_le_norm (s, a)
  have h₂ := D.abs_expectation_le u ha
  rw [abs_le] at h₁ h₂
  simp only [objective, abs_le]
  constructor <;> [linarith [h₁.1, h₂.1]; linarith [h₁.2, h₂.2]]

/-- The conjugated Bellman operator as a bare function. -/
noncomputable def bellmanFn (u : S →ᵇ ℝ) (s : S) : ℝ :=
  maxValue (D.objective u) D.feasible s

theorem le_bellmanFn (u : S →ᵇ ℝ) {s : S} {a : A} (ha : a ∈ D.feasible s) :
    D.objective u s a ≤ D.bellmanFn u s :=
  le_maxValue (D.continuous_uncurry_objective u) (D.isCompact_feasible s) ha

theorem bellmanFn_le (u : S →ᵇ ℝ) {s : S} {c : ℝ}
    (h : ∀ a ∈ D.feasible s, D.objective u s a ≤ c) : D.bellmanFn u s ≤ c :=
  maxValue_le (D.feasible_nonempty s) h

theorem abs_bellmanFn_le (u : S →ᵇ ℝ) (s : S) :
    |D.bellmanFn u s| ≤ ‖D.rewardOverWeight‖ + D.modulus * ‖u‖ := by
  obtain ⟨a, ha⟩ := D.feasible_nonempty s
  rw [abs_le]
  refine ⟨?_, D.bellmanFn_le u fun b hb => (le_abs_self _).trans (D.abs_objective_le u hb)⟩
  exact le_trans (neg_le_of_abs_le (D.abs_objective_le u ha)) (D.le_bellmanFn u ha)

/-- The **conjugated Bellman operator** `u ↦ T (u * w) / w` on bounded continuous
functions. -/
noncomputable def bellman (u : S →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (D.bellmanFn u)
    (continuous_maxValue (D.continuous_uncurry_objective u) D.feasible_nonempty
      D.isCompact_feasible D.upperHemicontinuous_feasible D.lowerHemicontinuous_feasible)
    (‖D.rewardOverWeight‖ + D.modulus * ‖u‖)
    fun s => by simpa [Real.norm_eq_abs] using D.abs_bellmanFn_le u s

@[simp]
theorem bellman_apply (u : S →ᵇ ℝ) (s : S) :
    D.bellman u s = maxValue (D.objective u) D.feasible s := rfl

/-- **Blackwell's conditions hold for the conjugated operator.** Monotonicity comes from
nonnegativity of the coefficients; discounting is exactly the drift condition. -/
theorem blackwell : Blackwell D.modulus D.bellman where
  monotone := by
    intro u v huv s
    have hβ : (0 : ℝ) ≤ D.discount := D.discount.coe_nonneg
    have key : ∀ a ∈ D.feasible s, D.objective u s a ≤ D.bellmanFn v s := by
      intro a ha
      refine le_trans ?_ (D.le_bellmanFn v ha)
      have hsum : ∑ z, D.prob z (s, a) * D.w (D.transition z (s, a)) * u (D.transition z (s, a))
          ≤ ∑ z, D.prob z (s, a) * D.w (D.transition z (s, a)) * v (D.transition z (s, a)) := by
        refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (D.prob_nonneg z _) (D.w_pos _).le)
        simpa using huv (D.transition z (s, a))
      have hw := D.w_pos s
      simp only [objective, expectation]
      gcongr
    exact D.bellmanFn_le u key
  discounting := by
    intro u c hc s
    have hβ : (0 : ℝ) ≤ D.discount := D.discount.coe_nonneg
    have key : ∀ a ∈ D.feasible s, D.objective (u + const S c) s a
        ≤ D.bellmanFn u s + D.modulus * c := by
      intro a ha
      have hw := D.w_pos s
      have hterm : ∀ z : Z,
          D.prob z (s, a) * D.w (D.transition z (s, a)) * (u + const S c) (D.transition z (s, a))
            = D.prob z (s, a) * D.w (D.transition z (s, a)) * u (D.transition z (s, a))
              + D.prob z (s, a) * D.w (D.transition z (s, a)) * c := fun z => by
        simp only [coe_add, const_apply, Pi.add_apply]; ring
      have hsplit : D.expectation (u + const S c) (s, a)
          = D.expectation u (s, a)
            + (D.discount * ∑ z, D.prob z (s, a) * D.w (D.transition z (s, a)) * c) / D.w s := by
        simp only [expectation]
        rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_add_distrib, mul_add, add_div]
      -- the drift condition turns the extra term into at most `modulus * c`
      have hextra : (D.discount * ∑ z, D.prob z (s, a) * D.w (D.transition z (s, a)) * c) / D.w s
          ≤ D.modulus * c := by
        rw [div_le_iff₀ hw]
        have hdrift := D.drift s a ha
        have : ∑ z, D.prob z (s, a) * D.w (D.transition z (s, a)) * c
            = (∑ z, D.prob z (s, a) * D.w (D.transition z (s, a))) * c := by
          rw [← Finset.sum_mul]
        rw [this]
        calc (D.discount : ℝ) * ((∑ z, D.prob z (s, a) * D.w (D.transition z (s, a))) * c)
            = ((D.discount : ℝ) * ∑ z, D.prob z (s, a) * D.w (D.transition z (s, a))) * c := by
              ring
          _ ≤ (D.modulus * D.w s) * c := mul_le_mul_of_nonneg_right hdrift hc
          _ = D.modulus * c * D.w s := by ring
      have hle := D.le_bellmanFn u (s := s) ha
      simp only [objective] at hle ⊢
      rw [hsplit]
      linarith
    exact D.bellmanFn_le (u + const S c) key

/-- The supremum is attained: an optimal action exists at every state. -/
theorem exists_optimal_action (u : S →ᵇ ℝ) (s : S) :
    ∃ a ∈ D.feasible s, D.bellman u s = D.objective u s a ∧
      ∀ b ∈ D.feasible s, D.objective u s b ≤ D.objective u s a := by
  obtain ⟨a, ha, hmax⟩ :=
    argmax_nonempty (D.continuous_uncurry_objective u) (D.feasible_nonempty s)
      (D.isCompact_feasible s)
  exact ⟨a, ha,
    maxValue_eq (D.continuous_uncurry_objective u) (D.isCompact_feasible s) ⟨ha, hmax⟩,
    fun b hb => isMaxOn_iff.mp hmax b hb⟩

section ValueFunction

/-- The fixed point of the conjugated operator: the value function divided by the
weight. -/
noncomputable def normalisedValue : S →ᵇ ℝ := D.blackwell.valueFunction D.modulus_lt_one

/-- The **value function** of the original, unbounded problem. It need not be bounded; it
is bounded relative to the weight, which is the whole point. -/
noncomputable def valueFunction (s : S) : ℝ := D.normalisedValue s * D.w s

theorem bellman_normalisedValue : D.bellman D.normalisedValue = D.normalisedValue :=
  D.blackwell.isFixedPt_valueFunction D.modulus_lt_one

theorem eq_normalisedValue {u : S →ᵇ ℝ} (hu : D.bellman u = u) : u = D.normalisedValue :=
  D.blackwell.eq_valueFunction D.modulus_lt_one hu

theorem tendsto_iterate_normalisedValue (u : S →ᵇ ℝ) :
    Tendsto (fun n => D.bellman^[n] u) atTop (𝓝 D.normalisedValue) :=
  D.blackwell.tendsto_iterate_valueFunction D.modulus_lt_one u

/-- **The Bellman equation of the unbounded problem.** Multiplying the weight back in, the
value function satisfies the equation with the original reward `rewardOverWeight * w` and
the original discounted expectation -- no weights left in sight. -/
theorem exists_optimal_policy (s : S) :
    ∃ a ∈ D.feasible s, D.valueFunction s
      = D.rewardOverWeight (s, a) * D.w s
        + D.discount * ∑ z, D.prob z (s, a) * D.valueFunction (D.transition z (s, a)) := by
  obtain ⟨a, ha, heq, -⟩ := D.exists_optimal_action D.normalisedValue s
  refine ⟨a, ha, ?_⟩
  rw [D.bellman_normalisedValue] at heq
  have hw := D.w_pos s
  have hsum : ∑ z, D.prob z (s, a) * D.normalisedValue (D.transition z (s, a))
        * D.w (D.transition z (s, a))
      = ∑ z, D.prob z (s, a) * D.w (D.transition z (s, a))
        * D.normalisedValue (D.transition z (s, a)) :=
    Finset.sum_congr rfl fun z _ => by ring
  simp only [valueFunction, heq, objective, expectation]
  field_simp
  rw [hsum]

end ValueFunction

end WeightedDynamicProgram

/-- A bounded-reward stochastic program is the weighted case with `w = 1`: the drift
condition then reads `β ≤ β`, and the modulus is the discount factor. -/
noncomputable def StochasticDynamicProgram.toWeighted (D : StochasticDynamicProgram S A Z) :
    WeightedDynamicProgram S A Z where
  feasible := D.feasible
  isCompact_feasible := D.isCompact_feasible
  feasible_nonempty := D.feasible_nonempty
  upperHemicontinuous_feasible := D.upperHemicontinuous_feasible
  lowerHemicontinuous_feasible := D.lowerHemicontinuous_feasible
  w := ⟨fun _ => 1, continuous_const⟩
  one_le_w _ := le_refl 1
  rewardOverWeight := D.reward
  transition := D.transition
  prob := D.prob
  prob_nonneg := D.prob_nonneg
  discount := D.discount
  modulus := D.discount
  modulus_lt_one := D.discount_lt_one
  drift s a _ := by simp [D.prob_sum (s, a)]

end LeanEconomics
