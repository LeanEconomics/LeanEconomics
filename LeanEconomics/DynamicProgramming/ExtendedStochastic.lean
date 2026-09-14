/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Extended
import LeanEconomics.DynamicProgramming.Stochastic

/-!
# Stochastic dynamic programs with extended-real rewards

`LeanEconomics.DynamicProgramming.Extended` allows a reward of `-∞` but has a deterministic
law of motion; `LeanEconomics.DynamicProgramming.Stochastic` has finitely many shocks but a
real-valued reward. This file is the combination, and it is what a stochastic model with
log or CRRA utility needs if it is not to carry a floor.

## Why the combination is routine

The expectation `∑ z, p z * v (g z)` is a sum of *real* numbers, since value functions stay
real-valued. So the objective is again `reward + ↑(real)`: an extended real plus a finite
coercion, exactly the shape `Extended` already handles. Neither half has to be redone --
the reward's `-∞` never meets the expectation's arithmetic, and `⊥ + ⊤` never arises.

Accordingly the two facts about the expectation are the same two as in the real stochastic
file: `prob_nonneg` gives monotonicity, `prob_sum` gives discounting.

## Main results

* `LeanEconomics.ExtendedStochasticProgram.blackwell` : the operator is a contraction.
* `LeanEconomics.ExtendedStochasticProgram.exists_optimal_policy` : the stochastic Bellman
  equation, with the reward an extended real and no floor.
-/

open scoped NNReal
open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

variable {S A Z : Type*} [TopologicalSpace S] [TopologicalSpace A] [Fintype Z]

/-- A stochastic dynamic program whose reward may be `-∞`. -/
structure ExtendedStochasticProgram (S A Z : Type*) [TopologicalSpace S] [TopologicalSpace A]
    [Fintype Z] where
  /-- The actions available at each state. -/
  feasible : S → Set A
  isCompact_feasible : ∀ s, IsCompact (feasible s)
  feasible_nonempty : ∀ s, (feasible s).Nonempty
  upperHemicontinuous_feasible : UpperHemicontinuous feasible
  lowerHemicontinuous_feasible : LowerHemicontinuous feasible
  /-- The reward, possibly `-∞`. -/
  reward : C(S × A, EReal)
  /-- An upper bound on the reward, needed only on the feasible graph. -/
  rewardMax : ℝ
  reward_le : ∀ s, ∀ a ∈ feasible s, reward (s, a) ≤ (rewardMax : EReal)
  /-- A continuous feasible policy whose reward is bounded below. -/
  select : C(S, A)
  select_mem : ∀ s, select s ∈ feasible s
  rewardMin : ℝ
  le_reward_select : ∀ s, (rewardMin : EReal) ≤ reward (s, select s)
  /-- The state reached when shock `z` occurs. -/
  transition : Z → C(S × A, S)
  /-- The probability that shock `z` occurs. -/
  prob : Z → C(S × A, ℝ)
  prob_nonneg : ∀ z p, 0 ≤ prob z p
  prob_sum : ∀ p, ∑ z, prob z p = 1
  discount : ℝ≥0
  discount_lt_one : discount < 1

namespace ExtendedStochasticProgram

variable (D : ExtendedStochasticProgram S A Z)

/-- The expected continuation value: a sum of reals, so it never meets the reward's `-∞`. -/
noncomputable def expect (v : S →ᵇ ℝ) (p : S × A) : ℝ :=
  ∑ z, D.prob z p * v (D.transition z p)

/-- The objective, in the extended reals. -/
noncomputable def objectiveE (v : S →ᵇ ℝ) (s : S) (a : A) : EReal :=
  D.reward (s, a) + ((D.discount * D.expect v (s, a) : ℝ) : EReal)

/-- The value of the one-period problem, in the extended reals. -/
noncomputable def maxE (v : S →ᵇ ℝ) (s : S) : EReal := maxValueE (D.objectiveE v) D.feasible s

/-- The upper bound on the one-period value. -/
noncomputable def hiBound (v : S →ᵇ ℝ) : ℝ := D.rewardMax + D.discount * ‖v‖

/-- The lower bound on the one-period value. -/
noncomputable def loBound (v : S →ᵇ ℝ) : ℝ := D.rewardMin - D.discount * ‖v‖

theorem continuous_expect (v : S →ᵇ ℝ) : Continuous (D.expect v) :=
  continuous_finsetSum _ fun z _ =>
    (D.prob z).continuous.mul (v.continuous.comp (D.transition z).continuous)

theorem continuous_uncurry_objectiveE (v : S →ᵇ ℝ) : Continuous ↿(D.objectiveE v) := by
  have h1 : Continuous fun p : S × A => D.reward p := D.reward.continuous
  have h2 : Continuous fun p : S × A => ((D.discount * D.expect v p : ℝ) : EReal) :=
    continuous_coe_real_ereal.comp (continuous_const.mul (D.continuous_expect v))
  rw [continuous_iff_continuousAt]
  intro p
  exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).comp
    (h1.continuousAt.prodMk h2.continuousAt)

/-- An average of values of `v` is no larger than the size of `v`. -/
theorem abs_expect_le (v : S →ᵇ ℝ) (p : S × A) : |D.expect v p| ≤ ‖v‖ := by
  calc |D.expect v p| ≤ ∑ z, |D.prob z p * v (D.transition z p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, D.prob z p * |v (D.transition z p)| := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [abs_mul, abs_of_nonneg (D.prob_nonneg z p)]
    _ ≤ ∑ z, D.prob z p * ‖v‖ := by
        refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (D.prob_nonneg z p)
        simpa [Real.norm_eq_abs] using v.norm_coe_le_norm (D.transition z p)
    _ = ‖v‖ := by rw [← Finset.sum_mul, D.prob_sum, one_mul]

theorem maxE_le (v : S →ᵇ ℝ) (s : S) : D.maxE v s ≤ ((D.hiBound v : ℝ) : EReal) := by
  refine maxValueE_le fun a ha => ?_
  have h1 : D.reward (s, a) ≤ ((D.rewardMax : ℝ) : EReal) := D.reward_le s a ha
  have h2 : ((D.discount * D.expect v (s, a) : ℝ) : EReal) ≤ ((D.discount * ‖v‖ : ℝ) : EReal) := by
    rw [EReal.coe_le_coe_iff]
    exact mul_le_mul_of_nonneg_left (abs_le.mp (D.abs_expect_le v (s, a))).2 D.discount.coe_nonneg
  calc D.objectiveE v s a ≤ ((D.rewardMax : ℝ) : EReal) + ((D.discount * ‖v‖ : ℝ) : EReal) :=
        add_le_add h1 h2
    _ = ((D.hiBound v : ℝ) : EReal) := by rw [hiBound, EReal.coe_add]

theorem le_maxE (v : S →ᵇ ℝ) (s : S) : ((D.loBound v : ℝ) : EReal) ≤ D.maxE v s := by
  refine le_trans ?_ (le_maxValueE (D.select_mem s))
  have h1 : ((D.rewardMin : ℝ) : EReal) ≤ D.reward (s, D.select s) := D.le_reward_select s
  have h2 : ((-(D.discount * ‖v‖) : ℝ) : EReal)
      ≤ ((D.discount * D.expect v (s, D.select s) : ℝ) : EReal) := by
    rw [EReal.coe_le_coe_iff]
    have := (abs_le.mp (D.abs_expect_le v (s, D.select s))).1
    have h := mul_le_mul_of_nonneg_left this D.discount.coe_nonneg
    linarith
  calc ((D.loBound v : ℝ) : EReal)
      = ((D.rewardMin : ℝ) : EReal) + ((-(D.discount * ‖v‖) : ℝ) : EReal) := by
        rw [← EReal.coe_add]
        congr 1
    _ ≤ _ := add_le_add h1 h2

theorem maxE_ne_top (v : S →ᵇ ℝ) (s : S) : D.maxE v s ≠ ⊤ := by
  intro h
  have hle := D.maxE_le v s
  rw [h, top_le_iff] at hle
  exact EReal.coe_ne_top _ hle

theorem maxE_ne_bot (v : S →ᵇ ℝ) (s : S) : D.maxE v s ≠ ⊥ := by
  intro h
  have hle := D.le_maxE v s
  rw [h, le_bot_iff] at hle
  exact EReal.coe_ne_bot _ hle

/-- The Bellman operator as a bare real-valued function. -/
noncomputable def bellmanFn (v : S →ᵇ ℝ) (s : S) : ℝ := (D.maxE v s).toReal

@[simp]
theorem coe_bellmanFn (v : S →ᵇ ℝ) (s : S) : ((D.bellmanFn v s : ℝ) : EReal) = D.maxE v s :=
  EReal.coe_toReal (D.maxE_ne_top v s) (D.maxE_ne_bot v s)

theorem le_bellmanFn (v : S →ᵇ ℝ) {s : S} {a : A} (ha : a ∈ D.feasible s) :
    D.objectiveE v s a ≤ ((D.bellmanFn v s : ℝ) : EReal) := by
  rw [D.coe_bellmanFn]
  exact le_maxValueE ha

theorem bellmanFn_le (v : S →ᵇ ℝ) {s : S} {c : ℝ}
    (h : ∀ a ∈ D.feasible s, D.objectiveE v s a ≤ (c : EReal)) : D.bellmanFn v s ≤ c := by
  have hle : D.maxE v s ≤ (c : EReal) := maxValueE_le h
  rw [← D.coe_bellmanFn, EReal.coe_le_coe_iff] at hle
  exact hle

theorem bellmanFn_bounds (v : S →ᵇ ℝ) (s : S) :
    D.loBound v ≤ D.bellmanFn v s ∧ D.bellmanFn v s ≤ D.hiBound v := by
  constructor
  · have := D.le_maxE v s
    rw [← D.coe_bellmanFn, EReal.coe_le_coe_iff] at this
    exact this
  · have := D.maxE_le v s
    rw [← D.coe_bellmanFn, EReal.coe_le_coe_iff] at this
    exact this

theorem abs_bellmanFn_le (v : S →ᵇ ℝ) (s : S) :
    |D.bellmanFn v s| ≤ max |D.loBound v| |D.hiBound v| := by
  obtain ⟨h1, h2⟩ := D.bellmanFn_bounds v s
  rw [abs_le]
  constructor
  · have h3 : -|D.loBound v| ≤ D.loBound v := neg_abs_le _
    have h4 : -(max |D.loBound v| |D.hiBound v|) ≤ -|D.loBound v| := neg_le_neg (le_max_left _ _)
    linarith
  · exact h2.trans ((le_abs_self _).trans (le_max_right _ _))

theorem continuous_bellmanFn (v : S →ᵇ ℝ) : Continuous (D.bellmanFn v) := by
  have hcont : Continuous (D.maxE v) :=
    continuous_maxValueE (D.continuous_uncurry_objectiveE v) D.feasible_nonempty
      D.isCompact_feasible D.upperHemicontinuous_feasible D.lowerHemicontinuous_feasible
  refine EReal.continuousOn_toReal.comp_continuous hcont fun s => ?_
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨D.maxE_ne_bot v s, D.maxE_ne_top v s⟩

/-- The **stochastic Bellman operator** with an extended-real reward. -/
noncomputable def bellman (v : S →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (D.bellmanFn v) (D.continuous_bellmanFn v)
    (max |D.loBound v| |D.hiBound v|)
    fun s => by simpa [Real.norm_eq_abs] using D.abs_bellmanFn_le v s

@[simp]
theorem bellman_apply (v : S →ᵇ ℝ) (s : S) : D.bellman v s = D.bellmanFn v s := rfl

/-- Adding a constant to the continuation value adds exactly that constant to the
expectation: this is `prob_sum`. -/
theorem expect_add_const (v : S →ᵇ ℝ) (c : ℝ) (p : S × A) :
    D.expect (v + const S c) p = D.expect v p + c := by
  have hterm : ∀ z : Z, D.prob z p * (v + const S c) (D.transition z p)
      = D.prob z p * v (D.transition z p) + D.prob z p * c := fun z => by
    simp only [coe_add, const_apply, Pi.add_apply]; ring
  simp only [expect]
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_add_distrib, ← Finset.sum_mul,
    D.prob_sum, one_mul]

/-- **Blackwell's conditions hold.** -/
theorem blackwell : Blackwell D.discount D.bellman where
  monotone := by
    intro v w hvw s
    refine D.bellmanFn_le v fun a ha => ?_
    refine le_trans ?_ (D.le_bellmanFn w ha)
    simp only [objectiveE]
    refine add_le_add (le_refl _) ?_
    rw [EReal.coe_le_coe_iff]
    refine mul_le_mul_of_nonneg_left ?_ D.discount.coe_nonneg
    refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (D.prob_nonneg z _)
    simpa using hvw (D.transition z (s, a))
  discounting := by
    intro v c _ s
    have hgoal : ((D.bellman v + const S ((D.discount : ℝ) * c)) s : ℝ)
        = D.bellmanFn v s + (D.discount : ℝ) * c := by simp
    refine le_trans (D.bellmanFn_le (v + const S c)
      (c := D.bellmanFn v s + (D.discount : ℝ) * c) fun a ha => ?_) (le_of_eq hgoal.symm)
    have hsplit : D.objectiveE (v + const S c) s a
        = D.objectiveE v s a + ((D.discount * c : ℝ) : EReal) := by
      simp only [objectiveE, D.expect_add_const]
      rw [show (D.discount : ℝ) * (D.expect v (s, a) + c)
          = D.discount * D.expect v (s, a) + D.discount * c by ring,
        EReal.coe_add, add_assoc]
    rw [hsplit]
    calc D.objectiveE v s a + ((D.discount * c : ℝ) : EReal)
        ≤ ((D.bellmanFn v s : ℝ) : EReal) + ((D.discount * c : ℝ) : EReal) :=
          add_le_add (D.le_bellmanFn v ha) (le_refl _)
      _ = ((D.bellmanFn v s + D.discount * c : ℝ) : EReal) := (EReal.coe_add _ _).symm

/-- The supremum is attained: an optimal action exists at every state. -/
theorem exists_optimal_action (v : S →ᵇ ℝ) (s : S) :
    ∃ a ∈ D.feasible s, D.objectiveE v s a = ((D.bellmanFn v s : ℝ) : EReal) := by
  obtain ⟨a, ha, heq⟩ := maxValueE_eq (D.continuous_uncurry_objectiveE v)
    (D.feasible_nonempty s) (D.isCompact_feasible s)
  exact ⟨a, ha, by rw [D.coe_bellmanFn]; exact heq.symm⟩

section ValueFunction

/-- The **value function** of the program. -/
noncomputable def valueFunction : S →ᵇ ℝ := D.blackwell.valueFunction D.discount_lt_one

theorem bellman_valueFunction : D.bellman D.valueFunction = D.valueFunction :=
  D.blackwell.isFixedPt_valueFunction D.discount_lt_one

theorem eq_valueFunction {v : S →ᵇ ℝ} (hv : D.bellman v = v) : v = D.valueFunction :=
  D.blackwell.eq_valueFunction D.discount_lt_one hv

theorem tendsto_iterate_valueFunction (v : S →ᵇ ℝ) :
    Tendsto (fun n => D.bellman^[n] v) atTop (𝓝 D.valueFunction) :=
  D.blackwell.tendsto_iterate_valueFunction D.discount_lt_one v

/-- **The stochastic Bellman equation**, with the reward an extended real and no floor. -/
theorem exists_optimal_policy (s : S) :
    ∃ a ∈ D.feasible s, ((D.valueFunction s : ℝ) : EReal)
      = D.reward (s, a)
        + ((D.discount * ∑ z, D.prob z (s, a) * D.valueFunction (D.transition z (s, a)) :
            ℝ) : EReal) := by
  obtain ⟨a, ha, heq⟩ := D.exists_optimal_action D.valueFunction s
  refine ⟨a, ha, ?_⟩
  have hfix : D.bellmanFn D.valueFunction s = D.valueFunction s := by
    conv_rhs => rw [← D.bellman_valueFunction]
    rfl
  rw [← hfix, ← heq]
  rfl

end ValueFunction

end ExtendedStochasticProgram

end LeanEconomics
