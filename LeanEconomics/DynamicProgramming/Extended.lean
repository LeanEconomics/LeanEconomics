/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Bellman
import LeanEconomics.Topology.BergeEReal

/-!
# Dynamic programs with extended-real rewards

The reward may take the value `-∞`, as `log c` does at zero consumption. The value function
stays real-valued and bounded, so the contraction theory applies unchanged.

## What this is for

Every model in this library that handles utility unbounded below does it with a *floor*:
replace `u` by `max floor u`, which is bounded, and then prove separately that the floor
never binds at an optimum. That argument has to be redone per model, and it fails outright
once the state space is unbounded, because the bound on the value function that it needs is
itself inflated by the floor. Admitting `-∞` removes the device rather than working around
it.

## Why the value function is still bounded

Two hypotheses do it, and both are economically ordinary:

* `reward_le` bounds the reward above on the feasible graph. Only there: off it the reward
  may do anything, which matters because an action outside the budget set typically has no
  sensible reward at all.
* `select` is a continuous feasible policy whose reward is bounded below by `rewardMin`.
  This says the agent always has *some* decent option -- it never faces a situation where
  every available action is catastrophic. Without it the value would be `-∞` and there
  would be nothing to compute.

Between them the supremum sits in `[rewardMin - β‖v‖, rewardMax + β‖v‖]`, so it is finite,
and `EReal.toReal` turns it back into a bounded continuous real function.

## Main results

* `LeanEconomics.ExtendedProgram.blackwell` : the operator is a contraction.
* `LeanEconomics.ExtendedProgram.exists_optimal_policy` : the value function satisfies the
  Bellman equation, with the reward appearing as an `EReal` and no floor anywhere.
-/

open scoped NNReal
open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

variable {S A : Type*} [TopologicalSpace S] [TopologicalSpace A]

/-- A dynamic program whose reward may be `-∞`. -/
structure ExtendedProgram (S A : Type*) [TopologicalSpace S] [TopologicalSpace A] where
  /-- The actions available at each state. -/
  feasible : S → Set A
  isCompact_feasible : ∀ s, IsCompact (feasible s)
  feasible_nonempty : ∀ s, (feasible s).Nonempty
  upperHemicontinuous_feasible : UpperHemicontinuous feasible
  lowerHemicontinuous_feasible : LowerHemicontinuous feasible
  /-- The reward, continuous into the extended reals and possibly `-∞`. -/
  reward : C(S × A, EReal)
  /-- An upper bound on the reward, needed only on the feasible graph. -/
  rewardMax : ℝ
  reward_le : ∀ s, ∀ a ∈ feasible s, reward (s, a) ≤ (rewardMax : EReal)
  /-- A continuous feasible policy. -/
  select : C(S, A)
  select_mem : ∀ s, select s ∈ feasible s
  /-- Its reward is bounded below: the agent always has a decent option. -/
  rewardMin : ℝ
  le_reward_select : ∀ s, (rewardMin : EReal) ≤ reward (s, select s)
  /-- The law of motion. -/
  transition : C(S × A, S)
  discount : ℝ≥0
  discount_lt_one : discount < 1

namespace ExtendedProgram

variable (D : ExtendedProgram S A)

/-- The objective, in the extended reals. -/
noncomputable def objectiveE (v : S →ᵇ ℝ) (s : S) (a : A) : EReal :=
  D.reward (s, a) + ((D.discount * v (D.transition (s, a)) : ℝ) : EReal)

/-- The value of the one-period problem, in the extended reals. -/
noncomputable def maxE (v : S →ᵇ ℝ) (s : S) : EReal := maxValueE (D.objectiveE v) D.feasible s

/-- The upper bound on the one-period value. -/
noncomputable def hiBound (v : S →ᵇ ℝ) : ℝ := D.rewardMax + D.discount * ‖v‖

/-- The lower bound on the one-period value, coming from the feasible selection. -/
noncomputable def loBound (v : S →ᵇ ℝ) : ℝ := D.rewardMin - D.discount * ‖v‖

theorem continuous_uncurry_objectiveE (v : S →ᵇ ℝ) : Continuous ↿(D.objectiveE v) := by
  have h1 : Continuous fun p : S × A => D.reward p := D.reward.continuous
  have h2 : Continuous fun p : S × A => ((D.discount * v (D.transition p) : ℝ) : EReal) :=
    continuous_coe_real_ereal.comp
      (continuous_const.mul (v.continuous.comp D.transition.continuous))
  rw [continuous_iff_continuousAt]
  intro p
  exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).comp
    (h1.continuousAt.prodMk h2.continuousAt)

theorem abs_discount_smul_le (v : S →ᵇ ℝ) (t : S) :
    |(D.discount : ℝ) * v t| ≤ D.discount * ‖v‖ := by
  rw [abs_mul, abs_of_nonneg D.discount.coe_nonneg]
  exact mul_le_mul_of_nonneg_left
    (by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm t) D.discount.coe_nonneg

theorem maxE_le (v : S →ᵇ ℝ) (s : S) : D.maxE v s ≤ ((D.hiBound v : ℝ) : EReal) := by
  refine maxValueE_le fun a ha => ?_
  have h1 : D.reward (s, a) ≤ ((D.rewardMax : ℝ) : EReal) := D.reward_le s a ha
  have h2 : ((D.discount * v (D.transition (s, a)) : ℝ) : EReal)
      ≤ ((D.discount * ‖v‖ : ℝ) : EReal) := by
    rw [EReal.coe_le_coe_iff]
    exact (abs_le.mp (D.abs_discount_smul_le v (D.transition (s, a)))).2
  calc D.objectiveE v s a ≤ ((D.rewardMax : ℝ) : EReal) + ((D.discount * ‖v‖ : ℝ) : EReal) :=
        add_le_add h1 h2
    _ = ((D.hiBound v : ℝ) : EReal) := by rw [hiBound, EReal.coe_add]

theorem le_maxE (v : S →ᵇ ℝ) (s : S) : ((D.loBound v : ℝ) : EReal) ≤ D.maxE v s := by
  refine le_trans ?_ (le_maxValueE (D.select_mem s))
  have h1 : ((D.rewardMin : ℝ) : EReal) ≤ D.reward (s, D.select s) := D.le_reward_select s
  have h2 : ((-(D.discount * ‖v‖) : ℝ) : EReal)
      ≤ ((D.discount * v (D.transition (s, D.select s)) : ℝ) : EReal) := by
    rw [EReal.coe_le_coe_iff]
    exact (abs_le.mp (D.abs_discount_smul_le v (D.transition (s, D.select s)))).1
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
  · have : -|D.loBound v| ≤ D.loBound v := neg_abs_le _
    have h3 : -(max |D.loBound v| |D.hiBound v|) ≤ -|D.loBound v| := neg_le_neg (le_max_left _ _)
    linarith
  · exact h2.trans ((le_abs_self _).trans (le_max_right _ _))

theorem continuous_bellmanFn (v : S →ᵇ ℝ) : Continuous (D.bellmanFn v) := by
  have hcont : Continuous (D.maxE v) :=
    continuous_maxValueE (D.continuous_uncurry_objectiveE v) D.feasible_nonempty
      D.isCompact_feasible D.upperHemicontinuous_feasible D.lowerHemicontinuous_feasible
  refine EReal.continuousOn_toReal.comp_continuous hcont fun s => ?_
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨D.maxE_ne_bot v s, D.maxE_ne_top v s⟩

/-- The **Bellman operator** on bounded continuous functions, with an extended-real
reward. -/
noncomputable def bellman (v : S →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (D.bellmanFn v) (D.continuous_bellmanFn v)
    (max |D.loBound v| |D.hiBound v|)
    fun s => by simpa [Real.norm_eq_abs] using D.abs_bellmanFn_le v s

@[simp]
theorem bellman_apply (v : S →ᵇ ℝ) (s : S) : D.bellman v s = D.bellmanFn v s := rfl

/-- **Blackwell's conditions hold.** The extended-real reward is a common summand on both
sides of each inequality, so it plays no part: monotonicity and discounting are facts about
the continuation term alone. -/
theorem blackwell : Blackwell D.discount D.bellman where
  monotone := by
    intro v w hvw s
    refine D.bellmanFn_le v fun a ha => ?_
    refine le_trans ?_ (D.le_bellmanFn w ha)
    simp only [objectiveE]
    refine add_le_add (le_refl _) ?_
    rw [EReal.coe_le_coe_iff]
    exact mul_le_mul_of_nonneg_left (by simpa using hvw (D.transition (s, a)))
      D.discount.coe_nonneg
  discounting := by
    intro v c _ s
    have hgoal : ((D.bellman v + const S ((D.discount : ℝ) * c)) s : ℝ)
        = D.bellmanFn v s + (D.discount : ℝ) * c := by simp
    refine le_trans (D.bellmanFn_le (v + const S c)
      (c := D.bellmanFn v s + (D.discount : ℝ) * c) fun a ha => ?_) (le_of_eq hgoal.symm)
    have hsplit : D.objectiveE (v + const S c) s a
        = D.objectiveE v s a + ((D.discount * c : ℝ) : EReal) := by
      simp only [objectiveE, coe_add, const_apply, Pi.add_apply]
      rw [show (D.discount : ℝ) * (v (D.transition (s, a)) + c)
          = D.discount * v (D.transition (s, a)) + D.discount * c by ring,
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

/-- **The Bellman equation**, with the reward an extended real and no floor anywhere. -/
theorem exists_optimal_policy (s : S) :
    ∃ a ∈ D.feasible s, ((D.valueFunction s : ℝ) : EReal)
      = D.reward (s, a) + ((D.discount * D.valueFunction (D.transition (s, a)) : ℝ) : EReal) := by
  obtain ⟨a, ha, heq⟩ := D.exists_optimal_action D.valueFunction s
  refine ⟨a, ha, ?_⟩
  have hfix : D.bellmanFn D.valueFunction s = D.valueFunction s := by
    conv_rhs => rw [← D.bellman_valueFunction]
    rfl
  rw [← hfix, ← heq]
  rfl

end ValueFunction

end ExtendedProgram

end LeanEconomics
