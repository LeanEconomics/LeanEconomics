/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Blackwell
import Mathlib.Topology.Order.Compact

/-!
# The Bellman operator of a deterministic dynamic program

The operator

  `T v s = sup { r (s, a) + β * v (g (s, a)) | a ∈ A }`

is shown to map bounded continuous functions to bounded continuous functions, and to
satisfy Blackwell's sufficient conditions. Combined with `LeanEconomics.Blackwell` this
gives the value function of the program, its uniqueness, and convergence of value function
iteration.

## The formulation

A program is given by a compact nonempty set of actions `A`, a bounded continuous reward
`r : (S × A) →ᵇ ℝ`, a continuous law of motion `g : C(S × A, S)`, and a discount factor
`β < 1`. Constraints on the agent are carried by the law of motion rather than by a
state-dependent feasible set: the action is a decision whose *consequence* `g (s, a)`
depends on the state. A budget constraint, for instance, is imposed by letting the action
be the fraction of resources saved, so that the feasible set itself does not move with the
state.

That restriction is what keeps this file free of Berge's maximum theorem, which Mathlib
does not have. A genuinely state-dependent correspondence `Γ : S → Set A` needs the
continuity of `T v` to come from Berge; here it comes from
`IsCompact.continuous_sSup` instead. Extending to a moving feasible set means proving
Berge first.

## Main definitions

* `LeanEconomics.DynamicProgram` : the data of a deterministic dynamic program.
* `LeanEconomics.DynamicProgram.bellman` : its Bellman operator on `S →ᵇ ℝ`.
* `LeanEconomics.DynamicProgram.valueFunction` : the value function.

## Main results

* `LeanEconomics.DynamicProgram.blackwell` : the Bellman operator satisfies Blackwell's
  conditions, hence is a contraction.
* `LeanEconomics.DynamicProgram.bellman_valueFunction`,
  `LeanEconomics.DynamicProgram.eq_valueFunction` : the value function is the unique
  solution of the Bellman equation.
* `LeanEconomics.DynamicProgram.exists_optimal_action` : the supremum is attained, so a
  greedy policy exists.

## References

* Stokey, Lucas and Prescott, *Recursive Methods in Economic Dynamics*, chapter 4.
-/

open scoped NNReal
open Filter Topology BoundedContinuousFunction

namespace LeanEconomics

variable {S A : Type*} [TopologicalSpace S] [TopologicalSpace A]

/-- A **deterministic dynamic program**: the agent observes a state, picks an action from a
fixed compact set, collects a reward, and moves to the state the law of motion dictates. -/
structure DynamicProgram (S A : Type*) [TopologicalSpace S] [TopologicalSpace A] where
  /-- The actions available to the agent. -/
  actions : Set A
  /-- The action set is compact, so that the supremum over it is attained. -/
  isCompact_actions : IsCompact actions
  /-- The agent always has something to do. -/
  actions_nonempty : actions.Nonempty
  /-- The one-period reward, bounded and continuous in state and action jointly. -/
  reward : (S × A) →ᵇ ℝ
  /-- The law of motion. -/
  transition : C(S × A, S)
  /-- The discount factor. -/
  discount : ℝ≥0
  /-- Future rewards are discounted strictly, which is what makes the operator a
  contraction. -/
  discount_lt_one : discount < 1

namespace DynamicProgram

variable (D : DynamicProgram S A)

/-- What the agent gets from action `a` in state `s`: this period's reward plus the
discounted continuation value at the state the action leads to. -/
noncomputable def objective (v : S →ᵇ ℝ) (s : S) (a : A) : ℝ :=
  D.reward (s, a) + D.discount * v (D.transition (s, a))

theorem continuous_uncurry_objective (v : S →ᵇ ℝ) : Continuous ↿(D.objective v) :=
  D.reward.continuous.add (continuous_const.mul (v.continuous.comp D.transition.continuous))

theorem continuous_objective (v : S →ᵇ ℝ) (s : S) : Continuous (D.objective v s) :=
  (D.continuous_uncurry_objective v).comp (Continuous.prodMk_right s)

/-- The objective is bounded uniformly in the state and the action, by the size of the
reward plus the discounted size of the continuation value. -/
theorem abs_objective_le (v : S →ᵇ ℝ) (s : S) (a : A) :
    |D.objective v s a| ≤ ‖D.reward‖ + D.discount * ‖v‖ := by
  have h₁ : |D.reward (s, a)| ≤ ‖D.reward‖ := by
    simpa [Real.norm_eq_abs] using D.reward.norm_coe_le_norm (s, a)
  have h₂ : |v (D.transition (s, a))| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using v.norm_coe_le_norm (D.transition (s, a))
  have hβ : (0 : ℝ) ≤ D.discount := D.discount.coe_nonneg
  rw [abs_le] at h₁ h₂
  simp only [objective, abs_le]
  constructor <;>
    nlinarith [h₁.1, h₁.2, h₂.1, h₂.2, mul_le_mul_of_nonneg_left h₂.1 hβ,
      mul_le_mul_of_nonneg_left h₂.2 hβ]

theorem nonempty_image (v : S →ᵇ ℝ) (s : S) : (D.objective v s '' D.actions).Nonempty :=
  D.actions_nonempty.image _

theorem bddAbove_image (v : S →ᵇ ℝ) (s : S) : BddAbove (D.objective v s '' D.actions) := by
  refine ⟨‖D.reward‖ + D.discount * ‖v‖, ?_⟩
  rintro _ ⟨a, -, rfl⟩
  exact (le_abs_self _).trans (D.abs_objective_le v s a)

/-- The Bellman operator as a bare function, before packaging it up. -/
noncomputable def bellmanFn (v : S →ᵇ ℝ) (s : S) : ℝ := sSup (D.objective v s '' D.actions)

theorem le_bellmanFn (v : S →ᵇ ℝ) {s : S} {a : A} (ha : a ∈ D.actions) :
    D.objective v s a ≤ D.bellmanFn v s :=
  le_csSup (D.bddAbove_image v s) ⟨a, ha, rfl⟩

theorem bellmanFn_le (v : S →ᵇ ℝ) {s : S} {c : ℝ} (h : ∀ a ∈ D.actions, D.objective v s a ≤ c) :
    D.bellmanFn v s ≤ c :=
  csSup_le (D.nonempty_image v s) (by rintro _ ⟨a, ha, rfl⟩; exact h a ha)

theorem abs_bellmanFn_le (v : S →ᵇ ℝ) (s : S) :
    |D.bellmanFn v s| ≤ ‖D.reward‖ + D.discount * ‖v‖ := by
  obtain ⟨a, ha⟩ := D.actions_nonempty
  rw [abs_le]
  refine ⟨?_, D.bellmanFn_le v fun b _ => (le_abs_self _).trans (D.abs_objective_le v s b)⟩
  exact le_trans (neg_le_of_abs_le (D.abs_objective_le v s a)) (D.le_bellmanFn v ha)

/-- The **Bellman operator** on bounded continuous functions. Continuity of the image is
`IsCompact.continuous_sSup`; boundedness is `abs_bellmanFn_le`. -/
noncomputable def bellman (v : S →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (D.bellmanFn v)
    (D.isCompact_actions.continuous_sSup (D.continuous_uncurry_objective v))
    (‖D.reward‖ + D.discount * ‖v‖)
    fun s => by simpa [Real.norm_eq_abs] using D.abs_bellmanFn_le v s

@[simp]
theorem bellman_apply (v : S →ᵇ ℝ) (s : S) :
    D.bellman v s = sSup (D.objective v s '' D.actions) := rfl

/-- **The Bellman operator satisfies Blackwell's sufficient conditions.** Monotonicity
holds because a larger continuation value raises the objective at every action;
discounting holds because the continuation value enters multiplied by `β`. -/
theorem blackwell : Blackwell D.discount D.bellman where
  monotone := by
    intro v w hvw s
    have hβ : (0 : ℝ) ≤ D.discount := D.discount.coe_nonneg
    have key : ∀ a ∈ D.actions, D.objective v s a ≤ D.bellmanFn w s := by
      intro a ha
      refine le_trans ?_ (D.le_bellmanFn w ha)
      have hx : v (D.transition (s, a)) ≤ w (D.transition (s, a)) := by
        simpa using hvw (D.transition (s, a))
      simp only [objective]
      nlinarith
    exact D.bellmanFn_le v key
  discounting := by
    intro v c _ s
    have key : ∀ a ∈ D.actions, D.objective (v + const S c) s a
        ≤ D.bellmanFn v s + D.discount * c := by
      intro a ha
      have h : D.objective (v + const S c) s a = D.objective v s a + D.discount * c := by
        simp only [objective, coe_add, const_apply, Pi.add_apply]
        ring
      rw [h]
      have := D.le_bellmanFn v (s := s) ha
      linarith
    exact D.bellmanFn_le (v + const S c) key

/-- The supremum defining the Bellman operator is **attained**: in every state there is an
optimal action. This is what makes a greedy policy well defined. -/
theorem exists_optimal_action (v : S →ᵇ ℝ) (s : S) :
    ∃ a ∈ D.actions, D.bellman v s = D.objective v s a ∧
      ∀ b ∈ D.actions, D.objective v s b ≤ D.objective v s a :=
  D.isCompact_actions.exists_sSup_image_eq_and_ge D.actions_nonempty
    (D.continuous_objective v s).continuousOn

section ValueFunction

/-- The **value function** of the program: the unique fixed point of its Bellman
operator. -/
noncomputable def valueFunction : S →ᵇ ℝ :=
  D.blackwell.valueFunction D.discount_lt_one

/-- The value function satisfies the **Bellman equation**. -/
theorem bellman_valueFunction : D.bellman D.valueFunction = D.valueFunction :=
  D.blackwell.isFixedPt_valueFunction D.discount_lt_one

/-- The Bellman equation has **no other** bounded continuous solution. -/
theorem eq_valueFunction {v : S →ᵇ ℝ} (hv : D.bellman v = v) : v = D.valueFunction :=
  D.blackwell.eq_valueFunction D.discount_lt_one hv

/-- **Value function iteration converges** to the value function from any starting
guess. -/
theorem tendsto_iterate_valueFunction (v : S →ᵇ ℝ) :
    Tendsto (fun n => D.bellman^[n] v) atTop (𝓝 D.valueFunction) :=
  D.blackwell.tendsto_iterate_valueFunction D.discount_lt_one v

/-- The geometric error bound for value function iteration on a dynamic program. -/
theorem norm_iterate_sub_valueFunction_le (v : S →ᵇ ℝ) (n : ℕ) :
    ‖D.bellman^[n] v - D.valueFunction‖
      ≤ (D.discount : ℝ) ^ n / (1 - D.discount) * ‖D.bellman v - v‖ :=
  D.blackwell.norm_iterate_sub_valueFunction_le D.discount_lt_one v n

/-- In every state, the value function is attained by some action: the **optimal policy**
exists, and the value function is the reward it collects plus the discounted value of the
state it leads to. -/
theorem exists_optimal_policy (s : S) :
    ∃ a ∈ D.actions, D.valueFunction s
      = D.reward (s, a) + D.discount * D.valueFunction (D.transition (s, a)) := by
  obtain ⟨a, ha, heq, -⟩ := D.exists_optimal_action D.valueFunction s
  rw [D.bellman_valueFunction] at heq
  exact ⟨a, ha, heq⟩

end ValueFunction

end DynamicProgram

end LeanEconomics
