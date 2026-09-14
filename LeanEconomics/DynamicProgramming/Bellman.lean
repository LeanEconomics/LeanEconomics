/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Blackwell
import LeanEconomics.Topology.Berge

/-!
# The Bellman operator of a deterministic dynamic program

The operator

  `T v s = sup { r (s, a) + β * v (g (s, a)) | a ∈ Γ s }`

is shown to map bounded continuous functions to bounded continuous functions, and to
satisfy Blackwell's sufficient conditions. Combined with `LeanEconomics.Blackwell` this
gives the value function of the program, its uniqueness, and convergence of value function
iteration.

## The formulation

A program is given by a feasible correspondence `Γ : S → Set A` with nonempty compact
values that is continuous -- upper and lower hemicontinuous -- together with a bounded
continuous reward `r : (S × A) →ᵇ ℝ`, a continuous law of motion `g : C(S × A, S)`, and a
discount factor `β < 1`.

The feasible set moves with the state, which is what a budget constraint does. The price of
that generality is the continuity of `T v`, and it is paid by Berge's maximum theorem in
`LeanEconomics.Topology.Berge`: `continuous_maxValue` is exactly the statement that the
value of a parametrised maximisation problem is continuous in the parameter.

Verifying that a particular `Γ` is hemicontinuous is real work, done per model. The two
programs in `LeanEconomics.DynamicProgramming.Examples` discharge it in the two cheapest
ways: a constraint set that does not move, and one pinned to a single continuously varying
point.

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

/-- A **deterministic dynamic program**: the agent observes a state, picks an action from
the feasible set at that state, collects a reward, and moves to the state the law of motion
dictates. -/
structure DynamicProgram (S A : Type*) [TopologicalSpace S] [TopologicalSpace A] where
  /-- The actions available to the agent, as a function of the state. -/
  feasible : S → Set A
  /-- Each feasible set is compact, so that the supremum over it is attained. -/
  isCompact_feasible : ∀ s, IsCompact (feasible s)
  /-- The agent always has something to do. -/
  feasible_nonempty : ∀ s, (feasible s).Nonempty
  /-- The feasible set does not explode as the state moves. -/
  upperHemicontinuous_feasible : UpperHemicontinuous feasible
  /-- The feasible set does not collapse as the state moves. -/
  lowerHemicontinuous_feasible : LowerHemicontinuous feasible
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

/-- The Bellman operator as a bare function: the value of the one-period problem, in the
sense of `LeanEconomics.maxValue`. -/
noncomputable def bellmanFn (v : S →ᵇ ℝ) (s : S) : ℝ :=
  maxValue (D.objective v) D.feasible s

theorem le_bellmanFn (v : S →ᵇ ℝ) {s : S} {a : A} (ha : a ∈ D.feasible s) :
    D.objective v s a ≤ D.bellmanFn v s :=
  le_maxValue (D.continuous_uncurry_objective v) (D.isCompact_feasible s) ha

theorem bellmanFn_le (v : S →ᵇ ℝ) {s : S} {c : ℝ}
    (h : ∀ a ∈ D.feasible s, D.objective v s a ≤ c) : D.bellmanFn v s ≤ c :=
  maxValue_le (D.feasible_nonempty s) h

theorem abs_bellmanFn_le (v : S →ᵇ ℝ) (s : S) :
    |D.bellmanFn v s| ≤ ‖D.reward‖ + D.discount * ‖v‖ := by
  obtain ⟨a, ha⟩ := D.feasible_nonempty s
  rw [abs_le]
  refine ⟨?_, D.bellmanFn_le v fun b _ => (le_abs_self _).trans (D.abs_objective_le v s b)⟩
  exact le_trans (neg_le_of_abs_le (D.abs_objective_le v s a)) (D.le_bellmanFn v ha)

/-- The **Bellman operator** on bounded continuous functions. Continuity of the image is
Berge's maximum theorem; boundedness is `abs_bellmanFn_le`. -/
noncomputable def bellman (v : S →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (D.bellmanFn v)
    (continuous_maxValue (D.continuous_uncurry_objective v) D.feasible_nonempty
      D.isCompact_feasible D.upperHemicontinuous_feasible D.lowerHemicontinuous_feasible)
    (‖D.reward‖ + D.discount * ‖v‖)
    fun s => by simpa [Real.norm_eq_abs] using D.abs_bellmanFn_le v s

@[simp]
theorem bellman_apply (v : S →ᵇ ℝ) (s : S) :
    D.bellman v s = maxValue (D.objective v) D.feasible s := rfl

/-- **The Bellman operator satisfies Blackwell's sufficient conditions.** Monotonicity
holds because a larger continuation value raises the objective at every action;
discounting holds because the continuation value enters multiplied by `β`. -/
theorem blackwell : Blackwell D.discount D.bellman where
  monotone := by
    intro v w hvw s
    have hβ : (0 : ℝ) ≤ D.discount := D.discount.coe_nonneg
    have key : ∀ a ∈ D.feasible s, D.objective v s a ≤ D.bellmanFn w s := by
      intro a ha
      refine le_trans ?_ (D.le_bellmanFn w ha)
      have hx : v (D.transition (s, a)) ≤ w (D.transition (s, a)) := by
        simpa using hvw (D.transition (s, a))
      simp only [objective]
      nlinarith
    exact D.bellmanFn_le v key
  discounting := by
    intro v c _ s
    have key : ∀ a ∈ D.feasible s, D.objective (v + const S c) s a
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
    ∃ a ∈ D.feasible s, D.bellman v s = D.objective v s a ∧
      ∀ b ∈ D.feasible s, D.objective v s b ≤ D.objective v s a := by
  obtain ⟨a, ha, hmax⟩ :=
    argmax_nonempty (D.continuous_uncurry_objective v) (D.feasible_nonempty s)
      (D.isCompact_feasible s)
  exact ⟨a, ha,
    maxValue_eq (D.continuous_uncurry_objective v) (D.isCompact_feasible s) ⟨ha, hmax⟩,
    fun b hb => isMaxOn_iff.mp hmax b hb⟩

/-- The maximiser correspondence of the one-period problem is upper hemicontinuous, by the
second half of Berge's theorem. -/
theorem upperHemicontinuous_argmax (v : S →ᵇ ℝ) :
    UpperHemicontinuous (argmax (D.objective v) D.feasible) := fun s =>
  upperHemicontinuousAt_argmax (D.continuous_uncurry_objective v) D.feasible_nonempty
    D.isCompact_feasible (D.upperHemicontinuous_feasible s) (D.lowerHemicontinuous_feasible s)

section Monotone

variable [Preorder S]

/-- The Bellman operator preserves monotonicity when the feasible set grows with the state,
the reward rises with it, and the law of motion is monotone in it. -/
theorem monotone_bellman
    (hfeas : ∀ s s', s ≤ s' → D.feasible s ⊆ D.feasible s')
    (hreward : ∀ a, Monotone fun s => D.reward (s, a))
    (htrans : ∀ a, Monotone fun s => D.transition (s, a))
    (v : S →ᵇ ℝ) (hv : Monotone ⇑v) : Monotone ⇑(D.bellman v) := by
  intro s s' hss
  refine D.bellmanFn_le v fun a ha => ?_
  refine le_trans ?_ (D.le_bellmanFn v (hfeas s s' hss ha))
  have h₁ : D.reward (s, a) ≤ D.reward (s', a) := hreward a hss
  have h₂ : v (D.transition (s, a)) ≤ v (D.transition (s', a)) := hv (htrans a hss)
  have hβ : (0 : ℝ) ≤ D.discount := D.discount.coe_nonneg
  simp only [objective]
  nlinarith

end Monotone

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

/-- In every state, the value function is attained by some feasible action: the **optimal
policy** exists, and the value function is the reward it collects plus the discounted value
of the state it leads to. -/
theorem exists_optimal_policy (s : S) :
    ∃ a ∈ D.feasible s, D.valueFunction s
      = D.reward (s, a) + D.discount * D.valueFunction (D.transition (s, a)) := by
  obtain ⟨a, ha, heq, -⟩ := D.exists_optimal_action D.valueFunction s
  rw [D.bellman_valueFunction] at heq
  exact ⟨a, ha, heq⟩

/-- **The value function is increasing in the state** when the feasible set grows with the
state, the reward rises with it, and the law of motion is monotone in it. -/
theorem monotone_valueFunction [Preorder S]
    (hfeas : ∀ s s', s ≤ s' → D.feasible s ⊆ D.feasible s')
    (hreward : ∀ a, Monotone fun s => D.reward (s, a))
    (htrans : ∀ a, Monotone fun s => D.transition (s, a)) :
    Monotone ⇑D.valueFunction :=
  D.blackwell.monotone_valueFunction D.discount_lt_one
    fun v hv => D.monotone_bellman hfeas hreward htrans v hv

end ValueFunction

end DynamicProgram

end LeanEconomics
