/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Bellman

/-!
# Worked examples

These are checks on the definitions rather than results of interest. A structure that
cannot be instantiated makes every theorem about it vacuously true, and a Bellman operator
that is subtly mis-stated still yields a perfectly good fixed point -- of the wrong
equation.

`constProgram` pays a fixed reward `r₀` regardless of what the agent does. Its value must
be the present value of that reward stream, `r₀ / (1 - β)`, and
`constProgram_valueFunction` proves it is. This exercises the whole chain: the maximisation,
the contraction, and uniqueness of the fixed point.

`ruleProgram` is the more informative of the two. Its feasible set is the single point
picked out by a continuous rule, so the constraint set genuinely *moves* with the state --
which `constProgram` does not exercise at all, and which is the case the hemicontinuity
fields of `DynamicProgram` exist to handle. Its value function satisfies the Bellman
equation with the supremum stripped away, since there is nothing to choose between.
-/

open scoped NNReal
open BoundedContinuousFunction

namespace LeanEconomics

variable {S A : Type*} [TopologicalSpace S] [TopologicalSpace A]

/-! ### A constant reward -/

/-- A dynamic program paying the constant reward `r₀`, whatever the agent does and wherever
it leads. The feasible set, law of motion and discount factor are arbitrary. -/
noncomputable def constProgram (K : Set A) (hK : IsCompact K) (hKne : K.Nonempty)
    (g : C(S × A, S)) (r₀ : ℝ) (β : ℝ≥0) (hβ : β < 1) : DynamicProgram S A where
  feasible _ := K
  isCompact_feasible _ := hK
  feasible_nonempty _ := hKne
  upperHemicontinuous_feasible := upperHemicontinuous_const K
  lowerHemicontinuous_feasible := lowerHemicontinuous_const K
  reward := const (S × A) r₀
  transition := g
  discount := β
  discount_lt_one := hβ

/-- **The present value of a constant reward stream.** The value function of
`constProgram` is the constant `r₀ / (1 - β)`, as the geometric sum
`r₀ + β r₀ + β² r₀ + ⋯` requires. -/
theorem constProgram_valueFunction (K : Set A) (hK : IsCompact K) (hKne : K.Nonempty)
    (g : C(S × A, S)) (r₀ : ℝ) (β : ℝ≥0) (hβ : β < 1) :
    (constProgram K hK hKne g r₀ β hβ).valueFunction = const S (r₀ / (1 - β)) := by
  have hβ' : (β : ℝ) < 1 := by exact_mod_cast hβ
  have hne : (1 : ℝ) - β ≠ 0 := by linarith
  symm
  apply DynamicProgram.eq_valueFunction
  ext s
  have hobj : (constProgram K hK hKne g r₀ β hβ).objective (const S (r₀ / (1 - β))) s
      = fun _ : A => r₀ + (β : ℝ) * (r₀ / (1 - β)) := by
    funext a
    simp [DynamicProgram.objective, constProgram]
  rw [DynamicProgram.bellman_apply, maxValue,
    show (constProgram K hK hKne g r₀ β hβ).feasible s = K from rfl, hobj,
    hKne.image_const, csSup_singleton, const_apply]
  field_simp
  ring

/-! ### A feasible set that moves with the state -/

section Rule

variable (g : S → A) (hg : Continuous g) (r : (S × A) →ᵇ ℝ) (tr : C(S × A, S))
  (β : ℝ≥0) (hβ : β < 1)

/-- A dynamic program in which a continuous rule `g` dictates the action: the feasible set
is the single point `{g s}`, which moves with the state. The agent has no choice, but the
correspondence is genuinely state-dependent, so this instantiates the hemicontinuity
hypotheses non-trivially. -/
noncomputable def ruleProgram : DynamicProgram S A where
  feasible s := {g s}
  isCompact_feasible _ := isCompact_singleton
  feasible_nonempty _ := Set.singleton_nonempty _
  upperHemicontinuous_feasible := upperHemicontinuous_singleton_iff.mpr hg
  lowerHemicontinuous_feasible := lowerHemicontinuous_singleton_iff.mpr hg
  reward := r
  transition := tr
  discount := β
  discount_lt_one := hβ

/-- With a single feasible action the supremum disappears. -/
theorem ruleProgram_bellman (v : S →ᵇ ℝ) (s : S) :
    (ruleProgram g hg r tr β hβ).bellman v s = r (s, g s) + β * v (tr (s, g s)) := by
  rw [DynamicProgram.bellman_apply, maxValue,
    show (ruleProgram g hg r tr β hβ).feasible s = {g s} from rfl,
    Set.image_singleton, csSup_singleton]
  rfl

/-- The value of following the rule: the Bellman equation with nothing to choose. -/
theorem ruleProgram_valueFunction (s : S) :
    (ruleProgram g hg r tr β hβ).valueFunction s
      = r (s, g s) + β * (ruleProgram g hg r tr β hβ).valueFunction (tr (s, g s)) := by
  conv_lhs => rw [← (ruleProgram g hg r tr β hβ).bellman_valueFunction]
  exact ruleProgram_bellman g hg r tr β hβ _ s

end Rule

end LeanEconomics
