/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Bellman

/-!
# Worked examples

These are checks on the definitions rather than results of interest. A structure that
cannot be instantiated makes every theorem about it vacuously true, and a Bellman operator
that is subtly mis-stated still yields a perfectly good fixed point -- of the wrong
equation. So we build a program and compute its value function in closed form.

`constProgram` pays a fixed reward `r₀` regardless of what the agent does. Its value must
be the present value of that reward stream, `r₀ / (1 - β)`, and
`constProgram_valueFunction` proves it is. This exercises the whole chain: the supremum
over the action set, the contraction, and uniqueness of the fixed point.
-/

open scoped NNReal
open BoundedContinuousFunction

namespace LeanEconomics

variable {S A : Type*} [TopologicalSpace S] [TopologicalSpace A]

/-- A dynamic program paying the constant reward `r₀`, whatever the agent does and wherever
it leads. The action set, law of motion and discount factor are arbitrary. -/
noncomputable def constProgram (K : Set A) (hK : IsCompact K) (hKne : K.Nonempty)
    (g : C(S × A, S)) (r₀ : ℝ) (β : ℝ≥0) (hβ : β < 1) : DynamicProgram S A where
  actions := K
  isCompact_actions := hK
  actions_nonempty := hKne
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
  have hact : (constProgram K hK hKne g r₀ β hβ).actions = K := rfl
  have hobj : (constProgram K hK hKne g r₀ β hβ).objective (const S (r₀ / (1 - β))) s
      = fun _ : A => r₀ + (β : ℝ) * (r₀ / (1 - β)) := by
    funext a
    simp [DynamicProgram.objective, constProgram]
  rw [DynamicProgram.bellman_apply, hact, hobj, hKne.image_const, csSup_singleton, const_apply]
  field_simp
  ring

end LeanEconomics
