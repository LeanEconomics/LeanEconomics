/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Recursive

/-!
# Consistent selections of sequential equilibria give recursive equilibria

Milestone MR1 of `MINIMAL_STATE_PLAN.md`. `Recursive.lean` builds a recursive equilibrium on the
minimal state `(z, μ)` from uniqueness of sequential equilibrium, but uses uniqueness only
through one consequence: the selected equilibrium is **consistent**, its continuation below the
child `[z']` being the equilibrium selected at the child's state.

A **consistent selection** (`ConsistentSelection`) picks a sequential equilibrium `sel z μ` from
every shock and distribution, consistently one step down the tree. Then:

* consistency holds at every node (`shiftPath_sel`), by induction, re-rooting one step at a
  time (`nodeDist_shift`, `pricePath_shift`);
* along every selected equilibrium, at every node `h` with state `(z_h, μ_h)`, capital is mean
  assets, households save by `recursivePolicy z_h μ_h`, and the distribution at each child is
  `lawOfMotion z_h μ_h z'` (`isRecursive`): **a recursive equilibrium on the minimal state**.

Uniqueness gives a consistent selection (`ofUnique`); the monotone route (MR3) gives another,
the greatest equilibrium, without uniqueness. No continuity in `μ` is asked: a selection from a
non-singleton equilibrium set need not be continuous.
-/

open Set MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **A consistent selection of sequential equilibria**: from every shock and distribution a
sequential equilibrium, whose continuation below each child `[z']` is the equilibrium selected at
the child's shock and distribution. -/
structure ConsistentSelection where
  /-- The selected capital path from `(z, μ)`. -/
  sel : Z → ProbabilityMeasure M.AState → List Z → ℝ
  sel_spec : ∀ (z : Z) (μ : ProbabilityMeasure M.AState),
    M.IsSequentialEquilibrium z (μ : Measure M.AState) (sel z μ)
  sel_shift : ∀ (z : Z) (μ : ProbabilityMeasure M.AState) (z' : Z), shiftPath (sel z μ) [z'] =
    sel z' ⟨M.nodeDist z (μ : Measure M.AState)
      (M.pricePath z (M.initMass (μ : Measure M.AState)) (sel z μ)) [z'],
      M.isProbabilityMeasure_nodeDist z _ _ [z']⟩

namespace ConsistentSelection

variable {M} (S : M.ConsistentSelection)

/-- The price path of the selected equilibrium. -/
noncomputable def prices (z : Z) (μ : ProbabilityMeasure M.AState) : List Z → ℝ × ℝ :=
  M.pricePath z (M.initMass (μ : Measure M.AState)) (S.sel z μ)

/-- The distribution at node `h` along the selected equilibrium from `(z, μ)`. -/
noncomputable def nodeProb (z : Z) (μ : ProbabilityMeasure M.AState) (h : List Z) :
    ProbabilityMeasure M.AState :=
  ⟨M.nodeDist z (μ : Measure M.AState) (S.prices z μ) h,
    M.isProbabilityMeasure_nodeDist z _ _ h⟩

/-- **The law of motion**: next period's distribution when the shock moves to `z'`. -/
noncomputable def lawOfMotion (z : Z) (μ : ProbabilityMeasure M.AState) (z' : Z) :
    ProbabilityMeasure M.AState :=
  S.nodeProb z μ [z']

/-- **The policy**: saving at `(a, e)` when the aggregate state is `(z, μ)`. -/
noncomputable def recursivePolicy (z : Z) (μ : ProbabilityMeasure M.AState) (x : M.AState) : ℝ :=
  M.policy z (S.prices z μ) (x.1, ⟨x.2.idio, []⟩)

theorem nodeProb_nil (z : Z) (μ : ProbabilityMeasure M.AState) : S.nodeProb z μ [] = μ :=
  Subtype.ext rfl

omit [Fintype Z] in
theorem shiftPath_cons {α : Type*} (K : List Z → α) (z' : Z) (h : List Z) :
    shiftPath K (z' :: h) = shiftPath (shiftPath K h) [z'] := by
  funext g
  simp only [shiftPath_apply, List.append_assoc, List.singleton_append]

/-- **Consistency at every node**: the path below `h` is the equilibrium selected at the state at
`h`, and the distribution at `z' :: h` is the law of motion at the state at `h`. -/
theorem shiftPath_sel_and_nodeProb (z : Z) (μ : ProbabilityMeasure M.AState) :
    ∀ h : List Z, shiftPath (S.sel z μ) h = S.sel (shockAt z h) (S.nodeProb z μ h) ∧
      ∀ z', S.nodeProb z μ (z' :: h) = S.lawOfMotion (shockAt z h) (S.nodeProb z μ h) z'
  | [] => by
    refine ⟨?_, fun z' => ?_⟩
    · rw [nodeProb_nil]
      funext g
      simp only [shiftPath_apply, List.append_nil, shockAt_nil]
    · rw [nodeProb_nil]
      rfl
  | z' :: h => by
    obtain ⟨IH, IHnp⟩ := shiftPath_sel_and_nodeProb z μ h
    have hstep : shiftPath (S.sel z μ) (z' :: h)
        = S.sel z' (S.nodeProb z μ (z' :: h)) := by
      rw [shiftPath_cons, IH, S.sel_shift, IHnp z']
      rfl
    refine ⟨hstep, fun z'' => ?_⟩
    apply Subtype.ext
    change M.nodeDist z (μ : Measure M.AState) (S.prices z μ) (z'' :: z' :: h)
      = M.nodeDist z' (S.nodeProb z μ (z' :: h) : Measure M.AState)
          (M.pricePath z' (M.initMass (S.nodeProb z μ (z' :: h) : Measure M.AState))
            (S.sel z' (S.nodeProb z μ (z' :: h)))) [z'']
    rw [← hstep]
    change _ = M.nodeDist (shockAt z (z' :: h))
      (M.nodeDist z (μ : Measure M.AState) (S.prices z μ) (z' :: h))
      (M.pricePath (shockAt z (z' :: h))
        (M.initMass (M.nodeDist z (μ : Measure M.AState) (S.prices z μ) (z' :: h)))
        (shiftPath (S.sel z μ) (z' :: h))) [z'']
    unfold prices
    rw [M.pricePath_shift z (μ : Measure M.AState) (S.sel z μ) (z' :: h)]
    exact (M.nodeDist_shift z _ (z' :: h) (μ : Measure M.AState) [z'']).symm

theorem shiftPath_sel (z : Z) (μ : ProbabilityMeasure M.AState) (h : List Z) :
    shiftPath (S.sel z μ) h = S.sel (shockAt z h) (S.nodeProb z μ h) :=
  (S.shiftPath_sel_and_nodeProb z μ h).1

theorem nodeProb_cons (z : Z) (μ : ProbabilityMeasure M.AState) (z' : Z) (h : List Z) :
    S.nodeProb z μ (z' :: h) = S.lawOfMotion (shockAt z h) (S.nodeProb z μ h) z' :=
  (S.shiftPath_sel_and_nodeProb z μ h).2 z'

theorem prices_nodeProb (z : Z) (μ : ProbabilityMeasure M.AState) (h : List Z) :
    S.prices (shockAt z h) (S.nodeProb z μ h) = shiftPath (S.prices z μ) h := by
  rw [prices, ← S.shiftPath_sel z μ h]
  exact M.pricePath_shift z (μ : Measure M.AState) (S.sel z μ) h

/-- **Households save by the recursive policy at every node.** -/
theorem policy_eq_recursivePolicy (z : Z) (μ : ProbabilityMeasure M.AState) (h : List Z)
    (x : M.AState) :
    M.policy z (S.prices z μ) (x.1, ⟨x.2.idio, h⟩)
      = S.recursivePolicy (shockAt z h) (S.nodeProb z μ h) x := by
  rw [recursivePolicy, S.prices_nodeProb z μ h, M.policy_shift]
  rfl

/-- **The recursive structure of a consistent selection**: along the selected equilibrium from
any `(z, μ)`, at every node `h` with state `(z_h, μ_h)`, capital is mean assets of `μ_h`,
households save by `recursivePolicy z_h μ_h`, and the distribution at every child `z' :: h` is
`lawOfMotion z_h μ_h z'`. -/
theorem isRecursive (z : Z) (μ : ProbabilityMeasure M.AState) (h : List Z) :
    S.sel z μ h = ∫ x, M.assets x ∂(S.nodeProb z μ h : Measure M.AState) ∧
      (∀ x : M.AState, M.policy z (S.prices z μ) (x.1, ⟨x.2.idio, h⟩)
          = S.recursivePolicy (shockAt z h) (S.nodeProb z μ h) x) ∧
      ∀ z' : Z, S.nodeProb z μ (z' :: h) = S.lawOfMotion (shockAt z h) (S.nodeProb z μ h) z' :=
  ⟨S.sel_spec z μ h, S.policy_eq_recursivePolicy z μ h, fun z' => S.nodeProb_cons z μ z' h⟩

end ConsistentSelection

variable {M}

/-- **Uniqueness gives a consistent selection**: the equilibrium path. -/
noncomputable def UniqueSequentialEquilibrium.consistentSelection
    (hU : M.UniqueSequentialEquilibrium) : M.ConsistentSelection where
  sel := M.eqPath
  sel_spec := M.eqPath_spec
  sel_shift z μ z' := shiftPath_eqPath hU z μ [z']

end KSModel

end KrusellSmith

end LeanEconomics
