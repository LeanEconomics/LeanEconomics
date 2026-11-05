/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Model
import LeanEconomics.MarkovEquilibrium.Measures

/-!
# Infinite shock histories and assignments of distributions

Milestone TS1 of `SEQUENCE_STATE_PLAN.md`.

**Infinite histories** (`History Z = ℕ → Z`), newest first: `ω 0` is today's aggregate shock,
`ω 1` yesterday's, and so on. `cons z ω` is the history after tomorrow's shock `z`; every history
is `cons (ω 0) (tail ω)` (`cons_head_tail`). A finite list of future shocks `g` (newest first, as
the nodes of the tree in `Model.lean`) is **prepended**: `prepend g ω`, so that the node `g` of
the tree rooted at the history `ω` is the history `prepend g ω`, and its newest shock is
`shockAt (ω 0) g` (`prepend_zero`); prepending is compatible with concatenation
(`prepend_append`).

**Assignments** `μ : H → P(X)` give a probability measure at every history. Embedded coordinatewise
by `MarkovEquilibrium.embed` into the locally convex Hausdorff space `H → ((X →ᵇ ℝ≥0) → ℝ)`, they
form a compact (`isCompact_range_embedAssign`) and convex (`convex_range_embedAssign`) set, and
the embedding is a topological embedding (`isEmbedding_embedAssign`): the setting of
Schauder–Tychonoff for the sequence-state equilibrium (TS3).
-/

open MeasureTheory Set Topology BoundedContinuousFunction
open scoped NNReal

namespace LeanEconomics

namespace KrusellSmith

/-- **Infinite histories of aggregate shocks**, newest first. -/
abbrev History (Z : Type*) := ℕ → Z

namespace History

variable {Z : Type*}

/-- The history after the shock `z`. -/
def cons (z : Z) (ω : History Z) : History Z
  | 0 => z
  | n + 1 => ω n

/-- The history one period earlier. -/
def tail (ω : History Z) : History Z := fun n => ω (n + 1)

@[simp] theorem cons_zero (z : Z) (ω : History Z) : cons z ω 0 = z := rfl

@[simp] theorem cons_succ (z : Z) (ω : History Z) (n : ℕ) : cons z ω (n + 1) = ω n := rfl

@[simp] theorem tail_cons (z : Z) (ω : History Z) : tail (cons z ω) = ω := rfl

/-- **Every history is today's shock after yesterday's history.** -/
theorem cons_head_tail (ω : History Z) : cons (ω 0) (tail ω) = ω := by
  funext n
  cases n <;> rfl

theorem cons_inj {z z' : Z} {ω ω' : History Z} : cons z ω = cons z' ω' ↔ z = z' ∧ ω = ω' := by
  constructor
  · intro h
    exact ⟨congrFun h 0, funext fun n => congrFun h (n + 1)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **Prepending finite future shocks** (newest first) to an infinite history. -/
def prepend : List Z → History Z → History Z
  | [], ω => ω
  | z :: g, ω => cons z (prepend g ω)

@[simp] theorem prepend_nil (ω : History Z) : prepend [] ω = ω := rfl

@[simp] theorem prepend_cons (z : Z) (g : List Z) (ω : History Z) :
    prepend (z :: g) ω = cons z (prepend g ω) := rfl

theorem prepend_singleton (z : Z) (ω : History Z) : prepend [z] ω = cons z ω := rfl

theorem prepend_append (g g' : List Z) (ω : History Z) :
    prepend (g ++ g') ω = prepend g (prepend g' ω) := by
  induction g with
  | nil => rfl
  | cons z g ih => simp only [List.cons_append, prepend_cons, ih]

/-- **The newest shock at a node** of the tree rooted at `ω`. -/
theorem prepend_zero (g : List Z) (ω : History Z) : prepend g ω 0 = shockAt (ω 0) g := by
  cases g <;> rfl

end History

/-! ### Assignments of distributions to histories -/

section Assign

variable {H X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.MetrizableSpace X] [CompactSpace X]

/-- **The coordinatewise embedding** of assignments of probability measures. -/
noncomputable def embedAssign (μ : H → ProbabilityMeasure X) : H → ((X →ᵇ ℝ≥0) → ℝ) :=
  fun ω => MarkovEquilibrium.embed (μ ω)

omit [CompactSpace X] in
theorem isEmbedding_embedAssign :
    IsEmbedding (embedAssign : (H → ProbabilityMeasure X) → H → ((X →ᵇ ℝ≥0) → ℝ)) :=
  IsEmbedding.piMap fun _ => MarkovEquilibrium.isEmbedding_embed

theorem isCompact_range_embedAssign :
    IsCompact (range (embedAssign : (H → ProbabilityMeasure X) → H → ((X →ᵇ ℝ≥0) → ℝ))) :=
  isCompact_range isEmbedding_embedAssign.continuous

/-- The pointwise mixture of two assignments. -/
noncomputable def mixAssign (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (μ ν : H → ProbabilityMeasure X) :
    H → ProbabilityMeasure X :=
  fun ω => MarkovEquilibrium.mix t ht (μ ω) (ν ω)

omit [CompactSpace X] [TopologicalSpace.MetrizableSpace X] [BorelSpace X] in
theorem embedAssign_mix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (μ ν : H → ProbabilityMeasure X) :
    embedAssign (mixAssign t ht μ ν) = t • embedAssign μ + (1 - t) • embedAssign ν := by
  funext ω
  exact MarkovEquilibrium.embed_mix t ht (μ ω) (ν ω)

omit [CompactSpace X] [TopologicalSpace.MetrizableSpace X] [BorelSpace X] in
theorem convex_range_embedAssign :
    Convex ℝ (range (embedAssign : (H → ProbabilityMeasure X) → H → ((X →ᵇ ℝ≥0) → ℝ))) := by
  rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ a b ha hb hab
  refine ⟨mixAssign a ⟨ha, by linarith⟩ μ ν, ?_⟩
  obtain rfl : b = 1 - a := by linarith
  exact embedAssign_mix a ⟨ha, by linarith⟩ μ ν

omit [MeasurableSpace X] [BorelSpace X] [TopologicalSpace.MetrizableSpace X]
  [CompactSpace X] in
/-- The ambient space is locally convex and Hausdorff. -/
example : LocallyConvexSpace ℝ (H → ((X →ᵇ ℝ≥0) → ℝ)) ∧ T2Space (H → ((X →ᵇ ℝ≥0) → ℝ)) :=
  ⟨inferInstance, inferInstance⟩

end Assign

end KrusellSmith

end LeanEconomics
