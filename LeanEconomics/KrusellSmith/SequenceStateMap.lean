/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ClosedGraph
import LeanEconomics.KrusellSmith.InfiniteHistory

/-!
# The sequence-state map

Milestone TS2 of `SEQUENCE_STATE_PLAN.md`.

An **assignment** `μ : History Z → P(AState)` gives the distribution of households at every
infinite history of aggregate shocks. From it:

* `seqPrices μ ω`: the price inputs seen at the history `ω`, on the tree of its future
  extensions: at the node `g`, capital is mean assets of `μ (prepend g ω)` and labour is the
  efficiency-weighted mass of households there;
* `seqStep μ`: **the update**. At the history `cons z' ω` it is tomorrow's distribution after the
  shock `z'`, from today's `μ ω`, when households at `ω` save optimally against `seqPrices μ ω`
  (`seqStep_cons`). A fixed point of `seqStep` is a sequence-state equilibrium (TS3).

`continuous_seqStep`: **the update is continuous** in the product of weak topologies. Each
coordinate depends on `μ ω` and, through the price path, on the countably many `μ (prepend g ω)`;
both enter continuously (`continuous_seqPrices`), and the distribution one node down the tree is
jointly continuous in today's distribution and the price path
(`continuousAt_integral_nodeDist_joint`).
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **The price inputs seen at the history `ω`**: capital and labour at every node `g` of the
tree of its future extensions, read off the assignment at `prepend g ω`. -/
noncomputable def seqPrices (μ : History Z → ProbabilityMeasure M.AState) (ω : History Z) :
    List Z → ℝ × ℝ :=
  fun g => (∫ x, M.assets x ∂(μ (History.prepend g ω) : Measure M.AState),
    ∑ e, M.initMass (μ (History.prepend g ω) : Measure M.AState) e * M.efficiency e)

/-- The prices seen at a later history are those of the original tree, shifted. -/
theorem seqPrices_prepend (μ : History Z → ProbabilityMeasure M.AState) (ω : History Z)
    (g g' : List Z) : M.seqPrices μ (History.prepend g ω) g' = M.seqPrices μ ω (g' ++ g) := by
  simp only [seqPrices, History.prepend_append]

/-- Labour in `seqPrices` is labour at the root of the tree started from the masses there. -/
theorem seqPrices_snd (μ : History Z → ProbabilityMeasure M.AState) (ω : History Z)
    (g : List Z) (z₀ : Z) :
    (M.seqPrices μ ω g).2
      = M.labour z₀ (M.initMass (μ (History.prepend g ω) : Measure M.AState)) [] := rfl

/-- One node down the tree rooted at the shock `z₀`, after the shock `z'`, from the distribution
`p.1` under the price path `p.2`, as a probability measure. -/
noncomputable def pushRoot (z₀ z' : Z) (p : ProbabilityMeasure M.AState × (List Z → ℝ × ℝ)) :
    ProbabilityMeasure M.AState :=
  ⟨M.pushNode z₀ p.2 [] z' (p.1 : Measure M.AState), M.isProbabilityMeasure_pushNode _ _ _ _ _⟩

/-- **The update**: at every history, the distribution after its newest shock, from the
distribution one period earlier, under the saving policy against the prices seen there. -/
noncomputable def seqStep (μ : History Z → ProbabilityMeasure M.AState) :
    History Z → ProbabilityMeasure M.AState :=
  fun ω' => M.pushRoot (History.tail ω' 0) (ω' 0)
    (μ (History.tail ω'), M.seqPrices μ (History.tail ω'))

theorem coe_seqStep_cons (μ : History Z → ProbabilityMeasure M.AState) (z' : Z)
    (ω : History Z) :
    (M.seqStep μ (History.cons z' ω) : Measure M.AState)
      = M.pushNode (ω 0) (M.seqPrices μ ω) [] z' (μ ω : Measure M.AState) := rfl

/-- One step of the update is one node down the tree rooted at `ω`, from `μ ω`. -/
theorem coe_seqStep_cons_eq_nodeDist (μ : History Z → ProbabilityMeasure M.AState) (z' : Z)
    (ω : History Z) :
    (M.seqStep μ (History.cons z' ω) : Measure M.AState)
      = M.nodeDist (ω 0) (μ ω : Measure M.AState) (M.seqPrices μ ω) [z'] := rfl

/-! ### Continuity -/

/-- The price path seen at a history is continuous in the assignment. -/
theorem continuous_seqPrices (ω : History Z) :
    Continuous fun μ : History Z → ProbabilityMeasure M.AState => M.seqPrices μ ω := by
  refine continuous_pi fun g => ?_
  have hev : Continuous fun μ : History Z → ProbabilityMeasure M.AState =>
      μ (History.prepend g ω) := continuous_apply _
  refine Continuous.prodMk ?_ ?_
  · exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction M.assets).comp hev
  · exact continuous_finsetSum _ fun e _ =>
      (((continuous_apply e).comp M.continuous_initMass).comp hev).mul continuous_const

/-- One node down the tree, as a probability measure, is jointly continuous in today's
distribution and the price path. -/
theorem continuous_pushRoot (z₀ z' : Z) : Continuous (M.pushRoot z₀ z') := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
  exact M.continuousAt_integral_nodeDist_joint z₀ p₀ [z'] f

/-- **The update is continuous** in the product of weak topologies. -/
theorem continuous_seqStep : Continuous M.seqStep := by
  refine continuous_pi fun ω' => ?_
  have hq : Continuous fun μ : History Z → ProbabilityMeasure M.AState =>
      (μ (History.tail ω'), M.seqPrices μ (History.tail ω')) :=
    (continuous_apply _).prodMk (M.continuous_seqPrices _)
  exact (M.continuous_pushRoot (History.tail ω' 0) (ω' 0)).comp hq

end KSModel

end KrusellSmith

end LeanEconomics
