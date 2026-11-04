/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Continuation
import Mathlib.Topology.Maps.Proper.Basic

/-!
# From unique sequential equilibrium to recursive equilibrium on the minimal state

A **recursive equilibrium on the minimal state** describes the economy by the aggregate shock and
the distribution of households alone: a law of motion `(z, μ, z') ↦ μ'` for the distribution and a
saving policy `(z, μ, a, e) ↦ a'`. Existence of one in Krusell–Smith economies is open. This module
reduces it to uniqueness of sequential equilibrium.

**Hypothesis** (`UniqueSequentialEquilibrium`): from every aggregate shock and every initial
probability distribution there is at most one sequential equilibrium. Existence is
`exists_sequentialEquilibrium`, so the equilibrium path `eqPath z μ` is a function of `(z, μ)`.

**The recursive equilibrium.** The distribution at the child `[z']` of the root defines the **law
of motion** `lawOfMotion z μ z'`, and saving at the root defines the **policy**
`recursivePolicy z μ`. Along every sequential equilibrium, at every node `h`
(`isRecursive`):

* the path below `h` is the equilibrium path from the state `(z_h, μ_h)` at `h`
  (`shiftPath_eqPath`, by the continuation theorem and uniqueness);
* the distribution at `z' :: h` is `lawOfMotion z_h μ_h z'` (`nodeProb_cons`);
* households save by `recursivePolicy z_h μ_h` (`policy_eq_recursivePolicy`);
* aggregate capital is mean assets of `μ_h`.

So the equilibrium depends on history only through `(z_h, μ_h)`.

**Continuity.** The equilibrium path is continuous in the initial distribution
(`continuous_eqPath`): its graph is closed (`isClosed_equilibriumGraph`) and it maps into a
compact set, so `continuous_of_isClosed_graph` applies. Hence the law of motion is weakly
continuous in the distribution (`continuous_lawOfMotion`) and the policy is jointly continuous
in the distribution and the household's state (`continuous_recursivePolicy`). No measurable
selection theorem is needed.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **Uniqueness of sequential equilibrium**, from every shock and initial distribution. -/
def UniqueSequentialEquilibrium : Prop :=
  ∀ (z : Z) (μ : ProbabilityMeasure M.AState) (K K' : List Z → ℝ),
    M.IsSequentialEquilibrium z (μ : Measure M.AState) K →
    M.IsSequentialEquilibrium z (μ : Measure M.AState) K' → K = K'

/-- A sequential equilibrium path from `(z, μ)`. -/
noncomputable def eqPath (z : Z) (μ : ProbabilityMeasure M.AState) : List Z → ℝ :=
  (M.exists_sequentialEquilibrium z (μ : Measure M.AState)).choose

theorem eqPath_spec (z : Z) (μ : ProbabilityMeasure M.AState) :
    M.IsSequentialEquilibrium z (μ : Measure M.AState) (M.eqPath z μ) :=
  (M.exists_sequentialEquilibrium z (μ : Measure M.AState)).choose_spec.2

/-- The distribution of households at node `h` along the equilibrium path from `(z, μ)`. -/
noncomputable def nodeProb (z : Z) (μ : ProbabilityMeasure M.AState) (h : List Z) :
    ProbabilityMeasure M.AState :=
  ⟨M.nodeDist z (μ : Measure M.AState)
      (M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ)) h,
    M.isProbabilityMeasure_nodeDist z _ _ h⟩

/-- **The law of motion**: next period's distribution when the aggregate shock moves to `z'`. -/
noncomputable def lawOfMotion (z : Z) (μ : ProbabilityMeasure M.AState) (z' : Z) :
    ProbabilityMeasure M.AState :=
  M.nodeProb z μ [z']

/-- **The policy**: saving at the state `(a, e)` when the aggregate state is `(z, μ)`. -/
noncomputable def recursivePolicy (z : Z) (μ : ProbabilityMeasure M.AState)
    (x : M.AState) : ℝ :=
  M.policy z (M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ))
    (x.1, ⟨x.2.idio, []⟩)

variable {M}

/-- Under uniqueness, every sequential equilibrium is the equilibrium path. -/
theorem UniqueSequentialEquilibrium.eq_eqPath (hU : M.UniqueSequentialEquilibrium) {z : Z}
    {μ : ProbabilityMeasure M.AState} {K : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium z (μ : Measure M.AState) K) : K = M.eqPath z μ :=
  hU z μ K _ hK (M.eqPath_spec z μ)

/-- **The path below a node is the equilibrium path from the state at that node.** -/
theorem shiftPath_eqPath (hU : M.UniqueSequentialEquilibrium) (z : Z)
    (μ : ProbabilityMeasure M.AState) (h : List Z) :
    shiftPath (M.eqPath z μ) h = M.eqPath (shockAt z h) (M.nodeProb z μ h) :=
  hU.eq_eqPath ((M.eqPath_spec z μ).continuation M z (μ : Measure M.AState) h)

theorem pricePath_nodeProb (hU : M.UniqueSequentialEquilibrium) (z : Z)
    (μ : ProbabilityMeasure M.AState) (h : List Z) :
    M.pricePath (shockAt z h) (M.initMass (M.nodeProb z μ h : Measure M.AState))
        (M.eqPath (shockAt z h) (M.nodeProb z μ h))
      = shiftPath (M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ)) h := by
  rw [← shiftPath_eqPath hU z μ h]
  exact M.pricePath_shift z (μ : Measure M.AState) (M.eqPath z μ) h

/-- **The distribution at `z' :: h` is the law of motion applied to the state at `h`.** -/
theorem nodeProb_cons (hU : M.UniqueSequentialEquilibrium) (z : Z)
    (μ : ProbabilityMeasure M.AState) (z' : Z) (h : List Z) :
    M.nodeProb z μ (z' :: h) = M.lawOfMotion (shockAt z h) (M.nodeProb z μ h) z' := by
  apply Subtype.ext
  change M.nodeDist z (μ : Measure M.AState)
      (M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ)) (z' :: h)
    = M.nodeDist (shockAt z h) (M.nodeProb z μ h : Measure M.AState)
      (M.pricePath (shockAt z h) (M.initMass (M.nodeProb z μ h : Measure M.AState))
        (M.eqPath (shockAt z h) (M.nodeProb z μ h))) [z']
  rw [pricePath_nodeProb hU z μ h]
  exact (M.nodeDist_shift z _ h (μ : Measure M.AState) [z']).symm

/-- **Households save by the recursive policy at every node.** -/
theorem policy_eq_recursivePolicy (hU : M.UniqueSequentialEquilibrium) (z : Z)
    (μ : ProbabilityMeasure M.AState) (h : List Z) (x : M.AState) :
    M.policy z (M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ))
        (x.1, ⟨x.2.idio, h⟩)
      = M.recursivePolicy (shockAt z h) (M.nodeProb z μ h) x := by
  rw [recursivePolicy, pricePath_nodeProb hU z μ h, M.policy_shift]
  rfl

/-- Aggregate capital at every node is mean assets of the distribution there. -/
theorem eqPath_eq_meanAssets (z : Z) (μ : ProbabilityMeasure M.AState) (h : List Z) :
    M.eqPath z μ h = ∫ x, M.assets x ∂(M.nodeProb z μ h : Measure M.AState) :=
  M.eqPath_spec z μ h

/-- **The recursive structure of the equilibrium.** Under uniqueness, along the equilibrium from
any `(z, μ)`, at every node `h` with state `(z_h, μ_h)`: capital is mean assets of `μ_h`,
households save by `recursivePolicy z_h μ_h`, and the distribution at every child `z' :: h` is
`lawOfMotion z_h μ_h z'`. -/
theorem isRecursive (hU : M.UniqueSequentialEquilibrium) (z : Z)
    (μ : ProbabilityMeasure M.AState) (h : List Z) :
    M.eqPath z μ h = ∫ x, M.assets x ∂(M.nodeProb z μ h : Measure M.AState) ∧
      (∀ x : M.AState,
        M.policy z (M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ))
            (x.1, ⟨x.2.idio, h⟩)
          = M.recursivePolicy (shockAt z h) (M.nodeProb z μ h) x) ∧
      ∀ z' : Z, M.nodeProb z μ (z' :: h) = M.lawOfMotion (shockAt z h) (M.nodeProb z μ h) z' :=
  ⟨eqPath_eq_meanAssets z μ h, policy_eq_recursivePolicy hU z μ h,
    fun z' => nodeProb_cons hU z μ z' h⟩

/-! ### Continuity in the distribution -/

/-- The equilibrium path, as a map into the compact set of paths with values in
`[0, assetCap]`. -/
noncomputable def eqPathPi (z : Z) (μ : ProbabilityMeasure M.AState) :
    ↥(univ.pi fun _ : List Z => Icc (0 : ℝ) M.assetCap) :=
  ⟨M.eqPath z μ, M.equilibrium_mem_pi z μ (M.eqPath_spec z μ)⟩

/-- **The equilibrium path is continuous in the initial distribution**, under uniqueness. -/
theorem continuous_eqPath (hU : M.UniqueSequentialEquilibrium) (z : Z) :
    Continuous (M.eqPath z) := by
  have : CompactSpace ↥(univ.pi fun _ : List Z => Icc (0 : ℝ) M.assetCap) :=
    isCompact_iff_compactSpace.1 M.isCompact_pi
  have hgraph : IsClosed (Function.graph (M.eqPathPi z)) := by
    have heq : Function.graph (M.eqPathPi z)
        = (Prod.map id Subtype.val) ⁻¹' M.equilibriumGraph z := by
      ext ⟨μ, K⟩
      constructor
      · rintro rfl
        exact M.eqPath_spec z μ
      · intro hK
        exact Subtype.ext (hU.eq_eqPath hK).symm
    rw [heq]
    exact (M.isClosed_equilibriumGraph z).preimage
      (continuous_id.prodMap continuous_subtype_val)
  exact continuous_subtype_val.comp (continuous_of_isClosed_graph hgraph)

/-- **The law of motion is weakly continuous in the distribution**, under uniqueness. -/
theorem continuous_lawOfMotion (hU : M.UniqueSequentialEquilibrium) (z z' : Z) :
    Continuous fun μ => M.lawOfMotion z μ z' := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hq : Continuous fun μ : ProbabilityMeasure M.AState => (μ, M.eqPath z μ) :=
    continuous_id.prodMk (continuous_eqPath hU z)
  have hp : Continuous fun μ : ProbabilityMeasure M.AState =>
      M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ) :=
    Continuous.comp (g := fun p : ProbabilityMeasure M.AState × (List Z → ℝ) =>
        M.pricePath z (M.initMass (p.1 : Measure M.AState)) p.2)
      (f := fun μ : ProbabilityMeasure M.AState => (μ, M.eqPath z μ))
      (M.continuous_pricePath_joint z) hq
  have hq' : Continuous fun μ : ProbabilityMeasure M.AState =>
      (μ, M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ)) :=
    continuous_id.prodMk hp
  change Continuous fun μ : ProbabilityMeasure M.AState => ∫ x, f x
    ∂(M.nodeDist z (μ : Measure M.AState)
      (M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ)) [z'])
  refine continuous_iff_continuousAt.2 fun μ => ?_
  exact ContinuousAt.comp
    (g := fun p : ProbabilityMeasure M.AState × (List Z → ℝ × ℝ) =>
      ∫ x, f x ∂(M.nodeDist z (p.1 : Measure M.AState) p.2 [z']))
    (f := fun μ : ProbabilityMeasure M.AState =>
      (μ, M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ)))
    (M.continuousAt_integral_nodeDist_joint z _ [z'] f) hq'.continuousAt

/-- **The recursive policy is jointly continuous** in the distribution and the household's state,
under uniqueness. -/
theorem continuous_recursivePolicy (hU : M.UniqueSequentialEquilibrium) (z : Z) :
    Continuous fun p : ProbabilityMeasure M.AState × M.AState =>
      M.recursivePolicy z p.1 p.2 := by
  have hpath : Continuous fun p : ProbabilityMeasure M.AState × M.AState =>
      M.pricePath z (M.initMass (p.1 : Measure M.AState)) (M.eqPath z p.1) :=
    Continuous.comp (g := fun q : ProbabilityMeasure M.AState × (List Z → ℝ) =>
        M.pricePath z (M.initMass (q.1 : Measure M.AState)) q.2)
      (f := fun p : ProbabilityMeasure M.AState × M.AState => (p.1, M.eqPath z p.1))
      (M.continuous_pricePath_joint z)
      (continuous_fst.prodMk ((continuous_eqPath hU z).comp continuous_fst))
  have hlab : Continuous fun i : Idio E => (⟨i.idio, []⟩ : Label Z E) :=
    continuous_of_discreteTopology
  have hstate : Continuous fun p : ProbabilityMeasure M.AState × M.AState =>
      ((p.2.1, ⟨p.2.2.idio, []⟩) : M.State) :=
    (continuous_fst.comp continuous_snd).prodMk (hlab.comp (continuous_snd.comp continuous_snd))
  change Continuous fun p : ProbabilityMeasure M.AState × M.AState =>
    M.policy z (M.pricePath z (M.initMass (p.1 : Measure M.AState)) (M.eqPath z p.1))
      (p.2.1, ⟨p.2.2.idio, []⟩)
  exact Continuous.comp (g := fun q : (List Z → ℝ × ℝ) × M.State => M.policy z q.1 q.2)
    (f := fun p : ProbabilityMeasure M.AState × M.AState =>
      (M.pricePath z (M.initMass (p.1 : Measure M.AState)) (M.eqPath z p.1),
        ((p.2.1, ⟨p.2.2.idio, []⟩) : M.State)))
    (M.continuous_policy z) (hpath.prodMk hstate)

end KSModel

end KrusellSmith

end LeanEconomics
