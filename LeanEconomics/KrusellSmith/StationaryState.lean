/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ValueState

/-!
# The state space of a stationary recursive equilibrium

Milestone S5 (step 7) of `STATIONARITY_PLAN.md`. Following Cao (2020, §6), a state of the economy
is `ξ = (z, μ, v, a)`: the aggregate shock, the distribution of households, their value function
and their saving policy (`KSState`). Value and policy carry the supremum norm, the distribution
the weak topology; `KSState` is metrizable and is given its Borel σ-algebra.

* `rootPolicy z μ K`: saving at the root along the path `K`, as a bounded continuous function.
* `continuous_bcf_of_joint`: a family of functions on a compact space, jointly continuous in the
  parameter and the point, is continuous into the supremum norm. With the joint continuity of the
  value function and the policy in the path (`continuous_valueFunction_joint`,
  `continuous_policy`) this makes `(μ, K) ↦ (rootValue, rootPolicy)` continuous into the sup norm
  (`continuous_rootValue`, `continuous_rootPolicy`).
* `equilibriumStates`: Cao's `J*`, the states `(z, μ, rootValue, rootPolicy)` of sequential
  equilibria from `(z, μ)`. **It is compact** (`isCompact_equilibriumStates`): a finite union over
  `z` of continuous images of the compact equilibrium graph (`isClosed_equilibriumGraph`).
* `nodeState`: the state at node `h` along an equilibrium; it is again in `J*`
  (`nodeState_mem`), by the continuation theorem, `rootValue_shift` and `rootPolicy_shift`.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory Metric

namespace LeanEconomics

namespace KrusellSmith

/-- An aggregate shock, as a point of a discrete space. -/
structure AggShock (Z : Type*) where
  /-- The shock. -/
  val : Z

namespace AggShock

variable (Z : Type*)

instance : TopologicalSpace (AggShock Z) := ⊥

instance : DiscreteTopology (AggShock Z) := ⟨rfl⟩

end AggShock

/-- A family of functions on a compact space, jointly continuous in the parameter and the point,
is continuous into the supremum norm. -/
theorem continuous_bcf_of_joint {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace X] {G : P → X →ᵇ ℝ} (hG : Continuous fun q : P × X => G q.1 q.2) :
    Continuous G := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hfc : ContinuousOn (Function.uncurry fun (p : P) (x : X) => G p x) (univ ×ˢ univ) :=
    hG.continuousOn
  obtain ⟨w, hw, hwf⟩ := isCompact_univ.mem_uniformity_of_prod hfc (mem_univ p₀)
    (dist_mem_uniformity (half_pos hε))
  rw [nhdsWithin_univ] at hw
  filter_upwards [hw] with p hp
  exact lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).2
    fun x => (hwf p hp x (mem_univ x)).le) (half_lt_self hε)

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-! ### The policy at a node -/

/-- **Saving at node `h`** along the path of capital `K` from `(z, μ)`, as a function of assets
and idiosyncratic state. -/
theorem continuous_policy_placeAt (z : Z) (P : List Z → ℝ × ℝ) (h : List Z) :
    Continuous fun x : M.AState => M.policy z P (M.placeAt h x) := by
  have hc : Continuous fun x : M.AState => (P, M.placeAt h x) :=
    continuous_const.prodMk (M.continuous_placeAt h)
  have := (M.continuous_policy z).comp hc
  exact this

noncomputable def nodePolicy (z : Z) (μ : Measure M.AState) (K : List Z → ℝ) (h : List Z) :
    M.AState →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact (ContinuousMap.mk
    (fun x => M.policy z (M.pricePath z (M.initMass μ) K) (M.placeAt h x))
    (M.continuous_policy_placeAt z _ h))

/-- **Saving at the root** along the path of capital `K` from `(z, μ)`. -/
noncomputable def rootPolicy (z : Z) (μ : Measure M.AState) (K : List Z → ℝ) : M.AState →ᵇ ℝ :=
  M.nodePolicy z μ K []

theorem nodePolicy_apply (z : Z) (μ : Measure M.AState) (K : List Z → ℝ) (h : List Z)
    (x : M.AState) :
    M.nodePolicy z μ K h x = M.policy z (M.pricePath z (M.initMass μ) K) (M.placeAt h x) := rfl

/-- **The root policy of the continuation below `h` is the policy at `h`.** -/
theorem rootPolicy_shift (z : Z) (μ : Measure M.AState) [IsProbabilityMeasure μ]
    (K : List Z → ℝ) (h : List Z) :
    M.rootPolicy (shockAt z h) (M.nodeDist z μ (M.pricePath z (M.initMass μ) K) h)
        (shiftPath K h)
      = M.nodePolicy z μ K h := by
  ext x
  simp only [rootPolicy, nodePolicy_apply]
  rw [M.pricePath_shift z μ K h, M.policy_shift z _ h]
  rfl

/-- The root value is jointly continuous in the initial distribution and the capital path, into
the supremum norm. -/
theorem continuous_rootValue (z : Z) :
    Continuous fun p : ProbabilityMeasure M.AState × (List Z → ℝ) =>
      M.rootValue z (p.1 : Measure M.AState) p.2 := by
  refine continuous_bcf_of_joint (G := fun p : ProbabilityMeasure M.AState × (List Z → ℝ) =>
    M.rootValue z (p.1 : Measure M.AState) p.2) ?_
  exact ((M.continuous_valueFunction_joint z).comp
    (((M.continuous_pricePath_joint z).comp continuous_fst).prodMk
      ((M.continuous_placeAt []).comp continuous_snd))).congr fun q =>
    (M.nodeValue_apply z _ _ [] q.2).symm

/-- The root policy is jointly continuous in the initial distribution and the capital path, into
the supremum norm. -/
theorem continuous_rootPolicy (z : Z) :
    Continuous fun p : ProbabilityMeasure M.AState × (List Z → ℝ) =>
      M.rootPolicy z (p.1 : Measure M.AState) p.2 := by
  refine continuous_bcf_of_joint (G := fun p : ProbabilityMeasure M.AState × (List Z → ℝ) =>
    M.rootPolicy z (p.1 : Measure M.AState) p.2) ?_
  exact ((M.continuous_policy z).comp
    (((M.continuous_pricePath_joint z).comp continuous_fst).prodMk
      ((M.continuous_placeAt []).comp continuous_snd))).congr fun q =>
    (M.nodePolicy_apply z _ _ [] q.2).symm

/-! ### States -/

/-- **A state of the economy** `(z, μ, v, a)`: aggregate shock, distribution of households, their
value function and their saving policy. -/
structure KSState where
  /-- The aggregate shock. -/
  shock : Z
  /-- The distribution of households over assets and idiosyncratic states. -/
  dist : ProbabilityMeasure M.AState
  /-- The households' value function. -/
  value : M.AState →ᵇ ℝ
  /-- The households' saving policy. -/
  policy : M.AState →ᵇ ℝ

namespace KSState

variable {M}

/-- A state as a point of the product space. -/
def toProd (ξ : M.KSState) :
    AggShock Z × ProbabilityMeasure M.AState × (M.AState →ᵇ ℝ) × (M.AState →ᵇ ℝ) :=
  (⟨ξ.shock⟩, ξ.dist, ξ.value, ξ.policy)

theorem toProd_injective : Function.Injective (toProd : M.KSState → _) := by
  rintro ⟨z, μ, v, a⟩ ⟨z', μ', v', a'⟩ h
  simp only [toProd, Prod.mk.injEq, AggShock.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

variable (M)

noncomputable instance : TopologicalSpace M.KSState :=
  TopologicalSpace.induced toProd inferInstance

variable {M}

theorem isEmbedding_toProd : Topology.IsEmbedding (toProd : M.KSState → _) :=
  ⟨⟨rfl⟩, toProd_injective⟩

variable (M)

instance : TopologicalSpace.MetrizableSpace M.KSState := isEmbedding_toProd.metrizableSpace

noncomputable instance : MeasurableSpace M.KSState := borel _

instance : BorelSpace M.KSState := ⟨rfl⟩

variable {M}

theorem continuous_toProd : Continuous (toProd : M.KSState → _) := continuous_induced_dom

theorem continuous_shock : Continuous fun ξ : M.KSState => (⟨ξ.shock⟩ : AggShock Z) :=
  continuous_fst.comp continuous_toProd

theorem continuous_dist : Continuous fun ξ : M.KSState => ξ.dist :=
  continuous_fst.comp (continuous_snd.comp continuous_toProd)

theorem continuous_value : Continuous fun ξ : M.KSState => ξ.value :=
  continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_toProd))

theorem continuous_policy : Continuous fun ξ : M.KSState => ξ.policy :=
  continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_toProd))

/-- A map into states is continuous when its four coordinates are. -/
theorem continuous_mk {X : Type*} [TopologicalSpace X] {z : X → Z} {μ : X → ProbabilityMeasure M.AState}
    {v a : X → M.AState →ᵇ ℝ} (hz : Continuous fun x => (⟨z x⟩ : AggShock Z)) (hμ : Continuous μ)
    (hv : Continuous v) (ha : Continuous a) :
    Continuous fun x => (⟨z x, μ x, v x, a x⟩ : M.KSState) :=
  continuous_induced_rng.2 (hz.prodMk (hμ.prodMk (hv.prodMk ha)))

end KSState

/-! ### The equilibrium states `J*` -/

/-- **Cao's `J*`**: the states `(z, μ, v, a)` at the root of a sequential equilibrium `K` from
`(z, μ)`, with `v` and `a` the households' value and saving there. -/
def equilibriumStates : Set M.KSState :=
  {ξ | ∃ K, M.IsSequentialEquilibrium ξ.shock (ξ.dist : Measure M.AState) K ∧
    M.rootValue ξ.shock (ξ.dist : Measure M.AState) K = ξ.value ∧
    M.rootPolicy ξ.shock (ξ.dist : Measure M.AState) K = ξ.policy}

/-- The root state of the path `K` from `(z, μ)`. -/
noncomputable def rootState (z : Z) (p : ProbabilityMeasure M.AState × (List Z → ℝ)) :
    M.KSState :=
  ⟨z, p.1, M.rootValue z (p.1 : Measure M.AState) p.2, M.rootPolicy z (p.1 : Measure M.AState) p.2⟩

theorem continuous_rootState (z : Z) : Continuous (M.rootState z) :=
  KSState.continuous_mk continuous_const continuous_fst (M.continuous_rootValue z)
    (M.continuous_rootPolicy z)

theorem equilibriumStates_eq :
    M.equilibriumStates = ⋃ z, M.rootState z '' M.equilibriumGraph z := by
  ext ξ
  constructor
  · rintro ⟨K, hK, hv, ha⟩
    refine mem_iUnion.2 ⟨ξ.shock, (ξ.dist, K), hK, ?_⟩
    obtain ⟨z, μ, v, a⟩ := ξ
    simp only at hv ha
    simp only [rootState, hv, ha]
  · intro h
    obtain ⟨z, p, hp, rfl⟩ := mem_iUnion.1 h
    exact ⟨p.2, hp, rfl, rfl⟩

/-- **`J*` is compact.** -/
theorem isCompact_equilibriumStates : IsCompact M.equilibriumStates := by
  rw [equilibriumStates_eq]
  refine isCompact_iUnion fun z => IsCompact.image ?_ (M.continuous_rootState z)
  refine (isCompact_univ.prod M.isCompact_pi).of_isClosed_subset (M.isClosed_equilibriumGraph z) ?_
  exact fun p hp => ⟨mem_univ _, M.equilibrium_mem_pi z p.1 hp⟩

/-- `J*` is nonempty. -/
theorem equilibriumStates_nonempty [Nonempty Z] [Nonempty E] : M.equilibriumStates.Nonempty := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  let μ : ProbabilityMeasure M.AState :=
    ⟨Measure.dirac (⟨0, le_rfl, M.assetCap_pos.le⟩, ⟨Classical.arbitrary E⟩), inferInstance⟩
  obtain ⟨K, -, hK⟩ := M.exists_sequentialEquilibrium z (μ : Measure M.AState)
  exact ⟨M.rootState z (μ, K), K, hK, rfl, rfl⟩

/-- **The state at node `h`** along the path `K` from `(z, μ)`. -/
noncomputable def nodeState (z : Z) (μ : ProbabilityMeasure M.AState) (K : List Z → ℝ)
    (h : List Z) : M.KSState :=
  ⟨shockAt z h,
    ⟨M.nodeDist z (μ : Measure M.AState) (M.pricePath z (M.initMass (μ : Measure M.AState)) K) h,
      M.isProbabilityMeasure_nodeDist z _ _ h⟩,
    M.nodeValue z (μ : Measure M.AState) K h, M.nodePolicy z (μ : Measure M.AState) K h⟩

/-- **States along an equilibrium are equilibrium states**: the continuation below `h` is a
sequential equilibrium with the value and policy at `h`. -/
theorem nodeState_mem (z : Z) (μ : ProbabilityMeasure M.AState) {K : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium z (μ : Measure M.AState) K) (h : List Z) :
    M.nodeState z μ K h ∈ M.equilibriumStates :=
  ⟨shiftPath K h, hK.continuation M z (μ : Measure M.AState) h,
    M.rootValue_shift z (μ : Measure M.AState) K h,
    M.rootPolicy_shift z (μ : Measure M.AState) K h⟩

end KSModel

end KrusellSmith

end LeanEconomics
