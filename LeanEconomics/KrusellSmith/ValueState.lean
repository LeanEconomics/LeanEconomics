/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Recursive

/-!
# Recursive equilibrium with the value function as a state variable: the extended state

Milestone V1 of `VALUESTATE_PLAN.md`. Without uniqueness of sequential equilibrium, the aggregate
shock and the distribution of households need not determine the future (Kubler–Schmedders 2002).
Following Cao (2020, Proposition 3) and Miao (2006), we add the households' **current value
function** to the state.

* `nodeValue z μ K h`: the household's value at node `h` along the path `K`, as a function of
  assets and idiosyncratic state; `rootValue` is the value at the root.
* `rootValue_shift`: the root value of the continuation below `h` is the value at `h`.
* `ExtState`: the **extended states** `(z, μ, v)` for which some sequential equilibrium from
  `(z, μ)` gives households the value `v` (Cao's set `J`). Every `(z, μ)` extends
  (`ExtState.extend`).
* `ExtState.path`: a sequential equilibrium witnessing an extended state, chosen once and for all;
  no measurability is asked.
* `ExtState.next ξ z'`: **the next state** when the aggregate shock moves to `z'`: the distribution
  and the value at the child `[z']` along the chosen path. It is again an extended state, by the
  continuation theorem (`IsSequentialEquilibrium.continuation`) and `rootValue_shift`. The
  continuation actually chosen at the next state may be a different equilibrium; it gives
  households the same value, which is all their decision today depends on (milestone V3).
* `ExtState.value_eq_rootValue_eqPath`: under uniqueness of sequential equilibrium the value is a
  function of `(z, μ)`, and the extended state collapses to the minimal one of `Recursive.lean`.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-! ### Values at a node -/

/-- A household at `x` placed at node `h`. -/
def placeAt (h : List Z) (x : M.AState) : M.State := (x.1, ⟨x.2.idio, h⟩)

theorem continuous_placeAt (h : List Z) : Continuous (M.placeAt h) :=
  continuous_fst.prodMk ((continuous_of_discreteTopology
    (f := fun i : Idio E => (⟨i.idio, h⟩ : Label Z E))).comp continuous_snd)

/-- Placing households at node `h`, as a continuous map. -/
def placeAtMap (h : List Z) : C(M.AState, M.State) := ⟨M.placeAt h, M.continuous_placeAt h⟩

/-- **The households' value at node `h`** along the path of capital `K` from `(z, μ)`, as a
function of assets and idiosyncratic state. -/
noncomputable def nodeValue (z : Z) (μ : Measure M.AState) (K : List Z → ℝ) (h : List Z) :
    M.AState →ᵇ ℝ :=
  ((M.household z (M.pricePath z (M.initMass μ) K)).valueFunction).compContinuous
    (M.placeAtMap h)

/-- **The households' value at the root** along the path of capital `K` from `(z, μ)`. -/
noncomputable def rootValue (z : Z) (μ : Measure M.AState) (K : List Z → ℝ) : M.AState →ᵇ ℝ :=
  M.nodeValue z μ K []

theorem nodeValue_apply (z : Z) (μ : Measure M.AState) (K : List Z → ℝ) (h : List Z)
    (x : M.AState) :
    M.nodeValue z μ K h x
      = (M.household z (M.pricePath z (M.initMass μ) K)).valueFunction (x.1, ⟨x.2.idio, h⟩) :=
  rfl

/-- **The root value of the continuation below `h` is the value at `h`.** -/
theorem rootValue_shift (z : Z) (μ : Measure M.AState) [IsProbabilityMeasure μ]
    (K : List Z → ℝ) (h : List Z) :
    M.rootValue (shockAt z h) (M.nodeDist z μ (M.pricePath z (M.initMass μ) K) h)
        (shiftPath K h)
      = M.nodeValue z μ K h := by
  ext x
  simp only [rootValue, nodeValue, compContinuous_apply]
  rw [M.pricePath_shift z μ K h, M.valueFunction_shift z _ h, compContinuous_apply]
  rfl

/-! ### The extended state -/

/-- **An extended state** `(z, μ, v)`: an aggregate shock, a distribution of households, and a
value function such that some sequential equilibrium from `(z, μ)` gives households the value `v`.
-/
structure ExtState where
  /-- The aggregate shock. -/
  shock : Z
  /-- The distribution of households over assets and idiosyncratic states. -/
  dist : ProbabilityMeasure M.AState
  /-- The households' value function. -/
  value : M.AState →ᵇ ℝ
  exists_path : ∃ K, M.IsSequentialEquilibrium shock (dist : Measure M.AState) K ∧
    M.rootValue shock (dist : Measure M.AState) K = value

namespace ExtState

variable {M}

/-- **A sequential equilibrium witnessing the extended state**, chosen once and for all. -/
noncomputable def path (ξ : M.ExtState) : List Z → ℝ := ξ.exists_path.choose

theorem path_spec (ξ : M.ExtState) :
    M.IsSequentialEquilibrium ξ.shock (ξ.dist : Measure M.AState) ξ.path :=
  ξ.exists_path.choose_spec.1

theorem rootValue_path (ξ : M.ExtState) :
    M.rootValue ξ.shock (ξ.dist : Measure M.AState) ξ.path = ξ.value :=
  ξ.exists_path.choose_spec.2

/-- Prices along the chosen path. -/
noncomputable def prices (ξ : M.ExtState) : List Z → ℝ × ℝ :=
  M.pricePath ξ.shock (M.initMass (ξ.dist : Measure M.AState)) ξ.path

/-- **The saving policy** at the extended state: saving at the root along the chosen path. -/
noncomputable def policy (ξ : M.ExtState) (x : M.AState) : ℝ :=
  M.policy ξ.shock ξ.prices (M.placeAt [] x)

/-- **Capital at the extended state is mean assets of its distribution**, whichever equilibrium
was chosen: prices at the extended state depend on `(z, μ)` alone. -/
theorem path_nil (ξ : M.ExtState) : ξ.path [] = ∫ x, M.assets x ∂(ξ.dist : Measure M.AState) :=
  ξ.path_spec []

variable (M)

/-- **Every shock and distribution extend to an extended state.** -/
noncomputable def extend (z : Z) (μ : ProbabilityMeasure M.AState) : M.ExtState where
  shock := z
  dist := μ
  value := M.rootValue z (μ : Measure M.AState) (M.eqPath z μ)
  exists_path := ⟨M.eqPath z μ, M.eqPath_spec z μ, rfl⟩

variable {M}

/-- The distribution at the child `[z']` along the chosen path. -/
noncomputable def nextDist (ξ : M.ExtState) (z' : Z) : ProbabilityMeasure M.AState :=
  ⟨M.nodeDist ξ.shock (ξ.dist : Measure M.AState) ξ.prices [z'],
    M.isProbabilityMeasure_nodeDist ξ.shock _ _ [z']⟩

/-- **The next extended state** when the aggregate shock moves to `z'`: the distribution and the
households' value at the child `[z']` along the chosen path. -/
noncomputable def next (ξ : M.ExtState) (z' : Z) : M.ExtState where
  shock := z'
  dist := ξ.nextDist z'
  value := M.nodeValue ξ.shock (ξ.dist : Measure M.AState) ξ.path [z']
  exists_path := ⟨shiftPath ξ.path [z'],
    ξ.path_spec.continuation M ξ.shock (ξ.dist : Measure M.AState) [z'],
    M.rootValue_shift ξ.shock (ξ.dist : Measure M.AState) ξ.path [z']⟩

@[simp] theorem next_shock (ξ : M.ExtState) (z' : Z) : (ξ.next z').shock = z' := rfl

theorem next_dist (ξ : M.ExtState) (z' : Z) :
    ((ξ.next z').dist : Measure M.AState)
      = M.nodeDist ξ.shock (ξ.dist : Measure M.AState) ξ.prices [z'] := rfl

theorem next_value_apply (ξ : M.ExtState) (z' : Z) (x : M.AState) :
    (ξ.next z').value x
      = (M.household ξ.shock ξ.prices).valueFunction (x.1, ⟨x.2.idio, [z']⟩) := rfl

/-- **Under uniqueness the value is a function of `(z, μ)`**: the extended state collapses to the
minimal state of `Recursive.lean`. -/
theorem value_eq_rootValue_eqPath (hU : M.UniqueSequentialEquilibrium) (ξ : M.ExtState) :
    ξ.value = M.rootValue ξ.shock (ξ.dist : Measure M.AState) (M.eqPath ξ.shock ξ.dist) := by
  rw [← ξ.rootValue_path, hU.eq_eqPath ξ.path_spec]

end ExtState

end KSModel

end KrusellSmith

end LeanEconomics
