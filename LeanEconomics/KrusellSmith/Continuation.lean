/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ClosedGraph

/-!
# The continuation of a sequential equilibrium is a sequential equilibrium

A sequential equilibrium from `(z₀, μ₀)` is a path of capital on the whole tree of histories.
Restricted to the subtree below a node `h`, and re-indexed so that `h` becomes the root
(`shiftPath K h g = K (g ++ h)`), it is a sequential equilibrium from the shock at `h` and the
distribution of households at `h` (`IsSequentialEquilibrium.continuation`). This is the recursive
structure of sequential equilibria: what happens from `h` on depends on the past only through the
state `(z_h, μ_h)`.

The proof re-roots each layer of the construction:

* shocks and labour: `shockAt_append`, `stateMass_append`, and the masses of `μ_h` are those of
  the recursion at `h` (`real_nodeDist_idio`);
* the household: the Bellman operator commutes with the shift of nodes (`bellman_shift`), so the
  shifted value function is the value function along the shifted path (`valueFunction_shift`),
  and by uniqueness of the optimal saving so is the policy (`policy_shift`);
* distributions: by induction on the subtree, the distributions along the shifted path are those
  of the original path (`nodeDist_shift`), hence so is mean capital.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

/-- The path below node `h`, re-indexed with `h` as the root. -/
def shiftPath {Z α : Type*} (K : List Z → α) (h : List Z) : List Z → α := fun g => K (g ++ h)

@[simp] theorem shiftPath_apply {Z α : Type*} (K : List Z → α) (h g : List Z) :
    shiftPath K h g = K (g ++ h) := rfl

theorem shockAt_append {Z : Type*} (z₀ : Z) (g h : List Z) :
    shockAt (shockAt z₀ h) g = shockAt z₀ (g ++ h) := by
  cases g <;> rfl

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z)

/-! ### Labour re-rooted -/

theorem stateMass_append (m₀ : E → ℝ) (h : List Z) :
    ∀ (g : List Z) (e : E),
      M.stateMass (shockAt z₀ h) (M.stateMass z₀ m₀ h) g e = M.stateMass z₀ m₀ (g ++ h) e
  | [], _ => rfl
  | z' :: g, e' => by
    simp only [stateMass, List.cons_append]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [stateMass_append m₀ h g e, shockAt_append]

theorem labour_append (m₀ : E → ℝ) (h g : List Z) :
    M.labour (shockAt z₀ h) (M.stateMass z₀ m₀ h) g = M.labour z₀ m₀ (g ++ h) := by
  simp only [labour, M.stateMass_append z₀ m₀ h g]

/-! ### The household re-rooted -/

variable (K : List Z → ℝ × ℝ) (h : List Z)

/-- Moving a state down to the subtree below `h`. -/
def shiftState (s : M.State) : M.State := (s.1, ⟨s.2.idio, s.2.node ++ h⟩)

theorem continuous_shiftState : Continuous (M.shiftState h) :=
  continuous_fst.prodMk ((continuous_of_discreteTopology
    (f := fun l : Label Z E => (⟨l.idio, l.node ++ h⟩ : Label Z E))).comp continuous_snd)

/-- The shift of states, as a continuous map. -/
def shiftMap : C(M.State, M.State) := ⟨M.shiftState h, M.continuous_shiftState h⟩

theorem cash_shift (s : M.State) :
    M.cash (shockAt z₀ h) (shiftPath K h) s = M.cash z₀ K (M.shiftState h s) := by
  simp only [cash, returnAt, wageAt, shiftPath_apply, shiftState, shockAt_append]

theorem feasible_shift (s : M.State) :
    (M.household (shockAt z₀ h) (shiftPath K h)).feasible s
      = (M.household z₀ K).feasible (M.shiftState h s) := by
  change Icc 0 (M.maxSaving _ _ s) = Icc 0 (M.maxSaving _ _ _)
  simp only [maxSaving, M.cash_shift z₀ K h s]

theorem objective_shift (v : M.State →ᵇ ℝ) (s : M.State) (a : ℝ) :
    (M.household (shockAt z₀ h) (shiftPath K h)).objective (v.compContinuous (M.shiftMap h)) s a
      = (M.household z₀ K).objective v (M.shiftState h s) a := by
  simp only [StochasticDynamicProgram.objective, StochasticDynamicProgram.expectation]
  congr 1
  · change M.utility (M.clampedConsumption _ _ (s, a))
      = M.utility (M.clampedConsumption _ _ (M.shiftState h s, a))
    simp only [clampedConsumption, M.cash_shift z₀ K h s]
  · congr 1
    refine Finset.sum_congr rfl fun ze _ => ?_
    change M.aggProb (shockAt (shockAt z₀ h) s.2.node) ze.1
        * M.idioProb (shockAt (shockAt z₀ h) s.2.node) ze.1 s.2.idio ze.2 * _
      = M.aggProb (shockAt z₀ (s.2.node ++ h)) ze.1
        * M.idioProb (shockAt z₀ (s.2.node ++ h)) ze.1 s.2.idio ze.2 * _
    rw [shockAt_append]
    rfl

/-- **The Bellman operator commutes with re-rooting.** -/
theorem bellman_shift (v : M.State →ᵇ ℝ) :
    (M.household (shockAt z₀ h) (shiftPath K h)).bellman (v.compContinuous (M.shiftMap h))
      = ((M.household z₀ K).bellman v).compContinuous (M.shiftMap h) := by
  ext s
  simp only [StochasticDynamicProgram.bellman_apply, compContinuous_apply, maxValue]
  rw [M.feasible_shift z₀ K h s]
  congr 1
  exact Set.image_congr fun a _ => M.objective_shift z₀ K h v s a

/-- **The value function re-rooted at `h`** is the value function along the shifted path. -/
theorem valueFunction_shift :
    (M.household (shockAt z₀ h) (shiftPath K h)).valueFunction
      = ((M.household z₀ K).valueFunction).compContinuous (M.shiftMap h) := by
  symm
  refine (M.household (shockAt z₀ h) (shiftPath K h)).eq_valueFunction ?_
  rw [M.bellman_shift z₀ K h, (M.household z₀ K).bellman_valueFunction]

/-- **The policy re-rooted at `h`** is the policy along the shifted path. -/
theorem policy_shift (s : M.State) :
    M.policy (shockAt z₀ h) (shiftPath K h) s = M.policy z₀ K (M.shiftState h s) := by
  have hmem := M.policy_mem z₀ K (M.shiftState h s)
  rw [← M.feasible_shift z₀ K h s] at hmem
  refine (M.optimal_saving_unique (shockAt z₀ h) (shiftPath K h)
    (M.policy_mem (shockAt z₀ h) (shiftPath K h) s) hmem ?_ ?_)
  · exact (M.policy_optimal (shockAt z₀ h) (shiftPath K h) s).symm
  · rw [M.valueFunction_shift z₀ K h, M.objective_shift z₀ K h]
    change _ = (M.household (shockAt z₀ h) (shiftPath K h)).bellman _ s
    rw [M.bellman_shift z₀ K h, compContinuous_apply]
    change _ = (M.household z₀ K).bellman _ (M.shiftState h s)
    rw [M.policy_optimal z₀ K (M.shiftState h s)]

/-! ### Distributions re-rooted -/

theorem nextA_shift (g : List Z) (e' : E) (x : M.AState) :
    M.nextA (shockAt z₀ h) (shiftPath K h) g e' x = M.nextA z₀ K (g ++ h) e' x := by
  simp only [nextA]
  rw [M.policy_shift z₀ K h]
  rfl

theorem nextProb_shift (g : List Z) (z' : Z) (e' : E) (x : M.AState) :
    M.nextProb (shockAt z₀ h) g z' e' x = M.nextProb z₀ (g ++ h) z' e' x := by
  simp only [nextProb, shockAt_append]

theorem pushNode_shift (g : List Z) (z' : Z) (μ : Measure M.AState) :
    M.pushNode (shockAt z₀ h) (shiftPath K h) g z' μ = M.pushNode z₀ K (g ++ h) z' μ := by
  have hd : M.dens (shockAt z₀ h) g z' = M.dens z₀ (g ++ h) z' := by
    funext e' x
    simp only [dens, M.nextProb_shift z₀ h g z' e' x]
  have hn : M.nextA (shockAt z₀ h) (shiftPath K h) g = M.nextA z₀ K (g ++ h) := by
    funext e' x
    exact M.nextA_shift z₀ K h g e' x
  simp only [pushNode, hd, hn]

/-- **The distributions re-rooted at `h`** are the distributions on the subtree below `h`. -/
theorem nodeDist_shift (μ₀ : Measure M.AState) :
    ∀ g : List Z, M.nodeDist (shockAt z₀ h) (M.nodeDist z₀ μ₀ K h) (shiftPath K h) g
      = M.nodeDist z₀ μ₀ K (g ++ h)
  | [] => rfl
  | z' :: g => by
    change M.pushNode (shockAt z₀ h) (shiftPath K h) g z'
        (M.nodeDist (shockAt z₀ h) (M.nodeDist z₀ μ₀ K h) (shiftPath K h) g)
      = M.pushNode z₀ K (g ++ h) z' (M.nodeDist z₀ μ₀ K (g ++ h))
    rw [nodeDist_shift μ₀ g, M.pushNode_shift z₀ K h]

theorem meanCapital_shift (μ₀ : Measure M.AState) (g : List Z) :
    M.meanCapital (shockAt z₀ h) (M.nodeDist z₀ μ₀ K h) (shiftPath K h) g
      = M.meanCapital z₀ μ₀ K (g ++ h) := by
  simp only [meanCapital, M.nodeDist_shift z₀ K h μ₀ g]

/-! ### The continuation -/

/-- The masses of the distribution at `h` are those of the labour recursion at `h`. -/
theorem initMass_nodeDist (μ₀ : Measure M.AState) [IsProbabilityMeasure μ₀]
    (K : List Z → ℝ × ℝ) (h : List Z) :
    M.initMass (M.nodeDist z₀ μ₀ K h) = M.stateMass z₀ (M.initMass μ₀) h := by
  funext e
  exact M.real_nodeDist_idio z₀ μ₀ K h e

/-- Re-rooting the price path of a capital path is the price path of the re-rooted capital path,
started from the distribution at `h`. -/
theorem pricePath_shift (μ₀ : Measure M.AState) [IsProbabilityMeasure μ₀] (K : List Z → ℝ)
    (h : List Z) :
    M.pricePath (shockAt z₀ h)
        (M.initMass (M.nodeDist z₀ μ₀ (M.pricePath z₀ (M.initMass μ₀) K) h)) (shiftPath K h)
      = shiftPath (M.pricePath z₀ (M.initMass μ₀) K) h := by
  funext g
  simp only [pricePath, shiftPath_apply, M.initMass_nodeDist z₀ μ₀, M.labour_append]

/-- **The continuation of a sequential equilibrium is a sequential equilibrium.** If `K` is a
sequential equilibrium from `(z₀, μ₀)`, then for every node `h` the path below `h`, re-rooted at
`h`, is a sequential equilibrium from the shock at `h` and the distribution of households at
`h`. -/
theorem IsSequentialEquilibrium.continuation (μ₀ : Measure M.AState) [IsProbabilityMeasure μ₀]
    {K : List Z → ℝ} (hK : M.IsSequentialEquilibrium z₀ μ₀ K) (h : List Z) :
    M.IsSequentialEquilibrium (shockAt z₀ h)
      (M.nodeDist z₀ μ₀ (M.pricePath z₀ (M.initMass μ₀) K) h) (shiftPath K h) := by
  intro g
  rw [M.pricePath_shift z₀ μ₀ K h, M.meanCapital_shift z₀ _ h μ₀ g, shiftPath_apply]
  exact hK (g ++ h)

end KSModel

end KrusellSmith

end LeanEconomics
