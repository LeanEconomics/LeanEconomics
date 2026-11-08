/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.AntitoneEquilibrium
import LeanEconomics.KrusellSmith.CobbDouglasRedistribution

/-!
# The expectations map

Milestone B2 of the bracket route (`EXISTENCE_EXTENSIONS_PLAN.md`, item 6).

**Why not the equilibrium map.** `eqFn` prices every node at the path's own capital `K h`, while the
households there hold mean assets `Ā h`, which off equilibrium differ. With Cobb–Douglas prices
aggregate cash at the node then moves with `K h` at the rate `∝ L (K h − Ā h)`
(`CobbDouglasRedistribution.integral_cash_change`): up where the path overshoots, down where it
undershoots. That channel is not ordered, so `eqFn` cannot be order-reversing on all paths.

**The expectations map** (`expDist`, `expMap`). Households expect the future capital path `K`, but
today's prices clear at actual mean assets: at node `h` the price path is `K` with the entry at `h`
replaced by `(Ā h, L h)`. Today's aggregate cash then depends on `Ā` alone (Euler: output plus
undepreciated capital), and `K` enters only through expectations of future prices.

**Same fixed points** (`expMap_eq_iff`): a capital path is a fixed point of the expectations map iff
it is a sequential equilibrium. So the bracket theorem applies to it
(`uniqueSequentialEquilibrium_of_expMap`): if the expectations map reverses order and its square is
concave at the top of the bracket, sequential equilibrium is unique and the minimal-state recursive
equilibrium exists. Order reversal of `expMap` is the remaining content of B2.
-/

open MeasureTheory Set

namespace LeanEconomics

namespace KrusellSmith

namespace CobbDouglasRedistribution

/-- **Aggregate cash moves with capital at the rate `∝ L (K − Ā)`**: the weights `K e − L a` of the
cash change integrate to `L (K − Ā)` over a cross-section with mean assets `Ā` and mean efficiency
`L`; zero exactly when capital equals mean assets. -/
theorem integral_cash_change {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {a e : X → ℝ} (ha : Integrable a ν) (he : Integrable e ν)
    {K Abar L : ℝ} (hKa : ∫ x, a x ∂ν = Abar) (hLe : ∫ x, e x ∂ν = L) :
    ∫ x, (K * e x - L * a x) ∂ν = L * (K - Abar) := by
  rw [integral_sub (he.const_mul K) (ha.const_mul L), integral_const_mul, integral_const_mul, hKa,
    hLe]
  ring

end CobbDouglasRedistribution

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- Mean assets of a probability measure lie in `[0, ā]`. -/
theorem integral_assets_mem (ν : Measure M.AState) [IsProbabilityMeasure ν] :
    ∫ x, M.assets x ∂ν ∈ Icc 0 M.assetCap := by
  constructor
  · exact integral_nonneg fun x => x.1.2.1
  · calc ∫ x, M.assets x ∂ν ≤ ∫ _x, M.assetCap ∂ν :=
          integral_mono (M.assets.integrable ν) (integrable_const _) fun x => x.1.2.2
      _ = M.assetCap := by simp

variable (z₀ : Z) (μ₀ : Measure M.AState) (K : List Z → ℝ)

open Classical in
/-- **Distributions under expectations `K`**: at every node households expect the path `K` for the
future, while today's prices clear at the node's actual mean assets. -/
noncomputable def expDist : List Z → Measure M.AState
  | [] => μ₀
  | z' :: h => M.pushNode z₀ (Function.update (M.pricePath z₀ (M.initMass μ₀) K) h
      (∫ x, M.assets x ∂(expDist h), M.labour z₀ (M.initMass μ₀) h)) h z' (expDist h)

theorem isProbabilityMeasure_expDist [IsProbabilityMeasure μ₀] :
    ∀ h, IsProbabilityMeasure (M.expDist z₀ μ₀ K h)
  | [] => ‹_›
  | z' :: h => by
    have := isProbabilityMeasure_expDist h
    exact M.isProbabilityMeasure_pushNode _ _ _ _ _

open Classical in
/-- Where mean assets match the path, the expectations distributions are the equilibrium-map
distributions. -/
theorem expDist_eq_nodeDist (hK : ∀ h, M.expDist z₀ μ₀ K h = M.nodeDist z₀ μ₀
      (M.pricePath z₀ (M.initMass μ₀) K) h → ∫ x, M.assets x ∂(M.expDist z₀ μ₀ K h) = K h) :
    ∀ h, M.expDist z₀ μ₀ K h = M.nodeDist z₀ μ₀ (M.pricePath z₀ (M.initMass μ₀) K) h
  | [] => rfl
  | z' :: h => by
    have ih := expDist_eq_nodeDist hK h
    have hm := hK h ih
    have hp : (K h, M.labour z₀ (M.initMass μ₀) h) = M.pricePath z₀ (M.initMass μ₀) K h := rfl
    change M.pushNode z₀ (Function.update (M.pricePath z₀ (M.initMass μ₀) K) h
        (∫ x, M.assets x ∂(M.expDist z₀ μ₀ K h), M.labour z₀ (M.initMass μ₀) h)) h z'
        (M.expDist z₀ μ₀ K h)
      = M.pushNode z₀ (M.pricePath z₀ (M.initMass μ₀) K) h z'
        (M.nodeDist z₀ μ₀ (M.pricePath z₀ (M.initMass μ₀) K) h)
    rw [hm, hp, Function.update_eq_self, ih]

variable {M}

/-- **The expectations map** on capital paths in `[0, ā]`: expected path to realised mean assets. -/
noncomputable def expMap (z : Z) (μ : ProbabilityMeasure M.AState) (K : M.CapPath) : M.CapPath :=
  fun h => ⟨∫ x, M.assets x ∂(M.expDist z (μ : Measure M.AState) (fun g => (K g : ℝ)) h),
    haveI := M.isProbabilityMeasure_expDist z (μ : Measure M.AState) (fun g => (K g : ℝ)) h
    M.integral_assets_mem _⟩

/-- **The expectations map has the sequential equilibria as its fixed points.** -/
theorem expMap_eq_iff (z : Z) (μ : ProbabilityMeasure M.AState) {K : List Z → ℝ}
    (hK : ∀ h, K h ∈ Icc 0 M.assetCap) :
    expMap z μ (fun h => ⟨K h, hK h⟩) = (fun h => ⟨K h, hK h⟩)
      ↔ M.IsSequentialEquilibrium z (μ : Measure M.AState) K := by
  constructor
  · intro hfix h
    have hm : ∀ g, ∫ x, M.assets x ∂(M.expDist z (μ : Measure M.AState) K g) = K g := fun g =>
      congrArg Subtype.val (congrFun hfix g)
    have he := M.expDist_eq_nodeDist z (μ : Measure M.AState) K (fun g _ => hm g)
    rw [← hm h, he h]
    rfl
  · intro hE
    have he : ∀ g, M.expDist z (μ : Measure M.AState) K g
        = M.nodeDist z (μ : Measure M.AState) (M.pricePath z (M.initMass (μ : Measure M.AState)) K)
          g :=
      M.expDist_eq_nodeDist z (μ : Measure M.AState) K fun g hg => by
        rw [hg]
        exact (hE g).symm
    funext h
    refine Subtype.ext ?_
    change ∫ x, M.assets x ∂(M.expDist z (μ : Measure M.AState) K h) = K h
    rw [he h]
    exact (hE h).symm

variable (M) in
/-- **The expectations map reverses order** (the content of milestone B2, open). -/
def ExpMapAntitone : Prop :=
  ∀ (z : Z) (μ : ProbabilityMeasure M.AState), Antitone (expMap (M := M) z μ)

/-- **Uniqueness and the minimal state from the expectations map**: if it reverses order and its
square is concave at the top of the bracket, sequential equilibrium is unique. -/
theorem uniqueSequentialEquilibrium_of_expMap (hA : M.ExpMapAntitone)
    (hC : M.SqConcaveAtTop (Φ := expMap) hA) : M.UniqueSequentialEquilibrium :=
  uniqueSequentialEquilibrium_of_antitoneMap hA
    (fun z μ _ hK => (expMap_eq_iff z μ _).2 hK) hC

end KSModel

end KrusellSmith

end LeanEconomics
