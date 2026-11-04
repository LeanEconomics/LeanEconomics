/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Distribution
import LeanEconomics.FixedPoint.SchauderTychonoff

/-!
# Existence of sequential equilibrium in a Krusell–Smith economy

A **sequential equilibrium** from an initial aggregate shock `z₀` and an initial distribution
`μ₀` of households over assets and idiosyncratic states is a path `K` of aggregate capital on the
tree of histories such that, when households face the prices `K` implies and save optimally
(`policy`), the distribution of households that results (`nodeDist`) has mean assets equal to
`K h` at every node `h`. Capital is predetermined: the assets households hold at `h` were chosen
at its parent, and the prices at `h` are those of `K h`. Aggregate labour on the tree is
exogenous, evolving from the idiosyncratic masses of `μ₀` (`initMass`).

`exists_sequentialEquilibrium`: **such a path exists**, for every initial shock and every initial
probability distribution. It is a fixed point of the map `K ↦ (h ↦ mean assets at h)`, which
sends the compact convex set of paths `capitalPaths` into itself and is continuous in the product
topology (`continuousAt_meanCapital`), so the Schauder–Tychonoff theorem applies.

The hypotheses are those of `KSModel`: finitely many aggregate and idiosyncratic states, strictly
concave utility continuous on `[0, ∞)`, a cap on assets, and bounded continuous price functions.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z) (μ₀ : Measure M.AState)

/-- The initial mass of households in each idiosyncratic state. -/
noncomputable def initMass (e : E) : ℝ := μ₀.real {x | x.2.idio = e}

/-- Aggregate capital at the root: mean assets under the initial distribution. -/
noncomputable def initCapital : ℝ := ∫ x, M.assets x ∂μ₀

/-- The path of price inputs a capital path implies: capital `K h` and the exogenous aggregate
labour of the tree started from the masses `m₀`, at every node. -/
noncomputable def pricePath (m₀ : E → ℝ) (K : List Z → ℝ) : List Z → ℝ × ℝ :=
  fun h => (K h, M.labour z₀ m₀ h)

theorem continuous_pricePath (m₀ : E → ℝ) : Continuous (M.pricePath z₀ m₀) :=
  continuous_pi fun h => (continuous_apply h).prodMk continuous_const

/-- **Sequential equilibrium**: at every node, aggregate capital is the mean assets of the
households there, when every household saves optimally against the prices the path implies. -/
def IsSequentialEquilibrium (K : List Z → ℝ) : Prop :=
  ∀ h, K h = M.meanCapital z₀ μ₀ (M.pricePath z₀ (M.initMass μ₀) K) h

/-- The equilibrium map: a path of capital to the path of mean assets it induces. -/
noncomputable def equilibriumMap (K : List Z → ℝ) : List Z → ℝ :=
  fun h => M.meanCapital z₀ μ₀ (M.pricePath z₀ (M.initMass μ₀) K) h

theorem continuous_equilibriumMap [IsProbabilityMeasure μ₀] :
    Continuous (M.equilibriumMap z₀ μ₀) :=
  continuous_pi fun h => continuous_iff_continuousAt.2 fun _ =>
    (M.continuousAt_meanCapital z₀ μ₀ _ h).comp
      (M.continuous_pricePath z₀ (M.initMass μ₀)).continuousAt

theorem mapsTo_equilibriumMap [IsProbabilityMeasure μ₀] :
    MapsTo (M.equilibriumMap z₀ μ₀) (M.capitalPaths (M.initCapital μ₀))
      (M.capitalPaths (M.initCapital μ₀)) := fun _ _ =>
  ⟨rfl, fun h => M.meanCapital_mem z₀ μ₀ _ h⟩

/-- **Existence of sequential equilibrium in a Krusell–Smith economy**, from every initial
aggregate shock and every initial probability distribution of households. -/
theorem exists_sequentialEquilibrium [IsProbabilityMeasure μ₀] :
    ∃ K ∈ M.capitalPaths (M.initCapital μ₀), M.IsSequentialEquilibrium z₀ μ₀ K := by
  have hK₀ : M.initCapital μ₀ ∈ Icc 0 M.assetCap :=
    M.meanCapital_mem z₀ μ₀ (fun _ => (0, 0)) []
  obtain ⟨K, hK, hfix⟩ := FixedPoint.schauderTychonoff (M.isCompact_capitalPaths _)
    (M.convex_capitalPaths _) (M.capitalPaths_nonempty hK₀)
    (M.continuous_equilibriumMap z₀ μ₀).continuousOn (M.mapsTo_equilibriumMap z₀ μ₀)
  exact ⟨K, hK, fun h => (congrFun hfix h).symm⟩

end KSModel

end KrusellSmith

end LeanEconomics
