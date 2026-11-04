/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Labour
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The equilibrium correspondence has a closed graph in the initial distribution

`exists_sequentialEquilibrium` gives, for every initial distribution `μ₀`, a sequential equilibrium
path of capital. This module shows that the set of all pairs `(μ₀, K)` with `K` a sequential
equilibrium from `μ₀` is **closed**, for the weak topology on initial distributions
(`ProbabilityMeasure`) and the product topology on paths (`isClosed_equilibriumGraph`).
Equilibrium paths also lie in the compact set `[0, assetCap]^nodes`
(`equilibrium_mem_pi`), so the equilibrium correspondence is a closed-graph correspondence into a
compact set: if equilibrium is unique, the equilibrium path is a continuous function of the
initial distribution (the step from sequential to recursive equilibrium).

The initial distribution enters in two places, and both are continuous:

* at the root of the tree of distributions. Node distributions are **jointly** weakly continuous in
  the initial distribution and the path of capital and labour
  (`continuousAt_integral_nodeDist_joint`), by the induction of
  `continuousAt_integral_nodeDist` with the initial distribution entering at the root;
* through labour on the tree, which starts from the idiosyncratic masses of `μ₀`. These are
  integrals of the bounded continuous indicators of idiosyncratic states, hence weakly continuous
  (`continuous_initMass`), and labour is linear in them (`continuous_labour`).
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory Metric

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z)

/-! ### Labour is continuous in the initial distribution -/

theorem continuous_stateMass : ∀ (h : List Z) (e : E),
    Continuous fun m₀ : E → ℝ => M.stateMass z₀ m₀ h e
  | [], e => continuous_apply e
  | z' :: h, e' => by
    simp only [stateMass]
    exact continuous_finsetSum _ fun e _ => (continuous_stateMass h e).mul continuous_const

theorem continuous_labour (h : List Z) : Continuous fun m₀ : E → ℝ => M.labour z₀ m₀ h :=
  continuous_finsetSum _ fun e _ => (M.continuous_stateMass z₀ h e).mul continuous_const

theorem continuous_initMass :
    Continuous fun μ : ProbabilityMeasure M.AState => M.initMass (μ : Measure M.AState) := by
  refine continuous_pi fun e => ?_
  have heq : (fun μ : ProbabilityMeasure M.AState => M.initMass (μ : Measure M.AState) e)
      = fun μ : ProbabilityMeasure M.AState => ∫ x, M.idioInd e x ∂(μ : Measure M.AState) :=
    funext fun μ => (M.integral_idioInd _ e).symm
  rw [heq]
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction _

/-- The price path is jointly continuous in the initial distribution and the capital path. -/
theorem continuous_pricePath_joint :
    Continuous fun p : ProbabilityMeasure M.AState × (List Z → ℝ) =>
      M.pricePath z₀ (M.initMass (p.1 : Measure M.AState)) p.2 :=
  continuous_pi fun h => ((continuous_apply h).comp continuous_snd).prodMk
    ((M.continuous_labour z₀ h).comp ((M.continuous_initMass).comp continuous_fst))

/-! ### Node distributions are jointly continuous -/

/-- Uniformly over states, the expected next value moves little when the path moves little. -/
theorem eventually_expectedNext (h : List Z) (z' : Z) (f : M.AState →ᵇ ℝ)
    (K₀ : List Z → ℝ × ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K in 𝓝 K₀, ∀ x : M.AState,
      dist (M.expectedNext z₀ K h z' f x) (M.expectedNext z₀ K₀ h z' f x) < ε := by
  have hfc : ContinuousOn (Function.uncurry fun (K : List Z → ℝ × ℝ) (x : M.AState) =>
      M.expectedNext z₀ K h z' f x) (univ ×ˢ univ) :=
    (M.continuous_expectedNext_joint z₀ h z' f).continuousOn
  obtain ⟨w, hw, hwf⟩ := isCompact_univ.mem_uniformity_of_prod hfc (mem_univ K₀)
    (dist_mem_uniformity hε)
  rw [nhdsWithin_univ] at hw
  filter_upwards [hw] with K hK x
  exact hwf K hK x (mem_univ x)

/-- **The distribution at every node is jointly weakly continuous** in the initial distribution
(weak topology) and the path of capital and labour (product topology). -/
theorem continuousAt_integral_nodeDist_joint
    (p₀ : ProbabilityMeasure M.AState × (List Z → ℝ × ℝ)) :
    ∀ (h : List Z) (f : M.AState →ᵇ ℝ),
      ContinuousAt (fun p : ProbabilityMeasure M.AState × (List Z → ℝ × ℝ) =>
        ∫ x, f x ∂(M.nodeDist z₀ (p.1 : Measure M.AState) p.2 h)) p₀
  | [], f => by
    change ContinuousAt (fun p : ProbabilityMeasure M.AState × (List Z → ℝ × ℝ) =>
      ∫ x, f x ∂(p.1 : Measure M.AState)) p₀
    exact ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp
      continuous_fst).continuousAt
  | z' :: h, f => by
    have hdual : ∀ p : ProbabilityMeasure M.AState × (List Z → ℝ × ℝ),
        ∫ x, f x ∂(M.nodeDist z₀ (p.1 : Measure M.AState) p.2 (z' :: h))
          = ∫ x, M.expectedNext z₀ p.2 h z' f x
              ∂(M.nodeDist z₀ (p.1 : Measure M.AState) p.2 h) := by
      intro p
      have := M.isProbabilityMeasure_nodeDist z₀ (p.1 : Measure M.AState) p.2 h
      exact M.integral_pushNode z₀ p.2 h z' _ f
    simp only [hdual]
    have IH := continuousAt_integral_nodeDist_joint p₀ h (M.expectedNext z₀ p₀.2 h z' f)
    rw [Metric.continuousAt_iff'] at IH ⊢
    intro ε hε
    have hunif : ∀ᶠ p in 𝓝 p₀, ∀ x : M.AState,
        dist (M.expectedNext z₀ p.2 h z' f x) (M.expectedNext z₀ p₀.2 h z' f x) < ε / 2 :=
      (continuous_snd.tendsto p₀).eventually
        (M.eventually_expectedNext z₀ h z' f p₀.2 (half_pos hε))
    filter_upwards [hunif, IH (ε / 2) (half_pos hε)] with p hK hK'
    have := M.isProbabilityMeasure_nodeDist z₀ (p.1 : Measure M.AState) p.2 h
    have hsplit : ∫ x, M.expectedNext z₀ p.2 h z' f x
            ∂(M.nodeDist z₀ (p.1 : Measure M.AState) p.2 h)
          - ∫ x, M.expectedNext z₀ p₀.2 h z' f x ∂(M.nodeDist z₀ (p.1 : Measure M.AState) p.2 h)
        = ∫ x, (M.expectedNext z₀ p.2 h z' f x - M.expectedNext z₀ p₀.2 h z' f x)
            ∂(M.nodeDist z₀ (p.1 : Measure M.AState) p.2 h) :=
      (integral_sub ((M.expectedNext z₀ p.2 h z' f).integrable _)
        ((M.expectedNext z₀ p₀.2 h z' f).integrable _)).symm
    have h1 : ‖∫ x, (M.expectedNext z₀ p.2 h z' f x - M.expectedNext z₀ p₀.2 h z' f x)
        ∂(M.nodeDist z₀ (p.1 : Measure M.AState) p.2 h)‖ ≤ ε / 2 := by
      have := norm_integral_le_of_norm_le_const
        (μ := M.nodeDist z₀ (p.1 : Measure M.AState) p.2 h)
        (f := fun x => M.expectedNext z₀ p.2 h z' f x - M.expectedNext z₀ p₀.2 h z' f x)
        (C := ε / 2) (Filter.Eventually.of_forall fun x => by
          rw [← dist_eq_norm]
          exact (hK x).le)
      rwa [probReal_univ, mul_one] at this
    rw [dist_eq_norm] at hK' ⊢
    calc ‖∫ x, M.expectedNext z₀ p.2 h z' f x ∂(M.nodeDist z₀ (p.1 : Measure M.AState) p.2 h)
          - ∫ x, M.expectedNext z₀ p₀.2 h z' f x
              ∂(M.nodeDist z₀ (p₀.1 : Measure M.AState) p₀.2 h)‖
        ≤ ‖∫ x, M.expectedNext z₀ p.2 h z' f x ∂(M.nodeDist z₀ (p.1 : Measure M.AState) p.2 h)
            - ∫ x, M.expectedNext z₀ p₀.2 h z' f x
                ∂(M.nodeDist z₀ (p.1 : Measure M.AState) p.2 h)‖
          + ‖∫ x, M.expectedNext z₀ p₀.2 h z' f x
                ∂(M.nodeDist z₀ (p.1 : Measure M.AState) p.2 h)
            - ∫ x, M.expectedNext z₀ p₀.2 h z' f x
                ∂(M.nodeDist z₀ (p₀.1 : Measure M.AState) p₀.2 h)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := by rw [hsplit]; exact add_lt_add_of_le_of_lt h1 hK'
      _ = ε := add_halves ε

/-- Mean capital at a node, along the price path of a capital path, is jointly continuous in the
initial distribution and the capital path. -/
theorem continuous_meanCapital_joint (h : List Z) :
    Continuous fun p : ProbabilityMeasure M.AState × (List Z → ℝ) =>
      M.meanCapital z₀ (p.1 : Measure M.AState)
        (M.pricePath z₀ (M.initMass (p.1 : Measure M.AState)) p.2) h := by
  have hq : Continuous fun p : ProbabilityMeasure M.AState × (List Z → ℝ) =>
      (p.1, M.pricePath z₀ (M.initMass (p.1 : Measure M.AState)) p.2) :=
    continuous_fst.prodMk (M.continuous_pricePath_joint z₀)
  refine continuous_iff_continuousAt.2 fun p => ?_
  exact (M.continuousAt_integral_nodeDist_joint z₀ _ h M.assets).comp hq.continuousAt

/-! ### The closed graph -/

/-- The graph of the equilibrium correspondence: initial distributions paired with the
sequential equilibrium paths from them. -/
def equilibriumGraph : Set (ProbabilityMeasure M.AState × (List Z → ℝ)) :=
  {p | M.IsSequentialEquilibrium z₀ (p.1 : Measure M.AState) p.2}

/-- **The equilibrium correspondence has a closed graph**, for the weak topology on initial
distributions and the product topology on capital paths. -/
theorem isClosed_equilibriumGraph : IsClosed (M.equilibriumGraph z₀) := by
  have heq : M.equilibriumGraph z₀ = ⋂ h, {p : ProbabilityMeasure M.AState × (List Z → ℝ) |
      p.2 h = M.meanCapital z₀ (p.1 : Measure M.AState)
        (M.pricePath z₀ (M.initMass (p.1 : Measure M.AState)) p.2) h} := by
    ext p
    simp [equilibriumGraph, IsSequentialEquilibrium]
  rw [heq]
  exact isClosed_iInter fun h =>
    isClosed_eq ((continuous_apply h).comp continuous_snd) (M.continuous_meanCapital_joint z₀ h)

/-- **Equilibrium paths lie in a compact set**, the same for every initial distribution. -/
theorem equilibrium_mem_pi (μ₀ : ProbabilityMeasure M.AState) {K : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium z₀ (μ₀ : Measure M.AState) K) :
    K ∈ univ.pi fun _ : List Z => Icc 0 M.assetCap := fun h _ => by
  rw [hK h]
  exact M.meanCapital_mem z₀ _ _ h

theorem isCompact_pi : IsCompact (univ.pi fun _ : List Z => Icc (0 : ℝ) M.assetCap) :=
  isCompact_univ_pi fun _ => isCompact_Icc

end KSModel

end KrusellSmith

end LeanEconomics
