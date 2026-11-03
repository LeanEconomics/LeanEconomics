/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Policy
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# The distribution of households along the tree, and its mean

Along a path `K` of aggregate capital, households start from a probability measure `μ₀` over
assets and idiosyncratic states and save by the policy `policy K`. At each node `h` of the tree
of histories this gives a distribution `nodeDist μ₀ K h` over assets and idiosyncratic states:
the child `z' :: h` is reached by saving at `h` and drawing the next idiosyncratic state from
`idioProb z_h z'`. The aggregate shock is not drawn, since the node records it.

The distribution at a node lives on `[0, assetCap] × E`, not on the full state with its node, so
that the integrand of a push stays on a compact space. That compactness is what the continuity
argument uses.

* `integral_pushNode`: **duality**, integrating `f` against the child is integrating
  `Σ_{e'} idioProb · f(next state)` against the parent (as `integral_push` in
  `LeanEconomics.Distribution.Feller`).
* `continuousAt_integral_nodeDist`: **the distribution at every node is weakly continuous in the
  path** (product topology): for every bounded continuous `f`, `K ↦ ∫ f d(nodeDist μ₀ K h)` is
  continuous. By induction on the node. The integrand of the push converges uniformly, because
  the policy is jointly continuous and the space is compact; and its integral against the parent
  converges by the induction hypothesis.
* `meanCapital`: mean assets at a node, continuous in the path and in `[0, assetCap]`.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory Metric
open scoped NNReal ENNReal

namespace LeanEconomics

namespace KrusellSmith

/-- An idiosyncratic state, with the discrete topology and the discrete σ-algebra. -/
structure Idio (E : Type*) where
  /-- The idiosyncratic state. -/
  idio : E

namespace Idio

variable (E : Type*)

instance : TopologicalSpace (Idio E) := ⊥

instance : DiscreteTopology (Idio E) := ⟨rfl⟩

instance : MeasurableSpace (Idio E) := ⊤

instance : BorelSpace (Idio E) := ⟨borel_eq_top_of_discrete.symm⟩

/-- `Idio E` is `E`. -/
def equiv : Idio E ≃ E := ⟨Idio.idio, Idio.mk, fun _ => rfl, fun _ => rfl⟩

instance [Finite E] : Finite (Idio E) := Finite.of_equiv E (equiv E).symm

end Idio

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z) (m₀ : E → ℝ)

/-- What a distribution of households is over at a node: assets and idiosyncratic state. -/
abbrev AState := ↥(Icc (0 : ℝ) M.assetCap) × Idio E

/-- A household at `x` at node `h`, saving by the policy for the path `K`, moves to `e'`. -/
noncomputable def nextA (K : List Z → ℝ) (h : List Z) (e' : E) (x : M.AState) : M.AState :=
  (M.clampAssets (M.policy z₀ m₀ K (x.1, ⟨x.2.idio, h⟩)), ⟨e'⟩)

theorem continuous_nextA_joint (h : List Z) (e' : E) :
    Continuous fun p : (List Z → ℝ) × M.AState => M.nextA z₀ m₀ p.1 h e' p.2 := by
  have hlab : Continuous fun i : Idio E => (⟨i.idio, h⟩ : Label Z E) :=
    continuous_of_discreteTopology
  refine Continuous.prodMk ?_ continuous_const
  exact continuous_projIcc.comp ((M.continuous_policy z₀ m₀).comp (continuous_fst.prodMk
    ((continuous_fst.comp continuous_snd).prodMk (hlab.comp (continuous_snd.comp continuous_snd)))))

theorem continuous_nextA (K : List Z → ℝ) (h : List Z) (e' : E) :
    Continuous (M.nextA z₀ m₀ K h e') :=
  Continuous.comp (g := fun p : (List Z → ℝ) × M.AState => M.nextA z₀ m₀ p.1 h e' p.2)
    (f := fun x : M.AState => (K, x)) (M.continuous_nextA_joint z₀ m₀ h e')
    (continuous_const.prodMk continuous_id)

/-- The probability of moving to `e'` at node `h` when the next aggregate shock is `z'`. -/
def nextProb (h : List Z) (z' : Z) (e' : E) (x : M.AState) : ℝ :=
  M.idioProb (shockAt z₀ h) z' x.2.idio e'

theorem continuous_nextProb (h : List Z) (z' : Z) (e' : E) :
    Continuous (M.nextProb z₀ h z' e') :=
  (continuous_of_discreteTopology
    (f := fun i : Idio E => M.idioProb (shockAt z₀ h) z' i.idio e')).comp continuous_snd

theorem nextProb_nonneg (h : List Z) (z' : Z) (e' : E) (x : M.AState) :
    0 ≤ M.nextProb z₀ h z' e' x :=
  M.idioProb_nonneg _ _ _ _

theorem sum_nextProb (h : List Z) (z' : Z) (x : M.AState) : ∑ e', M.nextProb z₀ h z' e' x = 1 :=
  M.idioProb_sum _ _ _

/-- The reweighting density, as an `ℝ≥0`-valued function. -/
noncomputable def dens (h : List Z) (z' : Z) (e' : E) (x : M.AState) : ℝ≥0 :=
  (M.nextProb z₀ h z' e' x).toNNReal

theorem measurable_dens (h : List Z) (z' : Z) (e' : E) : Measurable (M.dens z₀ h z' e') :=
  (continuous_real_toNNReal.comp (M.continuous_nextProb z₀ h z' e')).measurable

theorem coe_dens (h : List Z) (z' : Z) (e' : E) (x : M.AState) :
    ((M.dens z₀ h z' e' x : ℝ≥0) : ℝ) = M.nextProb z₀ h z' e' x :=
  Real.coe_toNNReal _ (M.nextProb_nonneg z₀ h z' e' x)

theorem sum_dens (h : List Z) (z' : Z) (x : M.AState) :
    ∑ e', ((M.dens z₀ h z' e' x : ℝ≥0) : ℝ≥0∞) = 1 := by
  have hz : ∀ e' : E, ((M.dens z₀ h z' e' x : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal (M.nextProb z₀ h z' e' x) := fun _ => rfl
  rw [Finset.sum_congr rfl fun e' _ => hz e',
    ← ENNReal.ofReal_sum_of_nonneg fun e' _ => M.nextProb_nonneg z₀ h z' e' x,
    M.sum_nextProb z₀ h z' x, ENNReal.ofReal_one]

/-- One step down the tree, from node `h` to `z' :: h`. -/
noncomputable def pushNode (K : List Z → ℝ) (h : List Z) (z' : Z) (μ : Measure M.AState) :
    Measure M.AState :=
  Measure.sum fun e' : E =>
    (μ.withDensity fun x => (M.dens z₀ h z' e' x : ℝ≥0∞)).map (M.nextA z₀ m₀ K h e')

theorem measurable_nextA (K : List Z → ℝ) (h : List Z) (e' : E) :
    Measurable (M.nextA z₀ m₀ K h e') :=
  (M.continuous_nextA z₀ m₀ K h e').measurable

theorem isProbabilityMeasure_pushNode (K : List Z → ℝ) (h : List Z) (z' : Z)
    (μ : Measure M.AState) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (M.pushNode z₀ m₀ K h z' μ) := by
  constructor
  rw [pushNode, Measure.sum_apply _ MeasurableSet.univ]
  have hterm : ∀ e' : E,
      ((μ.withDensity fun x => (M.dens z₀ h z' e' x : ℝ≥0∞)).map (M.nextA z₀ m₀ K h e')) univ
        = ∫⁻ x, (M.dens z₀ h z' e' x : ℝ≥0∞) ∂μ := by
    intro e'
    rw [Measure.map_apply (M.measurable_nextA z₀ m₀ K h e') MeasurableSet.univ,
      Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [tsum_fintype]
  simp only [hterm]
  rw [← lintegral_finsetSum _ fun e' _ => (M.measurable_dens z₀ h z' e').coe_nnreal_ennreal]
  simp only [M.sum_dens]
  simp

theorem integrable_term (K : List Z → ℝ) (h : List Z) (z' : Z) (μ : Measure M.AState)
    [IsProbabilityMeasure μ] (f : M.AState →ᵇ ℝ) (e' : E) :
    Integrable (fun x => M.nextProb z₀ h z' e' x * f (M.nextA z₀ m₀ K h e' x)) μ := by
  refine (integrable_const ‖f‖).mono' ?_ ?_
  · exact ((M.continuous_nextProb z₀ h z' e').mul (f.continuous.comp
      (M.continuous_nextA z₀ m₀ K h e'))).measurable.aestronglyMeasurable
  · filter_upwards with x
    have h1 : M.nextProb z₀ h z' e' x ≤ 1 := by
      rw [← M.sum_nextProb z₀ h z' x]
      exact Finset.single_le_sum (fun i _ => M.nextProb_nonneg z₀ h z' i x) (Finset.mem_univ e')
    have h2 : |f (M.nextA z₀ m₀ K h e' x)| ≤ ‖f‖ := by
      simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (M.nextA z₀ m₀ K h e' x)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (M.nextProb_nonneg z₀ h z' e' x)]
    nlinarith [M.nextProb_nonneg z₀ h z' e' x, abs_nonneg (f (M.nextA z₀ m₀ K h e' x))]

/-- **Duality.** Integrating against the child is integrating the expected next value against
the parent. -/
theorem integral_pushNode (K : List Z → ℝ) (h : List Z) (z' : Z) (μ : Measure M.AState)
    [IsProbabilityMeasure μ] (f : M.AState →ᵇ ℝ) :
    ∫ x, f x ∂(M.pushNode z₀ m₀ K h z' μ)
      = ∫ x, ∑ e', M.nextProb z₀ h z' e' x * f (M.nextA z₀ m₀ K h e' x) ∂μ := by
  have hterm : ∀ e' : E,
      ∫ x, f x ∂((μ.withDensity fun x => (M.dens z₀ h z' e' x : ℝ≥0∞)).map
          (M.nextA z₀ m₀ K h e'))
        = ∫ x, M.nextProb z₀ h z' e' x * f (M.nextA z₀ m₀ K h e' x) ∂μ := by
    intro e'
    rw [integral_map (M.measurable_nextA z₀ m₀ K h e').aemeasurable
      f.continuous.measurable.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul (M.measurable_dens z₀ h z' e')]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    calc (M.dens z₀ h z' e' x : ℝ≥0) • f (M.nextA z₀ m₀ K h e' x)
        = ((M.dens z₀ h z' e' x : ℝ≥0) : ℝ) • f (M.nextA z₀ m₀ K h e' x) := NNReal.smul_def _ _
      _ = M.nextProb z₀ h z' e' x * f (M.nextA z₀ m₀ K h e' x) := by
          rw [smul_eq_mul, M.coe_dens z₀ h z' e' x]
  have := M.isProbabilityMeasure_pushNode z₀ m₀ K h z' μ
  have hint : Integrable (fun x => f x) (M.pushNode z₀ m₀ K h z' μ) := f.integrable _
  rw [pushNode] at hint ⊢
  rw [integral_sum_measure hint, tsum_fintype]
  simp only [hterm]
  rw [← integral_finsetSum _ fun e' _ => M.integrable_term z₀ m₀ K h z' μ f e']

variable (μ₀ : Measure M.AState)

/-- **The distribution of households at each node** along the path `K`, from `μ₀` at the root. -/
noncomputable def nodeDist (K : List Z → ℝ) : List Z → Measure M.AState
  | [] => μ₀
  | z' :: h => M.pushNode z₀ m₀ K h z' (nodeDist K h)

theorem isProbabilityMeasure_nodeDist [IsProbabilityMeasure μ₀] (K : List Z → ℝ) :
    ∀ h, IsProbabilityMeasure (M.nodeDist z₀ m₀ μ₀ K h)
  | [] => ‹_›
  | z' :: h => by
    have := isProbabilityMeasure_nodeDist K h
    exact M.isProbabilityMeasure_pushNode z₀ m₀ K h z' _

/-- The expected next value of `f`, as a bounded continuous function, along the path `K`. -/
noncomputable def expectedNext (K : List Z → ℝ) (h : List Z) (z' : Z) (f : M.AState →ᵇ ℝ) :
    M.AState →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ∑ e', M.nextProb z₀ h z' e' x * f (M.nextA z₀ m₀ K h e' x))
    (continuous_finsetSum _ fun e' _ => (M.continuous_nextProb z₀ h z' e').mul (f.continuous.comp
      (M.continuous_nextA z₀ m₀ K h e')))
    ‖f‖ fun x => by
      rw [Real.norm_eq_abs]
      calc |∑ e', M.nextProb z₀ h z' e' x * f (M.nextA z₀ m₀ K h e' x)|
          ≤ ∑ e', |M.nextProb z₀ h z' e' x * f (M.nextA z₀ m₀ K h e' x)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ e', M.nextProb z₀ h z' e' x * ‖f‖ := by
            refine Finset.sum_le_sum fun e' _ => ?_
            rw [abs_mul, abs_of_nonneg (M.nextProb_nonneg z₀ h z' e' x)]
            exact mul_le_mul_of_nonneg_left
              (by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _)
              (M.nextProb_nonneg z₀ h z' e' x)
        _ = ‖f‖ := by rw [← Finset.sum_mul, M.sum_nextProb z₀ h z' x, one_mul]

theorem continuous_expectedNext_joint (h : List Z) (z' : Z) (f : M.AState →ᵇ ℝ) :
    Continuous fun p : (List Z → ℝ) × M.AState => M.expectedNext z₀ m₀ p.1 h z' f p.2 :=
  continuous_finsetSum _ fun e' _ => ((M.continuous_nextProb z₀ h z' e').comp continuous_snd).mul
    (f.continuous.comp (M.continuous_nextA_joint z₀ m₀ h e'))

/-- **The distribution at every node is weakly continuous in the path of capital.** -/
theorem continuousAt_integral_nodeDist [IsProbabilityMeasure μ₀] (K₀ : List Z → ℝ) :
    ∀ (h : List Z) (f : M.AState →ᵇ ℝ),
      ContinuousAt (fun K => ∫ x, f x ∂(M.nodeDist z₀ m₀ μ₀ K h)) K₀
  | [], _ => continuousAt_const
  | z' :: h, f => by
    have hdual : ∀ K, ∫ x, f x ∂(M.nodeDist z₀ m₀ μ₀ K (z' :: h))
        = ∫ x, M.expectedNext z₀ m₀ K h z' f x ∂(M.nodeDist z₀ m₀ μ₀ K h) := by
      intro K
      have := M.isProbabilityMeasure_nodeDist z₀ m₀ μ₀ K h
      exact M.integral_pushNode z₀ m₀ K h z' _ f
    simp only [hdual]
    have IH := continuousAt_integral_nodeDist K₀ h (M.expectedNext z₀ m₀ K₀ h z' f)
    rw [Metric.continuousAt_iff'] at IH ⊢
    intro ε hε
    -- the integrand converges uniformly
    have hunif : ∀ᶠ K in 𝓝 K₀, ∀ x : M.AState,
        dist (M.expectedNext z₀ m₀ K h z' f x) (M.expectedNext z₀ m₀ K₀ h z' f x) < ε / 2 := by
      have hfc : ContinuousOn (Function.uncurry fun (K : List Z → ℝ) (x : M.AState) =>
          M.expectedNext z₀ m₀ K h z' f x) (univ ×ˢ univ) :=
        (M.continuous_expectedNext_joint z₀ m₀ h z' f).continuousOn
      obtain ⟨w, hw, hwf⟩ := isCompact_univ.mem_uniformity_of_prod hfc (mem_univ K₀)
        (dist_mem_uniformity (half_pos hε))
      rw [nhdsWithin_univ] at hw
      filter_upwards [hw] with K hK x
      exact hwf K hK x (mem_univ x)
    filter_upwards [hunif, IH (ε / 2) (half_pos hε)] with K hK hK'
    have := M.isProbabilityMeasure_nodeDist z₀ m₀ μ₀ K h
    have hsplit : ∫ x, M.expectedNext z₀ m₀ K h z' f x ∂(M.nodeDist z₀ m₀ μ₀ K h)
          - ∫ x, M.expectedNext z₀ m₀ K₀ h z' f x ∂(M.nodeDist z₀ m₀ μ₀ K h)
        = ∫ x, (M.expectedNext z₀ m₀ K h z' f x - M.expectedNext z₀ m₀ K₀ h z' f x)
            ∂(M.nodeDist z₀ m₀ μ₀ K h) :=
      (integral_sub ((M.expectedNext z₀ m₀ K h z' f).integrable _)
        ((M.expectedNext z₀ m₀ K₀ h z' f).integrable _)).symm
    have h1 : ‖∫ x, (M.expectedNext z₀ m₀ K h z' f x - M.expectedNext z₀ m₀ K₀ h z' f x)
        ∂(M.nodeDist z₀ m₀ μ₀ K h)‖ ≤ ε / 2 := by
      have := norm_integral_le_of_norm_le_const (μ := M.nodeDist z₀ m₀ μ₀ K h)
        (f := fun x => M.expectedNext z₀ m₀ K h z' f x - M.expectedNext z₀ m₀ K₀ h z' f x)
        (C := ε / 2) (Filter.Eventually.of_forall fun x => by
          rw [← dist_eq_norm]
          exact (hK x).le)
      rwa [probReal_univ, mul_one] at this
    rw [dist_eq_norm] at hK' ⊢
    calc ‖∫ x, M.expectedNext z₀ m₀ K h z' f x ∂(M.nodeDist z₀ m₀ μ₀ K h)
          - ∫ x, M.expectedNext z₀ m₀ K₀ h z' f x ∂(M.nodeDist z₀ m₀ μ₀ K₀ h)‖
        ≤ ‖∫ x, M.expectedNext z₀ m₀ K h z' f x ∂(M.nodeDist z₀ m₀ μ₀ K h)
            - ∫ x, M.expectedNext z₀ m₀ K₀ h z' f x ∂(M.nodeDist z₀ m₀ μ₀ K h)‖
          + ‖∫ x, M.expectedNext z₀ m₀ K₀ h z' f x ∂(M.nodeDist z₀ m₀ μ₀ K h)
            - ∫ x, M.expectedNext z₀ m₀ K₀ h z' f x ∂(M.nodeDist z₀ m₀ μ₀ K₀ h)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := by rw [hsplit]; exact add_lt_add_of_le_of_lt h1 hK'
      _ = ε := add_halves ε

/-! ### Mean capital -/

/-- Assets, as a bounded continuous function on `[0, assetCap] × E`. -/
noncomputable def assets : M.AState →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (x.1 : ℝ))
    (continuous_subtype_val.comp continuous_fst) M.assetCap fun x => by
      rw [Real.norm_of_nonneg x.1.2.1]
      exact x.1.2.2

/-- **Mean assets at node `h`** along the path `K`: next period's aggregate capital there. -/
noncomputable def meanCapital (K : List Z → ℝ) (h : List Z) : ℝ :=
  ∫ x, M.assets x ∂(M.nodeDist z₀ m₀ μ₀ K h)

theorem continuousAt_meanCapital [IsProbabilityMeasure μ₀] (K₀ : List Z → ℝ) (h : List Z) :
    ContinuousAt (fun K => M.meanCapital z₀ m₀ μ₀ K h) K₀ :=
  M.continuousAt_integral_nodeDist z₀ m₀ μ₀ K₀ h M.assets

theorem meanCapital_mem [IsProbabilityMeasure μ₀] (K : List Z → ℝ) (h : List Z) :
    M.meanCapital z₀ m₀ μ₀ K h ∈ Icc 0 M.assetCap := by
  have := M.isProbabilityMeasure_nodeDist z₀ m₀ μ₀ K h
  refine ⟨integral_nonneg fun x => x.1.2.1, ?_⟩
  calc M.meanCapital z₀ m₀ μ₀ K h ≤ ∫ _x, M.assetCap ∂(M.nodeDist z₀ m₀ μ₀ K h) :=
        integral_mono (M.assets.integrable _) (integrable_const _) fun x => x.1.2.2
    _ = M.assetCap := by simp

theorem meanCapital_nil (K : List Z → ℝ) :
    M.meanCapital z₀ m₀ μ₀ K [] = ∫ x, M.assets x ∂μ₀ := rfl

end KSModel

end KrusellSmith

end LeanEconomics
