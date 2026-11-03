/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Krylov–Bogolyubov for a random map on a compact metric space

A Markov chain of the kind that appears in a state-space model,

  `X_{t+1} = F (X_t, W_{t+1})`,   `W_t` i.i.d. with law `ν`,

where `F` is jointly measurable and continuous in the state for each shock. If the state space
is a compact metric space, the chain has an invariant probability measure.

`LeanEconomics.IncomeFluctuation.exists_isStationary` proves this for the income fluctuation
problem, where the shock is finite and the Markov operator is a finite sum. Here the shock law
is an arbitrary probability measure, and the two places that change are:

* **Duality** (`integral_push`): `∫ h d(Tμ) = ∫ (Mh) dμ`, with `Mh x = ∫ h (F x w) dν w`, is
  change of variables followed by Fubini.
* **Feller** (`continuous_markovFn`): `Mh` is continuous, by dominated convergence, since `h`
  is bounded and `F (·, w)` is continuous for each `w`.

The rest (Cesàro averages, Prokhorov compactness, the telescoping estimate) is the same.
-/

open scoped NNReal ENNReal
open Set Filter Topology BoundedContinuousFunction MeasureTheory Function

namespace LeanEconomics

/-- A **random map** on `X` driven by shocks in `W`: the law `shock` of the shock and the map
`map x w` giving tomorrow's state, jointly measurable and continuous in the state. -/
structure RandomMap (X W : Type*) [TopologicalSpace X] [MeasurableSpace X]
    [MeasurableSpace W] where
  /-- The law of the shock. -/
  shock : Measure W
  isProbabilityMeasure_shock : IsProbabilityMeasure shock
  /-- Tomorrow's state as a function of today's state and the shock. -/
  map : X → W → X
  measurable_map : Measurable (uncurry map)
  continuous_map : ∀ w, Continuous fun x ↦ map x w

namespace RandomMap

variable {X W : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace W] (R : RandomMap X W)

instance : IsProbabilityMeasure R.shock := R.isProbabilityMeasure_shock

/-- One period of the chain: the law of `map X W` with `X ∼ μ` independent of `W ∼ shock`. -/
noncomputable def push (μ : Measure X) : Measure X := (μ.prod R.shock).map (uncurry R.map)

instance isProbabilityMeasure_push (μ : Measure X) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (R.push μ) := by
  unfold push
  infer_instance

/-- An **invariant** (stationary) probability measure of the chain. -/
def IsInvariant (μ : Measure X) : Prop := R.push μ = μ

/-- The expected value of `h` next period. -/
noncomputable def markovFn (h : X →ᵇ ℝ) (x : X) : ℝ := ∫ w, h (R.map x w) ∂R.shock

omit [BorelSpace X] in
theorem measurable_map_left (x : X) : Measurable fun w ↦ R.map x w :=
  R.measurable_map.comp measurable_prodMk_left

/-- **The Feller property**, by dominated convergence. -/
theorem continuous_markovFn (h : X →ᵇ ℝ) : Continuous (R.markovFn h) := by
  refine continuous_of_dominated (bound := fun _ ↦ ‖h‖) (fun x ↦ ?_) (fun x ↦ ?_)
    (integrable_const _) (Eventually.of_forall fun w ↦ h.continuous.comp (R.continuous_map w))
  · exact (h.continuous.measurable.comp (R.measurable_map_left x)).aestronglyMeasurable
  · exact Eventually.of_forall fun w ↦ h.norm_coe_le_norm _

omit [BorelSpace X] in
theorem abs_markovFn_le (h : X →ᵇ ℝ) (x : X) : |R.markovFn h x| ≤ ‖h‖ := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ‖h‖) ?_).trans_eq ?_
  · exact Eventually.of_forall fun w ↦ h.norm_coe_le_norm _
  · simp

/-- **The Markov operator**, on bounded continuous functions. -/
noncomputable def markovOp (h : X →ᵇ ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (R.markovFn h) (R.continuous_markovFn h) ‖h‖
    fun x ↦ by simpa [Real.norm_eq_abs] using R.abs_markovFn_le h x

@[simp]
theorem markovOp_apply (h : X →ᵇ ℝ) (x : X) : R.markovOp h x = R.markovFn h x := rfl

/-- **Duality**: change of variables, then Fubini. -/
theorem integral_push (μ : Measure X) [IsProbabilityMeasure μ] (h : X →ᵇ ℝ) :
    ∫ x, h x ∂(R.push μ) = ∫ x, R.markovOp h x ∂μ := by
  have hmeas : AEStronglyMeasurable (fun x ↦ h x) (R.push μ) :=
    h.continuous.measurable.aestronglyMeasurable
  have hint : Integrable (fun p : X × W ↦ h (uncurry R.map p)) (μ.prod R.shock) :=
    (integrable_map_measure hmeas R.measurable_map.aemeasurable).mp (h.integrable _)
  rw [push, integral_map R.measurable_map.aemeasurable hmeas, integral_prod _ hint]
  rfl

/-- The chain's action on probability measures. -/
noncomputable def pushProb (μ : ProbabilityMeasure X) : ProbabilityMeasure X :=
  ⟨R.push (μ : Measure X), R.isProbabilityMeasure_push _⟩

omit [BorelSpace X] in
@[simp]
theorem coe_pushProb (μ : ProbabilityMeasure X) :
    ((R.pushProb μ : ProbabilityMeasure X) : Measure X) = R.push (μ : Measure X) := rfl

/-- Integration against a bounded continuous function is weakly continuous. -/
theorem continuous_integral_bcf (h : X →ᵇ ℝ) :
    Continuous fun ν : ProbabilityMeasure X ↦ ∫ x, h x ∂(ν : Measure X) := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_id : Tendsto id (𝓝 μ) (𝓝 μ)) h

omit [BorelSpace X] in
theorem abs_integral_le (ν : Measure X) [IsProbabilityMeasure ν] (h : X →ᵇ ℝ) :
    |∫ x, h x ∂ν| ≤ ‖h‖ := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ‖h‖) ?_).trans_eq ?_
  · filter_upwards with x using h.norm_coe_le_norm x
  · simp

/-- The average of the first `n + 1` iterates. -/
noncomputable def cesaro (μ₀ : ProbabilityMeasure X) (n : ℕ) : Measure X :=
  (((n : ℝ≥0∞) + 1))⁻¹ • ∑ k ∈ Finset.range (n + 1),
    ((R.pushProb^[k] μ₀ : ProbabilityMeasure X) : Measure X)

instance isProbabilityMeasure_cesaro (μ₀ : ProbabilityMeasure X) (n : ℕ) :
    IsProbabilityMeasure (R.cesaro μ₀ n) := by
  constructor
  have hsum : (∑ k ∈ Finset.range (n + 1),
      ((R.pushProb^[k] μ₀ : ProbabilityMeasure X) : Measure X)) univ = (n : ℝ≥0∞) + 1 := by
    rw [Measure.finsetSum_apply]
    simp [measure_univ]
  rw [cesaro, Measure.smul_apply, hsum, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by positivity) (by simp)

theorem integral_cesaro (μ₀ : ProbabilityMeasure X) (n : ℕ) (h : X →ᵇ ℝ) :
    ∫ x, h x ∂(R.cesaro μ₀ n)
      = (↑(n + 1))⁻¹ * ∑ k ∈ Finset.range (n + 1),
          ∫ x, h x ∂((R.pushProb^[k] μ₀ : ProbabilityMeasure X) : Measure X) := by
  rw [cesaro, integral_smul_measure, integral_finsetSum_measure]
  · push_cast
    rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simp)]
    simp [smul_eq_mul]
  · intro k _
    exact h.integrable _

theorem integral_markovOp_iterate (μ₀ : ProbabilityMeasure X) (k : ℕ) (h : X →ᵇ ℝ) :
    ∫ x, R.markovOp h x ∂((R.pushProb^[k] μ₀ : ProbabilityMeasure X) : Measure X)
      = ∫ x, h x ∂((R.pushProb^[k + 1] μ₀ : ProbabilityMeasure X) : Measure X) := by
  rw [Function.iterate_succ_apply', R.coe_pushProb]
  exact (R.integral_push _ h).symm

/-- **The telescoping estimate.** -/
theorem integral_cesaro_sub (μ₀ : ProbabilityMeasure X) (n : ℕ) (h : X →ᵇ ℝ) :
    ∫ x, R.markovOp h x ∂(R.cesaro μ₀ n) - ∫ x, h x ∂(R.cesaro μ₀ n)
      = (↑(n + 1))⁻¹ *
        (∫ x, h x ∂((R.pushProb^[n + 1] μ₀ : ProbabilityMeasure X) : Measure X)
          - ∫ x, h x ∂(μ₀ : Measure X)) := by
  rw [R.integral_cesaro μ₀ n (R.markovOp h), R.integral_cesaro μ₀ n h, ← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  have hstep : ∀ k ∈ Finset.range (n + 1),
      (∫ x, R.markovOp h x ∂((R.pushProb^[k] μ₀ : ProbabilityMeasure X) : Measure X))
        - ∫ x, h x ∂((R.pushProb^[k] μ₀ : ProbabilityMeasure X) : Measure X)
      = (fun j ↦ ∫ x, h x ∂((R.pushProb^[j] μ₀ : ProbabilityMeasure X) : Measure X)) (k + 1)
        - (fun j ↦ ∫ x, h x ∂((R.pushProb^[j] μ₀ : ProbabilityMeasure X) : Measure X)) k :=
    fun k _ ↦ by rw [R.integral_markovOp_iterate]
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub
    (fun j ↦ ∫ x, h x ∂((R.pushProb^[j] μ₀ : ProbabilityMeasure X) : Measure X))]
  simp

theorem tendsto_cesaro_sub (μ₀ : ProbabilityMeasure X) (h : X →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x, R.markovOp h x ∂(R.cesaro μ₀ n) - ∫ x, h x ∂(R.cesaro μ₀ n))
      atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ,
      ‖∫ x, R.markovOp h x ∂(R.cesaro μ₀ n) - ∫ x, h x ∂(R.cesaro μ₀ n)‖
        ≤ (((n : ℝ) + 1))⁻¹ * (2 * ‖h‖) := by
    intro n
    rw [Real.norm_eq_abs, R.integral_cesaro_sub μ₀ n h, abs_mul]
    push_cast
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (abs_sub _ _).trans ?_
    have h1 := abs_integral_le ((R.pushProb^[n + 1] μ₀ : ProbabilityMeasure X) : Measure X) h
    have h2 := abs_integral_le ((μ₀ : ProbabilityMeasure X) : Measure X) h
    linarith
  refine squeeze_zero_norm hbound ?_
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (2 * ‖h‖))

/-- **Krylov–Bogolyubov.** A random map on a nonempty compact metric space, continuous in the
state, has an invariant probability measure. -/
theorem exists_isInvariant [CompactSpace X] [Nonempty X] :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ R.IsInvariant μ := by
  let μ₀ : ProbabilityMeasure X := ⟨Measure.dirac (Classical.arbitrary X), inferInstance⟩
  set ν : ℕ → ProbabilityMeasure X := fun n ↦ ⟨R.cesaro μ₀ n, inferInstance⟩ with hν
  obtain ⟨μ, hμ⟩ := exists_clusterPt_of_compactSpace (Filter.map ν atTop)
  refine ⟨μ, inferInstance, ?_⟩
  have key : ∀ h : X →ᵇ ℝ,
      ∫ x, h x ∂((R.pushProb μ : ProbabilityMeasure X) : Measure X)
        = ∫ x, h x ∂(μ : Measure X) := by
    intro h
    set g : ProbabilityMeasure X → ℝ := fun ρ ↦
      ∫ x, R.markovOp h x ∂(ρ : Measure X) - ∫ x, h x ∂(ρ : Measure X) with hg
    have hgc : Continuous g := (continuous_integral_bcf _).sub (continuous_integral_bcf _)
    have hgt : Filter.map (g ∘ ν) atTop ≤ 𝓝 0 := R.tendsto_cesaro_sub μ₀ h
    have hcl : ClusterPt (g μ) (Filter.map (g ∘ ν) atTop) := by
      rw [← Filter.map_map]
      exact hμ.map hgc.continuousAt le_rfl
    have hz : g μ = 0 := by
      by_contra hne
      have hdisj : Disjoint (𝓝 (g μ)) (𝓝 (0 : ℝ)) := disjoint_nhds_nhds.mpr hne
      have : (𝓝 (g μ) ⊓ Filter.map (g ∘ ν) atTop).NeBot := hcl
      exact (this.mono (inf_le_inf_left _ hgt)).ne (_root_.disjoint_iff.mp hdisj)
    have := R.integral_push (μ : Measure X) h
    simp only [hg, sub_eq_zero] at hz
    rw [R.coe_pushProb, this, hz]
  have hfin : (R.pushProb μ).toFiniteMeasure = μ.toFiniteMeasure :=
    FiniteMeasure.ext_of_forall_integral_eq key
  have := ProbabilityMeasure.toMeasure_injective
    (congrArg (fun x : FiniteMeasure X ↦ (x : Measure X)) hfin)
  exact congrArg (fun x : ProbabilityMeasure X ↦ (x : Measure X)) this

end RandomMap

end LeanEconomics
