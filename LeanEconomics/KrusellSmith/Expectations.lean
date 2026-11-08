/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.StationaryState
import LeanEconomics.MarkovEquilibrium.Ergodic

/-!
# The expectations correspondence

Milestone S5 (step 8) of `STATIONARITY_PLAN.md`: Cao's (2020) expectations correspondence on the
compact set `J*` of equilibrium states (`StationaryState.lean`). At a state `ξ = (z, μ, v, a)`, a
probability measure `γ` on `J*` (beliefs about tomorrow's state) is **consistent with `ξ`**,
`γ ∈ expectations ξ`, when

1. **shocks and distributions**: tomorrow's shock is `z'` with probability `π(z, z')`, and then
   tomorrow's distribution is today's pushed forward by the policy `a` and the idiosyncratic
   transition (`nextDist ξ z'`); stated for all test functions `g` of the distribution:
   `∫ 1[ξ'.shock = z'] g(ξ'.dist) dγ = π(z, z') g(nextDist ξ z')`;
2. **feasibility**: `a x ∈ [0, maxSaving ξ x]`;
3. **Bellman, attained**: `v x = u(cash ξ x − a x) + β ∫ Σ_{e'} q(z, ξ'.shock, e, e') ξ'.v(a x, e') dγ`;
4. **Bellman, optimality**: no feasible saving does better than `v x`.

Prices depend on `(z, μ)` only (`cash`). The conditions are affine in `γ`, so the values are
convex under mixtures (`mix_mem_expectations`), and they are equalities and inequalities between
functions jointly continuous in `(ξ, γ)`, so the graph is closed (`isClosed_graph_expectations`).
Continuity comes from `continuous_integral_of_joint`: the integral of a jointly continuous function
against a continuously moving probability measure on a compact space moves continuously.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory Metric
open scoped ENNReal NNReal Classical

namespace LeanEconomics

namespace KrusellSmith

/-! ### Integrals of jointly continuous functions -/

/-- **Integration is jointly continuous** in the integrand (supremum norm) and the probability
measure (weak topology). -/
theorem continuous_integral_joint {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] :
    Continuous fun q : (X →ᵇ ℝ) × ProbabilityMeasure X => ∫ x, q.1 x ∂(q.2 : Measure X) := by
  refine continuous_iff_continuousAt.2 fun q₀ => ?_
  rw [Metric.continuousAt_iff']
  intro ε hε
  have h1 : ∀ᶠ q in 𝓝 q₀, dist q.1 q₀.1 < ε / 2 :=
    (continuous_fst.continuousAt (x := q₀)) (ball_mem_nhds _ (half_pos hε))
  have h2 : ∀ᶠ q in 𝓝 q₀,
      dist (∫ x, q₀.1 x ∂(q.2 : Measure X)) (∫ x, q₀.1 x ∂(q₀.2 : Measure X)) < ε / 2 :=
    (((ProbabilityMeasure.continuous_integral_boundedContinuousFunction q₀.1).comp
      continuous_snd).continuousAt (x := q₀)) (ball_mem_nhds _ (half_pos hε))
  filter_upwards [h1, h2] with q hq1 hq2
  have h3 : dist (∫ x, q.1 x ∂(q.2 : Measure X)) (∫ x, q₀.1 x ∂(q.2 : Measure X)) ≤ ε / 2 := by
    rw [dist_eq_norm, ← integral_sub (q.1.integrable _) (q₀.1.integrable _)]
    have := norm_integral_le_of_norm_le_const (μ := (q.2 : Measure X)) (C := ε / 2)
      (f := fun x => q.1 x - q₀.1 x) (Eventually.of_forall fun x => by
        rw [← dist_eq_norm]
        exact (dist_coe_le_dist x).trans hq1.le)
    rwa [probReal_univ, mul_one] at this
  calc dist (∫ x, q.1 x ∂(q.2 : Measure X)) (∫ x, q₀.1 x ∂(q₀.2 : Measure X))
      ≤ dist (∫ x, q.1 x ∂(q.2 : Measure X)) (∫ x, q₀.1 x ∂(q.2 : Measure X))
        + dist (∫ x, q₀.1 x ∂(q.2 : Measure X)) (∫ x, q₀.1 x ∂(q₀.2 : Measure X)) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt h3 hq2
    _ = ε := add_halves ε

/-- **The integral of a jointly continuous function against a continuously moving probability
measure on a compact space is continuous.** -/
theorem continuous_integral_of_joint {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {h : P → X → ℝ}
    (hh : Continuous fun q : P × X => h q.1 q.2) {m : P → ProbabilityMeasure X}
    (hm : Continuous m) : Continuous fun p => ∫ x, h p x ∂(m p : Measure X) := by
  have hH : Continuous fun p => BoundedContinuousFunction.mkOfCompact
      (ContinuousMap.mk (h p) (hh.comp (continuous_const.prodMk continuous_id))) :=
    continuous_bcf_of_joint hh
  exact continuous_integral_joint.comp (hH.prodMk hm)

/-- A continuous function on a compact space is integrable for every probability measure. -/
theorem integrable_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {f : X → ℝ} (hf : Continuous f)
    (μ : ProbabilityMeasure X) : Integrable f (μ : Measure X) :=
  (BoundedContinuousFunction.mkOfCompact (ContinuousMap.mk f hf)).integrable _

/-- Integrals against a mixture. -/
theorem integral_mix {α : Type*} [MeasurableSpace α] (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (ρ σ : ProbabilityMeasure α) {f : α → ℝ} (hρ : Integrable f (ρ : Measure α))
    (hσ : Integrable f (σ : Measure α)) :
    ∫ x, f x ∂(MarkovEquilibrium.mix t ht ρ σ : Measure α)
      = t * ∫ x, f x ∂(ρ : Measure α) + (1 - t) * ∫ x, f x ∂(σ : Measure α) := by
  rw [MarkovEquilibrium.coe_mix, integral_add_measure (hρ.smul_measure ENNReal.ofReal_ne_top)
      (hσ.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal ht.1, ENNReal.toReal_ofReal (sub_nonneg.2 ht.2), smul_eq_mul,
    smul_eq_mul]

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- `J*` is a compact space. -/
instance : CompactSpace ↥M.equilibriumStates :=
  isCompact_iff_compactSpace.1 M.isCompact_equilibriumStates

namespace KSState

variable {M}

/-! ### Prices and the next distribution at a state -/

/-- Capital at a state: mean assets. -/
noncomputable def capital (ξ : M.KSState) : ℝ := ∫ x, M.assets x ∂(ξ.dist : Measure M.AState)

/-- Labour at a state: the efficiency-weighted mass. -/
noncomputable def labour (ξ : M.KSState) : ℝ :=
  ∑ e, M.initMass (ξ.dist : Measure M.AState) e * M.efficiency e

/-- Cash on hand at a state. -/
noncomputable def cash (ξ : M.KSState) (x : M.AState) : ℝ :=
  M.grossReturn ξ.shock ξ.capital ξ.labour * x.1 + M.wage ξ.shock ξ.capital ξ.labour * M.efficiency x.2.idio
    - M.grossReturn ξ.shock ξ.capital ξ.labour * M.borrowLimit

/-- The largest feasible saving at a state. -/
noncomputable def maxSaving (ξ : M.KSState) (x : M.AState) : ℝ :=
  min M.assetCap (ξ.cash x - M.consFloor)

/-- The asset and idiosyncratic state reached by saving by the policy and moving to `e'`. -/
noncomputable def nextPoint (ξ : M.KSState) (e' : E) (x : M.AState) : M.AState :=
  (M.clampAssets (ξ.policy x), ⟨e'⟩)

theorem continuous_nextPoint (ξ : M.KSState) (e' : E) : Continuous (ξ.nextPoint e') :=
  (continuous_projIcc.comp ξ.policy.continuous).prodMk continuous_const

/-- **The next distribution** when the shock moves to `z'`: today's pushed forward by the policy
and the idiosyncratic transition. -/
noncomputable def nextMeasure (ξ : M.KSState) (z' : Z) : Measure M.AState :=
  Measure.sum fun e' : E =>
    ((ξ.dist : Measure M.AState).withDensity fun x => (M.dens ξ.shock [] z' e' x : ℝ≥0∞)).map
      (ξ.nextPoint e')

theorem isProbabilityMeasure_nextMeasure (ξ : M.KSState) (z' : Z) :
    IsProbabilityMeasure (ξ.nextMeasure z') := by
  constructor
  rw [nextMeasure, Measure.sum_apply _ MeasurableSet.univ]
  have hterm : ∀ e' : E,
      (((ξ.dist : Measure M.AState).withDensity fun x => (M.dens ξ.shock [] z' e' x : ℝ≥0∞)).map
        (ξ.nextPoint e')) univ = ∫⁻ x, (M.dens ξ.shock [] z' e' x : ℝ≥0∞) ∂(ξ.dist : Measure _) := by
    intro e'
    rw [Measure.map_apply (ξ.continuous_nextPoint e').measurable MeasurableSet.univ,
      Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [tsum_fintype]
  simp only [hterm]
  rw [← lintegral_finsetSum _ fun e' _ => (M.measurable_dens ξ.shock [] z' e').coe_nnreal_ennreal]
  simp only [M.sum_dens]
  simp

/-- The next distribution, as a probability measure. -/
noncomputable def nextDist (ξ : M.KSState) (z' : Z) : ProbabilityMeasure M.AState :=
  ⟨ξ.nextMeasure z', ξ.isProbabilityMeasure_nextMeasure z'⟩

/-- **Duality** for the next distribution. -/
theorem integral_nextDist (ξ : M.KSState) (z' : Z) (f : M.AState →ᵇ ℝ) :
    ∫ x, f x ∂(ξ.nextDist z' : Measure M.AState)
      = ∫ x, ∑ e', M.idioProb ξ.shock z' x.2.idio e' * f (ξ.nextPoint e' x)
          ∂(ξ.dist : Measure M.AState) := by
  have hterm : ∀ e' : E,
      ∫ x, f x ∂(((ξ.dist : Measure M.AState).withDensity
          fun x => (M.dens ξ.shock [] z' e' x : ℝ≥0∞)).map (ξ.nextPoint e'))
        = ∫ x, M.idioProb ξ.shock z' x.2.idio e' * f (ξ.nextPoint e' x)
            ∂(ξ.dist : Measure M.AState) := by
    intro e'
    rw [integral_map (ξ.continuous_nextPoint e').measurable.aemeasurable
      f.continuous.measurable.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul (M.measurable_dens ξ.shock [] z' e')]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    calc (M.dens ξ.shock [] z' e' x : ℝ≥0) • f (ξ.nextPoint e' x)
        = ((M.dens ξ.shock [] z' e' x : ℝ≥0) : ℝ) • f (ξ.nextPoint e' x) := NNReal.smul_def _ _
      _ = M.idioProb ξ.shock z' x.2.idio e' * f (ξ.nextPoint e' x) := by
          rw [smul_eq_mul, M.coe_dens ξ.shock [] z' e' x]
          rfl
  have := ξ.isProbabilityMeasure_nextMeasure z'
  have hint : Integrable (fun x => f x) (ξ.nextMeasure z') := f.integrable _
  change ∫ x, f x ∂(ξ.nextMeasure z') = _
  rw [nextMeasure] at hint ⊢
  rw [integral_sum_measure hint, tsum_fintype]
  simp only [hterm]
  rw [← integral_finsetSum _ fun e' _ => ?_]
  have hc : Continuous fun x : M.AState => M.idioProb ξ.shock z' x.2.idio e' * f (ξ.nextPoint e' x) :=
    ((continuous_of_discreteTopology (f := fun i : Idio E => M.idioProb ξ.shock z' i.idio e')).comp
      continuous_snd).mul (f.continuous.comp (ξ.continuous_nextPoint e'))
  exact integrable_of_continuous hc (ξ.dist)

/-! ### Continuity in the state -/

omit [Fintype Z] in
/-- A function of the shock and of a continuous quantity is continuous: shocks are discrete. -/
theorem continuous_shockDep {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace W] {f : Z → Y → W} (hf : ∀ z, Continuous (f z)) {s : X → Z}
    (hs : Continuous fun x => (⟨s x⟩ : AggShock Z)) {y : X → Y} (hy : Continuous y) :
    Continuous fun x => f (s x) (y x) := by
  have : Continuous fun p : AggShock Z × Y => f p.1.val p.2 :=
    continuous_prod_of_discrete_left.2 fun a => hf a.val
  exact this.comp (hs.prodMk hy)

theorem continuous_capital : Continuous fun ξ : M.KSState => ξ.capital :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction M.assets).comp continuous_dist

theorem continuous_labour : Continuous fun ξ : M.KSState => ξ.labour :=
  continuous_finsetSum _ fun e _ =>
    (((continuous_apply e).comp M.continuous_initMass).comp continuous_dist).mul continuous_const

theorem continuous_cash (x : M.AState) : Continuous fun ξ : M.KSState => ξ.cash x := by
  have hk : Continuous fun ξ : M.KSState => (ξ.capital, ξ.labour) :=
    continuous_capital.prodMk continuous_labour
  have hR := continuous_shockDep (f := fun z (k : ℝ × ℝ) => M.grossReturn z k.1 k.2)
    (fun z => M.continuous_grossReturn z) continuous_shock hk
  have hW := continuous_shockDep (f := fun z (k : ℝ × ℝ) => M.wage z k.1 k.2)
    (fun z => M.continuous_wage z) continuous_shock hk
  exact ((hR.mul continuous_const).add (hW.mul continuous_const)).sub (hR.mul continuous_const)

theorem continuous_maxSaving (x : M.AState) : Continuous fun ξ : M.KSState => ξ.maxSaving x :=
  continuous_const.min ((continuous_cash x).sub continuous_const)

/-- **The next distribution moves continuously with the state.** -/
theorem continuous_nextDist (z' : Z) : Continuous fun ξ : M.KSState => ξ.nextDist z' := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have e : (fun ξ : M.KSState => ∫ x, f x ∂(ξ.nextDist z' : Measure M.AState))
      = fun ξ => ∫ x, ∑ e', M.idioProb ξ.shock z' x.2.idio e' * f (ξ.nextPoint e' x)
          ∂(ξ.dist : Measure M.AState) :=
    funext fun ξ => ξ.integral_nextDist z' f
  rw [e]
  refine continuous_integral_of_joint
    (h := fun ξ x => ∑ e', M.idioProb ξ.shock z' x.2.idio e' * f (ξ.nextPoint e' x)) ?_
    continuous_dist
  refine continuous_finsetSum _ fun e' _ => Continuous.mul ?_ ?_
  · have : Continuous fun p : AggShock Z × Idio E => M.idioProb p.1.val z' p.2.idio e' :=
      continuous_of_discreteTopology
    exact this.comp ((continuous_shock.comp continuous_fst).prodMk
      (continuous_snd.comp continuous_snd))
  · have hp : Continuous fun q : M.KSState × M.AState => q.1.policy q.2 :=
      continuous_eval.comp ((continuous_policy.comp continuous_fst).prodMk continuous_snd)
    exact f.continuous.comp ((continuous_projIcc.comp hp).prodMk continuous_const)

/-! ### The household's objective against beliefs -/

/-- The continuation value at tomorrow's state `ξ'` of saving `b` at `x` today. -/
noncomputable def contValue (ξ : M.KSState) (x : M.AState) (b : ℝ) (ξ' : M.KSState) : ℝ :=
  ∑ e', M.idioProb ξ.shock ξ'.shock x.2.idio e' * ξ'.value (M.clampAssets b, ⟨e'⟩)

theorem continuous_contValue {P : Type*} [TopologicalSpace P] {ξ : P → M.KSState}
    (hξ : Continuous ξ) (x : M.AState) {b : P → ℝ} (hb : Continuous b) :
    Continuous fun q : P × M.KSState => (ξ q.1).contValue x (b q.1) q.2 := by
  refine continuous_finsetSum _ fun e' _ => Continuous.mul ?_ ?_
  · have : Continuous fun p : AggShock Z × AggShock Z => M.idioProb p.1.val p.2.val x.2.idio e' :=
      continuous_of_discreteTopology
    exact this.comp ((continuous_shock.comp (hξ.comp continuous_fst)).prodMk
      (continuous_shock.comp continuous_snd))
  · exact continuous_eval.comp ((continuous_value.comp continuous_snd).prodMk
      ((continuous_projIcc.comp (hb.comp continuous_fst)).prodMk continuous_const))

theorem continuous_contValue_right (ξ : M.KSState) (x : M.AState) (b : ℝ) :
    Continuous fun ξ' : M.KSState => ξ.contValue x b ξ' := by
  refine continuous_finsetSum _ fun e' _ => Continuous.mul ?_ ?_
  · exact (continuous_of_discreteTopology
      (f := fun s : AggShock Z => M.idioProb ξ.shock s.val x.2.idio e')).comp continuous_shock
  · exact (continuous_eval_const _).comp continuous_value

/-- **The household's objective at `ξ` against beliefs `γ`** about tomorrow's state: utility of
consumption plus the discounted expected continuation value. -/
noncomputable def objective (ξ : M.KSState) (γ : ProbabilityMeasure ↥M.equilibriumStates)
    (x : M.AState) (b : ℝ) : ℝ :=
  M.utility (max M.consFloor (ξ.cash x - b))
    + M.discount * ∫ ξ', ξ.contValue x b ξ'.1 ∂(γ : Measure ↥M.equilibriumStates)

theorem continuous_objective {P : Type*} [TopologicalSpace P] {ξ : P → M.KSState}
    (hξ : Continuous ξ) {γ : P → ProbabilityMeasure ↥M.equilibriumStates} (hγ : Continuous γ)
    (x : M.AState) {b : P → ℝ} (hb : Continuous b) :
    Continuous fun p => (ξ p).objective (γ p) x (b p) := by
  have hu : Continuous fun p => M.utility (max M.consFloor ((ξ p).cash x - b p)) :=
    M.continuousOn_utility.comp_continuous
      (continuous_const.max (((continuous_cash x).comp hξ).sub hb)) fun p =>
        mem_Ici.2 (le_max_left _ _)
  have hc := continuous_contValue hξ x hb
  have hi : Continuous fun p => ∫ ξ', (ξ p).contValue x (b p) ξ'.1
      ∂(γ p : Measure ↥M.equilibriumStates) :=
    continuous_integral_of_joint (h := fun p (ξ' : ↥M.equilibriumStates) =>
      (ξ p).contValue x (b p) ξ'.1)
      (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) hγ
  exact hu.add (continuous_const.mul hi)

end KSState

/-! ### The expectations correspondence -/

/-- The indicator of tomorrow's shock being `z'`. -/
noncomputable def shockInd (z' : Z) (ξ' : ↥M.equilibriumStates) : ℝ :=
  if ξ'.1.shock = z' then 1 else 0

theorem continuous_shockInd (z' : Z) : Continuous (M.shockInd z') :=
  (continuous_of_discreteTopology (f := fun s : AggShock Z => if s.val = z' then (1 : ℝ) else 0)).comp
    (KSState.continuous_shock.comp continuous_subtype_val)

/-- **Cao's expectations correspondence**: beliefs `γ` about tomorrow's state consistent with the
state `ξ` today. -/
def expectations (ξ : ↥M.equilibriumStates) : Set (ProbabilityMeasure ↥M.equilibriumStates) :=
  {γ | (∀ (z' : Z) (g : ProbabilityMeasure M.AState →ᵇ ℝ),
        ∫ ξ', M.shockInd z' ξ' * g ξ'.1.dist ∂(γ : Measure ↥M.equilibriumStates)
          = M.aggProb ξ.1.shock z' * g (ξ.1.nextDist z')) ∧
      (∀ x, ξ.1.policy x ∈ Icc 0 (ξ.1.maxSaving x)) ∧
      (∀ x, ξ.1.value x = ξ.1.objective γ x (ξ.1.policy x)) ∧
      (∀ x, ∀ b ∈ Icc 0 M.assetCap, ξ.1.objective γ x (min b (ξ.1.maxSaving x)) ≤ ξ.1.value x)}

theorem continuous_test (z' : Z) (g : ProbabilityMeasure M.AState →ᵇ ℝ) :
    Continuous fun ξ' : ↥M.equilibriumStates => M.shockInd z' ξ' * g ξ'.1.dist :=
  (M.continuous_shockInd z').mul
    (g.continuous.comp (KSState.continuous_dist.comp continuous_subtype_val))

/-- **The expectations correspondence has convex values** (closed under mixtures). -/
theorem mix_mem_expectations (ξ : ↥M.equilibriumStates) :
    ∀ ρ ∈ M.expectations ξ, ∀ σ ∈ M.expectations ξ, ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      MarkovEquilibrium.mix t ht ρ σ ∈ M.expectations ξ := by
  rintro ρ ⟨hρ1, hρ2, hρ3, hρ4⟩ σ ⟨hσ1, hσ2, hσ3, hσ4⟩ t ht
  have hcv : ∀ x b, Continuous fun ξ' : ↥M.equilibriumStates => ξ.1.contValue x b ξ'.1 :=
    fun x b => (KSState.continuous_contValue_right ξ.1 x b).comp continuous_subtype_val
  have hobj : ∀ x b, ξ.1.objective (MarkovEquilibrium.mix t ht ρ σ) x b
      = t * ξ.1.objective ρ x b + (1 - t) * ξ.1.objective σ x b := by
    intro x b
    unfold KSState.objective
    rw [integral_mix t ht ρ σ (integrable_of_continuous (hcv x b) ρ)
      (integrable_of_continuous (hcv x b) σ)]
    ring
  refine ⟨fun z' g => ?_, hρ2, fun x => ?_, fun x b hb => ?_⟩
  · rw [integral_mix t ht ρ σ (integrable_of_continuous (M.continuous_test z' g) ρ)
      (integrable_of_continuous (M.continuous_test z' g) σ), hρ1, hσ1]
    ring
  · rw [hobj, ← hρ3, ← hσ3]
    ring
  · rw [hobj]
    have h1 := hρ4 x b hb
    have h2 := hσ4 x b hb
    nlinarith [ht.1, ht.2]

/-- **The expectations correspondence has a closed graph.** -/
theorem isClosed_graph_expectations :
    IsClosed (MarkovEquilibrium.graphSet M.expectations) := by
  have e : MarkovEquilibrium.graphSet M.expectations =
      (⋂ z', ⋂ g : ProbabilityMeasure M.AState →ᵇ ℝ,
        {p : ↥M.equilibriumStates × ProbabilityMeasure ↥M.equilibriumStates |
          ∫ ξ', M.shockInd z' ξ' * g ξ'.1.dist ∂(p.2 : Measure ↥M.equilibriumStates)
            = M.aggProb p.1.1.shock z' * g (p.1.1.nextDist z')}) ∩
      ((⋂ x, {p : ↥M.equilibriumStates × ProbabilityMeasure ↥M.equilibriumStates |
          p.1.1.policy x ∈ Icc 0 (p.1.1.maxSaving x)}) ∩
      ((⋂ x, {p : ↥M.equilibriumStates × ProbabilityMeasure ↥M.equilibriumStates |
          p.1.1.value x = p.1.1.objective p.2 x (p.1.1.policy x)}) ∩
      (⋂ x, ⋂ b, ⋂ (_ : b ∈ Icc 0 M.assetCap),
        {p : ↥M.equilibriumStates × ProbabilityMeasure ↥M.equilibriumStates |
          p.1.1.objective p.2 x (min b (p.1.1.maxSaving x)) ≤ p.1.1.value x}))) := by
    ext p
    simp only [MarkovEquilibrium.graphSet, expectations, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [e]
  have hξ : Continuous fun p : ↥M.equilibriumStates × ProbabilityMeasure ↥M.equilibriumStates =>
      p.1.1 := continuous_subtype_val.comp continuous_fst
  have hpol : ∀ x, Continuous fun p : ↥M.equilibriumStates × ProbabilityMeasure ↥M.equilibriumStates =>
      p.1.1.policy x := fun x => (continuous_eval_const x).comp (KSState.continuous_policy.comp hξ)
  have hval : ∀ x, Continuous fun p : ↥M.equilibriumStates × ProbabilityMeasure ↥M.equilibriumStates =>
      p.1.1.value x := fun x => (continuous_eval_const x).comp (KSState.continuous_value.comp hξ)
  have hmax : ∀ x, Continuous fun p : ↥M.equilibriumStates × ProbabilityMeasure ↥M.equilibriumStates =>
      p.1.1.maxSaving x := fun x => (KSState.continuous_maxSaving x).comp hξ
  refine (isClosed_iInter fun z' => isClosed_iInter fun g => isClosed_eq ?_ ?_).inter
    ((isClosed_iInter fun x => ?_).inter ((isClosed_iInter fun x => isClosed_eq (hval x)
      (KSState.continuous_objective hξ continuous_snd x (hpol x))).inter
      (isClosed_iInter fun x => isClosed_iInter fun b => isClosed_iInter fun _ =>
        isClosed_le (KSState.continuous_objective hξ continuous_snd x
          (continuous_const.min (hmax x))) (hval x))))
  · exact continuous_integral_of_joint
      (h := fun (_ : ↥M.equilibriumStates × ProbabilityMeasure ↥M.equilibriumStates)
        (ξ' : ↥M.equilibriumStates) => M.shockInd z' ξ' * g ξ'.1.dist)
      ((M.continuous_test z' g).comp continuous_snd) continuous_snd
  · have ha : Continuous fun p : ↥M.equilibriumStates × ProbabilityMeasure ↥M.equilibriumStates =>
        M.aggProb p.1.1.shock z' :=
      (continuous_of_discreteTopology (f := fun s : AggShock Z => M.aggProb s.val z')).comp
        (KSState.continuous_shock.comp hξ)
    exact ha.mul (g.continuous.comp ((KSState.continuous_nextDist z').comp hξ))
  · exact (isClosed_le continuous_const (hpol x)).inter (isClosed_le (hpol x) (hmax x))

end KSModel

end KrusellSmith

end LeanEconomics
