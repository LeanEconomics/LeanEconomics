/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.SelfJustified

/-!
# Spotless beliefs

Milestone SP2 of `SPOTLESS_PLAN.md`. A belief `γ` about tomorrow's equilibrium state is
**spotless** (DGMM 1994, p. 756; Cao 2020, `P_F` in §6) if it is concentrated on the graph of a
function of tomorrow's shock: there is `f : Z → J*` with `γ {ξ' | ξ' = f (ξ'.shock)} = 1`. Given
tomorrow's shock, tomorrow's distribution, value and policy are then deterministic: no sunspot.

* `isClosed_spotless`: **the spotless beliefs form a closed set.** If `γₖ → γ` with `γₖ` spotless
  for `fₖ`, a subsequence of `fₖ` converges to some `f` in the compact `J*^Z` (`Z` is finite).
  Eventually every `γₖ` is concentrated on the closed `ε`-neighbourhood
  `{ξ' | dist ξ' (f ξ'.shock) ≤ ε}` of the graph of `f`, a weakly closed condition, so `γ` is too;
  these neighbourhoods shrink to the graph. (The plan's variance characterisation is not needed.)
* `justifiedBelief_spotless`: the beliefs justified by an equilibrium are spotless.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- The graph of a function of tomorrow's shock. -/
def shockGraph (f : Z → ↥M.equilibriumStates) : Set ↥M.equilibriumStates :=
  {ξ' | ξ' = f ξ'.1.shock}

/-- **Spotless beliefs**: concentrated on the graph of a function of tomorrow's shock. -/
def spotless : Set (ProbabilityMeasure ↥M.equilibriumStates) :=
  {γ | ∃ f : Z → ↥M.equilibriumStates,
    (γ : Measure ↥M.equilibriumStates) (M.shockGraph f) = 1}

theorem continuous_comp_shock {X : Type*} [TopologicalSpace X] (f : Z → X) :
    Continuous fun ξ' : ↥M.equilibriumStates => f ξ'.1.shock :=
  (continuous_of_discreteTopology (f := fun s : AggShock Z => f s.val)).comp
    (KSState.continuous_shock.comp continuous_subtype_val)

/-- **The spotless beliefs form a closed set.** -/
theorem isClosed_spotless : IsClosed M.spotless := by
  let _ := TopologicalSpace.metrizableSpaceMetric ↥M.equilibriumStates
  -- closed neighbourhoods of a graph
  set T : (Z → ↥M.equilibriumStates) → ℕ → Set ↥M.equilibriumStates :=
    fun f n => {ξ' | dist ξ' (f ξ'.1.shock) ≤ 1 / ((n : ℝ) + 1)} with hT
  have hTc : ∀ f n, IsClosed (T f n) := fun f n =>
    isClosed_le (continuous_id.dist (M.continuous_comp_shock f)) continuous_const
  have hgraph : ∀ f, M.shockGraph f = ⋂ n, T f n := by
    intro f
    ext ξ'
    simp only [shockGraph, mem_ofPred_eq, mem_iInter, hT]
    constructor
    · intro h n
      rw [← h, dist_self]
      positivity
    · intro h
      refine dist_le_zero.1 (le_of_forall_pos_le_add fun ε hε => ?_)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      rw [zero_add]
      exact (h n).trans hn.le
  refine IsSeqClosed.isClosed fun γs γ hmem hlim => ?_
  choose f hf using hmem
  obtain ⟨f₀, φ, hφ, hfl⟩ := CompactSpace.tendsto_subseq f
  refine ⟨f₀, ?_⟩
  have hTn : ∀ n, (γ : Measure ↥M.equilibriumStates) (T f₀ n) = 1 := by
    intro n
    refine (MarkovEquilibrium.isClosed_measure_eq_one (hTc f₀ n)).mem_of_tendsto
      (hlim.comp hφ.tendsto_atTop) ?_
    have hclose : ∀ᶠ k in atTop, ∀ z, dist (f (φ k) z) (f₀ z) < 1 / ((n : ℝ) + 1) := by
      rw [eventually_all]
      intro z
      exact (tendsto_pi_nhds.1 hfl z).eventually (ball_mem_nhds _ Nat.one_div_pos_of_nat)
    filter_upwards [hclose] with k hk
    refine MarkovEquilibrium.measure_eq_one_mono (fun ξ' hξ' => ?_) (hf (φ k))
    change dist ξ' (f₀ ξ'.1.shock) ≤ 1 / ((n : ℝ) + 1)
    have h : ξ' = f (φ k) ξ'.1.shock := hξ'
    have e : dist ξ' (f₀ ξ'.1.shock) = dist (f (φ k) ξ'.1.shock) (f₀ ξ'.1.shock) :=
      congrArg (fun y => dist y (f₀ ξ'.1.shock)) h
    rw [e]
    exact (hk _).le
  rw [hgraph, ← prob_compl_eq_zero_iff (isClosed_iInter (hTc f₀)).measurableSet, compl_iInter]
  exact measure_iUnion_null fun n =>
    (prob_compl_eq_zero_iff (hTc f₀ n).measurableSet).2 (hTn n)

/-- **Justified beliefs are spotless.** -/
theorem justifiedBelief_spotless (z : Z) (μ : ProbabilityMeasure M.AState) {K : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium z (μ : Measure M.AState) K) :
    M.justifiedBelief z μ hK ∈ M.spotless := by
  refine ⟨fun z' => ⟨M.nodeState z μ K [z'], M.nodeState_mem z μ hK [z']⟩, ?_⟩
  change (∑ z', ENNReal.ofReal (M.aggProb z z') • Measure.dirac
    (⟨M.nodeState z μ K [z'], M.nodeState_mem z μ hK [z']⟩ : ↥M.equilibriumStates)) _ = 1
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  have hmem : ∀ z', (⟨M.nodeState z μ K [z'], M.nodeState_mem z μ hK [z']⟩ :
      ↥M.equilibriumStates) ∈ M.shockGraph
        (fun z' => ⟨M.nodeState z μ K [z'], M.nodeState_mem z μ hK [z']⟩) := fun z' => rfl
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (hmem _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun z' _ => M.aggProb_nonneg z z', M.aggProb_sum,
    ENNReal.ofReal_one]

end KSModel

end KrusellSmith

end LeanEconomics
