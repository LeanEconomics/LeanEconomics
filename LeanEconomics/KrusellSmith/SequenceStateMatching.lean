/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.SequenceStateSynchronization

/-!
# Matched expectations on the sequence state

Milestone LS3 of `LEE_MATCHING_PLAN.md`: when is the continuation the matched-expectations-path
(MEP) method uses correct?

Along a simulated path the economy is at histories `ω_t`. For a counterfactual next shock `z'`
the household needs the continuation at the branch `cons z' ω_t`, which the path never visits.
MEP takes it from a date `s` on the path with `z_s = z'` and `K_s` close to the branch's capital.

* **The branch's capital is known** (`integral_assets_cons`): capital at `cons z' ω` is mean
  saving at `ω`, whatever `z'`, so the matching key is computed without the counterfactual
  distribution.
* **Exact matching** (`matching_exact_*`): if the matched history has the branch's shock and
  distribution and the sequential equilibrium from there is unique, the matched continuation
  (prices on the future, tomorrow's distributions, value, saving) is the branch's.
* **Matching on capital within a spell** (`eq_of_capital_eq_of_orbit`, Lee Theorem 1): if both
  distributions lie on one orbit (with its limit) along which capital is strictly monotone,
  equal capital means equal distribution, hence (with uniqueness there) equal continuation.
* **Approximate matching** (`matching_seqPolicy`, `matching_seqValue`, Lee Theorem 2): under
  uniqueness and a contracting law of motion, measured through a continuous injective `ι`, for
  every `ε > 0` there is `T₀` such that whenever the matched history agrees with the branch over
  its last `T + 1 ≥ T₀ + 1` shocks, the saving policy and the value differ by less than `ε` at
  every household state. The bound on distributions (`c ^ T * D`) is turned into one on value
  and policy by uniform continuity on the compact space of distributions
  (`exists_uniform_of_embedding`); no Lipschitz bound is needed.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

/-- **Closeness through a continuous injection controls a continuous function uniformly.** On a
compact space `P`, a continuous injection `ι` into a metric space and a continuous `G` on
`P × Y`, `Y` compact: `ι`-close points give `G`-values close uniformly in `y`. -/
theorem exists_uniform_of_embedding {P Y X : Type*} [TopologicalSpace P] [CompactSpace P]
    [TopologicalSpace Y] [CompactSpace Y] [MetricSpace X] {ι : P → X} (hc : Continuous ι)
    (hi : Function.Injective ι) {G : P × Y → ℝ} (hG : Continuous G) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ μ ν : P, dist (ι μ) (ι ν) < δ → ∀ y, |G (μ, y) - G (ν, y)| < ε := by
  let e := (hc.isClosedEmbedding hi).isEmbedding.toHomeomorph
  have : CompactSpace (range ι) := isCompact_iff_compactSpace.1 (isCompact_range hc)
  let H : C(P, C(Y, ℝ)) := ContinuousMap.curry ⟨G, hG⟩
  have hu := CompactSpace.uniformContinuous_of_continuous (H.continuous.comp e.symm.continuous)
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1 hu ε hε
  refine ⟨δ, hδ, fun μ ν h y => ?_⟩
  have h1 := hδε (a := e μ) (b := e ν) h
  simp only [Function.comp, Homeomorph.symm_apply_apply] at h1
  have h2 := (ContinuousMap.dist_apply_le_dist (f := H μ) (g := H ν) y).trans_lt h1
  rwa [ContinuousMap.curry_apply, ContinuousMap.curry_apply, Real.dist_eq] at h2

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **The recursive value**: the value at `(a, e)` when the aggregate state is `(z, μ)`. -/
noncomputable def recursiveValue (z : Z) (μ : ProbabilityMeasure M.AState) (x : M.AState) : ℝ :=
  (M.household z (M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ))).valueFunction
    (x.1, ⟨x.2.idio, []⟩)

variable {M}

/-- **The recursive value is jointly continuous** in the distribution and the household's state,
under uniqueness. -/
theorem continuous_recursiveValue (hU : M.UniqueSequentialEquilibrium) (z : Z) :
    Continuous fun p : ProbabilityMeasure M.AState × M.AState => M.recursiveValue z p.1 p.2 := by
  have hpath : Continuous fun p : ProbabilityMeasure M.AState × M.AState =>
      M.pricePath z (M.initMass (p.1 : Measure M.AState)) (M.eqPath z p.1) :=
    Continuous.comp (g := fun q : ProbabilityMeasure M.AState × (List Z → ℝ) =>
        M.pricePath z (M.initMass (q.1 : Measure M.AState)) q.2)
      (f := fun p : ProbabilityMeasure M.AState × M.AState => (p.1, M.eqPath z p.1))
      (M.continuous_pricePath_joint z)
      (continuous_fst.prodMk ((continuous_eqPath hU z).comp continuous_fst))
  have hlab : Continuous fun i : Idio E => (⟨i.idio, []⟩ : Label Z E) :=
    continuous_of_discreteTopology
  have hstate : Continuous fun p : ProbabilityMeasure M.AState × M.AState =>
      ((p.2.1, ⟨p.2.2.idio, []⟩) : M.State) :=
    (continuous_fst.comp continuous_snd).prodMk (hlab.comp (continuous_snd.comp continuous_snd))
  exact Continuous.comp
    (g := fun q : (List Z → ℝ × ℝ) × M.State => (M.household z q.1).valueFunction q.2)
    (f := fun p : ProbabilityMeasure M.AState × M.AState =>
      (M.pricePath z (M.initMass (p.1 : Measure M.AState)) (M.eqPath z p.1),
        ((p.2.1, ⟨p.2.2.idio, []⟩) : M.State)))
    (M.continuous_valueFunction_joint z) (hpath.prodMk hstate)

variable {μ : History Z → ProbabilityMeasure M.AState}

/-- **The value is the recursive value** of today's shock and distribution, under uniqueness. -/
theorem IsSeqStateEquilibrium.seqValue_eq_recursiveValue (hμ : M.IsSeqStateEquilibrium μ)
    (hU : M.UniqueSequentialEquilibrium) (ω : History Z) (a : ↥(Icc (0 : ℝ) M.assetCap))
    (e : E) : M.seqValue μ ω a e = M.recursiveValue (ω 0) (μ ω) (a, ⟨e⟩) := by
  rw [recursiveValue, ← hμ.seqCapital_eq_eqPath hU ω, hμ.pricePath_eq ω]
  rfl

/-! ### The matching key -/

/-- **Capital at a branch is mean saving today**, whatever the new shock: the matching key is
known without the branch's distribution. -/
theorem IsSeqStateEquilibrium.integral_assets_cons (hμ : M.IsSeqStateEquilibrium μ)
    (ω : History Z) (z' : Z) :
    ∫ x, M.assets x ∂(μ (History.cons z' ω) : Measure M.AState)
      = ∫ x, (M.seqPolicy μ ω x.1 x.2.idio : ℝ) ∂(μ ω : Measure M.AState) :=
  hμ.toRecursive.capital_cons ω z'

/-! ### Exact matching -/

section Exact

variable (hμ : M.IsSeqStateEquilibrium μ) {ω ω' : History Z} (hz : ω 0 = ω' 0)
  (hd : μ ω = μ ω') (hU : M.UniqueFrom (ω 0) (μ ω))
include hμ hz hd hU

/-- **Exact matching, saving**: a matched history with the branch's shock and distribution, and a
unique sequential equilibrium there, has the branch's saving policy. -/
theorem IsSeqStateEquilibrium.matching_exact_seqPolicy : M.seqPolicy μ ω = M.seqPolicy μ ω' :=
  hμ.markov_seqPolicy hz hd hU

/-- **Exact matching, value.** -/
theorem IsSeqStateEquilibrium.matching_exact_seqValue : M.seqValue μ ω = M.seqValue μ ω' :=
  hμ.markov_seqValue hz hd hU

/-- **Exact matching, distributions on the future**: the matched history and the branch generate
the same distributions after every finite sequence of shocks. -/
theorem IsSeqStateEquilibrium.matching_exact_prepend (g : List Z) :
    μ (History.prepend g ω) = μ (History.prepend g ω') := by
  have hP := hμ.markov_seqPrices hz hd hU
  have h1 := hμ.nodeDist_eq ω g
  have h2 := hμ.nodeDist_eq ω' g
  rw [hP, hz, hd] at h1
  exact ProbabilityMeasure.toMeasure_injective (h1.symm.trans h2)

end Exact

/-! ### Matching on capital within a spell -/

variable (M) in
/-- Aggregate capital of a distribution. -/
noncomputable def capitalOf (ν : ProbabilityMeasure M.AState) : ℝ :=
  ∫ x, M.assets x ∂(ν : Measure M.AState)

/-- **Within a spell, equal capital means equal distribution** (Lee, Theorem 1): if the two
distributions lie on one orbit (with its limit) along which capital is strictly monotone and
converges, they are equal. -/
theorem eq_of_capital_eq_of_orbit {Φ : ℕ → ProbabilityMeasure M.AState}
    {Φcs : ProbabilityMeasure M.AState}
    (hmono : StrictMono (M.capitalOf ∘ Φ) ∨ StrictAnti (M.capitalOf ∘ Φ))
    (hlim : Tendsto (M.capitalOf ∘ Φ) atTop (𝓝 (M.capitalOf Φcs)))
    {ν ν' : ProbabilityMeasure M.AState} (hν : ν ∈ range Φ ∪ {Φcs})
    (hν' : ν' ∈ range Φ ∪ {Φcs}) (hK : M.capitalOf ν = M.capitalOf ν') : ν = ν' := by
  rcases hmono with hm | hm
  · exact injOn_orbit_of_strictMono hm hlim hν hν' hK
  · exact injOn_orbit_of_strictAnti hm hlim hν hν' hK

/-- **Matching on capital within a spell is exact**: with the distributions at `ω` and `ω'` on one
capital-monotone orbit, the same shock and the same capital, and a unique sequential equilibrium
there, the saving policies agree. -/
theorem IsSeqStateEquilibrium.matching_capital_seqPolicy (hμ : M.IsSeqStateEquilibrium μ)
    {Φ : ℕ → ProbabilityMeasure M.AState} {Φcs : ProbabilityMeasure M.AState}
    (hmono : StrictMono (M.capitalOf ∘ Φ) ∨ StrictAnti (M.capitalOf ∘ Φ))
    (hlim : Tendsto (M.capitalOf ∘ Φ) atTop (𝓝 (M.capitalOf Φcs)))
    {ω ω' : History Z} (hω : μ ω ∈ range Φ ∪ {Φcs}) (hω' : μ ω' ∈ range Φ ∪ {Φcs})
    (hz : ω 0 = ω' 0) (hK : M.capitalOf (μ ω) = M.capitalOf (μ ω'))
    (hU : M.UniqueFrom (ω 0) (μ ω)) : M.seqPolicy μ ω = M.seqPolicy μ ω' :=
  hμ.markov_seqPolicy hz (eq_of_capital_eq_of_orbit hmono hlim hω hω' hK) hU

/-! ### Approximate matching -/

section Approximate

variable {X : Type*} [MetricSpace X] {ι : ProbabilityMeasure M.AState → X} {c D : ℝ}
  (hμ : M.IsSeqStateEquilibrium μ) (hU : M.UniqueSequentialEquilibrium)
  (hc : Continuous ι) (hι : Function.Injective ι) (h : M.LawContraction ι univ c D)
include hμ hU hc hι h

omit hμ hU in
/-- For each continuous recursive object, a depth `T₁` beyond which `c ^ T * D`-close
distributions give values within `ε`, uniformly in the household's state. -/
theorem LawContraction.exists_depth {G : Z → ProbabilityMeasure M.AState × M.AState → ℝ}
    (hG : ∀ z, Continuous (G z)) {ε : ℝ} (hε : 0 < ε) (z : Z) :
    ∃ T₁ : ℕ, ∀ T ≥ T₁, ∀ ν ν' : ProbabilityMeasure M.AState,
      dist (ι ν) (ι ν') ≤ c ^ T * D → ∀ x, |G z (ν, x) - G z (ν', x)| < ε := by
  obtain ⟨δ, hδ, hδε⟩ := exists_uniform_of_embedding hc hι (hG z) hε
  have hlim : Tendsto (fun T : ℕ => c ^ T * D) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one h.rate_nonneg h.rate_lt_one).mul_const D
    rwa [zero_mul] at this
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 δ hδ)
  exact ⟨T₁, fun T hT ν ν' hd x => hδε ν ν' (hd.trans_lt (hT₁ T hT)) x⟩

/-- **Approximate matching, saving**: for every `ε > 0` there is a depth `T₀` such that a matched
history agreeing with the branch over its last `T + 1` shocks, `T ≥ T₀`, has saving within `ε` of
the branch's at every household state. -/
theorem IsSeqStateEquilibrium.matching_seqPolicy {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ ω ω' : History Z, (∀ n ≤ T, ω n = ω' n) →
      ∀ a e, |(M.seqPolicy μ ω a e : ℝ) - M.seqPolicy μ ω' a e| < ε := by
  have key := fun z => h.exists_depth hc hι
    (G := fun z p => M.recursivePolicy z p.1 p.2) (continuous_recursivePolicy hU) hε z
  choose T₁ hT₁ using key
  refine ⟨Finset.univ.sup T₁, fun T hT ω ω' hag a e => ?_⟩
  have h0 : ω 0 = ω' 0 := hag 0 (Nat.zero_le _)
  rw [hμ.seqPolicy_eq_recursivePolicy hU, hμ.seqPolicy_eq_recursivePolicy hU, ← h0]
  exact hT₁ (ω 0) T ((Finset.le_sup (Finset.mem_univ _)).trans hT) _ _
    (hμ.dist_le_of_agree hU hι h (fun _ => mem_univ _) T hag) _

/-- **Approximate matching, value.** -/
theorem IsSeqStateEquilibrium.matching_seqValue {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ ω ω' : History Z, (∀ n ≤ T, ω n = ω' n) →
      ∀ a e, |M.seqValue μ ω a e - M.seqValue μ ω' a e| < ε := by
  have key := fun z => h.exists_depth hc hι
    (G := fun z p => M.recursiveValue z p.1 p.2) (continuous_recursiveValue hU) hε z
  choose T₁ hT₁ using key
  refine ⟨Finset.univ.sup T₁, fun T hT ω ω' hag a e => ?_⟩
  have h0 : ω 0 = ω' 0 := hag 0 (Nat.zero_le _)
  rw [hμ.seqValue_eq_recursiveValue hU, hμ.seqValue_eq_recursiveValue hU, ← h0]
  exact hT₁ (ω 0) T ((Finset.le_sup (Finset.mem_univ _)).trans hT) _ _
    (hμ.dist_le_of_agree hU hι h (fun _ => mem_univ _) T hag) _

end Approximate

end KSModel

end KrusellSmith

end LeanEconomics
