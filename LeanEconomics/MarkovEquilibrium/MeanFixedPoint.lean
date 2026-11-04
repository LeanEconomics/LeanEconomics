/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.MarkovEquilibrium.Measures
import LeanEconomics.FixedPoint.FanGlicksberg

/-!
# The DGMM correspondence and its fixed point

Milestone S2 of `KrusellSmith/STATIONARITY_PLAN.md` (Duffie, Geanakoplos, Mas-Colell and McLennan
1994, proof of Theorem 1.1, steps 2–3). `J` is a compact metrizable space and
`G : J → Set (P(J))` has closed graph `Gr G` and nonempty values. A measure `ν` on `J × P(J)` is
*supported on the graph* if `ν (Gr G) = 1`. DGMM's correspondence on `P(J)` is
`Φ(μ) = {E (m₂ ν) : ν supported on the graph, m₁ ν = μ}`, with `m₁, m₂` the marginals and `E` the
mean (`Measures.lean`).

* **Nonemptiness** (`exists_supported`): every `μ` is the first marginal of a measure supported on
  the graph. DGMM use density of finitely supported measures; we instead push `μ` forward along
  measurable selections that are exact up to `ε` in the state (pick a point of `G` at each point of
  a countable dense set, use it on the first ball containing the state), and take a limit point:
  closed thickenings of the graph are weakly closed conditions, and they shrink to the graph.
* **Convexity** (mixtures of supporting measures) and **closed graph** (the graph of `Φ` is a
  continuous image of the compact set of supporting measures), in the embedding of `P(J)` into
  `(J →ᵇ ℝ≥0) → ℝ`.
* **The fixed point** (`exists_mean_fixedPoint`, Fan–Glicksberg): there is a measure `ν` supported
  on the graph with `m₁ ν = E (m₂ ν)`.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction TopologicalSpace
open scoped ENNReal NNReal

namespace LeanEconomics.MarkovEquilibrium

/-! ### Mixtures commute with push-forwards and the mean -/

section MixLemmas

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem mix_apply (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ρ σ : ProbabilityMeasure α) (A : Set α) :
    (mix t ht ρ σ : Measure α) A
      = ENNReal.ofReal t * (ρ : Measure α) A + ENNReal.ofReal (1 - t) * (σ : Measure α) A := by
  rw [coe_mix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul]

theorem lintegral_mix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ρ σ : ProbabilityMeasure α)
    (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂(mix t ht ρ σ : Measure α)
      = ENNReal.ofReal t * ∫⁻ x, g x ∂(ρ : Measure α)
        + ENNReal.ofReal (1 - t) * ∫⁻ x, g x ∂(σ : Measure α) := by
  rw [coe_mix, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul,
    smul_eq_mul]

theorem map_mix {f : α → β} (hf : Measurable f) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (ρ σ : ProbabilityMeasure α) :
    (mix t ht ρ σ).map f = mix t ht (ρ.map f) (σ.map f) := by
  apply Subtype.ext
  change ((mix t ht ρ σ : Measure α)).map f = (mix t ht (ρ.map f) (σ.map f) : Measure β)
  rw [coe_mix, coe_mix, Measure.map_add _ _ hf, Measure.map_smul, Measure.map_smul]
  all_goals first | rfl | exact hf.aemeasurable

theorem mix_self (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ρ : ProbabilityMeasure α) : mix t ht ρ ρ = ρ := by
  apply Subtype.ext
  change (mix t ht ρ ρ : Measure α) = ρ
  rw [coe_mix, ← add_smul, ← ENNReal.ofReal_add ht.1 (sub_nonneg.2 ht.2), add_sub_cancel,
    ENNReal.ofReal_one, one_smul]

theorem mix_apply_eq_one (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) {ρ σ : ProbabilityMeasure α} {A : Set α}
    (hρ : (ρ : Measure α) A = 1) (hσ : (σ : Measure α) A = 1) : (mix t ht ρ σ : Measure α) A = 1 := by
  rw [mix_apply, hρ, hσ, mul_one, mul_one, ← ENNReal.ofReal_add ht.1 (sub_nonneg.2 ht.2),
    add_sub_cancel, ENNReal.ofReal_one]

end MixLemmas

variable {J : Type*} [TopologicalSpace J] [MeasurableSpace J] [BorelSpace J]

omit [TopologicalSpace J] [BorelSpace J] in
theorem mean_apply (η : ProbabilityMeasure (ProbabilityMeasure J)) {A : Set J}
    (hA : MeasurableSet A) :
    (mean η : Measure J) A = ∫⁻ ρ, (ρ : Measure J) A ∂(η : Measure (ProbabilityMeasure J)) :=
  Measure.bind_apply hA measurable_toMeasureFn.aemeasurable

omit [TopologicalSpace J] [BorelSpace J] in
/-- **The mean of a mixture is the mixture of the means.** -/
theorem mean_mix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (η θ : ProbabilityMeasure (ProbabilityMeasure J)) :
    mean (mix t ht η θ) = mix t ht (mean η) (mean θ) := by
  apply Subtype.ext
  ext A hA
  change (mean (mix t ht η θ) : Measure J) A = (mix t ht (mean η) (mean θ) : Measure J) A
  rw [mean_apply _ hA, lintegral_mix, mix_apply, mean_apply _ hA, mean_apply _ hA]

/-! ### Measures supported on a closed set -/

/-- Being supported on a closed set is a weakly closed condition. -/
theorem isClosed_measure_eq_one [HasOuterApproxClosed J] {F : Set J} (hF : IsClosed F) :
    IsClosed {ρ : ProbabilityMeasure J | (ρ : Measure J) F = 1} := by
  have e : {ρ : ProbabilityMeasure J | (ρ : Measure J) F = 1}
      = (fun ρ : ProbabilityMeasure J => (ρ : Measure J) Fᶜ) ⁻¹' Iic 0 := by
    ext ρ
    simp only [mem_ofPred_eq, mem_preimage, mem_Iic, nonpos_iff_eq_zero]
    exact (prob_compl_eq_zero_iff hF.measurableSet).symm
  rw [e]
  exact (lowerSemicontinuous_measure_open hF.isOpen_compl).isClosed_preimage 0

omit [TopologicalSpace J] [BorelSpace J] in
theorem measure_eq_one_mono {ρ : ProbabilityMeasure J} {A B : Set J} (hAB : A ⊆ B)
    (hA : (ρ : Measure J) A = 1) : (ρ : Measure J) B = 1 :=
  le_antisymm prob_le_one (hA ▸ measure_mono hAB)

/-- The graph of a correspondence. -/
def graphSet (G : J → Set (ProbabilityMeasure J)) : Set (J × ProbabilityMeasure J) :=
  {p | p.2 ∈ G p.1}

/-! ### Nonemptiness: approximate selections and a limit point -/

section Selection

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The graph thickened by `ε` in the state coordinate. -/
def thickGraph (Gr : Set (M × ProbabilityMeasure M)) (ε : ℝ) : Set (M × ProbabilityMeasure M) :=
  {p | ∃ x, dist p.1 x ≤ ε ∧ (x, p.2) ∈ Gr}

omit [CompactSpace M] [BorelSpace M] in
theorem thickGraph_mono (Gr : Set (M × ProbabilityMeasure M)) {ε δ : ℝ} (h : ε ≤ δ) :
    thickGraph Gr ε ⊆ thickGraph Gr δ :=
  fun _ ⟨x, hx, hxg⟩ => ⟨x, hx.trans h, hxg⟩

theorem isClosed_thickGraph {Gr : Set (M × ProbabilityMeasure M)} (hGr : IsClosed Gr) (ε : ℝ) :
    IsClosed (thickGraph Gr ε) := by
  set C : Set (M × M × ProbabilityMeasure M) := {q | dist q.1 q.2.1 ≤ ε ∧ (q.2.1, q.2.2) ∈ Gr}
  have hC : IsCompact C :=
    ((isClosed_le (continuous_fst.dist (continuous_fst.comp continuous_snd)) continuous_const).inter
      (hGr.preimage ((continuous_fst.comp continuous_snd).prodMk
        (continuous_snd.comp continuous_snd)))).isCompact
  have e : thickGraph Gr ε = (fun q : M × M × ProbabilityMeasure M => (q.1, q.2.2)) '' C := by
    ext ⟨s, g⟩
    constructor
    · rintro ⟨x, hx, hxg⟩
      exact ⟨(s, x, g), ⟨hx, hxg⟩, rfl⟩
    · rintro ⟨⟨s', x, g'⟩, ⟨hx, hxg⟩, h⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨x, hx, hxg⟩
  rw [e]
  exact (hC.image (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).isClosed

omit [CompactSpace M] in
/-- The thickenings shrink to the (closed) graph. -/
theorem mem_of_forall_thickGraph {Gr : Set (M × ProbabilityMeasure M)} (hGr : IsClosed Gr)
    {p : M × ProbabilityMeasure M} (h : ∀ n : ℕ, p ∈ thickGraph Gr (1 / ((n : ℝ) + 1))) :
    p ∈ Gr := by
  choose x hx hxg using h
  have hlim : Tendsto x atTop (𝓝 p.1) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => by rw [dist_comm]; exact hx n)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact hGr.mem_of_tendsto (hlim.prodMk_nhds tendsto_const_nhds) (Eventually.of_forall hxg)

/-- **Approximate selections**: `μ` pushed forward along a measurable selection that is exact up to
`ε` in the state. -/
theorem exists_approx_supported {G : M → Set (ProbabilityMeasure M)}
    (hGr : IsClosed (graphSet G)) (hne : ∀ s, (G s).Nonempty)
    (μ : ProbabilityMeasure M) {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : ProbabilityMeasure (M × ProbabilityMeasure M),
      marginalFst ν = μ ∧ (ν : Measure _) (thickGraph (graphSet G) ε) = 1 := by
  classical
  have : Nonempty M := nonempty_of_isProbabilityMeasure (μ : Measure M)
  obtain ⟨xs, hxs⟩ := TopologicalSpace.exists_dense_seq M
  have hcov : ∀ s, ∃ n, s ∈ Metric.ball (xs n) ε := fun s => by
    obtain ⟨n, hn⟩ := hxs.exists_dist_lt s hε
    exact ⟨n, by rw [Metric.mem_ball]; exact hn⟩
  set idx : M → ℕ := fun s => Nat.find (hcov s)
  have hidx : Measurable idx := measurable_find hcov fun k => measurableSet_ball
  set g : ℕ → ProbabilityMeasure M := fun n => (hne (xs n)).some
  set σ : M → M × ProbabilityMeasure M := fun s => (s, g (idx s))
  have hσ : Measurable σ := measurable_id.prodMk ((measurable_from_nat (f := g)).comp hidx)
  refine ⟨μ.map σ, ?_, ?_⟩
  · apply Subtype.ext
    change ((μ : Measure M).map σ).map Prod.fst = (μ : Measure M)
    rw [Measure.map_map measurable_fst hσ]
    exact Measure.map_id
  · change ((μ : Measure M).map σ) _ = 1
    rw [Measure.map_apply hσ (isClosed_thickGraph hGr ε).measurableSet]
    have : σ ⁻¹' thickGraph (graphSet G) ε = univ := by
      refine eq_univ_of_forall fun s => ⟨xs (idx s), ?_, (hne (xs (idx s))).some_mem⟩
      exact (Metric.mem_ball.1 (Nat.find_spec (hcov s))).le
    rw [this, measure_univ]

/-- **Nonemptiness** (metric version): a limit point of the approximate selections. -/
theorem exists_supported_of_metric {G : M → Set (ProbabilityMeasure M)}
    (hGr : IsClosed (graphSet G)) (hne : ∀ s, (G s).Nonempty) (μ : ProbabilityMeasure M) :
    ∃ ν : ProbabilityMeasure (M × ProbabilityMeasure M),
      marginalFst ν = μ ∧ (ν : Measure _) (graphSet G) = 1 := by
  choose ν hν₁ hν₂ using fun n : ℕ =>
    exists_approx_supported hGr hne μ (ε := 1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  obtain ⟨ν₀, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq ν
  refine ⟨ν₀, ?_, ?_⟩
  · have h := (continuous_marginalFst.tendsto ν₀).comp hlim
    have hc : (marginalFst ∘ ν ∘ φ) = fun _ => μ := funext fun k => hν₁ (φ k)
    rw [hc] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · have hT : ∀ n : ℕ, (ν₀ : Measure _) (thickGraph (graphSet G) (1 / ((n : ℝ) + 1))) = 1 := by
      intro n
      refine (isClosed_measure_eq_one (isClosed_thickGraph hGr _)).mem_of_tendsto hlim ?_
      filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop n] with k hk
      exact measure_eq_one_mono (thickGraph_mono _ (Nat.one_div_le_one_div hk)) (hν₂ (φ k))
    rw [← prob_compl_eq_zero_iff hGr.measurableSet]
    refine measure_mono_null (t := ⋃ n : ℕ, (thickGraph (graphSet G) (1 / ((n : ℝ) + 1)))ᶜ)
      ?_ (measure_iUnion_null fun n =>
        (prob_compl_eq_zero_iff (isClosed_thickGraph hGr _).measurableSet).2 (hT n))
    intro p hp
    by_contra h
    simp only [mem_iUnion, mem_compl_iff, not_exists, not_not] at h
    exact hp (mem_of_forall_thickGraph hGr h)

end Selection

/-! ### The correspondence and its fixed point -/

variable [MetrizableSpace J] [CompactSpace J]

/-- **Nonemptiness**: every `μ` is the first marginal of a measure supported on the graph. -/
theorem exists_supported {G : J → Set (ProbabilityMeasure J)} (hGr : IsClosed (graphSet G))
    (hne : ∀ s, (G s).Nonempty) (μ : ProbabilityMeasure J) :
    ∃ ν : ProbabilityMeasure (J × ProbabilityMeasure J),
      marginalFst ν = μ ∧ (ν : Measure _) (graphSet G) = 1 := by
  let _ := TopologicalSpace.metrizableSpaceMetric J
  exact exists_supported_of_metric hGr hne μ

/-- **DGMM's correspondence** `Φ(μ) = {E (m₂ ν) : ν (Gr G) = 1, m₁ ν = μ}`, in the embedding. -/
def Phi (G : J → Set (ProbabilityMeasure J)) (x : (J →ᵇ ℝ≥0) → ℝ) : Set ((J →ᵇ ℝ≥0) → ℝ) :=
  {y | ∃ ν : ProbabilityMeasure (J × ProbabilityMeasure J), (ν : Measure _) (graphSet G) = 1 ∧
    embed (marginalFst ν) = x ∧ embed (mean (marginalSnd ν)) = y}

theorem Phi_nonempty {G : J → Set (ProbabilityMeasure J)} (hGr : IsClosed (graphSet G))
    (hne : ∀ s, (G s).Nonempty) {x : (J →ᵇ ℝ≥0) → ℝ} (hx : x ∈ range embed) :
    (Phi G x).Nonempty := by
  obtain ⟨μ, rfl⟩ := hx
  obtain ⟨ν, hν₁, hν₂⟩ := exists_supported hGr hne μ
  exact ⟨_, ν, hν₂, by rw [hν₁], rfl⟩

omit [BorelSpace J] [MetrizableSpace J] [CompactSpace J] in
theorem Phi_subset (G : J → Set (ProbabilityMeasure J)) (x : (J →ᵇ ℝ≥0) → ℝ) :
    Phi G x ⊆ range embed := by
  rintro _ ⟨ν, -, -, rfl⟩
  exact ⟨_, rfl⟩

omit [BorelSpace J] [MetrizableSpace J] [CompactSpace J] in
theorem convex_Phi (G : J → Set (ProbabilityMeasure J)) (x : (J →ᵇ ℝ≥0) → ℝ) :
    Convex ℝ (Phi G x) := by
  rintro _ ⟨ν₁, h₁, hx₁, rfl⟩ _ ⟨ν₂, h₂, hx₂, rfl⟩ a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  have ht : a ∈ Icc (0 : ℝ) 1 := ⟨ha, by linarith⟩
  refine ⟨mix a ht ν₁ ν₂, mix_apply_eq_one a ht h₁ h₂, ?_, ?_⟩
  · rw [marginalFst, map_mix measurable_fst, embed_mix]
    change a • embed (marginalFst ν₁) + (1 - a) • embed (marginalFst ν₂) = x
    rw [hx₁, hx₂]
    exact Convex.combo_self (by linarith) x
  · rw [marginalSnd, map_mix measurable_snd, mean_mix, embed_mix]
    rfl

/-- The supporting measures form a compact set. -/
theorem isCompact_supported (G : J → Set (ProbabilityMeasure J)) (hGr : IsClosed (graphSet G)) :
    IsCompact {ν : ProbabilityMeasure (J × ProbabilityMeasure J) | (ν : Measure _) (graphSet G) = 1} :=
  (isClosed_measure_eq_one hGr).isCompact

/-- **Closed graph**: the graph of `Φ` is a continuous image of the compact supporting measures. -/
theorem isClosed_graphOn_Phi (G : J → Set (ProbabilityMeasure J)) (hGr : IsClosed (graphSet G)) :
    IsClosed (FixedPoint.graphOn (range embed) (Phi G)) := by
  have e : FixedPoint.graphOn (range embed) (Phi G)
      = (fun ν : ProbabilityMeasure (J × ProbabilityMeasure J) =>
          (embed (marginalFst ν), embed (mean (marginalSnd ν))))
        '' {ν | (ν : Measure _) (graphSet G) = 1} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨-, ν, hν, hx, hy⟩
      exact ⟨ν, hν, Prod.ext hx hy⟩
    · rintro ⟨ν, hν, h⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨_, rfl⟩, ν, hν, rfl, rfl⟩
  rw [e]
  exact ((isCompact_supported G hGr).image
    ((continuous_embed.comp continuous_marginalFst).prodMk
      (continuous_embed.comp (continuous_mean.comp continuous_marginalSnd)))).isClosed

/-- **The DGMM fixed point** (Fan–Glicksberg): a measure on `J × P(J)` supported on the graph of
`G` whose first marginal is the mean of its second marginal. -/
theorem exists_mean_fixedPoint [Nonempty J] {G : J → Set (ProbabilityMeasure J)}
    (hGr : IsClosed (graphSet G)) (hne : ∀ s, (G s).Nonempty) :
    ∃ ν : ProbabilityMeasure (J × ProbabilityMeasure J),
      (ν : Measure _) (graphSet G) = 1 ∧ marginalFst ν = mean (marginalSnd ν) := by
  obtain ⟨j⟩ := ‹Nonempty J›
  obtain ⟨x, -, ν, hν, hx, hy⟩ := FixedPoint.fanGlicksberg isCompact_range_embed convex_range_embed
    ⟨embed (⟨Measure.dirac j, inferInstance⟩ : ProbabilityMeasure J), _, rfl⟩
    (fun x hx => Phi_nonempty hGr hne hx) (fun x _ => convex_Phi G x)
    (fun x _ => Phi_subset G x) (isClosed_graphOn_Phi G hGr)
  exact ⟨ν, hν, embed_injective (hx.trans hy.symm)⟩

end LeanEconomics.MarkovEquilibrium
