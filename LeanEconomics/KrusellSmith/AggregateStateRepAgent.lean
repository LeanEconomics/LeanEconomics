/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.AggregateStateIff

/-!
# `(z, K)` is sufficient without idiosyncratic heterogeneity

Milestone AK5 of `AGGREGATE_STATE_PLAN.md`, the representative-agent case: a single
idiosyncratic state (`[Unique E]`).

* `lawOfMotion_dirac`, `run_dirac`: the law of motion maps point masses to point masses;
* `integral_abs_sub_capAt` (small-share contraction): burning in from a point mass
  (`dist2_run`) puts the equilibrium distribution within `2 (1 + ā) r*ᵀ ω` of a point mass in mean
  absolute deviation, for every `T`, so **every household holds aggregate capital**:
  `ae_assets_eq_capAt`;
* hence capital determines the distribution, **`kInjective_of_unique`**, and `(z, K)` is a
  sufficient state, `kSufficient_of_unique`.

**`minMPC_smallShare_repAgent`**: for CRRA, clamped Cobb–Douglas, small capital shares and an
aggregate chain bounded below, with one idiosyncratic state, the unique sequence-state equilibrium
is represented by a recursive equilibrium on `(z, K)`, whose law of `(z, K)` is the unique ergodic
invariant law on the capital sets — the stochastic growth model.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction TopologicalSpace ProbabilityTheory
open scoped ENNReal NNReal

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

/-- **The law of motion maps point masses to point masses** with one idiosyncratic state. -/
theorem lawOfMotion_dirac [Unique E] (z z' : Z) (x : M.AState) :
    ∃ y : M.AState, M.lawOfMotion z (diracProba x) z' = diracProba y := by
  set K := M.pricePath z (M.initMass (Measure.dirac x)) (M.eqPath z (diracProba x))
  refine ⟨M.nextA z K [] default x, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  change M.pushNode z K [] z' (Measure.dirac x) = Measure.dirac (M.nextA z K [] default x)
  have : IsProbabilityMeasure (M.pushNode z K [] z' (Measure.dirac x)) :=
    M.isProbabilityMeasure_pushNode _ _ _ _ _
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [M.integral_pushNode, integral_dirac, integral_dirac, Fintype.sum_unique]
  have h1 : M.nextProb z [] z' default x = 1 := by
    have := M.idioProb_sum (shockAt z []) z' x.2.idio
    rwa [Fintype.sum_unique] at this
  rw [h1, one_mul]

theorem run_dirac [Unique E] : ∀ (T : ℕ) (ω : History Z) (x : M.AState),
    ∃ y : M.AState, run M.lawMap T ω (diracProba x) = diracProba y
  | 0, _, x => ⟨x, rfl⟩
  | T + 1, ω, x => by
    obtain ⟨y, hy⟩ := run_dirac T (History.tail ω) x
    obtain ⟨y', hy'⟩ := lawOfMotion_dirac (M := M) (ω 1) (ω 0) y
    refine ⟨y', ?_⟩
    change M.lawMap (ω 1) (ω 0) (run M.lawMap T (History.tail ω) (diracProba x)) = _
    rw [hy]
    exact hy'

namespace SlopeContraction

variable {ε : ℝ} (hminor : ∀ z z' e e', ε ≤ M.idioProb z z' e e') (S : M.SlopeContraction)
  {ℓL : ℝ} (hℓL : 0 ≤ ℓL)
  (hRL : ∀ z k L L', |M.grossReturn z k L - M.grossReturn z k L'| ≤ ℓL * |L - L'|)
  (hwL : ∀ z k L L', |M.wage z k L - M.wage z k L'| ≤ ℓL * |L - L'|)
  (hε : 0 < ε) (hκ : S.κ < 1) (hr : S.rate < 1) {μ : History Z → ProbabilityMeasure M.AState}
  (hμ : M.IsSeqStateEquilibrium μ)

include hminor hℓL hRL hwL hε hκ hr hμ in
/-- **No dispersion of assets**: with one idiosyncratic state, the mean absolute deviation of
assets from aggregate capital is zero. -/
theorem integral_abs_sub_capAt [Unique E] (ω : History Z) :
    ∫ x, |(x.1 : ℝ) - capAt μ ω| ∂(μ ω : Measure M.AState) = 0 := by
  set w := S.histWeight ℓL ε
  set r := S.histRate ε
  have hw1 : 1 ≤ w := S.one_le_histWeight hε hκ hℓL
  have hr0 : 0 ≤ r := (S.rate_nonneg hκ).trans (le_max_left _ _)
  have hr1 : r < 1 := S.histRate_lt_one hε hr
  have hA := M.assetCap_pos.le
  set I := ∫ x, |(x.1 : ℝ) - capAt μ ω| ∂(μ ω : Measure M.AState)
  have hI0 : 0 ≤ I := integral_nonneg fun x => abs_nonneg _
  have hcontI : Continuous fun x : M.AState => |(x.1 : ℝ) - capAt μ ω| :=
    ((continuous_subtype_val.comp continuous_fst).sub continuous_const).abs
  have hbound : ∀ T : ℕ, I ≤ 2 * ((1 + M.assetCap) * (r ^ T * w)) := by
    intro T
    let x₀ : M.AState := (⟨0, le_rfl, hA⟩, ⟨default⟩)
    obtain ⟨y, hy⟩ := run_dirac T ω x₀
    obtain ⟨da, dm, hda, hdm, hN, hD⟩ :=
      S.dist2_run hminor hℓL hRL hwL hε hκ hμ T ω (diracProba x₀)
    rw [hy] at hD
    change Dist2 da dm (μ ω : Measure M.AState) (Measure.dirac y) at hD
    -- the deviation from `y`
    set f : M.AState →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨fun x => |(x.1 : ℝ) - y.1|,
        ((continuous_subtype_val.comp continuous_fst).sub continuous_const).abs⟩
    have hf : AssetLip 1 f := by
      intro a b i
      change |(|(a : ℝ) - y.1| - |(b : ℝ) - y.1|)| ≤ 1 * |(a : ℝ) - b|
      rw [one_mul]
      calc _ ≤ |((a : ℝ) - y.1) - ((b : ℝ) - y.1)| := abs_abs_sub_abs_le_abs_sub _ _
        _ = |(a : ℝ) - b| := by ring_nf
    have hosc : ∀ x x', f x - f x' ≤ M.assetCap := by
      intro x x'
      change |(x.1 : ℝ) - y.1| - |(x'.1 : ℝ) - y.1| ≤ M.assetCap
      have h1 : |(x.1 : ℝ) - y.1| ≤ M.assetCap := by
        rw [abs_le]
        constructor <;> linarith [x.1.2.1, x.1.2.2, y.1.2.1, y.1.2.2]
      linarith [abs_nonneg ((x'.1 : ℝ) - y.1)]
    have hdev := hD 1 M.assetCap zero_le_one f hf hosc
    rw [integral_dirac] at hdev
    have hfy : f y = 0 := by
      change |(y.1 : ℝ) - y.1| = 0
      rw [sub_self, abs_zero]
    rw [hfy, sub_zero, one_mul] at hdev
    have hcap := hD.capital
    rw [integral_dirac] at hcap
    change |capAt μ ω - (y.1 : ℝ)| ≤ da + M.assetCap * dm at hcap
    -- `|a − K| ≤ |a − y| + |y − K|`
    have hfi : Integrable (fun x => f x) (μ ω : Measure M.AState) := f.integrable _
    have hadd : ∫ x, (f x + |(y.1 : ℝ) - capAt μ ω|) ∂(μ ω : Measure M.AState)
        = ∫ x, f x ∂(μ ω : Measure M.AState) + |(y.1 : ℝ) - capAt μ ω| := by
      rw [integral_add hfi (integrable_const _), integral_const, probReal_univ, one_smul]
    have hle : I ≤ ∫ x, f x ∂(μ ω : Measure M.AState) + |(y.1 : ℝ) - capAt μ ω| := by
      rw [← hadd]
      refine integral_mono (hcontI.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (hfi.add (integrable_const _)) fun x => ?_
      change |(x.1 : ℝ) - capAt μ ω| ≤ |(x.1 : ℝ) - y.1| + |(y.1 : ℝ) - capAt μ ω|
      exact abs_sub_le _ _ _
    have hfint : ∫ x, f x ∂(μ ω : Measure M.AState) ≤ da + M.assetCap * dm :=
      (le_abs_self _).trans hdev
    rw [abs_sub_comm] at hcap
    have h1 : M.assetCap * dm ≤ M.assetCap * (w * dm) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hdm hw1) hA
    have h2 : 0 ≤ w * dm := mul_nonneg (zero_le_one.trans hw1) hdm
    have h3 : da + M.assetCap * dm ≤ (1 + M.assetCap) * (r ^ T * w) := by
      calc da + M.assetCap * dm ≤ (1 + M.assetCap) * (da + w * dm) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left hN (by linarith)
    linarith
  have hlim : Tendsto (fun T : ℕ => 2 * ((1 + M.assetCap) * (r ^ T * w))) atTop
      (𝓝 (2 * ((1 + M.assetCap) * (0 * w)))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul tendsto_const_nhds))
  rw [zero_mul, mul_zero, mul_zero] at hlim
  exact le_antisymm (ge_of_tendsto' hlim hbound) hI0

include hminor hℓL hRL hwL hε hκ hr hμ in
/-- **Every household holds aggregate capital.** -/
theorem ae_assets_eq_capAt [Unique E] (ω : History Z) :
    ∀ᵐ x ∂(μ ω : Measure M.AState), (x.1 : ℝ) = capAt μ ω := by
  have hcont : Continuous fun x : M.AState => |(x.1 : ℝ) - capAt μ ω| :=
    ((continuous_subtype_val.comp continuous_fst).sub continuous_const).abs
  have h := (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _)
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1
    (S.integral_abs_sub_capAt hminor hℓL hRL hwL hε hκ hr hμ ω)
  filter_upwards [h] with x hx
  exact sub_eq_zero.1 (abs_eq_zero.1 hx)

include hminor hℓL hRL hwL hε hκ hr hμ in
/-- **Capital determines the distribution** with one idiosyncratic state. -/
theorem kInjective_of_unique [Unique E] : KInjective μ := by
  have hpt : ∀ ω : History Z, ∃ x₁ : M.AState, (x₁.1 : ℝ) = capAt μ ω ∧
      ∀ (f : M.AState →ᵇ ℝ), ∫ x, f x ∂(μ ω : Measure M.AState) = f x₁ := by
    intro ω
    have hae := S.ae_assets_eq_capAt hminor hℓL hRL hwL hε hκ hr hμ ω
    obtain ⟨x₁, hx₁⟩ := hae.exists
    refine ⟨x₁, hx₁, fun f => ?_⟩
    have hconst : ∀ᵐ x ∂(μ ω : Measure M.AState), f x = f x₁ := by
      filter_upwards [hae] with x hx
      have : x = x₁ := Prod.ext (Subtype.ext (hx.trans hx₁.symm)) (by
        cases x.2; cases x₁.2; congr 1; exact Subsingleton.elim _ _)
      rw [this]
    rw [integral_congr_ae hconst, integral_const, probReal_univ, one_smul]
  intro ω ω' _ hk
  obtain ⟨x₁, hx₁, h₁⟩ := hpt ω
  obtain ⟨x₂, hx₂, h₂⟩ := hpt ω'
  have hx : x₁ = x₂ := Prod.ext (Subtype.ext (hx₁.trans (hk.trans hx₂.symm))) (by
    cases x₁.2; cases x₂.2; congr 1; exact Subsingleton.elim _ _)
  apply ProbabilityMeasure.toMeasure_injective
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [h₁ f, h₂ f, hx]

include hminor hℓL hRL hwL hε hκ hr hμ in
/-- **`(z, K)` is a sufficient state** with one idiosyncratic state. -/
theorem kSufficient_of_unique [Unique E] : KSufficient μ :=
  KInjective.kSufficient hμ (S.uniqueSequentialEquilibrium hκ)
    (S.kInjective_of_unique hminor hℓL hRL hwL hε hκ hr hμ)

end SlopeContraction

end KSModel

/-! ### The small-share economy with one idiosyncratic state -/

variable [Nonempty Z] [Unique E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ}
  (hγ : 0 < γ) {εZ : ℝ} (hεZ : 0 < εZ) (hminorZ : ∀ z z', εZ ≤ V.aggProb z z')
include hεZ hminorZ

/-- **The stochastic growth model as a recursive equilibrium on `(z, K)`**: with one
idiosyncratic state, CRRA, clamped Cobb–Douglas with `0 ≤ δ < 1` and
`(β (1 − δ))^{1/γ} < 1 − δ`, the aggregate chain bounded below and small capital shares, the
unique sequence-state equilibrium satisfies `KSufficient` and is represented by a recursive
equilibrium on `(z, K)`; the capital sets are compact, the law of motion of capital is continuous
on them, and the law of `(z, K)` is invariant, ergodic and the only invariant law on the capital
sets. -/
theorem minMPC_smallShare_repAgent (hδ1 : T.depreciation < 1)
    (hgap : (V.discount * (1 - T.depreciation)) ^ (1 / γ) < 1 - T.depreciation) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃ μ : History Z → ProbabilityMeasure (crraModel V (T.withShare α h0 hα) hγ).AState,
        (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ ∧
        (∀ μ', (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ' → μ' = μ) ∧
        KSModel.KSufficient μ ∧
        (∃ R : (crraModel V (T.withShare α h0 hα) hγ).AggStateRecursiveEquilibrium,
          R.Represents μ) ∧
        (∀ z, IsCompact (KSModel.Kset μ z)) ∧
        (∀ z z', ContinuousOn (fun k => KSModel.lawK μ z k z') (KSModel.Kset μ z)) ∧
        ∃ P : ProbabilityMeasure (ShockPath Z),
          ShockPath.IsInvariant V.aggProb (P : Measure (ShockPath Z)) ∧
          KSModel.IsAggInvariant μ (KSModel.aggLaw (P : Measure (ShockPath Z)) μ) ∧
          KSModel.aggLaw (P : Measure (ShockPath Z)) μ (KSModel.Kgraph μ) = 1 ∧
          (∀ B, MeasurableSet B →
            (∀ᵐ s ∂(KSModel.aggLaw (P : Measure (ShockPath Z)) μ),
              s ∈ B → KSModel.aggKernel μ s B = 1) →
            KSModel.aggLaw (P : Measure (ShockPath Z)) μ B = 0 ∨
              KSModel.aggLaw (P : Measure (ShockPath Z)) μ B = 1) ∧
          ∀ (Λ : Measure (ShockVal Z × ℝ)) [IsProbabilityMeasure Λ],
            KSModel.IsAggInvariant μ Λ → Λ (KSModel.Kgraph μ) = 1 →
            Λ = KSModel.aggLaw (P : Measure (ShockPath Z)) μ := by
  obtain ⟨α₀, hα₀, h⟩ := minMPC_smallShare V T hγ hδ1 hgap
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, S, hκ, hr⟩ := h α h0 hα
  refine ⟨h1, ?_⟩
  have hminor' :
      ∀ z z' e e', (1 : ℝ) ≤ (crraModel V (T.withShare α h0 h1) hγ).idioProb z z' e e' := by
    intro z z' e e'
    have := (crraModel V (T.withShare α h0 h1) hγ).idioProb_sum z z' e
    rw [Fintype.sum_unique] at this
    rw [Subsingleton.elim e' default, this]
  have hℓL := (T.withShare α h0 h1).labLip_nonneg
  have hRL := (T.withShare α h0 h1).abs_grossReturn_sub_le_lab
  have hwL := (T.withShare α h0 h1).abs_wage_sub_le_lab
  obtain ⟨μ, hμ⟩ := (crraModel V (T.withShare α h0 h1) hγ).exists_seqStateEquilibrium
  have hc := S.continuous_seqState hminor' hℓL hRL hwL one_pos hκ hr hμ
  have hS := S.kSufficient_of_unique hminor' hℓL hRL hwL one_pos hκ hr hμ
  obtain ⟨P, hP, herg⟩ := ShockPath.exists_invariant_ergodic V.aggProb V.aggProb_nonneg
    V.aggProb_sum
  have huniq := ShockPath.stationary_unique_of_minor V.aggProb_sum hεZ hminorZ
  obtain ⟨hinv, hK, herg', huniq'⟩ :=
    S.stationary_aggLaw hμ hminor' hℓL hRL hwL one_pos hκ hr hS huniq hP herg
  exact ⟨μ, hμ, fun μ' hμ' => S.eq_of_rate_lt_one hκ hμ' hr hμ
      (hμ'.initMass_eq_of_minor hμ one_pos hminor'), hS,
    (KSModel.kSufficient_iff_exists_represents hμ).1 hS, fun z => KSModel.isCompact_Kset hc z,
    fun z z' => KSModel.continuousOn_lawK hS hc z z', P, hP, hinv, hK, herg', huniq'⟩

end KrusellSmith

end LeanEconomics
