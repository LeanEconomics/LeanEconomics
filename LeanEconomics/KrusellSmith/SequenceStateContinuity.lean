/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.HistoryMarginalsCD
import LeanEconomics.KrusellSmith.StationarySequence
import LeanEconomics.KrusellSmith.DoeblinUniqueness

/-!
# The sequence-state equilibrium is continuous in the history

Milestone SS3 of `STATIONARY_SEQUENCE_PLAN.md`. The factor theorem (`StationarySequence.lean`)
needs the sequence-state equilibrium `μ` to be measurable in the history. When the law of motion
contracts (`HistoryMarginals.lean`), fading memory makes it continuous:

* `SlopeContraction.continuous_integral_of_assetLip`: for a test function `f` Lipschitz in assets,
  `ξ ↦ ∫ f dμ(ξ)` is continuous in the product topology on histories — histories agreeing over
  their last `T + 1` shocks give integrals within `(L ω + 2‖f‖) r* ^ T`;
* **`SlopeContraction.continuous_seqState`**: `ξ ↦ μ(ξ)` is continuous into the weak topology,
  since asset-Lipschitz functions are uniformly dense in `C(AState)` (Stone–Weierstrass,
  `assetLipSubalgebra_separatesPoints`) and uniform limits of continuous functions are continuous;
  hence measurable (`measurable_seqState`).

**`minMPC_smallShare_stationary`**: for CRRA, clamped Cobb–Douglas, `0 ≤ δ < 1` with
`(β (1 − δ))^{1/γ} < 1 − δ`, employment transitions bounded below and small capital shares, the
unique sequence-state equilibrium is continuous in the history, and its aggregate state has an
invariant, ergodic law under the equilibrium Markov process — a stationary ergodic sequential
equilibrium, with no recursive state space and no randomisation.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction TopologicalSpace ProbabilityTheory
open scoped ENNReal NNReal

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

namespace SlopeContraction

variable {ε : ℝ} (hminor : ∀ z z' e e', ε ≤ M.idioProb z z' e e') (S : M.SlopeContraction)
  {ℓL : ℝ} (hℓL : 0 ≤ ℓL)
  (hRL : ∀ z k L L', |M.grossReturn z k L - M.grossReturn z k L'| ≤ ℓL * |L - L'|)
  (hwL : ∀ z k L L', |M.wage z k L - M.wage z k L'| ≤ ℓL * |L - L'|)
  (hε : 0 < ε) (hκ : S.κ < 1) (hr : S.rate < 1) {μ : History Z → ProbabilityMeasure M.AState}
  (hμ : M.IsSeqStateEquilibrium μ)

include hminor hℓL hRL hwL hε hκ hr hμ in
/-- **Integrals of asset-Lipschitz test functions are continuous in the history.** -/
theorem continuous_integral_of_assetLip [Nonempty E] {L : ℝ} (hL : 0 ≤ L)
    {f : M.AState →ᵇ ℝ} (hf : AssetLip L f) :
    Continuous fun ξ : ShockPath Z => ∫ x, f x ∂(μ ξ.toHistory : Measure M.AState) := by
  rw [continuous_iff_continuousAt]
  intro ξ
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε' hε'
  set w := S.histWeight ℓL ε
  set r := S.histRate ε
  set B := 2 * ‖f‖
  have hB0 : 0 ≤ B := mul_nonneg zero_le_two (norm_nonneg f)
  have hw1 : 1 ≤ w := by
    have hJ := S.histJ_nonneg hℓL hκ
    have h1c : 0 < 1 - (1 - Fintype.card E * ε) := by
      have := mix_lt_one (E := E) hε
      linarith
    have : 0 ≤ 2 * S.histJ ℓL / (1 - (1 - Fintype.card E * ε)) := by positivity
    simp only [w, histWeight]
    linarith
  have hr0 : 0 ≤ r := (S.rate_nonneg hκ).trans (le_max_left _ _)
  have hr1 : r < 1 := S.histRate_lt_one hε hr
  set C := L * w + B + 1
  have hC : 0 < C := by
    have := mul_nonneg hL (zero_le_one.trans hw1)
    simp only [C]
    linarith
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one (div_pos hε' hC) hr1
  have hev : ∀ᶠ ξ' in 𝓝 ξ, ∀ i ∈ Finset.range (T + 1), ξ' i ∈ ({ξ i} : Set (ShockVal Z)) :=
    (Finset.eventually_all _).2 fun i _ =>
      ((continuous_apply i).tendsto ξ).eventually ((isOpen_discrete _).mem_nhds rfl)
  filter_upwards [hev] with ξ' h
  have hag : ∀ n ≤ T, ξ'.toHistory n = ξ.toHistory n := by
    intro n hn
    have := h n (Finset.mem_range.2 (by omega))
    rw [mem_singleton_iff] at this
    change (ξ' n).val = (ξ n).val
    rw [this]
  obtain ⟨da, dm, hda, hdm, hN, hD⟩ :=
    S.dist2_of_agree hminor hℓL hRL hwL hε hκ hμ T ξ'.toHistory ξ.toHistory hag
  have hosc : ∀ x y, f x - f y ≤ B := fun x y => by
    have h1 := f.norm_coe_le_norm x
    have h2 := f.norm_coe_le_norm y
    rw [Real.norm_eq_abs] at h1 h2
    simp only [B]
    linarith [(abs_le.1 h1).2, (abs_le.1 h2).1]
  have hb := hD L B hL f hf hosc
  have hda' : da ≤ r ^ T * w := by nlinarith
  have hdm' : dm ≤ r ^ T := by
    by_contra hc
    rw [not_le] at hc
    nlinarith
  have hrT := pow_nonneg hr0 T
  rw [Real.dist_eq]
  calc _ ≤ L * da + B * dm := hb
    _ ≤ L * (r ^ T * w) + B * r ^ T :=
        add_le_add (mul_le_mul_of_nonneg_left hda' hL) (mul_le_mul_of_nonneg_left hdm' hB0)
    _ ≤ C * r ^ T := by simp only [C]; nlinarith
    _ < C * (ε' / C) := mul_lt_mul_of_pos_left hT hC
    _ = ε' := by field_simp

include hminor hℓL hRL hwL hε hκ hr hμ in
/-- **The sequence-state equilibrium is continuous in the history** (weak topology). -/
theorem continuous_seqState [Nonempty E] :
    Continuous fun ξ : ShockPath Z => μ ξ.toHistory := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  set A : Subalgebra ℝ C(M.AState, ℝ) :=
    ((M.assetLipSubalgebra).map (toContinuousMapStarₐ ℝ)).toSubalgebra
  have hdense : A.topologicalClosure = ⊤ :=
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A
      assetLipSubalgebra_separatesPoints
  have hf : f.toContinuousMap ∈ closure (A : Set C(M.AState, ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe, hdense]
    trivial
  obtain ⟨g, hgA, hg⟩ := mem_closure_iff_seq_limit.1 hf
  have hb : ∀ n, ∃ b ∈ M.assetLipSubalgebra, toContinuousMapStarₐ ℝ b = g n :=
    fun n => (StarSubalgebra.mem_map).1 (hgA n)
  choose b hbA hbg using hb
  have hcont : ∀ n, Continuous fun ξ : ShockPath Z =>
      ∫ x, b n x ∂(μ ξ.toHistory : Measure M.AState) := by
    intro n
    obtain ⟨L, hL, hbL⟩ := hbA n
    exact S.continuous_integral_of_assetLip hminor hℓL hRL hwL hε hκ hr hμ hL hbL
  refine TendstoUniformly.continuous (p := (atTop : Filter ℕ)) ?_
    (Eventually.of_forall hcont).frequently
  rw [Metric.tendstoUniformly_iff]
  intro ε' hε'
  have hlim := (Metric.tendsto_atTop.1 hg) (ε' / 2) (half_pos hε')
  obtain ⟨N, hN⟩ := hlim
  refine eventually_atTop.2 ⟨N, fun n hn ξ => ?_⟩
  have hpt : ∀ x, ‖f x - b n x‖ ≤ dist (g n) f.toContinuousMap := by
    intro x
    rw [← dist_eq_norm, dist_comm]
    calc dist (b n x) (f x) = dist (g n x) (f.toContinuousMap x) := by rw [← hbg n]; rfl
      _ ≤ _ := ContinuousMap.dist_apply_le_dist x
  have hint := norm_integral_le_of_norm_le_const (μ := (μ ξ.toHistory : Measure M.AState))
    (f := fun x => f x - b n x) (Eventually.of_forall hpt)
  rw [probReal_univ, mul_one, integral_sub (f.integrable _) ((b n).integrable _)] at hint
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  exact hint.trans_lt ((hN n hn).trans (half_lt_self hε'))

include hminor hℓL hRL hwL hε hκ hr hμ in
theorem measurable_seqState [Nonempty E] :
    Measurable fun ξ : ShockPath Z => μ ξ.toHistory :=
  (S.continuous_seqState hminor hℓL hRL hwL hε hκ hr hμ).measurable

end SlopeContraction

end KSModel

/-! ### A stationary ergodic sequential equilibrium for small capital shares -/

variable [Nonempty Z] [Nonempty E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ}
  (hγ : 0 < γ) {ε : ℝ} (hε : 0 < ε) (hminor : ∀ z z' e e', ε ≤ V.idioProb z z' e e')
include hε hminor

/-- **A stationary, ergodic sequential equilibrium for small capital shares**: for CRRA, clamped
Cobb–Douglas with `0 ≤ δ < 1` and `(β (1 − δ))^{1/γ} < 1 − δ`, and employment transitions bounded
below, there is a share `α₀ > 0` below which the sequence-state equilibrium is unique and
continuous in the history, and for some invariant law `P` of the shock history its aggregate
state `(z, μ)` has an invariant, ergodic law under the equilibrium Markov process. -/
theorem minMPC_smallShare_stationary (hδ1 : T.depreciation < 1)
    (hgap : (V.discount * (1 - T.depreciation)) ^ (1 / γ) < 1 - T.depreciation) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃ μ : History Z → ProbabilityMeasure (crraModel V (T.withShare α h0 hα) hγ).AState,
        (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ ∧
        (∀ μ', (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ' → μ' = μ) ∧
        Continuous (fun ξ : ShockPath Z => μ ξ.toHistory) ∧
        ∃ P : ProbabilityMeasure (ShockPath Z),
          ShockPath.IsInvariant V.aggProb (P : Measure (ShockPath Z)) ∧
          (KSModel.stateLaw (P : Measure (ShockPath Z)) μ).bind
              (crraModel V (T.withShare α h0 hα) hγ).eqKernel
            = KSModel.stateLaw (P : Measure (ShockPath Z)) μ ∧
          ∀ B, MeasurableSet B →
            (∀ᵐ s ∂(KSModel.stateLaw (P : Measure (ShockPath Z)) μ),
              s ∈ B → (crraModel V (T.withShare α h0 hα) hγ).eqKernel s B = 1) →
            KSModel.stateLaw (P : Measure (ShockPath Z)) μ B = 0 ∨
              KSModel.stateLaw (P : Measure (ShockPath Z)) μ B = 1 := by
  obtain ⟨α₀, hα₀, h⟩ := minMPC_smallShare V T hγ hδ1 hgap
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, S, hκ, hr⟩ := h α h0 hα
  refine ⟨h1, ?_⟩
  have hminor' : ∀ z z' e e', ε ≤ (crraModel V (T.withShare α h0 h1) hγ).idioProb z z' e e' :=
    hminor
  have hℓL := (T.withShare α h0 h1).labLip_nonneg
  have hRL := (T.withShare α h0 h1).abs_grossReturn_sub_le_lab
  have hwL := (T.withShare α h0 h1).abs_wage_sub_le_lab
  have hU := S.uniqueSequentialEquilibrium hκ
  obtain ⟨μ, hμ⟩ := (crraModel V (T.withShare α h0 h1) hγ).exists_seqStateEquilibrium
  have hc := S.continuous_seqState hminor' hℓL hRL hwL hε hκ hr hμ
  obtain ⟨P, hP, herg⟩ := ShockPath.exists_invariant_ergodic V.aggProb V.aggProb_nonneg
    V.aggProb_sum
  refine ⟨μ, hμ, fun μ' hμ' => S.eq_of_rate_lt_one hκ hμ' hr hμ
      (hμ'.initMass_eq_of_minor hμ hε hminor'), hc, P, hP, ?_, ?_⟩
  · exact KSModel.isInvariant_stateLaw hU hμ hc.measurable hP
  · intro B hB hinv
    exact KSModel.ergodic_stateLaw hU hμ hc.measurable herg hB hinv

end KrusellSmith

end LeanEconomics
