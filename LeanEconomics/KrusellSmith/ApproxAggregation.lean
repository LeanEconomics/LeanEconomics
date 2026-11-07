/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.AggregateState
import LeanEconomics.KrusellSmith.SequenceStateMatching
import LeanEconomics.KrusellSmith.Aggregates

/-!
# Approximate aggregation

Milestone AK6 of `AGGREGATE_STATE_PLAN.md`: how far `(z, K)` is from a sufficient state, as an
analytic bound.

* **`kSufficient_of_forecast_exact`** (AA0): `(z, K)` is sufficient as soon as the one-step
  forecast of capital from `(z, K)` is exact — the whole price tree follows by induction, labour
  from employment marginals pinned by the shock.
* **`abs_integral_sub_le_of_band`** (AA1): **nonlinearity × distance**. If a function's slopes in
  assets lie in `[θlo, θhi]`, two cross-sections with the same mean assets and within `d` in the
  asset-Wasserstein distance `DistLE` integrate it to within `(θhi − θlo)/2 · d`: subtract the
  mid-slope times assets, which the equal means cancel.
* **`SlopeContraction.capital_gap`** (AA2): next capital from two cross-sections with the same
  mean differs by at most `((θ − θlo)/2 + G/(1 − κ)) d` — the nonlinearity of saving plus the
  feedback of prices. The common slope of saving drops out; saving is monotone, so `θlo = 0` is
  always available (`savingSlopeLower_zero`).
* **`SlopeContraction.forecast_gap`**, `forecast_gap_of_agree` (AA3): two histories with the same
  `(z, K)` have next capital within `ε d`, with `d = 2 ā` in general and `d = r^T 2 ā` when they
  agree over their last `T + 1` shocks.
* **`SlopeContraction.approxAggregation`** (AA4): an approximate law of motion `ℓ(z, K)` — a
  representative history in each fibre — forecasts next capital at every history with error at
  most `((θ − θlo)/2 + G/(1 − κ)) · 2 ā`.

The bound explains approximate aggregation by near-linearity of saving and weak price feedback;
it vanishes for affine saving with prices that do not respond to capital. It does not make the
error small at Krusell–Smith parameters: saving is flat at the borrowing constraint, so
`θ − θlo` is not small in general.
-/

open MeasureTheory Set Filter BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

/-! ### AA0: exact one-step forecasts give a sufficient state -/

/-- **`(z, K)` is sufficient when the one-step forecast of capital from `(z, K)` is exact**, with
employment marginals pinned by today's shock. -/
theorem kSufficient_of_forecast_exact {μ : History Z → ProbabilityMeasure M.AState}
    (hm : ∀ ω ω' : History Z, ω 0 = ω' 0 →
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ ω' : Measure M.AState))
    (h : ∀ ω ω' : History Z, ω 0 = ω' 0 → capAt μ ω = capAt μ ω' →
      ∀ z', capAt μ (History.cons z' ω) = capAt μ (History.cons z' ω')) :
    KSufficient μ := by
  intro ω ω' hz hK
  have key : ∀ g : List Z, History.prepend g ω 0 = History.prepend g ω' 0 ∧
      capAt μ (History.prepend g ω) = capAt μ (History.prepend g ω') := by
    intro g
    induction g with
    | nil => exact ⟨hz, hK⟩
    | cons z' g ih => exact ⟨rfl, h _ _ ih.1 ih.2 z'⟩
  funext g
  obtain ⟨h0, hc⟩ := key g
  refine Prod.ext hc ?_
  change ∑ e, M.initMass (μ (History.prepend g ω) : Measure M.AState) e * M.efficiency e
    = ∑ e, M.initMass (μ (History.prepend g ω') : Measure M.AState) e * M.efficiency e
  rw [hm _ _ h0]

/-! ### AA1: nonlinearity times distance -/

/-- **Nonlinearity × distance**: slopes in `[θlo, θhi]`, equal mean assets and distance `d` give
integrals within `(θhi − θlo)/2 · d`. -/
theorem abs_integral_sub_le_of_band {θlo θhi d : ℝ} (hle : θlo ≤ θhi) (f : M.AState →ᵇ ℝ)
    (hband : ∀ (a b : ↥(Icc (0 : ℝ) M.assetCap)) (i : Idio E), (a : ℝ) ≤ b →
      θlo * ((b : ℝ) - a) ≤ f (b, i) - f (a, i) ∧ f (b, i) - f (a, i) ≤ θhi * ((b : ℝ) - a))
    {ν ν' : Measure M.AState} [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hd : DistLE d ν ν') (hmean : ∫ x, M.assets x ∂ν = ∫ x, M.assets x ∂ν') :
    |∫ x, f x ∂ν - ∫ x, f x ∂ν'| ≤ (θhi - θlo) / 2 * d := by
  set g : M.AState →ᵇ ℝ := f - ((θlo + θhi) / 2) • (M.assets : M.AState →ᵇ ℝ) with hgdef
  have hgx : ∀ x, g x = f x - (θlo + θhi) / 2 * M.assets x := fun x => by
    simp [g, smul_eq_mul]
  have hg : AssetLip ((θhi - θlo) / 2) g := by
    intro a b i
    rw [hgx, hgx]
    change |f (a, i) - (θlo + θhi) / 2 * (a : ℝ) - (f (b, i) - (θlo + θhi) / 2 * (b : ℝ))| ≤ _
    rcases le_total (a : ℝ) b with hab | hab
    · obtain ⟨h1, h2⟩ := hband a b i hab
      rw [abs_le, abs_of_nonpos (by linarith : (a : ℝ) - b ≤ 0)]
      constructor <;> nlinarith
    · obtain ⟨h1, h2⟩ := hband b a i hab
      rw [abs_le, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (a : ℝ) - b)]
      constructor <;> nlinarith
  have hint : ∀ (μ' : Measure M.AState) [IsProbabilityMeasure μ'],
      ∫ x, g x ∂μ' = ∫ x, f x ∂μ' - (θlo + θhi) / 2 * ∫ x, M.assets x ∂μ' := by
    intro μ' _
    simp only [hgx]
    rw [integral_sub (f.integrable μ') ((M.assets.integrable μ').const_mul _),
      integral_const_mul]
  have h := hd _ (by linarith) g hg
  rw [hint ν, hint ν', hmean] at h
  have e : ∫ x, f x ∂ν - (θlo + θhi) / 2 * ∫ x, M.assets x ∂ν'
      - (∫ x, f x ∂ν' - (θlo + θhi) / 2 * ∫ x, M.assets x ∂ν') = ∫ x, f x ∂ν - ∫ x, f x ∂ν' := by
    ring
  rwa [e] at h

variable (M) in
/-- **Saving rises at least at slope `θlo` in assets**, along every path and at every label. -/
def SavingSlopeLower (θlo : ℝ) : Prop :=
  ∀ (z₀ : Z) (K : List Z → ℝ × ℝ) (a b : ↥(Icc (0 : ℝ) M.assetCap)) (l : Label Z E),
    (a : ℝ) ≤ b → θlo * ((b : ℝ) - a) ≤ M.policy z₀ K (b, l) - M.policy z₀ K (a, l)

/-- Saving is monotone in assets: slope at least `0`. -/
theorem savingSlopeLower_zero : M.SavingSlopeLower 0 := fun z₀ K _ _ l hab => by
  rw [zero_mul, sub_nonneg]
  exact policy_mono_assets z₀ K hab l

namespace SlopeContraction

variable (S : M.SlopeContraction)

/-! ### AA2: next capital from cross-sections with the same mean -/

/-- **Next capital from two cross-sections with the same mean** differs by at most the
nonlinearity of saving plus the feedback of prices, times their distance. -/
theorem capital_gap (hκ : S.κ < 1) {θlo : ℝ} (hθlo : θlo ≤ S.θ) (hlo : M.SavingSlopeLower θlo)
    (z : Z) {ν ν' : ProbabilityMeasure M.AState} {d : ℝ}
    (hd : DistLE d (ν : Measure M.AState) ν')
    (hmean : ∫ x, M.assets x ∂(ν : Measure M.AState) = ∫ x, M.assets x ∂(ν' : Measure M.AState)) :
    |∫ x, M.recursivePolicy z ν x ∂(ν : Measure M.AState)
        - ∫ x, M.recursivePolicy z ν' x ∂(ν' : Measure M.AState)|
      ≤ ((S.θ - θlo) / 2 + S.gain / (1 - S.κ)) * d := by
  set P := M.pricePath z (M.initMass (ν : Measure M.AState)) (M.eqPath z ν)
  set P' := M.pricePath z (M.initMass (ν' : Measure M.AState)) (M.eqPath z ν')
  -- the nonlinearity of saving, at today's prices from `ν`
  have h1 : |∫ x, M.savingAt z P [] x ∂(ν : Measure M.AState)
      - ∫ x, M.savingAt z P [] x ∂(ν' : Measure M.AState)| ≤ (S.θ - θlo) / 2 * d := by
    refine abs_integral_sub_le_of_band hθlo (M.savingAt z P []) (fun a b i hab => ⟨?_, ?_⟩) hd
      hmean
    · exact hlo z P a b ⟨i.idio, []⟩ hab
    · have := S.slope z P b a ⟨i.idio, []⟩
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b : ℝ) - a)] at this
      exact (le_abs_self _).trans this
  -- the feedback of prices
  have h2 : |∫ x, M.savingAt z P [] x ∂(ν' : Measure M.AState)
      - ∫ x, M.savingAt z P' [] x ∂(ν' : Measure M.AState)| ≤ S.gain * (d / (1 - S.κ)) := by
    rw [← integral_sub ((M.savingAt z P []).integrable _) ((M.savingAt z P' []).integrable _)]
    have := norm_integral_le_of_norm_le_const (μ := (ν' : Measure M.AState))
      (f := fun x => M.savingAt z P [] x - M.savingAt z P' [] x) (C := S.gain * (d / (1 - S.κ)))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact S.recursivePolicy_gap hκ hd x)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  change |∫ x, M.savingAt z P [] x ∂(ν : Measure M.AState)
      - ∫ x, M.savingAt z P' [] x ∂(ν' : Measure M.AState)| ≤ _
  calc _ ≤ |∫ x, M.savingAt z P [] x ∂(ν : Measure M.AState)
          - ∫ x, M.savingAt z P [] x ∂(ν' : Measure M.AState)|
        + |∫ x, M.savingAt z P [] x ∂(ν' : Measure M.AState)
          - ∫ x, M.savingAt z P' [] x ∂(ν' : Measure M.AState)| := abs_sub_le _ _ _
    _ ≤ (S.θ - θlo) / 2 * d + S.gain * (d / (1 - S.κ)) := add_le_add h1 h2
    _ = ((S.θ - θlo) / 2 + S.gain / (1 - S.κ)) * d := by ring

/-! ### AA3: forecasting next capital from `(z, K)` on the sequence state -/

variable (hκ : S.κ < 1) {θlo : ℝ} (hθlo : θlo ≤ S.θ) (hlo : M.SavingSlopeLower θlo)
  {μ : History Z → ProbabilityMeasure M.AState} (hμ : M.IsSeqStateEquilibrium μ)
include hκ hθlo hlo hμ

omit hθlo hlo in
/-- Capital after a history is mean recursive saving at it. -/
theorem capAt_cons (ω : History Z) (z' : Z) :
    capAt μ (History.cons z' ω)
      = ∫ x, M.recursivePolicy (ω 0) (μ ω) x ∂(μ ω : Measure M.AState) := by
  have hU := S.uniqueSequentialEquilibrium hκ
  change ∫ x, M.assets x ∂(μ (History.cons z' ω) : Measure M.AState) = _
  rw [hμ.integral_assets_cons ω z']
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    hμ.seqPolicy_eq_recursivePolicy hU ω x.1 x.2.idio)

/-- **Histories with the same `(z, K)` forecast next capital to within `ε d`**, `d` the distance
between their cross-sections. -/
theorem forecast_gap {ω ω' : History Z} (hz : ω 0 = ω' 0) (hK : capAt μ ω = capAt μ ω') {d : ℝ}
    (hd : DistLE d (μ ω : Measure M.AState) (μ ω')) (z' z'' : Z) :
    |capAt μ (History.cons z' ω) - capAt μ (History.cons z'' ω')|
      ≤ ((S.θ - θlo) / 2 + S.gain / (1 - S.κ)) * d := by
  rw [S.capAt_cons hκ hμ, S.capAt_cons hκ hμ, ← hz]
  exact S.capital_gap hκ hθlo hlo (ω 0) hd hK

/-- **Uniform forecast error**: with employment marginals pinned by the shock, histories with the
same `(z, K)` forecast next capital to within `ε · 2 ā`. -/
theorem forecast_gap_uniform
    (hm : ∀ ω ω' : History Z, ω 0 = ω' 0 →
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ ω' : Measure M.AState))
    {ω ω' : History Z} (hz : ω 0 = ω' 0) (hK : capAt μ ω = capAt μ ω') (z' z'' : Z) :
    |capAt μ (History.cons z' ω) - capAt μ (History.cons z'' ω')|
      ≤ ((S.θ - θlo) / 2 + S.gain / (1 - S.κ)) * (2 * M.assetCap) :=
  S.forecast_gap hκ hθlo hlo hμ hz hK (distLE_of_initMass_eq (hm ω ω' hz)) z' z''

/-- **Fading memory sharpens the forecast**: histories with the same `(z, K)` that agree over their
last `T + 1` shocks forecast next capital to within `ε r^T 2 ā`. -/
theorem forecast_gap_of_agree
    (hm : ∀ ω ω' : History Z, ω 0 = ω' 0 →
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ ω' : Measure M.AState))
    (T : ℕ) {ω ω' : History Z} (hag : ∀ n ≤ T, ω n = ω' n) (hK : capAt μ ω = capAt μ ω')
    (z' z'' : Z) :
    |capAt μ (History.cons z' ω) - capAt μ (History.cons z'' ω')|
      ≤ ((S.θ - θlo) / 2 + S.gain / (1 - S.κ)) * (S.rate ^ T * (2 * M.assetCap)) :=
  S.forecast_gap hκ hθlo hlo hμ (hag 0 (Nat.zero_le T)) hK
    (S.distLE_of_agree hκ hμ hm T ω ω' hag) z' z''

/-! ### AA4: an approximate law of motion on `(z, K)` -/

open Classical in
/-- **Approximate aggregation**: a law of motion `ℓ(z, K)` — next capital at a representative
history of each fibre — forecasts next capital at every history to within
`((θ − θlo)/2 + G/(1 − κ)) · 2 ā`. -/
theorem approxAggregation (D : EmploymentDesign M.idioProb) :
    ∃ ℓ : Z → ℝ → ℝ, ∀ (ω : History Z) (z' : Z),
      |capAt μ (History.cons z' ω) - ℓ (ω 0) (capAt μ ω)|
        ≤ ((S.θ - θlo) / 2 + S.gain / (1 - S.κ)) * (2 * M.assetCap) := by
  have hm : ∀ ω ω' : History Z, ω 0 = ω' 0 →
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ ω' : Measure M.AState) :=
    fun ω ω' hz => by rw [hμ.initMass_eq_design D ω, hμ.initMass_eq_design D ω', hz]
  refine ⟨fun z k => if h : ∃ ω : History Z, ω 0 = z ∧ capAt μ ω = k
    then capAt μ (History.cons z h.choose) else 0, fun ω z' => ?_⟩
  have h : ∃ ω' : History Z, ω' 0 = ω 0 ∧ capAt μ ω' = capAt μ ω := ⟨ω, rfl, rfl⟩
  simp only [h, ↓reduceDIte]
  obtain ⟨h0, hK⟩ := h.choose_spec
  exact S.forecast_gap_uniform hκ hθlo hlo hμ hm h0.symm hK.symm z' (ω 0)

end SlopeContraction

end KSModel

section SmallShare

variable [Nonempty Z] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)

/-- **Approximate aggregation for small capital shares**: for CRRA, clamped Cobb–Douglas with
`0 ≤ δ < 1` and `(β (1 − δ))^{1/γ} < 1 − δ`, and Krusell–Smith's employment design, below some
capital share every sequence-state equilibrium has a law of motion `ℓ(z, K)` forecasting next
capital to within `(θ/2 + G/(1 − κ)) · 2 ā`: half the minimal-MPC saving slope (the nonlinearity
of saving) plus the price feedback. -/
theorem minMPC_smallShare_approxAggregation (hδ1 : T.depreciation < 1)
    (hgap : (V.discount * (1 - T.depreciation)) ^ (1 / γ) < 1 - T.depreciation)
    (D : EmploymentDesign V.idioProb) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃ S : (crraModel V (T.withShare α h0 hα) hγ).SlopeContraction, S.κ < 1 ∧ S.rate < 1 ∧
        ∀ μ : History Z → ProbabilityMeasure (crraModel V (T.withShare α h0 hα) hγ).AState,
          (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ →
          ∃ ℓ : Z → ℝ → ℝ, ∀ (ω : History Z) (z' : Z),
            |KSModel.capAt μ (History.cons z' ω) - ℓ (ω 0) (KSModel.capAt μ ω)|
              ≤ (S.θ / 2 + S.gain / (1 - S.κ))
                * (2 * (crraModel V (T.withShare α h0 hα) hγ).assetCap) := by
  obtain ⟨α₀, hα₀, h⟩ := minMPC_smallShare V T hγ hδ1 hgap
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, S, hκ, hr⟩ := h α h0 hα
  refine ⟨h1, S, hκ, hr, fun μ hμ => ?_⟩
  have := S.approxAggregation hκ S.θ_nonneg KSModel.savingSlopeLower_zero hμ D
  simpa only [sub_zero] using this

end SmallShare

end KrusellSmith

end LeanEconomics
