/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.LawContraction

/-!
# The contraction with a sharper saving slope

`Contraction.lean` and `LawContraction.lean` bound the slope of saving in assets by the gross
return bound `R̄` (`abs_policy_sub_le`), so they need `λ R̄ < 1`, which with `β R̄ < λ` forces
`β R̄² < 1` and, for `λ = 1`, gross returns below one. Here the slope is any `θ` that bounds it
(`SavingSlope θ`) — for CRRA the minimal-MPC slope `R̄ (β R̄)^{1/γ} / R̲` (`MinimalMPC.lean`) —
and only `λ θ < 1` is needed (`SlopeContraction`), together with the base hypotheses of Track A
(`ContractionBase`: `β R̄ < λ ≤ 1`, the marginal-utility bounds, prices Lipschitz in capital).

With `G = ℓ C + A / m` (`gain`), `κ_θ = λ G / (1 − λ θ)` and `r_θ = θ + G / (1 − κ_θ)`:

* `SlopeContraction.seqEq_gap`: two sequential equilibria from distributions within `d` are
  within `d / (1 − κ_θ)` in the weighted norm; with `d = 0`,
  **`uniqueSequentialEquilibrium`** when `κ_θ < 1`;
* **`distLE_lawOfMotion`**: the law of motion contracts at `r_θ`;
* on the sequence state, with idiosyncratic marginals depending only on today's shock:
  **fading memory** (`distLE_of_agree`), **burn-in** (`distLE_run`), **explicit matching bounds**
  (`seqPolicy_gap_of_agree`, `seqCapital_gap_of_agree`) and **uniqueness**
  (`eq_of_rate_lt_one`) when `r_θ < 1`.

The proofs are those of `LawContraction.lean` with `θ` in place of `R̄`.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

variable (M) in
/-- **Saving is `θ`-Lipschitz in assets**, along every path and at every label. -/
def SavingSlope (θ : ℝ) : Prop :=
  ∀ (z₀ : Z) (K : List Z → ℝ × ℝ) (a b : ↥(Icc (0 : ℝ) M.assetCap)) (l : Label Z E),
    |M.policy z₀ K (a, l) - M.policy z₀ K (b, l)| ≤ θ * |(a : ℝ) - b|

variable (z₀ : Z)

/-- The pushed-forward test function is Lipschitz in assets, with the constant multiplied by the
saving slope. -/
theorem assetLip_expectedNext_of_slope {θ : ℝ} (hθ : M.SavingSlope θ) (K : List Z → ℝ × ℝ)
    (h : List Z) (z' : Z) {L : ℝ} (hL : 0 ≤ L) {f : M.AState →ᵇ ℝ} (hf : AssetLip L f) :
    AssetLip (θ * L) (M.expectedNext z₀ K h z' f) := by
  intro a b i
  change |∑ e', M.nextProb z₀ h z' e' (a, i) * f (M.nextA z₀ K h e' (a, i))
      - ∑ e', M.nextProb z₀ h z' e' (b, i) * f (M.nextA z₀ K h e' (b, i))| ≤ _
  rw [← Finset.sum_sub_distrib]
  have hpol := hθ z₀ K a b ⟨i.idio, h⟩
  calc |∑ e', (M.nextProb z₀ h z' e' (a, i) * f (M.nextA z₀ K h e' (a, i))
          - M.nextProb z₀ h z' e' (b, i) * f (M.nextA z₀ K h e' (b, i)))|
      ≤ ∑ e', |M.nextProb z₀ h z' e' (a, i) * f (M.nextA z₀ K h e' (a, i))
          - M.nextProb z₀ h z' e' (b, i) * f (M.nextA z₀ K h e' (b, i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e', M.nextProb z₀ h z' e' (a, i) * (L * (θ * |(a : ℝ) - b|)) := by
        refine Finset.sum_le_sum fun e' _ => ?_
        have hp : 0 ≤ M.nextProb z₀ h z' e' (a, i) := M.nextProb_nonneg z₀ h z' e' _
        have hpe : M.nextProb z₀ h z' e' (b, i) = M.nextProb z₀ h z' e' (a, i) := rfl
        rw [hpe, ← mul_sub, abs_mul, abs_of_nonneg hp]
        refine mul_le_mul_of_nonneg_left ?_ hp
        have hfa := hf (M.clampAssets (M.policy z₀ K ((a, i).1, ⟨(a, i).2.idio, h⟩)))
          (M.clampAssets (M.policy z₀ K ((b, i).1, ⟨(b, i).2.idio, h⟩))) ⟨e'⟩
        have hca : ((M.clampAssets (M.policy z₀ K (a, ⟨i.idio, h⟩)) : ↥(Icc (0 : ℝ) M.assetCap))
            : ℝ) = M.policy z₀ K (a, ⟨i.idio, h⟩) := by
          rw [M.clampAssets_of_mem (M.policy_mem_Icc z₀ K _)]
        have hcb : ((M.clampAssets (M.policy z₀ K (b, ⟨i.idio, h⟩)) : ↥(Icc (0 : ℝ) M.assetCap))
            : ℝ) = M.policy z₀ K (b, ⟨i.idio, h⟩) := by
          rw [M.clampAssets_of_mem (M.policy_mem_Icc z₀ K _)]
        change |f (M.clampAssets (M.policy z₀ K (a, ⟨i.idio, h⟩)), ⟨e'⟩)
            - f (M.clampAssets (M.policy z₀ K (b, ⟨i.idio, h⟩)), ⟨e'⟩)| ≤ _
        refine (hfa.trans ?_)
        change L * |((M.clampAssets (M.policy z₀ K (a, ⟨i.idio, h⟩)) : ↥(Icc (0 : ℝ) M.assetCap))
            : ℝ) - ((M.clampAssets (M.policy z₀ K (b, ⟨i.idio, h⟩)) : ↥(Icc (0 : ℝ) M.assetCap))
            : ℝ)| ≤ _
        rw [hca, hcb]
        exact mul_le_mul_of_nonneg_left hpol hL
    _ = θ * L * |(a : ℝ) - b| := by
        rw [← Finset.sum_mul, M.sum_nextProb' z₀ h z' (a, i), one_mul]
        ring

/-- **Distributions from two roots drift apart by at most the gap from the root distance**, with
the saving slope `θ`. -/
theorem integral_nodeDist_sub_le_of_slope {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : M.SavingSlope θ)
    (μ₀ μ₁ : Measure M.AState) [IsProbabilityMeasure μ₀]
    [IsProbabilityMeasure μ₁] (K K' : List Z → ℝ × ℝ) (P : List Z → ℝ)
    (hP : ∀ h (x : M.AState),
      |M.policy z₀ K (x.1, ⟨x.2.idio, h⟩) - M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩)| ≤ P h)
    {d₀ : ℝ} (h0 : DistLE d₀ μ₀ μ₁) :
    ∀ (h : List Z) {L : ℝ}, 0 ≤ L → ∀ {f : M.AState →ᵇ ℝ}, AssetLip L f →
      |∫ x, f x ∂(M.nodeDist z₀ μ₀ K h) - ∫ x, f x ∂(M.nodeDist z₀ μ₁ K' h)|
        ≤ L * gapFrom θ d₀ P h
  | [], L, hL, f, hf => h0 L hL f hf
  | z' :: h, L, hL, f, hf => by
    have := M.isProbabilityMeasure_nodeDist z₀ μ₀ K h
    have := M.isProbabilityMeasure_nodeDist z₀ μ₁ K' h
    have hd : ∫ x, f x ∂(M.nodeDist z₀ μ₀ K (z' :: h))
        = ∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K h) :=
      M.integral_pushNode z₀ K h z' _ f
    have hd' : ∫ x, f x ∂(M.nodeDist z₀ μ₁ K' (z' :: h))
        = ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₁ K' h) :=
      M.integral_pushNode z₀ K' h z' _ f
    rw [hd, hd']
    have h1 := integral_nodeDist_sub_le_of_slope hθ0 hθ μ₀ μ₁ K K' P hP h0 h (mul_nonneg hθ0 hL)
      (M.assetLip_expectedNext_of_slope z₀ hθ K h z' hL hf)
    have h2 : |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₁ K' h)
        - ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₁ K' h)| ≤ L * P h := by
      rw [← integral_sub ((M.expectedNext z₀ K h z' f).integrable _)
        ((M.expectedNext z₀ K' h z' f).integrable _)]
      have := norm_integral_le_of_norm_le_const (μ := M.nodeDist z₀ μ₁ K' h)
        (f := fun x => M.expectedNext z₀ K h z' f x - M.expectedNext z₀ K' h z' f x)
        (C := L * P h) (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          exact (M.abs_expectedNext_sub_le z₀ K K' h z' hf x).trans
            (mul_le_mul_of_nonneg_left (hP h x) hL))
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    calc |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K h)
          - ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₁ K' h)|
        ≤ |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K h)
            - ∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₁ K' h)|
          + |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₁ K' h)
            - ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₁ K' h)| :=
          abs_sub_le _ _ _
      _ ≤ θ * L * gapFrom θ d₀ P h + L * P h := add_le_add h1 h2
      _ = L * gapFrom θ d₀ P (z' :: h) := by simp only [gapFrom]; ring

variable (M) in
/-- **The contraction hypotheses with a saving slope `θ`**: Track A's base hypotheses, a slope
bound `θ` for saving, and `λ θ < 1`. -/
structure SlopeContraction where
  B : M.ContractionBase
  θ : ℝ
  θ_nonneg : 0 ≤ θ
  slope : M.SavingSlope θ
  lam_slope_lt : B.lam * θ < 1

namespace SlopeContraction

variable (S : M.SlopeContraction)

/-- The gain of saving in the capital-path gap, `G = ℓ C + A / m`. -/
noncomputable def gain : ℝ := S.B.ℓ * M.cashScale + S.B.A / S.B.m

/-- **The modulus of the equilibrium map**, `κ_θ = λ G / (1 − λ θ)`. -/
noncomputable def κ : ℝ := S.B.lam * S.gain / (1 - S.B.lam * S.θ)

/-- **The contraction rate of the law of motion**, `r_θ = θ + G / (1 − κ_θ)`. -/
noncomputable def rate : ℝ := S.θ + S.gain / (1 - S.κ)

theorem gain_nonneg : 0 ≤ S.gain :=
  add_nonneg (mul_nonneg S.B.ℓ_nonneg M.cashScale_nonneg) (div_nonneg S.B.A_nonneg S.B.m_pos.le)

theorem κ_nonneg : 0 ≤ S.κ :=
  div_nonneg (mul_nonneg S.B.lam_pos.le S.gain_nonneg) (sub_nonneg.2 S.lam_slope_lt.le)

theorem rate_nonneg (hκ : S.κ < 1) : 0 ≤ S.rate :=
  add_nonneg S.θ_nonneg (div_nonneg S.gain_nonneg (sub_pos.2 hκ).le)

theorem weighted_gapFrom {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ∀ h : List Z, S.B.lam ^ h.length * gapFrom S.θ d
        (fun h : List Z => c / S.B.lam ^ h.length) h
      ≤ d + S.B.lam * c / (1 - S.B.lam * S.θ)
  | [] => by
    simp only [gapFrom, List.length_nil, pow_zero, one_mul]
    have := div_nonneg (mul_nonneg S.B.lam_pos.le hc) (sub_nonneg.2 S.lam_slope_lt.le)
    linarith
  | z :: h => by
    have ih := weighted_gapFrom hc hd h
    set G := S.B.lam * c / (1 - S.B.lam * S.θ)
    have hG : G * (1 - S.B.lam * S.θ) = S.B.lam * c :=
      div_mul_cancel₀ _ (ne_of_gt (sub_pos.2 S.lam_slope_lt))
    have hne : S.B.lam ^ h.length ≠ 0 := (pow_pos S.B.lam_pos _).ne'
    have e : S.B.lam ^ (z :: h).length * gapFrom S.θ d
          (fun h : List Z => c / S.B.lam ^ h.length) (z :: h)
        = S.B.lam * S.θ * (S.B.lam ^ h.length * gapFrom S.θ d
          (fun h : List Z => c / S.B.lam ^ h.length) h) + S.B.lam * c := by
      simp only [gapFrom, List.length_cons, pow_succ]
      field_simp
    rw [e]
    have hlr : 0 ≤ S.B.lam * S.θ := mul_nonneg S.B.lam_pos.le S.θ_nonneg
    have h1 := mul_le_mul_of_nonneg_left ih hlr
    have h2 : S.B.lam * S.θ * d ≤ d := mul_le_of_le_one_left hd S.lam_slope_lt.le
    have h3 : S.B.lam * S.θ * (d + G) = S.B.lam * S.θ * d + S.B.lam * S.θ * G := by ring
    have h4 : S.B.lam * S.θ * G + S.B.lam * c = G := by linarith [hG]
    linarith

variable {z : Z} {ν ν' : ProbabilityMeasure M.AState} {d : ℝ}

/-- **Two sequential equilibria from distributions within `d`** are within `d / (1 − κ_θ)` in the
weighted norm. -/
theorem seqEq_gap (hκ : S.κ < 1) (hd : DistLE d (ν : Measure M.AState) ν') {K K' : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium z (ν : Measure M.AState) K)
    (hK' : M.IsSequentialEquilibrium z (ν' : Measure M.AState) K') (h : List Z) :
    S.B.lam ^ h.length * |K h - K' h| ≤ d / (1 - S.κ) := by
  have : Nonempty Z := ⟨z⟩
  have hm := hd.initMass_eq
  have hd0 := hd.nonneg
  have h1κ : 0 < 1 - S.κ := sub_pos.2 hκ
  set m₀ := M.initMass (ν : Measure M.AState)
  have eK : ∀ h, K h = ∫ x, M.assets x
      ∂(M.nodeDist z (ν : Measure M.AState) (M.pricePath z m₀ K) h) := fun h => hK h
  have eK' : ∀ h, K' h = ∫ x, M.assets x
      ∂(M.nodeDist z (ν' : Measure M.AState) (M.pricePath z m₀ K') h) := by
    intro h
    rw [show m₀ = M.initMass (ν' : Measure M.AState) from hm]
    exact hK' h
  have step : ∀ b, 0 ≤ b → (∀ h : List Z, S.B.lam ^ h.length * |K h - K' h| ≤ b) →
      ∀ h : List Z, S.B.lam ^ h.length * |K h - K' h| ≤ d + S.κ * b := by
    intro b hb0 hb h
    set c := S.gain * b
    have hc : 0 ≤ c := mul_nonneg S.gain_nonneg hb0
    have hP : ∀ h (x : M.AState),
        |M.policy z (M.pricePath z m₀ K) (x.1, ⟨x.2.idio, h⟩)
          - M.policy z (M.pricePath z m₀ K') (x.1, ⟨x.2.idio, h⟩)|
          ≤ (fun h : List Z => c / S.B.lam ^ h.length) h := by
      intro h x
      rw [le_div_iff₀ (pow_pos S.B.lam_pos _), mul_comm]
      exact S.B.weighted_policy_gap z m₀ K K' hb0 hb (x.1, ⟨x.2.idio, h⟩)
    have hi := M.integral_nodeDist_sub_le_of_slope z S.θ_nonneg S.slope (ν : Measure M.AState) ν'
      _ _ _ hP hd h zero_le_one assetLip_assets
    rw [← eK, ← eK', one_mul] at hi
    calc _ ≤ S.B.lam ^ h.length * gapFrom S.θ d
          (fun h : List Z => c / S.B.lam ^ h.length) h :=
          mul_le_mul_of_nonneg_left hi (pow_nonneg S.B.lam_pos.le _)
      _ ≤ d + S.B.lam * c / (1 - S.B.lam * S.θ) := S.weighted_gapFrom hc hd0 h
      _ = d + S.κ * b := by simp only [c, κ]; ring
  have hb : ∀ h, |K h - K' h| ≤ M.assetCap := by
    intro h
    have h1 := M.meanCapital_mem z (ν : Measure M.AState) (M.pricePath z m₀ K) h
    have h2 := M.meanCapital_mem z (ν' : Measure M.AState) (M.pricePath z m₀ K') h
    have e1 : K h = M.meanCapital z (ν : Measure M.AState) (M.pricePath z m₀ K) h := eK h
    have e2 : K' h = M.meanCapital z (ν' : Measure M.AState) (M.pricePath z m₀ K') h := eK' h
    rw [← e1] at h1
    rw [← e2] at h2
    exact abs_sub_le_iff.2 ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩
  have hcap : 0 ≤ M.assetCap := M.assetCap_pos.le
  have hiter : ∀ n : ℕ, ∀ h : List Z,
      S.B.lam ^ h.length * |K h - K' h| ≤ d / (1 - S.κ) + S.κ ^ n * M.assetCap := by
    intro n
    induction n with
    | zero =>
      intro h
      rw [pow_zero, one_mul]
      have := div_nonneg hd0 h1κ.le
      calc _ ≤ 1 * |K h - K' h| :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ S.B.lam_pos.le S.B.lam_le_one) (abs_nonneg _)
        _ ≤ M.assetCap := by rw [one_mul]; exact hb h
        _ ≤ _ := by linarith
    | succ n ih =>
      intro h
      have hb0 : 0 ≤ d / (1 - S.κ) + S.κ ^ n * M.assetCap :=
        add_nonneg (div_nonneg hd0 h1κ.le) (mul_nonneg (pow_nonneg S.κ_nonneg n) hcap)
      have := step _ hb0 ih h
      have e : d + S.κ * (d / (1 - S.κ) + S.κ ^ n * M.assetCap)
          = d / (1 - S.κ) + S.κ ^ (n + 1) * M.assetCap := by
        field_simp
        ring
      rwa [e] at this
  have hlim : Tendsto (fun n : ℕ => d / (1 - S.κ) + S.κ ^ n * M.assetCap) atTop
      (𝓝 (d / (1 - S.κ) + 0 * M.assetCap)) :=
    tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one S.κ_nonneg hκ).mul tendsto_const_nhds)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim fun n => hiter n h

/-- **Uniqueness of sequential equilibrium** when `κ_θ < 1`. -/
theorem uniqueSequentialEquilibrium (hκ : S.κ < 1) : M.UniqueSequentialEquilibrium := by
  intro z μ K K' hK hK'
  have hd : DistLE 0 (μ : Measure M.AState) μ := fun L _ f _ => by simp
  funext h
  have h0 := S.seqEq_gap hκ hd hK hK' h
  rw [zero_div] at h0
  have hw := pow_pos S.B.lam_pos h.length
  have habs : |K h - K' h| ≤ 0 := by
    by_contra hc
    replace hc := lt_of_not_ge hc
    have := mul_pos hw hc
    linarith
  exact sub_eq_zero.1 (abs_nonpos_iff.1 habs)

/-- **Today's saving policies from two distributions** differ by at most `G d / (1 − κ_θ)`. -/
theorem recursivePolicy_gap (hκ : S.κ < 1) (hd : DistLE d (ν : Measure M.AState) ν')
    (x : M.AState) :
    |M.recursivePolicy z ν x - M.recursivePolicy z ν' x| ≤ S.gain * (d / (1 - S.κ)) := by
  have : Nonempty Z := ⟨z⟩
  have hm := hd.initMass_eq
  have hη0 : 0 ≤ d / (1 - S.κ) := div_nonneg hd.nonneg (sub_pos.2 hκ).le
  have := S.B.weighted_policy_gap z (M.initMass (ν : Measure M.AState)) (M.eqPath z ν)
    (M.eqPath z ν') hη0 (fun h => S.seqEq_gap hκ hd (M.eqPath_spec z ν) (M.eqPath_spec z ν') h)
    (x.1, ⟨x.2.idio, []⟩)
  simp only [List.length_nil, pow_zero, one_mul] at this
  unfold recursivePolicy
  rw [← hm]
  exact this

/-- **The law of motion contracts at the rate `r_θ = θ + G / (1 − κ_θ)`.** -/
theorem distLE_lawOfMotion (hκ : S.κ < 1) (hd : DistLE d (ν : Measure M.AState) ν') (z' : Z) :
    DistLE (S.rate * d) (M.lawOfMotion z ν z' : Measure M.AState) (M.lawOfMotion z ν' z') := by
  have : Nonempty Z := ⟨z⟩
  have hm := hd.initMass_eq
  have hη0 : 0 ≤ d / (1 - S.κ) := div_nonneg hd.nonneg (sub_pos.2 hκ).le
  set m₀ := M.initMass (ν : Measure M.AState)
  set c := S.gain * (d / (1 - S.κ))
  have hP : ∀ h (x : M.AState),
      |M.policy z (M.pricePath z m₀ (M.eqPath z ν)) (x.1, ⟨x.2.idio, h⟩)
        - M.policy z (M.pricePath z m₀ (M.eqPath z ν')) (x.1, ⟨x.2.idio, h⟩)|
        ≤ (fun h : List Z => c / S.B.lam ^ h.length) h := by
    intro h x
    rw [le_div_iff₀ (pow_pos S.B.lam_pos _), mul_comm]
    exact S.B.weighted_policy_gap z m₀ _ _ hη0
      (fun h => S.seqEq_gap hκ hd (M.eqPath_spec z ν) (M.eqPath_spec z ν') h) (x.1, ⟨x.2.idio, h⟩)
  intro L hL f hf
  have hi := M.integral_nodeDist_sub_le_of_slope z S.θ_nonneg S.slope (ν : Measure M.AState) ν'
    _ _ _ hP hd [z'] hL hf
  change |∫ x, f x ∂(M.nodeDist z (ν : Measure M.AState) (M.pricePath z m₀ (M.eqPath z ν)) [z'])
      - ∫ x, f x ∂(M.nodeDist z (ν' : Measure M.AState)
        (M.pricePath z (M.initMass (ν' : Measure M.AState)) (M.eqPath z ν')) [z'])| ≤ _
  rw [← hm]
  refine hi.trans (le_of_eq ?_)
  simp only [gapFrom, List.length_nil, pow_zero, div_one, c, rate]
  ring

/-! ### Fading memory, burn-in, matching and uniqueness on the sequence state -/

variable (hκ : S.κ < 1) {μ : History Z → ProbabilityMeasure M.AState}
  (hμ : M.IsSeqStateEquilibrium μ)
include hκ hμ

theorem eq_lawOfMotion_tail (ω : History Z) :
    μ ω = M.lawOfMotion (ω 1) (μ (History.tail ω)) (ω 0) := by
  have := hμ.eq_lawOfMotion (S.uniqueSequentialEquilibrium hκ) (History.tail ω) (ω 0)
  rwa [History.cons_head_tail] at this

/-- **Fading memory**: histories agreeing over their last `T + 1` shocks carry distributions
within `r_θ ^ T · 2 assetCap`, when idiosyncratic marginals depend only on today's shock. -/
theorem distLE_of_agree
    (hm : ∀ ω ω' : History Z, ω 0 = ω' 0 →
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ ω' : Measure M.AState)) :
    ∀ (T : ℕ) (ω ω' : History Z), (∀ n ≤ T, ω n = ω' n) →
      DistLE (S.rate ^ T * (2 * M.assetCap)) (μ ω : Measure M.AState) (μ ω') := by
  intro T
  induction T with
  | zero =>
    intro ω ω' hag
    rw [pow_zero, one_mul]
    exact distLE_of_initMass_eq (hm ω ω' (hag 0 le_rfl))
  | succ T ih =>
    intro ω ω' hag
    have ih' := ih (History.tail ω) (History.tail ω') fun n hn => hag (n + 1) (by omega)
    rw [S.eq_lawOfMotion_tail hκ hμ ω, S.eq_lawOfMotion_tail hκ hμ ω', hag 0 (by omega),
      hag 1 (by omega)]
    have e : S.rate ^ (T + 1) * (2 * M.assetCap) = S.rate * (S.rate ^ T * (2 * M.assetCap)) := by
      ring
    rw [e]
    exact S.distLE_lawOfMotion hκ ih' (ω' 0)

/-- **Burn-in**: the distribution today is within `r_θ ^ T · 2 assetCap` of the one reached by
starting from any `ν` with the right idiosyncratic marginal, `T` periods back. -/
theorem distLE_run :
    ∀ (T : ℕ) (ω : History Z) (ν : ProbabilityMeasure M.AState),
      M.initMass (ν : Measure M.AState) = M.initMass (μ (History.drop T ω) : Measure M.AState) →
      DistLE (S.rate ^ T * (2 * M.assetCap)) (μ ω : Measure M.AState)
        ((run M.lawMap T ω ν : ProbabilityMeasure M.AState) : Measure M.AState) := by
  intro T
  induction T with
  | zero =>
    intro ω ν hν
    rw [pow_zero, one_mul]
    exact distLE_of_initMass_eq hν.symm
  | succ T ih =>
    intro ω ν hν
    have ih' := ih (History.tail ω) ν hν
    rw [S.eq_lawOfMotion_tail hκ hμ ω]
    have e : S.rate ^ (T + 1) * (2 * M.assetCap) = S.rate * (S.rate ^ T * (2 * M.assetCap)) := by
      ring
    rw [e]
    exact S.distLE_lawOfMotion hκ ih' (ω 0)

/-- **Matched expectations, saving**: at histories agreeing over their last `T + 1` shocks,
saving differs by at most `G r_θ ^ T 2 assetCap / (1 − κ_θ)`. -/
theorem seqPolicy_gap_of_agree
    (hm : ∀ ω ω' : History Z, ω 0 = ω' 0 →
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ ω' : Measure M.AState))
    (T : ℕ) {ω ω' : History Z} (hag : ∀ n ≤ T, ω n = ω' n)
    (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    |(M.seqPolicy μ ω a e : ℝ) - M.seqPolicy μ ω' a e|
      ≤ S.gain * (S.rate ^ T * (2 * M.assetCap) / (1 - S.κ)) := by
  have hU := S.uniqueSequentialEquilibrium hκ
  rw [hμ.seqPolicy_eq_recursivePolicy hU ω a e, hμ.seqPolicy_eq_recursivePolicy hU ω' a e,
    hag 0 (Nat.zero_le T)]
  exact S.recursivePolicy_gap hκ (S.distLE_of_agree hκ hμ hm T ω ω' hag) (a, ⟨e⟩)

/-- **Matched expectations, capital**: at histories agreeing over their last `T + 1` shocks,
capital at every future node `g` differs by at most `r_θ ^ T 2 assetCap / ((1 − κ_θ) λ^{|g|})`. -/
theorem seqCapital_gap_of_agree
    (hm : ∀ ω ω' : History Z, ω 0 = ω' 0 →
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ ω' : Measure M.AState))
    (T : ℕ) {ω ω' : History Z} (hag : ∀ n ≤ T, ω n = ω' n) (g : List Z) :
    S.B.lam ^ g.length * |M.seqCapital μ ω g - M.seqCapital μ ω' g|
      ≤ S.rate ^ T * (2 * M.assetCap) / (1 - S.κ) := by
  have hU := S.uniqueSequentialEquilibrium hκ
  rw [hμ.seqCapital_eq_eqPath hU ω, hμ.seqCapital_eq_eqPath hU ω', hag 0 (Nat.zero_le T)]
  exact S.seqEq_gap hκ (S.distLE_of_agree hκ hμ hm T ω ω' hag) (M.eqPath_spec _ _)
    (M.eqPath_spec _ _) g

/-- **Uniqueness**: when `r_θ < 1`, two sequence-state equilibria with the same idiosyncratic
marginals at every history are equal. -/
theorem eq_of_rate_lt_one (hr : S.rate < 1) {μ' : History Z → ProbabilityMeasure M.AState}
    (hμ' : M.IsSeqStateEquilibrium μ')
    (hm : ∀ ω : History Z,
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ' ω : Measure M.AState)) :
    μ = μ' := by
  have hT : ∀ (T : ℕ) (ω : History Z),
      DistLE (S.rate ^ T * (2 * M.assetCap)) (μ ω : Measure M.AState) (μ' ω) := by
    intro T
    induction T with
    | zero =>
      intro ω
      rw [pow_zero, one_mul]
      exact distLE_of_initMass_eq (hm ω)
    | succ T ih =>
      intro ω
      rw [S.eq_lawOfMotion_tail hκ hμ ω, S.eq_lawOfMotion_tail hκ hμ' ω]
      have e : S.rate ^ (T + 1) * (2 * M.assetCap)
          = S.rate * (S.rate ^ T * (2 * M.assetCap)) := by ring
      rw [e]
      exact S.distLE_lawOfMotion hκ (ih (History.tail ω)) (ω 0)
  funext ω
  apply ProbabilityMeasure.toMeasure_injective
  refine eq_of_forall_assetLip fun L hL f hf => ?_
  have hlim : Tendsto (fun T : ℕ => L * (S.rate ^ T * (2 * M.assetCap))) atTop
      (𝓝 (L * (0 * (2 * M.assetCap)))) :=
    tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (S.rate_nonneg hκ) hr).mul tendsto_const_nhds)
  rw [zero_mul, mul_zero] at hlim
  have h0 := ge_of_tendsto' hlim fun T => hT T ω L hL f hf
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

end SlopeContraction

end KSModel

end KrusellSmith

end LeanEconomics
