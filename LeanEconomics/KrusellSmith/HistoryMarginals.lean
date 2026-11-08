/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.SlopeContraction

/-!
# Fading memory when employment marginals depend on the history

`LawContraction.lean` and `SlopeContraction.lean` compare distributions with the same employment
marginal, so labour is the same and only capital feeds back into prices. Without the
Krusell–Smith design the marginal of a sequence-state equilibrium depends on the whole history,
and two histories that agree only recently carry different marginals and different labour. Here
the comparison allows that.

**The distance** (`Dist2 da dm`). Test functions are `L`-Lipschitz in assets with oscillation at
most `B` over all states; the distributions are within `(da, dm)` if every such function
integrates to within `L da + B dm`. Any two distributions are within `(0, 1)`
(`dist2_zero_one`); mean capital differs by at most `da + ā dm` and labour by at most
`(Σ e) dm` (`Dist2.capital`, `Dist2.labour`).

**One step down the tree** (`dist2_nodeDist`). If every transition probability is at least
`ε > 0` (Doeblin), pushing forward along a saving policy of slope `θ` turns a test function of
type `(L, B)` into one of type `(θ L, L ā + c B)`, `c = 1 − |E| ε` (`osc_expectedNext`): the
employment chain mixes. So `(da, dm) ↦ (θ da + ā dm + P, c dm)`, `P` the policy gap.

**Prices** (`seqEq_priceGap`). Labour gaps move prices too: with prices `ℓ_L`-Lipschitz in labour
(`hRL`, `hwL`), the weighted price gap of two sequential equilibria is at most
`(ℓ da + K_d dm) / (1 − κ_θ)`, through the price-gap versions of Track A's bounds
(`ContractionBase.weighted_du_gap_price`, `weighted_policy_gap_price`).

**The law of motion** (`dist2_lawOfMotion`, `norm_step`). In the norm `da + ω dm` the law of motion
contracts at `r* = max r_θ ((1 + c) / 2)`, for a weight `ω` that absorbs the labour channel: the
labour channel changes the weight, not the rate.

**Sequence state**, for every sequence-state equilibrium, with no condition on the marginals:
**fading memory** (`IsSeqStateEquilibrium.dist2_of_agree`) and **an explicit matching bound**
(`seqPolicy_gap_of_agree'`): at histories agreeing over their last `T + 1` shocks, saving differs
by at most `G₁ (ℓ ω + K_d) r* ^ T / (1 − κ_θ)`.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

/-! ### Track A against arbitrary price gaps -/

namespace ContractionBase

variable (H : M.ContractionBase)
include H

/-- The marginal-utility gap constant per unit of price gap. -/
noncomputable def A₁ : ℝ := (M.discount * H.D / H.lam + H.Mdu * M.cashScale) / (1 - H.q)

/-- The saving gap per unit of price gap, `G₁ = C + A₁ / m`. -/
noncomputable def G₁ : ℝ := M.cashScale + H.A₁ / H.m

theorem A₁_nonneg : 0 ≤ H.A₁ :=
  div_nonneg (add_nonneg (div_nonneg (mul_nonneg M.discount_pos.le H.D_nonneg) H.lam_pos.le)
    (mul_nonneg H.Mdu_nonneg M.cashScale_nonneg)) (sub_nonneg.2 H.q_lt_one.le)

theorem A₁_eq : H.A₁ * (1 - H.q) = M.discount * H.D / H.lam + H.Mdu * M.cashScale := by
  rw [A₁, div_mul_cancel₀]
  exact (sub_pos.2 H.q_lt_one).ne'

theorem A_eq_mul : H.A = H.ℓ * H.A₁ := by
  simp only [ContractionBase.A, A₁]
  ring

theorem G₁_nonneg : 0 ≤ H.G₁ := add_nonneg M.cashScale_nonneg (div_nonneg H.A₁_nonneg H.m_pos.le)

variable (z₀ : Z) (Q Q' : List Z → ℝ × ℝ)

omit H in
theorem cash_gap_price {g : ℝ} (s : M.State)
    (hR : |M.returnAt z₀ Q s.2.node - M.returnAt z₀ Q' s.2.node| ≤ g)
    (hw : |M.wageAt z₀ Q s.2.node - M.wageAt z₀ Q' s.2.node| ≤ g) :
    |M.cash z₀ Q s - M.cash z₀ Q' s| ≤ g * M.cashScale := by
  have ha := s.1.2
  have he : M.efficiency s.2.idio ≤ ∑ e, M.efficiency e :=
    Finset.single_le_sum (fun e _ => M.efficiency_nonneg e) (Finset.mem_univ _)
  have he0 := M.efficiency_nonneg s.2.idio
  have e : M.cash z₀ Q s - M.cash z₀ Q' s
      = (M.returnAt z₀ Q s.2.node - M.returnAt z₀ Q' s.2.node) * (s.1 - M.borrowLimit)
        + (M.wageAt z₀ Q s.2.node - M.wageAt z₀ Q' s.2.node) * M.efficiency s.2.idio := by
    simp only [cash]
    ring
  rw [e]
  have hg : 0 ≤ g := (abs_nonneg _).trans hR
  have hb := M.borrowLimit_nonneg
  have hab : |(s.1 : ℝ) - M.borrowLimit| ≤ M.assetCap + M.borrowLimit := by
    rw [abs_le]
    constructor <;> linarith [ha.1, ha.2]
  calc _ ≤ |M.returnAt z₀ Q s.2.node - M.returnAt z₀ Q' s.2.node| * |(s.1 : ℝ) - M.borrowLimit|
        + |M.wageAt z₀ Q s.2.node - M.wageAt z₀ Q' s.2.node| * M.efficiency s.2.idio := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
        · rw [abs_mul, abs_of_nonneg he0]
    _ ≤ g * (M.assetCap + M.borrowLimit) + g * ∑ e, M.efficiency e :=
        add_le_add (mul_le_mul hR hab (abs_nonneg _) hg) (mul_le_mul hw he he0 hg)
    _ = g * M.cashScale := by rw [cashScale]; ring

variable {η : ℝ}

/-- **Weighted marginal-utility gaps against weighted price gaps, `n` steps.** -/
theorem weighted_du_gap_price_iter (hη0 : 0 ≤ η)
    (hR : ∀ h : List Z, H.lam ^ h.length * |M.returnAt z₀ Q h - M.returnAt z₀ Q' h| ≤ η)
    (hw : ∀ h : List Z, H.lam ^ h.length * |M.wageAt z₀ Q h - M.wageAt z₀ Q' h| ≤ η) :
    ∀ (n : ℕ) (s : M.State),
      H.lam ^ s.2.node.length * |H.U.du (M.consumption z₀ Q s) - H.U.du (M.consumption z₀ Q' s)|
        ≤ H.A₁ * η + H.q ^ n * H.D
  | 0, s => by
    have h1 := H.abs_du_sub_le z₀ Q Q' s s
    have h2 : H.lam ^ s.2.node.length ≤ 1 := pow_le_one₀ H.lam_pos.le H.lam_le_one
    have h4 := mul_le_mul h2 h1 (abs_nonneg _) zero_le_one
    have h5 := mul_nonneg H.A₁_nonneg hη0
    rw [pow_zero, one_mul]
    linarith
  | n + 1, s => by
    set len := s.2.node.length
    have hlam := H.lam_pos
    have hW : 0 < H.lam ^ len := pow_pos hlam _
    have hW1 : 0 < H.lam ^ (len + 1) := pow_pos hlam _
    set T := H.A₁ * η + H.q ^ n * H.D with hT
    have hB : ∀ ze : Z × E, ∀ a' ∈ Icc 0 M.assetCap,
        |H.U.du (M.consumption z₀ Q (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩))
          - H.U.du (M.consumption z₀ Q' (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩))|
          ≤ T / H.lam ^ (len + 1) := by
      intro ze a' _
      have ih := weighted_du_gap_price_iter hη0 hR hw n (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
      rw [le_div_iff₀ hW1, mul_comm]
      exact ih
    have h1 := M.du_consumption_sub_le H.U z₀ (H.slack z₀ Q) (H.slack z₀ Q') H.floor_lt_cLo
      (H.cLo_le z₀ Q) H.du_lip H.Mdu_nonneg s (fun _ => T / H.lam ^ (len + 1)) hB
    have hS : ∑ ze : Z × E, M.shockProb z₀ ze (s, 0)
          * (|M.returnAt z₀ Q (ze.1 :: s.2.node) - M.returnAt z₀ Q' (ze.1 :: s.2.node)|
              * H.U.du H.cLo
            + M.returnBound * (T / H.lam ^ (len + 1)))
        ≤ (η * H.D + M.returnBound * T) / H.lam ^ (len + 1) := by
      have hterm : ∀ ze : Z × E,
          |M.returnAt z₀ Q (ze.1 :: s.2.node) - M.returnAt z₀ Q' (ze.1 :: s.2.node)| * H.U.du H.cLo
            + M.returnBound * (T / H.lam ^ (len + 1))
          ≤ (η * H.D + M.returnBound * T) / H.lam ^ (len + 1) := by
        intro ze
        have hc := hR (ze.1 :: s.2.node)
        have hlen : (ze.1 :: s.2.node).length = len + 1 := rfl
        rw [hlen] at hc
        have hgap : |M.returnAt z₀ Q (ze.1 :: s.2.node) - M.returnAt z₀ Q' (ze.1 :: s.2.node)|
            ≤ η / H.lam ^ (len + 1) := by
          rw [le_div_iff₀ hW1, mul_comm]
          exact hc
        have hD := H.D_nonneg
        have : |M.returnAt z₀ Q (ze.1 :: s.2.node) - M.returnAt z₀ Q' (ze.1 :: s.2.node)|
            * H.U.du H.cLo ≤ η / H.lam ^ (len + 1) * H.D :=
          mul_le_mul_of_nonneg_right hgap hD
        have e1 : η / H.lam ^ (len + 1) * H.D = η * H.D / H.lam ^ (len + 1) := by ring
        have e3 : (η * H.D + M.returnBound * T) / H.lam ^ (len + 1)
            = η * H.D / H.lam ^ (len + 1) + M.returnBound * T / H.lam ^ (len + 1) :=
          add_div _ _ _
        have e2 : M.returnBound * (T / H.lam ^ (len + 1))
            = M.returnBound * T / H.lam ^ (len + 1) := by ring
        linarith
      calc _ ≤ ∑ ze : Z × E, M.shockProb z₀ ze (s, 0)
            * ((η * H.D + M.returnBound * T) / H.lam ^ (len + 1)) :=
            Finset.sum_le_sum fun ze _ =>
              mul_le_mul_of_nonneg_left (hterm ze) (M.shockProb_nonneg' z₀ ze (s, 0))
        _ = (η * H.D + M.returnBound * T) / H.lam ^ (len + 1) := by
            rw [← Finset.sum_mul, M.shockProb_sum z₀, one_mul]
    have hX : |M.cash z₀ Q s - M.cash z₀ Q' s| ≤ M.cashScale * η / H.lam ^ len := by
      have hRs : |M.returnAt z₀ Q s.2.node - M.returnAt z₀ Q' s.2.node| ≤ η / H.lam ^ len := by
        rw [le_div_iff₀ hW, mul_comm]
        exact hR s.2.node
      have hws : |M.wageAt z₀ Q s.2.node - M.wageAt z₀ Q' s.2.node| ≤ η / H.lam ^ len := by
        rw [le_div_iff₀ hW, mul_comm]
        exact hw s.2.node
      calc _ ≤ η / H.lam ^ len * M.cashScale := ContractionBase.cash_gap_price z₀ Q Q' s hRs hws
        _ = M.cashScale * η / H.lam ^ len := by ring
    have hβ := M.discount_pos.le
    have hstep : H.lam ^ len * |H.U.du (M.consumption z₀ Q s) - H.U.du (M.consumption z₀ Q' s)|
        ≤ M.discount * (η * H.D + M.returnBound * T) / H.lam
          + H.Mdu * (M.cashScale * η) := by
      have hW' : H.lam ^ (len + 1) = H.lam ^ len * H.lam := pow_succ _ _
      have k1 := mul_le_mul_of_nonneg_left
        (h1.trans (add_le_add (mul_le_mul_of_nonneg_left hS hβ)
          (mul_le_mul_of_nonneg_left hX H.Mdu_nonneg))) hW.le
      calc _ ≤ H.lam ^ len * (M.discount * ((η * H.D + M.returnBound * T)
              / H.lam ^ (len + 1)) + H.Mdu * (M.cashScale * η / H.lam ^ len)) := k1
        _ = M.discount * (η * H.D + M.returnBound * T) / H.lam
            + H.Mdu * (M.cashScale * η) := by
            rw [hW']
            field_simp
    have hid : M.discount * (η * H.D + M.returnBound * T) / H.lam + H.Mdu * (M.cashScale * η)
        = H.A₁ * η + H.q ^ (n + 1) * H.D := by
      have hA := H.A₁_eq
      have hq : H.q = M.discount * M.returnBound / H.lam := rfl
      have e : M.discount * (η * H.D + M.returnBound * T) / H.lam + H.Mdu * (M.cashScale * η)
          = (M.discount * H.D / H.lam + H.Mdu * M.cashScale) * η + H.q * T := by
        rw [hq]
        field_simp
        ring
      rw [e, ← hA, hT, pow_succ]
      ring
    linarith

/-- **Weighted marginal-utility gaps against weighted price gaps**: at most `A₁ η`. -/
theorem weighted_du_gap_price [Nonempty Z] (hη0 : 0 ≤ η)
    (hR : ∀ h : List Z, H.lam ^ h.length * |M.returnAt z₀ Q h - M.returnAt z₀ Q' h| ≤ η)
    (hw : ∀ h : List Z, H.lam ^ h.length * |M.wageAt z₀ Q h - M.wageAt z₀ Q' h| ≤ η)
    (s : M.State) :
    H.lam ^ s.2.node.length * |H.U.du (M.consumption z₀ Q s) - H.U.du (M.consumption z₀ Q' s)|
      ≤ H.A₁ * η := by
  have hlim : Tendsto (fun n : ℕ => H.A₁ * η + H.q ^ n * H.D) atTop (𝓝 (H.A₁ * η + 0 * H.D)) :=
    tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one H.q_nonneg H.q_lt_one).mul tendsto_const_nhds)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim fun n => H.weighted_du_gap_price_iter z₀ Q Q' hη0 hR hw n s

/-- **Weighted saving gaps against weighted price gaps**: at most `G₁ η`. -/
theorem weighted_policy_gap_price [Nonempty Z] (hη0 : 0 ≤ η)
    (hR : ∀ h : List Z, H.lam ^ h.length * |M.returnAt z₀ Q h - M.returnAt z₀ Q' h| ≤ η)
    (hw : ∀ h : List Z, H.lam ^ h.length * |M.wageAt z₀ Q h - M.wageAt z₀ Q' h| ≤ η)
    (s : M.State) :
    H.lam ^ s.2.node.length * |M.policy z₀ Q s - M.policy z₀ Q' s| ≤ H.G₁ * η := by
  set w := H.lam ^ s.2.node.length
  have hw0 : 0 < w := pow_pos H.lam_pos _
  have hdu := H.weighted_du_gap_price z₀ Q Q' hη0 hR hw s
  have hcons : H.m * |M.consumption z₀ Q s - M.consumption z₀ Q' s|
      ≤ |H.U.du (M.consumption z₀ Q s) - H.U.du (M.consumption z₀ Q' s)| := by
    have sl := H.slack z₀ Q s
    have sl' := H.slack z₀ Q' s
    have up : M.consumption z₀ Q s ≤ M.maxCash := by
      have := (M.policy_mem_Icc z₀ Q s).1
      have := M.cash_le_maxCash z₀ Q s
      simp only [consumption]
      linarith
    have up' : M.consumption z₀ Q' s ≤ M.maxCash := by
      have := (M.policy_mem_Icc z₀ Q' s).1
      have := M.cash_le_maxCash z₀ Q' s
      simp only [consumption]
      linarith
    rcases le_total (M.consumption z₀ Q s) (M.consumption z₀ Q' s) with h | h
    · have := H.du_strong _ _ sl h up'
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
      exact this.trans (le_abs_self _)
    · have := H.du_strong _ _ sl' h up
      rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact this.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  have e : M.policy z₀ Q s - M.policy z₀ Q' s
      = (M.cash z₀ Q s - M.cash z₀ Q' s) - (M.consumption z₀ Q s - M.consumption z₀ Q' s) := by
    simp only [consumption]
    ring
  have hRs : |M.returnAt z₀ Q s.2.node - M.returnAt z₀ Q' s.2.node| ≤ η / w := by
    rw [le_div_iff₀ hw0, mul_comm]
    exact hR s.2.node
  have hws : |M.wageAt z₀ Q s.2.node - M.wageAt z₀ Q' s.2.node| ≤ η / w := by
    rw [le_div_iff₀ hw0, mul_comm]
    exact hw s.2.node
  have h1 : w * |M.cash z₀ Q s - M.cash z₀ Q' s| ≤ M.cashScale * η := by
    have hc := ContractionBase.cash_gap_price z₀ Q Q' s hRs hws
    calc _ ≤ w * (η / w * M.cashScale) := mul_le_mul_of_nonneg_left hc hw0.le
      _ = M.cashScale * η := by field_simp
  have h2 : w * |M.consumption z₀ Q s - M.consumption z₀ Q' s| ≤ H.A₁ * η / H.m := by
    rw [le_div_iff₀ H.m_pos]
    calc _ = w * (H.m * |M.consumption z₀ Q s - M.consumption z₀ Q' s|) := by ring
      _ ≤ w * |H.U.du (M.consumption z₀ Q s) - H.U.du (M.consumption z₀ Q' s)| :=
          mul_le_mul_of_nonneg_left hcons hw0.le
      _ ≤ H.A₁ * η := hdu
  rw [e]
  calc _ ≤ w * (|M.cash z₀ Q s - M.cash z₀ Q' s|
          + |M.consumption z₀ Q s - M.consumption z₀ Q' s|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hw0.le
    _ = w * |M.cash z₀ Q s - M.cash z₀ Q' s|
        + w * |M.consumption z₀ Q s - M.consumption z₀ Q' s| := by ring
    _ ≤ M.cashScale * η + H.A₁ * η / H.m := add_le_add h1 h2
    _ = H.G₁ * η := by simp only [G₁]; ring

end ContractionBase

/-! ### The two-part distance -/

/-- **`ν` and `ν'` are within `(da, dm)`**: every bounded continuous function that is
`L`-Lipschitz in assets and has oscillation at most `B` integrates to within `L da + B dm`. -/
def Dist2 (da dm : ℝ) (ν ν' : Measure M.AState) : Prop :=
  ∀ L B : ℝ, 0 ≤ L → ∀ f : M.AState →ᵇ ℝ, AssetLip L f → (∀ x y, f x - f y ≤ B) →
    |∫ x, f x ∂ν - ∫ x, f x ∂ν'| ≤ L * da + B * dm

/-- **Any two distributions are within `(0, 1)`.** -/
theorem dist2_zero_one (ν ν' : Measure M.AState) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] : Dist2 0 1 ν ν' := by
  intro L B _ f _ hB
  rw [mul_zero, zero_add, mul_one]
  have key : ∀ (μ μ' : Measure M.AState) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'],
      ∫ x, f x ∂μ - ∫ x, f x ∂μ' ≤ B := by
    intro μ μ' _ _
    have h1 : ∀ x, f x - ∫ y, f y ∂μ' ≤ B := by
      intro x
      have := integral_mono (μ := μ') (f := fun y => f x - f y) (g := fun _ => B)
        ((integrable_const (f x)).sub (f.integrable μ')) (integrable_const B) (fun y => hB x y)
      rwa [integral_sub (integrable_const _) (f.integrable μ'), integral_const, integral_const,
        probReal_univ, one_smul, one_smul] at this
    have := integral_mono (μ := μ) (f := fun x => f x - ∫ y, f y ∂μ') (g := fun _ => B)
      ((f.integrable μ).sub (integrable_const _)) (integrable_const B) h1
    rwa [integral_sub (f.integrable μ) (integrable_const _), integral_const, integral_const,
      probReal_univ, one_smul, one_smul] at this
  rw [abs_le]
  constructor
  · have := key ν' ν
    linarith
  · exact key ν ν'

/-- **Mean capital differs by at most `da + ā dm`.** -/
theorem Dist2.capital {da dm : ℝ} {ν ν' : Measure M.AState} (hd : Dist2 da dm ν ν') :
    |∫ x, M.assets x ∂ν - ∫ x, M.assets x ∂ν'| ≤ da + M.assetCap * dm := by
  have := hd 1 M.assetCap zero_le_one M.assets assetLip_assets fun x y => by
    change (x.1 : ℝ) - y.1 ≤ M.assetCap
    linarith [x.1.2.2, y.1.2.1]
  rwa [one_mul] at this

/-- Efficiency as a function on states. -/
noncomputable def effState (M : KSModel Z E) : M.AState →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => M.efficiency x.2.idio,
      (continuous_of_discreteTopology (f := fun i : Idio E => M.efficiency i.idio)).comp
        continuous_snd⟩

/-- **Labour differs by at most `(Σ e) dm`.** -/
theorem Dist2.labour {da dm : ℝ} {ν ν' : Measure M.AState} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (hd : Dist2 da dm ν ν') :
    |∑ e, M.initMass ν e * M.efficiency e - ∑ e, M.initMass ν' e * M.efficiency e|
      ≤ (∑ e, M.efficiency e) * dm := by
  have hlip : AssetLip 0 M.effState := fun a b i => by
    change |M.efficiency i.idio - M.efficiency i.idio| ≤ _
    simp
  have hosc : ∀ x y, M.effState x - M.effState y ≤ ∑ e, M.efficiency e := fun x y => by
    change M.efficiency x.2.idio - M.efficiency y.2.idio ≤ _
    have := Finset.single_le_sum (fun e _ => M.efficiency_nonneg e) (Finset.mem_univ x.2.idio)
    linarith [M.efficiency_nonneg y.2.idio]
  have h := hd 0 _ le_rfl M.effState hlip hosc
  have hi : ∀ (μ : Measure M.AState) [IsProbabilityMeasure μ],
      ∫ x, M.effState x ∂μ = ∑ e, M.initMass μ e * M.efficiency e := by
    intro μ _
    have := M.integral_of_idio (μ := μ) M.efficiency
    change ∫ x, M.efficiency x.2.idio ∂μ = _
    rw [this]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  rw [hi ν, hi ν', zero_mul, zero_add] at h
  exact h

/-! ### Mixing: the pushed-forward test function -/

variable (z₀ : Z) {ε : ℝ} (hminor : ∀ z z' e e', ε ≤ M.idioProb z z' e e')

include hminor in
/-- **The employment chain mixes**: a test function of oscillation `B`, `L`-Lipschitz in assets,
is pushed forward to one of oscillation at most `L ā + (1 − |E| ε) B`. -/
theorem osc_expectedNext (K : List Z → ℝ × ℝ) (h : List Z) (z' : Z) {L B : ℝ} (hL : 0 ≤ L)
    {f : M.AState →ᵇ ℝ} (hf : AssetLip L f) (hB : ∀ x y, f x - f y ≤ B) (x y : M.AState) :
    M.expectedNext z₀ K h z' f x - M.expectedNext z₀ K h z' f y
      ≤ L * M.assetCap + (1 - Fintype.card E * ε) * B := by
  set p : E → ℝ := fun e' => M.nextProb z₀ h z' e' x
  set q : E → ℝ := fun e' => M.nextProb z₀ h z' e' y
  set u : E → ℝ := fun e' => f (M.nextA z₀ K h e' x)
  set v : E → ℝ := fun e' => f (M.nextA z₀ K h e' y)
  change ∑ e', p e' * u e' - ∑ e', q e' * v e' ≤ _
  have hp1 : ∑ e', p e' = 1 := M.sum_nextProb z₀ h z' x
  have hq1 : ∑ e', q e' = 1 := M.sum_nextProb z₀ h z' y
  have hpε : ∀ e', ε ≤ p e' := fun e' => hminor _ _ _ _
  have hqε : ∀ e', ε ≤ q e' := fun e' => hminor _ _ _ _
  have e : ∑ e', p e' * u e' - ∑ e', q e' * v e'
      = ∑ e', p e' * (u e' - v e')
        + (∑ e', (p e' - ε) * v e' - ∑ e', (q e' - ε) * v e') := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [e]
  -- the assets part
  have h1 : ∑ e', p e' * (u e' - v e') ≤ L * M.assetCap := by
    have hb : ∀ e', u e' - v e' ≤ L * M.assetCap := by
      intro e'
      set a := M.clampAssets (M.policy z₀ K (x.1, ⟨x.2.idio, h⟩))
      set b := M.clampAssets (M.policy z₀ K (y.1, ⟨y.2.idio, h⟩))
      have hfa := hf a b ⟨e'⟩
      have hab : |(a : ℝ) - b| ≤ M.assetCap := by
        rw [abs_le]
        constructor <;> linarith [a.2.1, a.2.2, b.2.1, b.2.2]
      change f (a, ⟨e'⟩) - f (b, ⟨e'⟩) ≤ _
      exact (le_abs_self _).trans (hfa.trans (mul_le_mul_of_nonneg_left hab hL))
    calc _ ≤ ∑ e', p e' * (L * M.assetCap) :=
          Finset.sum_le_sum fun e' _ => mul_le_mul_of_nonneg_left (hb e')
            (M.nextProb_nonneg z₀ h z' e' x)
      _ = L * M.assetCap := by rw [← Finset.sum_mul, hp1, one_mul]
  -- the employment part
  obtain ⟨e₀, -, hmin⟩ := Finset.exists_min_image Finset.univ v ⟨x.2.idio, Finset.mem_univ _⟩
  have hv : ∀ e', v e' ≤ v e₀ + B := fun e' => by
    have := hB (M.nextA z₀ K h e' y) (M.nextA z₀ K h e₀ y)
    change v e' - v e₀ ≤ B at this
    linarith
  have hsum : ∀ r : E → ℝ, ∑ e', r e' = 1 → ∑ e', (r e' - ε) = 1 - Fintype.card E * ε := by
    intro r hr
    rw [Finset.sum_sub_distrib, hr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∑ e', (p e' - ε) * v e' ≤ (1 - Fintype.card E * ε) * (v e₀ + B) := by
    calc _ ≤ ∑ e', (p e' - ε) * (v e₀ + B) :=
          Finset.sum_le_sum fun e' _ => mul_le_mul_of_nonneg_left (hv e') (sub_nonneg.2 (hpε e'))
      _ = _ := by rw [← Finset.sum_mul, hsum p hp1]
  have h3 : (1 - Fintype.card E * ε) * v e₀ ≤ ∑ e', (q e' - ε) * v e' := by
    calc _ = ∑ e', (q e' - ε) * v e₀ := by rw [← Finset.sum_mul, hsum q hq1]
      _ ≤ _ := Finset.sum_le_sum fun e' _ =>
          mul_le_mul_of_nonneg_left (hmin e' (Finset.mem_univ _)) (sub_nonneg.2 (hqε e'))
  nlinarith [h1, h2, h3]

/-! ### Down the tree -/

/-- The asset part of the distance down the tree: `θ da + ā dm + P` each step. -/
def daPath (θ c a da dm : ℝ) (P : List Z → ℝ) : List Z → ℝ
  | [] => da
  | _ :: h => θ * daPath θ c a da dm P h + a * (c ^ h.length * dm) + P h

include hminor in
/-- **Distributions from two roots down the tree** are within `(daPath, c^{|h|} dm)`. -/
theorem dist2_nodeDist {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : M.SavingSlope θ)
    (μ₀ μ₁ : Measure M.AState) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (K K' : List Z → ℝ × ℝ) (P : List Z → ℝ)
    (hP : ∀ h (x : M.AState),
      |M.policy z₀ K (x.1, ⟨x.2.idio, h⟩) - M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩)| ≤ P h)
    {da dm : ℝ} (h0 : Dist2 da dm μ₀ μ₁) :
    ∀ h : List Z, Dist2 (daPath θ (1 - Fintype.card E * ε) M.assetCap da dm P h)
      ((1 - Fintype.card E * ε) ^ h.length * dm) (M.nodeDist z₀ μ₀ K h) (M.nodeDist z₀ μ₁ K' h)
  | [] => by
    simp only [daPath, List.length_nil, pow_zero, one_mul]
    exact h0
  | z' :: h => by
    intro L B hL f hf hB
    have := M.isProbabilityMeasure_nodeDist z₀ μ₀ K h
    have := M.isProbabilityMeasure_nodeDist z₀ μ₁ K' h
    have hd : ∫ x, f x ∂(M.nodeDist z₀ μ₀ K (z' :: h))
        = ∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K h) :=
      M.integral_pushNode z₀ K h z' _ f
    have hd' : ∫ x, f x ∂(M.nodeDist z₀ μ₁ K' (z' :: h))
        = ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₁ K' h) :=
      M.integral_pushNode z₀ K' h z' _ f
    rw [hd, hd']
    have h1 := dist2_nodeDist hθ0 hθ μ₀ μ₁ K K' P hP h0 h (θ * L)
      (L * M.assetCap + (1 - Fintype.card E * ε) * B) (mul_nonneg hθ0 hL)
      (M.expectedNext z₀ K h z' f) (M.assetLip_expectedNext_of_slope z₀ hθ K h z' hL hf)
      (M.osc_expectedNext z₀ hminor K h z' hL hf hB)
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
    calc _ ≤ |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K h)
            - ∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₁ K' h)|
          + |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₁ K' h)
            - ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₁ K' h)| :=
          abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by simp only [daPath, List.length_cons, pow_succ]; ring

/-! ### Equilibrium price gaps, the law of motion and the sequence state -/

namespace SlopeContraction

variable (S : M.SlopeContraction)

theorem gain_eq : S.gain = S.B.ℓ * S.B.G₁ := by
  simp only [gain, ContractionBase.G₁, S.B.A_eq_mul]
  field_simp

/-- The weight of the employment-marginal distance in prices, `K_d`. -/
noncomputable def labourGap (ℓL : ℝ) : ℝ :=
  S.B.ℓ * M.assetCap * (1 + S.B.lam / (1 - S.B.lam * S.θ)) + ℓL * ∑ e, M.efficiency e

/-- The coupling of the employment-marginal distance into the asset distance, `J`. -/
noncomputable def histJ (ℓL : ℝ) : ℝ := M.assetCap + S.B.G₁ * S.labourGap ℓL / (1 - S.κ)

/-- The weight on the employment-marginal distance, `ω = 2 J / (1 − c) + 1`. -/
noncomputable def histWeight (ℓL ε : ℝ) : ℝ :=
  2 * S.histJ ℓL / (1 - (1 - Fintype.card E * ε)) + 1

/-- The contraction rate with history-dependent marginals, `r* = max r_θ ((1 + c) / 2)`. -/
noncomputable def histRate (ε : ℝ) : ℝ := max S.rate ((1 + (1 - Fintype.card E * ε)) / 2)

theorem labourGap_nonneg {ℓL : ℝ} (hℓL : 0 ≤ ℓL) : 0 ≤ S.labourGap ℓL := by
  have h1 : 0 ≤ 1 - S.B.lam * S.θ := sub_nonneg.2 S.lam_slope_lt.le
  refine add_nonneg (mul_nonneg (mul_nonneg S.B.ℓ_nonneg M.assetCap_pos.le) ?_)
    (mul_nonneg hℓL (Finset.sum_nonneg fun e _ => M.efficiency_nonneg e))
  have := div_nonneg S.B.lam_pos.le h1
  linarith

theorem histJ_nonneg {ℓL : ℝ} (hℓL : 0 ≤ ℓL) (hκ : S.κ < 1) : 0 ≤ S.histJ ℓL :=
  add_nonneg M.assetCap_pos.le (div_nonneg (mul_nonneg S.B.G₁_nonneg (S.labourGap_nonneg hℓL))
    (sub_pos.2 hκ).le)

theorem weighted_daPath {c da dm b : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hda : 0 ≤ da)
    (hdm : 0 ≤ dm) (hb : 0 ≤ b) :
    ∀ h : List Z, S.B.lam ^ h.length * daPath S.θ c M.assetCap da dm
        (fun h : List Z => S.B.G₁ * b / S.B.lam ^ h.length) h
      ≤ da + S.B.lam * (M.assetCap * dm + S.B.G₁ * b) / (1 - S.B.lam * S.θ)
  | [] => by
    simp only [daPath, List.length_nil, pow_zero, one_mul]
    have := div_nonneg (mul_nonneg S.B.lam_pos.le (add_nonneg (mul_nonneg M.assetCap_pos.le hdm)
      (mul_nonneg S.B.G₁_nonneg hb))) (sub_nonneg.2 S.lam_slope_lt.le)
    linarith
  | z :: h => by
    have ih := weighted_daPath hc0 hc1 hda hdm hb h
    set X := S.B.lam * (M.assetCap * dm + S.B.G₁ * b) / (1 - S.B.lam * S.θ)
    have hX : X * (1 - S.B.lam * S.θ) = S.B.lam * (M.assetCap * dm + S.B.G₁ * b) :=
      div_mul_cancel₀ _ (ne_of_gt (sub_pos.2 S.lam_slope_lt))
    have hne : S.B.lam ^ h.length ≠ 0 := (pow_pos S.B.lam_pos _).ne'
    set D := daPath S.θ c M.assetCap da dm (fun h : List Z => S.B.G₁ * b / S.B.lam ^ h.length) h
    have e : S.B.lam ^ (z :: h).length * daPath S.θ c M.assetCap da dm
          (fun h : List Z => S.B.G₁ * b / S.B.lam ^ h.length) (z :: h)
        = S.B.lam * S.θ * (S.B.lam ^ h.length * D)
          + S.B.lam * M.assetCap * ((S.B.lam * c) ^ h.length * dm) + S.B.lam * (S.B.G₁ * b) := by
      simp only [daPath, List.length_cons, pow_succ, mul_pow, D]
      field_simp
    rw [e]
    have hlc : (S.B.lam * c) ^ h.length ≤ 1 :=
      pow_le_one₀ (mul_nonneg S.B.lam_pos.le hc0)
        (by nlinarith [S.B.lam_le_one, S.B.lam_pos])
    have hlr : 0 ≤ S.B.lam * S.θ := mul_nonneg S.B.lam_pos.le S.θ_nonneg
    have h1 := mul_le_mul_of_nonneg_left ih hlr
    have h2 : S.B.lam * S.θ * da ≤ da := mul_le_of_le_one_left hda S.lam_slope_lt.le
    have h3 : S.B.lam * M.assetCap * ((S.B.lam * c) ^ h.length * dm)
        ≤ S.B.lam * M.assetCap * dm := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg S.B.lam_pos.le M.assetCap_pos.le)
      calc _ ≤ 1 * dm := mul_le_mul_of_nonneg_right hlc hdm
        _ = dm := one_mul _
    have h4 : S.B.lam * S.θ * (da + X) = S.B.lam * S.θ * da + S.B.lam * S.θ * X := by ring
    have h5 : S.B.lam * S.θ * X + S.B.lam * (M.assetCap * dm + S.B.G₁ * b) = X := by
      linarith [hX]
    nlinarith

variable {ℓL : ℝ} (hℓL : 0 ≤ ℓL)
  (hRL : ∀ z k L L', |M.grossReturn z k L - M.grossReturn z k L'| ≤ ℓL * |L - L'|)
  (hwL : ∀ z k L L', |M.wage z k L - M.wage z k L'| ≤ ℓL * |L - L'|)
  (hε : 0 < ε)

include hminor in
theorem mix_nonneg [Nonempty E] (z : Z) : 0 ≤ 1 - Fintype.card E * ε := by
  obtain ⟨e₀⟩ := (inferInstance : Nonempty E)
  have h1 := M.idioProb_sum z z e₀
  have h2 : ∑ e' : E, ε ≤ ∑ e', M.idioProb z z e₀ e' :=
    Finset.sum_le_sum fun e' _ => hminor _ _ _ _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h1] at h2
  linarith

include hε in
theorem mix_lt_one [Nonempty E] : 1 - Fintype.card E * ε < 1 := by
  have hE : 0 < (Fintype.card E : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have := mul_pos hE hε
  linarith

variable {z : Z} {ν ν' : ProbabilityMeasure M.AState} {da dm : ℝ}

include hℓL hRL hwL hε hminor in
/-- **Two sequential equilibria from distributions within `(da, dm)`**: the weighted price gap
`ℓ |ΔK| + ℓ_L |ΔL|` is at most `(ℓ da + K_d dm) / (1 − κ_θ)`. -/
theorem seqEq_priceGap [Nonempty E] (hκ : S.κ < 1) (hda : 0 ≤ da) (hdm : 0 ≤ dm)
    (hd : Dist2 da dm (ν : Measure M.AState) ν') {K K' : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium z (ν : Measure M.AState) K)
    (hK' : M.IsSequentialEquilibrium z (ν' : Measure M.AState) K') (h : List Z) :
    S.B.lam ^ h.length * (S.B.ℓ * |K h - K' h|
        + ℓL * |M.labour z (M.initMass (ν : Measure M.AState)) h
          - M.labour z (M.initMass (ν' : Measure M.AState)) h|)
      ≤ (S.B.ℓ * da + S.labourGap ℓL * dm) / (1 - S.κ) := by
  have : Nonempty Z := ⟨z⟩
  set m := M.initMass (ν : Measure M.AState)
  set m' := M.initMass (ν' : Measure M.AState)
  set Q := M.pricePath z m K
  set Q' := M.pricePath z m' K'
  set c := 1 - Fintype.card E * ε
  have hc0 : 0 ≤ c := mix_nonneg hminor z
  have hc1 : c ≤ 1 := (mix_lt_one hε).le
  set ρ : List Z → ℝ := fun h => S.B.ℓ * |K h - K' h| + ℓL * |M.labour z m h - M.labour z m' h|
  have h1κ : 0 < 1 - S.κ := sub_pos.2 hκ
  set Φ := S.B.ℓ * da + S.labourGap ℓL * dm
  have hΦ : 0 ≤ Φ := add_nonneg (mul_nonneg S.B.ℓ_nonneg hda)
    (mul_nonneg (S.labourGap_nonneg hℓL) hdm)
  -- price gaps from capital and labour gaps
  have hRgap : ∀ h, |M.returnAt z Q h - M.returnAt z Q' h| ≤ ρ h := by
    intro h
    change |M.grossReturn (shockAt z h) (K h) (M.labour z m h)
        - M.grossReturn (shockAt z h) (K' h) (M.labour z m' h)| ≤ _
    calc _ ≤ |M.grossReturn (shockAt z h) (K h) (M.labour z m h)
            - M.grossReturn (shockAt z h) (K' h) (M.labour z m h)|
          + |M.grossReturn (shockAt z h) (K' h) (M.labour z m h)
            - M.grossReturn (shockAt z h) (K' h) (M.labour z m' h)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (S.B.return_lip _ _ _ _) (hRL _ _ _ _)
  have hwgap : ∀ h, |M.wageAt z Q h - M.wageAt z Q' h| ≤ ρ h := by
    intro h
    change |M.wage (shockAt z h) (K h) (M.labour z m h)
        - M.wage (shockAt z h) (K' h) (M.labour z m' h)| ≤ _
    calc _ ≤ |M.wage (shockAt z h) (K h) (M.labour z m h)
            - M.wage (shockAt z h) (K' h) (M.labour z m h)|
          + |M.wage (shockAt z h) (K' h) (M.labour z m h)
            - M.wage (shockAt z h) (K' h) (M.labour z m' h)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (S.B.wage_lip _ _ _ _) (hwL _ _ _ _)
  -- one step
  have step : ∀ b, 0 ≤ b → (∀ h : List Z, S.B.lam ^ h.length * ρ h ≤ b) →
      ∀ h : List Z, S.B.lam ^ h.length * ρ h ≤ Φ + S.κ * b := by
    intro b hb0 hb h
    have hR' : ∀ h : List Z, S.B.lam ^ h.length * |M.returnAt z Q h - M.returnAt z Q' h| ≤ b :=
      fun h => (mul_le_mul_of_nonneg_left (hRgap h) (pow_nonneg S.B.lam_pos.le _)).trans (hb h)
    have hw' : ∀ h : List Z, S.B.lam ^ h.length * |M.wageAt z Q h - M.wageAt z Q' h| ≤ b :=
      fun h => (mul_le_mul_of_nonneg_left (hwgap h) (pow_nonneg S.B.lam_pos.le _)).trans (hb h)
    have hP : ∀ h (x : M.AState),
        |M.policy z Q (x.1, ⟨x.2.idio, h⟩) - M.policy z Q' (x.1, ⟨x.2.idio, h⟩)|
          ≤ (fun h : List Z => S.B.G₁ * b / S.B.lam ^ h.length) h := by
      intro h x
      rw [le_div_iff₀ (pow_pos S.B.lam_pos _), mul_comm]
      exact S.B.weighted_policy_gap_price z Q Q' hb0 hR' hw' (x.1, ⟨x.2.idio, h⟩)
    have hD := M.dist2_nodeDist z hminor S.θ_nonneg S.slope (ν : Measure M.AState) ν' Q Q' _ hP
      hd h
    have := M.isProbabilityMeasure_nodeDist z (ν : Measure M.AState) Q h
    have := M.isProbabilityMeasure_nodeDist z (ν' : Measure M.AState) Q' h
    have hKc := hD.capital
    have hLc := hD.labour
    rw [M.initMass_nodeDist z, M.initMass_nodeDist z] at hLc
    have eK : K h = ∫ x, M.assets x ∂(M.nodeDist z (ν : Measure M.AState) Q h) := hK h
    have eK' : K' h = ∫ x, M.assets x ∂(M.nodeDist z (ν' : Measure M.AState) Q' h) := hK' h
    rw [← eK, ← eK'] at hKc
    have eL : ∀ m₀ : E → ℝ, M.labour z m₀ h = ∑ e, M.stateMass z m₀ h e * M.efficiency e :=
      fun _ => rfl
    rw [← eL, ← eL] at hLc
    set D := daPath S.θ c M.assetCap da dm (fun h : List Z => S.B.G₁ * b / S.B.lam ^ h.length) h
    have hwD := S.weighted_daPath hc0 hc1 hda hdm hb0 h
    have hlc : S.B.lam ^ h.length * c ^ h.length ≤ 1 := by
      rw [← mul_pow]
      exact pow_le_one₀ (mul_nonneg S.B.lam_pos.le hc0) (by nlinarith [S.B.lam_le_one, S.B.lam_pos])
    have hW := pow_nonneg S.B.lam_pos.le h.length
    have hcm : S.B.lam ^ h.length * (c ^ h.length * dm) ≤ dm := by
      rw [← mul_assoc]
      calc _ ≤ 1 * dm := mul_le_mul_of_nonneg_right hlc hdm
        _ = dm := one_mul _
    have hk1 : S.B.lam ^ h.length * |K h - K' h|
        ≤ da + S.B.lam * (M.assetCap * dm + S.B.G₁ * b) / (1 - S.B.lam * S.θ)
          + M.assetCap * dm := by
      calc _ ≤ S.B.lam ^ h.length * (D + M.assetCap * (c ^ h.length * dm)) :=
            mul_le_mul_of_nonneg_left hKc hW
        _ = S.B.lam ^ h.length * D + M.assetCap * (S.B.lam ^ h.length * (c ^ h.length * dm)) := by
            ring
        _ ≤ _ := add_le_add hwD (mul_le_mul_of_nonneg_left hcm M.assetCap_pos.le)
    have hl1 : S.B.lam ^ h.length * |M.labour z m h - M.labour z m' h|
        ≤ (∑ e, M.efficiency e) * dm := by
      calc _ ≤ S.B.lam ^ h.length * ((∑ e, M.efficiency e) * (c ^ h.length * dm)) :=
            mul_le_mul_of_nonneg_left hLc hW
        _ = (∑ e, M.efficiency e) * (S.B.lam ^ h.length * (c ^ h.length * dm)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcm
            (Finset.sum_nonneg fun e _ => M.efficiency_nonneg e)
    have hκe : S.κ = S.B.lam * (S.B.ℓ * S.B.G₁) / (1 - S.B.lam * S.θ) := by
      rw [κ, S.gain_eq]
    have hden : 0 < 1 - S.B.lam * S.θ := sub_pos.2 S.lam_slope_lt
    calc S.B.lam ^ h.length * ρ h
        = S.B.ℓ * (S.B.lam ^ h.length * |K h - K' h|)
          + ℓL * (S.B.lam ^ h.length * |M.labour z m h - M.labour z m' h|) := by
          simp only [ρ]; ring
      _ ≤ S.B.ℓ * (da + S.B.lam * (M.assetCap * dm + S.B.G₁ * b) / (1 - S.B.lam * S.θ)
            + M.assetCap * dm) + ℓL * ((∑ e, M.efficiency e) * dm) :=
          add_le_add (mul_le_mul_of_nonneg_left hk1 S.B.ℓ_nonneg)
            (mul_le_mul_of_nonneg_left hl1 hℓL)
      _ = Φ + S.κ * b := by
          rw [hκe]
          simp only [Φ, labourGap]
          field_simp
          ring
  -- a priori bound and iteration
  set b₀ := S.B.ℓ * M.assetCap + ℓL * ∑ e, M.efficiency e
  have hb₀ : 0 ≤ b₀ := add_nonneg (mul_nonneg S.B.ℓ_nonneg M.assetCap_pos.le)
    (mul_nonneg hℓL (Finset.sum_nonneg fun e _ => M.efficiency_nonneg e))
  have hρ0 : ∀ h : List Z, S.B.lam ^ h.length * ρ h ≤ b₀ := by
    intro h
    have h1 := M.meanCapital_mem z (ν : Measure M.AState) Q h
    have h2 := M.meanCapital_mem z (ν' : Measure M.AState) Q' h
    have e1 : K h = M.meanCapital z (ν : Measure M.AState) Q h := hK h
    have e2 : K' h = M.meanCapital z (ν' : Measure M.AState) Q' h := hK' h
    rw [← e1] at h1
    rw [← e2] at h2
    have hKb : |K h - K' h| ≤ M.assetCap :=
      abs_sub_le_iff.2 ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩
    have hs : ∀ e, M.efficiency e ≤ ∑ e, M.efficiency e := fun e =>
      Finset.single_le_sum (fun e _ => M.efficiency_nonneg e) (Finset.mem_univ e)
    have l1 := M.labour_mem z (ν : Measure M.AState) M.efficiency_nonneg hs h
    have l2 := M.labour_mem z (ν' : Measure M.AState) M.efficiency_nonneg hs h
    have hLb : |M.labour z m h - M.labour z m' h| ≤ ∑ e, M.efficiency e :=
      abs_sub_le_iff.2 ⟨by linarith [l1.2, l2.1], by linarith [l1.1, l2.2]⟩
    have hρb : ρ h ≤ b₀ := add_le_add (mul_le_mul_of_nonneg_left hKb S.B.ℓ_nonneg)
      (mul_le_mul_of_nonneg_left hLb hℓL)
    have hρ0' : 0 ≤ ρ h := add_nonneg (mul_nonneg S.B.ℓ_nonneg (abs_nonneg _))
      (mul_nonneg hℓL (abs_nonneg _))
    calc _ ≤ 1 * ρ h :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ S.B.lam_pos.le S.B.lam_le_one) hρ0'
      _ ≤ b₀ := by rw [one_mul]; exact hρb
  have hiter : ∀ n : ℕ, ∀ h : List Z,
      S.B.lam ^ h.length * ρ h ≤ Φ / (1 - S.κ) + S.κ ^ n * b₀ := by
    intro n
    induction n with
    | zero =>
      intro h
      have := div_nonneg hΦ h1κ.le
      rw [pow_zero, one_mul]
      linarith [hρ0 h]
    | succ n ih =>
      intro h
      have hb0 : 0 ≤ Φ / (1 - S.κ) + S.κ ^ n * b₀ :=
        add_nonneg (div_nonneg hΦ h1κ.le) (mul_nonneg (pow_nonneg S.κ_nonneg n) hb₀)
      have := step _ hb0 ih h
      have e : Φ + S.κ * (Φ / (1 - S.κ) + S.κ ^ n * b₀) = Φ / (1 - S.κ) + S.κ ^ (n + 1) * b₀ := by
        field_simp
        ring
      rwa [e] at this
  have hlim : Tendsto (fun n : ℕ => Φ / (1 - S.κ) + S.κ ^ n * b₀) atTop
      (𝓝 (Φ / (1 - S.κ) + 0 * b₀)) :=
    tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one S.κ_nonneg hκ).mul tendsto_const_nhds)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim fun n => hiter n h

include hℓL hRL hwL hε hminor in
/-- The weighted return and wage gaps of the equilibrium paths. -/
theorem eqPath_priceGap [Nonempty E] (hκ : S.κ < 1) (hda : 0 ≤ da) (hdm : 0 ≤ dm)
    (hd : Dist2 da dm (ν : Measure M.AState) ν') :
    (∀ h : List Z, S.B.lam ^ h.length
        * |M.returnAt z (M.pricePath z (M.initMass (ν : Measure M.AState)) (M.eqPath z ν)) h
          - M.returnAt z (M.pricePath z (M.initMass (ν' : Measure M.AState)) (M.eqPath z ν')) h|
        ≤ (S.B.ℓ * da + S.labourGap ℓL * dm) / (1 - S.κ)) ∧
      (∀ h : List Z, S.B.lam ^ h.length
        * |M.wageAt z (M.pricePath z (M.initMass (ν : Measure M.AState)) (M.eqPath z ν)) h
          - M.wageAt z (M.pricePath z (M.initMass (ν' : Measure M.AState)) (M.eqPath z ν')) h|
        ≤ (S.B.ℓ * da + S.labourGap ℓL * dm) / (1 - S.κ)) := by
  have hg := S.seqEq_priceGap hminor hℓL hRL hwL hε hκ hda hdm hd (M.eqPath_spec z ν)
    (M.eqPath_spec z ν')
  constructor
  · intro h
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg S.B.lam_pos.le _)) (hg h)
    change |M.grossReturn (shockAt z h) (M.eqPath z ν h)
        (M.labour z (M.initMass (ν : Measure M.AState)) h)
        - M.grossReturn (shockAt z h) (M.eqPath z ν' h)
          (M.labour z (M.initMass (ν' : Measure M.AState)) h)| ≤ _
    exact (abs_sub_le _ (M.grossReturn (shockAt z h) (M.eqPath z ν' h)
      (M.labour z (M.initMass (ν : Measure M.AState)) h)) _).trans
      (add_le_add (S.B.return_lip _ _ _ _) (hRL _ _ _ _))
  · intro h
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg S.B.lam_pos.le _)) (hg h)
    change |M.wage (shockAt z h) (M.eqPath z ν h)
        (M.labour z (M.initMass (ν : Measure M.AState)) h)
        - M.wage (shockAt z h) (M.eqPath z ν' h)
          (M.labour z (M.initMass (ν' : Measure M.AState)) h)| ≤ _
    exact (abs_sub_le _ (M.wage (shockAt z h) (M.eqPath z ν' h)
      (M.labour z (M.initMass (ν : Measure M.AState)) h)) _).trans
      (add_le_add (S.B.wage_lip _ _ _ _) (hwL _ _ _ _))

include hℓL hRL hwL hε hminor in
/-- **Today's saving policies from distributions within `(da, dm)`** differ by at most
`G₁ (ℓ da + K_d dm) / (1 − κ_θ)`. -/
theorem recursivePolicy_gap2 [Nonempty E] (hκ : S.κ < 1) (hda : 0 ≤ da) (hdm : 0 ≤ dm)
    (hd : Dist2 da dm (ν : Measure M.AState) ν') (x : M.AState) :
    |M.recursivePolicy z ν x - M.recursivePolicy z ν' x|
      ≤ S.B.G₁ * ((S.B.ℓ * da + S.labourGap ℓL * dm) / (1 - S.κ)) := by
  have : Nonempty Z := ⟨z⟩
  obtain ⟨hR, hw⟩ := S.eqPath_priceGap hminor hℓL hRL hwL hε hκ hda hdm hd
  have hη0 : 0 ≤ (S.B.ℓ * da + S.labourGap ℓL * dm) / (1 - S.κ) :=
    div_nonneg (add_nonneg (mul_nonneg S.B.ℓ_nonneg hda) (mul_nonneg (S.labourGap_nonneg hℓL) hdm))
      (sub_pos.2 hκ).le
  have := S.B.weighted_policy_gap_price z _ _ hη0 hR hw (x.1, ⟨x.2.idio, []⟩)
  simp only [List.length_nil, pow_zero, one_mul] at this
  exact this

include hℓL hRL hwL hε hminor in
/-- **The law of motion with history-dependent marginals**: distributions within `(da, dm)` go
to distributions within `(θ da + ā dm + G₁ (ℓ da + K_d dm) / (1 − κ_θ), c dm)`. -/
theorem dist2_lawOfMotion [Nonempty E] (hκ : S.κ < 1) (hda : 0 ≤ da) (hdm : 0 ≤ dm)
    (hd : Dist2 da dm (ν : Measure M.AState) ν') (z' : Z) :
    Dist2 (S.θ * da + M.assetCap * dm
        + S.B.G₁ * ((S.B.ℓ * da + S.labourGap ℓL * dm) / (1 - S.κ)))
      ((1 - Fintype.card E * ε) * dm)
      (M.lawOfMotion z ν z' : Measure M.AState) (M.lawOfMotion z ν' z') := by
  have : Nonempty Z := ⟨z⟩
  obtain ⟨hR, hw⟩ := S.eqPath_priceGap hminor hℓL hRL hwL hε hκ hda hdm hd
  set η := (S.B.ℓ * da + S.labourGap ℓL * dm) / (1 - S.κ)
  have hη0 : 0 ≤ η :=
    div_nonneg (add_nonneg (mul_nonneg S.B.ℓ_nonneg hda) (mul_nonneg (S.labourGap_nonneg hℓL) hdm))
      (sub_pos.2 hκ).le
  have hP : ∀ h (x : M.AState),
      |M.policy z (M.pricePath z (M.initMass (ν : Measure M.AState)) (M.eqPath z ν))
          (x.1, ⟨x.2.idio, h⟩)
        - M.policy z (M.pricePath z (M.initMass (ν' : Measure M.AState)) (M.eqPath z ν'))
          (x.1, ⟨x.2.idio, h⟩)|
        ≤ (fun h : List Z => S.B.G₁ * η / S.B.lam ^ h.length) h := by
    intro h x
    rw [le_div_iff₀ (pow_pos S.B.lam_pos _), mul_comm]
    exact S.B.weighted_policy_gap_price z _ _ hη0 hR hw (x.1, ⟨x.2.idio, h⟩)
  have hD := M.dist2_nodeDist z hminor S.θ_nonneg S.slope (ν : Measure M.AState) ν' _ _ _ hP hd
    [z']
  simp only [daPath, List.length_nil, pow_zero, one_mul, div_one, List.length_cons, zero_add,
    pow_one] at hD
  exact hD

include hℓL hε hminor in
/-- **The law of motion contracts in the norm `da + ω dm`** at the rate `r*`. -/
theorem norm_step [Nonempty E] (hκ : S.κ < 1) (hda : 0 ≤ da) (hdm : 0 ≤ dm) (z : Z) :
    (S.θ * da + M.assetCap * dm + S.B.G₁ * ((S.B.ℓ * da + S.labourGap ℓL * dm) / (1 - S.κ)))
        + S.histWeight ℓL ε * ((1 - Fintype.card E * ε) * dm)
      ≤ S.histRate ε * (da + S.histWeight ℓL ε * dm) := by
  set c := 1 - Fintype.card E * ε
  have hc0 : 0 ≤ c := mix_nonneg hminor z
  have hc1 : c < 1 := mix_lt_one hε
  have h1κ : 0 < 1 - S.κ := sub_pos.2 hκ
  set J := S.histJ ℓL
  have hJ : 0 ≤ J := S.histJ_nonneg hℓL hκ
  set w := S.histWeight ℓL ε
  have hw : w = 2 * J / (1 - c) + 1 := rfl
  have h1c : 0 < 1 - c := sub_pos.2 hc1
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hwJ : J + w * c ≤ (1 + c) / 2 * w := by
    have e : (1 + c) / 2 * w - w * c = J + (1 - c) / 2 := by
      rw [hw]
      field_simp
      ring
    linarith
  have hrate : S.rate = S.θ + S.B.ℓ * S.B.G₁ / (1 - S.κ) := by rw [rate, S.gain_eq]
  have e1 : S.θ * da + M.assetCap * dm
        + S.B.G₁ * ((S.B.ℓ * da + S.labourGap ℓL * dm) / (1 - S.κ)) + w * (c * dm)
      = S.rate * da + (J + w * c) * dm := by
    rw [hrate]
    simp only [J, histJ]
    field_simp
    ring
  rw [e1]
  have hr1 : S.rate ≤ S.histRate ε := le_max_left _ _
  have hr2 : (1 + c) / 2 ≤ S.histRate ε := le_max_right _ _
  have h2 : (J + w * c) * dm ≤ S.histRate ε * w * dm :=
    mul_le_mul_of_nonneg_right (hwJ.trans (mul_le_mul_of_nonneg_right hr2 hw0)) hdm
  have h3 : S.rate * da ≤ S.histRate ε * da := mul_le_mul_of_nonneg_right hr1 hda
  nlinarith [h2, h3]

include hε in
theorem histRate_lt_one [Nonempty E] (hr : S.rate < 1) : S.histRate ε < 1 :=
  max_lt hr (by have := mix_lt_one (E := E) hε; linarith)

/-! ### Every sequence-state equilibrium -/

variable (hκ : S.κ < 1) {μ : History Z → ProbabilityMeasure M.AState}
  (hμ : M.IsSeqStateEquilibrium μ)

include hminor hℓL hRL hwL hε hκ hμ in
/-- **Fading memory with history-dependent marginals**: histories agreeing over their last
`T + 1` shocks carry distributions within some `(da, dm)` with `da + ω dm ≤ r* ^ T ω`. -/
theorem dist2_of_agree [Nonempty E] :
    ∀ (T : ℕ) (ω ω' : History Z), (∀ n ≤ T, ω n = ω' n) →
      ∃ da dm : ℝ, 0 ≤ da ∧ 0 ≤ dm ∧
        da + S.histWeight ℓL ε * dm ≤ S.histRate ε ^ T * S.histWeight ℓL ε ∧
        Dist2 da dm (μ ω : Measure M.AState) (μ ω') := by
  intro T
  induction T with
  | zero =>
    intro ω ω' _
    exact ⟨0, 1, le_rfl, zero_le_one, by rw [pow_zero]; linarith, dist2_zero_one _ _⟩
  | succ T ih =>
    intro ω ω' hag
    obtain ⟨da, dm, hda, hdm, hN, hD⟩ :=
      ih (History.tail ω) (History.tail ω') fun n hn => hag (n + 1) (by omega)
    have hz0 := hag 0 (by omega)
    have hz1 := hag 1 (by omega)
    rw [S.eq_lawOfMotion_tail hκ hμ ω, S.eq_lawOfMotion_tail hκ hμ ω', hz0, hz1]
    have hD' := S.dist2_lawOfMotion hminor hℓL hRL hwL hε hκ hda hdm hD (z := ω' 1) (ω' 0)
    have hc0 := mix_nonneg hminor (ω 0)
    refine ⟨_, _, ?_, mul_nonneg hc0 hdm, ?_, hD'⟩
    · exact add_nonneg (add_nonneg (mul_nonneg S.θ_nonneg hda)
        (mul_nonneg M.assetCap_pos.le hdm)) (mul_nonneg S.B.G₁_nonneg (div_nonneg
          (add_nonneg (mul_nonneg S.B.ℓ_nonneg hda) (mul_nonneg (S.labourGap_nonneg hℓL) hdm))
          (sub_pos.2 hκ).le))
    · have hstep := S.norm_step hminor hℓL hε hκ hda hdm (ω 0)
      have hr0 : 0 ≤ S.histRate ε := (S.rate_nonneg hκ).trans (le_max_left _ _)
      calc _ ≤ S.histRate ε * (da + S.histWeight ℓL ε * dm) := hstep
        _ ≤ S.histRate ε * (S.histRate ε ^ T * S.histWeight ℓL ε) :=
            mul_le_mul_of_nonneg_left hN hr0
        _ = S.histRate ε ^ (T + 1) * S.histWeight ℓL ε := by ring

include hminor hℓL hRL hwL hε hκ hμ in
/-- **Burn-in with history-dependent marginals**: start from any distribution `ν`, `T` periods
back, and run the law of motion along the realized shocks; the result is within some `(da, dm)`
of the equilibrium distribution with `da + ω dm ≤ r* ^ T ω`. No condition on `ν`'s marginal. -/
theorem dist2_run [Nonempty E] :
    ∀ (T : ℕ) (ω : History Z) (ν : ProbabilityMeasure M.AState),
      ∃ da dm : ℝ, 0 ≤ da ∧ 0 ≤ dm ∧
        da + S.histWeight ℓL ε * dm ≤ S.histRate ε ^ T * S.histWeight ℓL ε ∧
        Dist2 da dm (μ ω : Measure M.AState)
          ((run M.lawMap T ω ν : ProbabilityMeasure M.AState) : Measure M.AState) := by
  intro T
  induction T with
  | zero =>
    intro ω ν
    exact ⟨0, 1, le_rfl, zero_le_one, by rw [pow_zero]; linarith, dist2_zero_one _ _⟩
  | succ T ih =>
    intro ω ν
    obtain ⟨da, dm, hda, hdm, hN, hD⟩ := ih (History.tail ω) ν
    rw [S.eq_lawOfMotion_tail hκ hμ ω]
    have hD' := S.dist2_lawOfMotion hminor hℓL hRL hwL hε hκ hda hdm hD (z := ω 1) (ω 0)
    have hc0 := mix_nonneg hminor (ω 0)
    refine ⟨_, _, ?_, mul_nonneg hc0 hdm, ?_, hD'⟩
    · exact add_nonneg (add_nonneg (mul_nonneg S.θ_nonneg hda)
        (mul_nonneg M.assetCap_pos.le hdm)) (mul_nonneg S.B.G₁_nonneg (div_nonneg
          (add_nonneg (mul_nonneg S.B.ℓ_nonneg hda) (mul_nonneg (S.labourGap_nonneg hℓL) hdm))
          (sub_pos.2 hκ).le))
    · have hstep := S.norm_step hminor hℓL hε hκ hda hdm (ω 0)
      have hr0 : 0 ≤ S.histRate ε := (S.rate_nonneg hκ).trans (le_max_left _ _)
      calc _ ≤ S.histRate ε * (da + S.histWeight ℓL ε * dm) := hstep
        _ ≤ S.histRate ε * (S.histRate ε ^ T * S.histWeight ℓL ε) :=
            mul_le_mul_of_nonneg_left hN hr0
        _ = S.histRate ε ^ (T + 1) * S.histWeight ℓL ε := by ring

include hminor hℓL hRL hwL hε hκ hμ in
/-- **Matched expectations with history-dependent marginals**: at histories agreeing over their
last `T + 1` shocks, saving differs by at most `G₁ (ℓ ω + K_d) r* ^ T / (1 − κ_θ)`, at every
household state, in every sequence-state equilibrium. -/
theorem seqPolicy_gap_of_agree' [Nonempty E] (T : ℕ) {ω ω' : History Z}
    (hag : ∀ n ≤ T, ω n = ω' n) (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    |(M.seqPolicy μ ω a e : ℝ) - M.seqPolicy μ ω' a e|
      ≤ S.B.G₁ * ((S.B.ℓ * S.histWeight ℓL ε + S.labourGap ℓL) * S.histRate ε ^ T
        / (1 - S.κ)) := by
  have hU := S.uniqueSequentialEquilibrium hκ
  obtain ⟨da, dm, hda, hdm, hN, hD⟩ := S.dist2_of_agree hminor hℓL hRL hwL hε hκ hμ T ω ω' hag
  rw [hμ.seqPolicy_eq_recursivePolicy hU ω a e, hμ.seqPolicy_eq_recursivePolicy hU ω' a e,
    hag 0 (Nat.zero_le T)]
  have hg := S.recursivePolicy_gap2 hminor hℓL hRL hwL hε (z := ω' 0) hκ hda hdm hD (a, ⟨e⟩)
  refine hg.trans (mul_le_mul_of_nonneg_left ?_ S.B.G₁_nonneg)
  refine div_le_div_of_nonneg_right ?_ (sub_pos.2 hκ).le
  set w := S.histWeight ℓL ε
  set r := S.histRate ε ^ T
  have hw1 : 1 ≤ w := by
    have hJ := S.histJ_nonneg hℓL hκ
    have h1c : 0 < 1 - (1 - Fintype.card E * ε) := by
      have := mix_lt_one (E := E) hε
      linarith
    have : 0 ≤ 2 * S.histJ ℓL / (1 - (1 - Fintype.card E * ε)) := by positivity
    simp only [w, histWeight]
    linarith
  have hda' : da ≤ r * w := by nlinarith
  have hdm' : dm ≤ r := by
    by_contra hc
    rw [not_le] at hc
    nlinarith
  have hK := S.labourGap_nonneg hℓL
  calc S.B.ℓ * da + S.labourGap ℓL * dm ≤ S.B.ℓ * (r * w) + S.labourGap ℓL * r :=
        add_le_add (mul_le_mul_of_nonneg_left hda' S.B.ℓ_nonneg)
          (mul_le_mul_of_nonneg_left hdm' hK)
    _ = (S.B.ℓ * w + S.labourGap ℓL) * r := by ring

end SlopeContraction

end KSModel

end KrusellSmith

end LeanEconomics
