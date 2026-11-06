/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Propagation
import LeanEconomics.KrusellSmith.Recursive

/-!
# Uniqueness of sequential equilibrium when prices respond weakly to capital

Milestone M4 of `UNIQUENESS_PLAN.md`. The equilibrium map — a path of capital to the path of mean
saving it induces — is a contraction in the weighted norm `sup_h λ^{|h|} |K_h|` when prices
respond weakly enough to capital, so sequential equilibrium is unique, and by `Recursive.lean`
there is a recursive equilibrium on the minimal state.

**Hypotheses** (`ContractionHyp`), with `D = u'(c̲)`, `C = assetCap + Σ efficiency`:

* utility: `u'` is `Mdu`-Lipschitz and strongly decreasing with modulus `m` on the consumption
  range, and consumption is at least `c̲ > consFloor` along every path;
* prices: the gross return and the wage are `ℓ`-Lipschitz in capital;
* weights: `β R̄ < λ ≤ 1` and `λ R̄ < 1`.

**Constants.** With `q = β R̄ / λ`,

* `A = (β ℓ D / λ + Mdu ℓ C) / (1 − q)` — marginal-utility gaps (`weighted_du_gap`),
* `κ = λ (ℓ C + A / m) / (1 − λ R̄)` — the contraction modulus, proportional to `ℓ`.

**Theorem** (`uniqueSequentialEquilibrium`): if `κ < 1`, sequential equilibrium is unique from
every initial shock and distribution.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

/-- Assets plus total efficiency: the multiplier of price gaps in cash gaps. -/
noncomputable def cashScale (M : KSModel Z E) : ℝ := M.assetCap + ∑ e, M.efficiency e

theorem cashScale_nonneg (M : KSModel Z E) : 0 ≤ M.cashScale :=
  add_nonneg M.assetCap_pos.le (Finset.sum_nonneg fun e _ => M.efficiency_nonneg e)

theorem returnBound_nonneg [Nonempty Z] (M : KSModel Z E) : 0 ≤ M.returnBound :=
  (M.grossReturn_nonneg (Classical.arbitrary Z) 0 0).trans
    (M.grossReturn_le (Classical.arbitrary Z) 0 0)

/-- **The hypotheses of the marginal-utility and policy-gap bounds**: everything in the
contraction argument except the condition `λ R̄ < 1` on the saving slope. -/
structure ContractionBase (M : KSModel Z E) where
  U : M.SmoothUtility
  cLo : ℝ
  floor_lt_cLo : M.consFloor < cLo
  cLo_le : ∀ (z₀ : Z) (K : List Z → ℝ × ℝ) (s : M.State), cLo ≤ M.consumption z₀ K s
  Mdu : ℝ
  Mdu_nonneg : 0 ≤ Mdu
  du_lip : ∀ x y, M.consFloor < x → x ≤ y → U.du x - U.du y ≤ Mdu * (y - x)
  m : ℝ
  m_pos : 0 < m
  du_strong : ∀ x y, M.consFloor < x → x ≤ y → y ≤ M.maxCash → m * (y - x) ≤ U.du x - U.du y
  ℓ : ℝ
  ℓ_nonneg : 0 ≤ ℓ
  return_lip : ∀ z k k' L, |M.grossReturn z k L - M.grossReturn z k' L| ≤ ℓ * |k - k'|
  wage_lip : ∀ z k k' L, |M.wage z k L - M.wage z k' L| ≤ ℓ * |k - k'|
  lam : ℝ
  lam_pos : 0 < lam
  lam_le_one : lam ≤ 1
  disc_lt : M.discount * M.returnBound < lam

/-- **The hypotheses of the contraction argument**: the base hypotheses and `λ R̄ < 1`, where
`R̄` bounds the slope of saving in assets (`policy_sub_le`). -/
structure ContractionHyp (M : KSModel Z E) extends M.ContractionBase where
  lam_return_lt : lam * M.returnBound < 1

namespace ContractionBase

variable (H : M.ContractionBase)
include H

/-- The bound on marginal utility. -/
noncomputable def D : ℝ := H.U.du H.cLo

/-- The decay factor of future influences. -/
noncomputable def q : ℝ := M.discount * M.returnBound / H.lam

/-- The constant of marginal-utility gaps. -/
noncomputable def A : ℝ :=
  (M.discount * H.ℓ * H.D / H.lam + H.Mdu * H.ℓ * M.cashScale) / (1 - H.q)

/-- **The contraction modulus.** -/
noncomputable def κ : ℝ := H.lam * (H.ℓ * M.cashScale + H.A / H.m) / (1 - H.lam * M.returnBound)

theorem q_nonneg [Nonempty Z] : 0 ≤ H.q :=
  div_nonneg (mul_nonneg M.discount_pos.le M.returnBound_nonneg) H.lam_pos.le

theorem q_lt_one : H.q < 1 := by
  rw [q, div_lt_one H.lam_pos]
  exact H.disc_lt

theorem D_nonneg : 0 ≤ H.D := H.U.du_nonneg H.floor_lt_cLo

theorem A_nonneg : 0 ≤ H.A := by
  refine div_nonneg (add_nonneg ?_ ?_) (sub_nonneg.2 H.q_lt_one.le)
  · exact div_nonneg (mul_nonneg (mul_nonneg M.discount_pos.le H.ℓ_nonneg) H.D_nonneg)
      H.lam_pos.le
  · exact mul_nonneg (mul_nonneg H.Mdu_nonneg H.ℓ_nonneg) M.cashScale_nonneg

/-- The defining identity of `A`. -/
theorem A_eq : H.A * (1 - H.q) = M.discount * H.ℓ * H.D / H.lam + H.Mdu * H.ℓ * M.cashScale := by
  rw [A, div_mul_cancel₀]
  exact (sub_pos.2 H.q_lt_one).ne'

theorem slack (z₀ : Z) (K : List Z → ℝ × ℝ) : M.Slack z₀ K := fun s =>
  H.floor_lt_cLo.trans_le (H.cLo_le z₀ K s)

theorem abs_du_sub_le (z₀ : Z) (K K' : List Z → ℝ × ℝ) (s s' : M.State) :
    |H.U.du (M.consumption z₀ K s) - H.U.du (M.consumption z₀ K' s')| ≤ H.D := by
  have h1 := H.U.du_nonneg (H.slack z₀ K s)
  have h2 := H.U.du_nonneg (H.slack z₀ K' s')
  have h3 := H.U.du_anti H.floor_lt_cLo (H.cLo_le z₀ K s)
  have h4 := H.U.du_anti H.floor_lt_cLo (H.cLo_le z₀ K' s')
  rw [abs_le]
  unfold D
  constructor <;> linarith

/-! ### Price and cash gaps -/

variable (z₀ : Z) (m₀ : E → ℝ) (K K' : List Z → ℝ)

theorem returnAt_gap (h : List Z) :
    |M.returnAt z₀ (M.pricePath z₀ m₀ K) h - M.returnAt z₀ (M.pricePath z₀ m₀ K') h|
      ≤ H.ℓ * |K h - K' h| :=
  H.return_lip _ _ _ _

theorem wageAt_gap (h : List Z) :
    |M.wageAt z₀ (M.pricePath z₀ m₀ K) h - M.wageAt z₀ (M.pricePath z₀ m₀ K') h|
      ≤ H.ℓ * |K h - K' h| :=
  H.wage_lip _ _ _ _

theorem cash_gap (s : M.State) :
    |M.cash z₀ (M.pricePath z₀ m₀ K) s - M.cash z₀ (M.pricePath z₀ m₀ K') s|
      ≤ H.ℓ * |K s.2.node - K' s.2.node| * M.cashScale := by
  have hR := H.returnAt_gap z₀ m₀ K K' s.2.node
  have hw := H.wageAt_gap z₀ m₀ K K' s.2.node
  have ha := s.1.2
  have he : M.efficiency s.2.idio ≤ ∑ e, M.efficiency e :=
    Finset.single_le_sum (fun e _ => M.efficiency_nonneg e) (Finset.mem_univ _)
  have he0 := M.efficiency_nonneg s.2.idio
  have e : M.cash z₀ (M.pricePath z₀ m₀ K) s - M.cash z₀ (M.pricePath z₀ m₀ K') s
      = (M.returnAt z₀ (M.pricePath z₀ m₀ K) s.2.node
          - M.returnAt z₀ (M.pricePath z₀ m₀ K') s.2.node) * s.1
        + (M.wageAt z₀ (M.pricePath z₀ m₀ K) s.2.node
          - M.wageAt z₀ (M.pricePath z₀ m₀ K') s.2.node) * M.efficiency s.2.idio := by
    simp only [cash]
    ring
  rw [e]
  have hδ := abs_nonneg (K s.2.node - K' s.2.node)
  calc _ ≤ |M.returnAt z₀ (M.pricePath z₀ m₀ K) s.2.node
          - M.returnAt z₀ (M.pricePath z₀ m₀ K') s.2.node| * s.1
        + |M.wageAt z₀ (M.pricePath z₀ m₀ K) s.2.node
          - M.wageAt z₀ (M.pricePath z₀ m₀ K') s.2.node| * M.efficiency s.2.idio := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg ha.1]
        · rw [abs_mul, abs_of_nonneg he0]
    _ ≤ H.ℓ * |K s.2.node - K' s.2.node| * M.assetCap
        + H.ℓ * |K s.2.node - K' s.2.node| * ∑ e, M.efficiency e :=
        add_le_add (mul_le_mul hR ha.2 ha.1 (mul_nonneg H.ℓ_nonneg hδ))
          (mul_le_mul hw he he0 (mul_nonneg H.ℓ_nonneg hδ))
    _ = H.ℓ * |K s.2.node - K' s.2.node| * M.cashScale := by rw [cashScale]; ring

/-! ### Marginal-utility gaps, weighted by depth -/

variable [Nonempty Z] {η : ℝ}

omit [Nonempty Z] in
/-- **Weighted marginal-utility gaps, `n` steps of the recursion.** -/
theorem weighted_du_gap_iter (hη0 : 0 ≤ η)
    (hη : ∀ h : List Z, H.lam ^ h.length * |K h - K' h| ≤ η) :
    ∀ (n : ℕ) (s : M.State),
      H.lam ^ s.2.node.length * |H.U.du (M.consumption z₀ (M.pricePath z₀ m₀ K) s)
          - H.U.du (M.consumption z₀ (M.pricePath z₀ m₀ K') s)|
        ≤ H.A * η + H.q ^ n * H.D
  | 0, s => by
    have h1 := H.abs_du_sub_le z₀ (M.pricePath z₀ m₀ K) (M.pricePath z₀ m₀ K') s s
    have h2 : H.lam ^ s.2.node.length ≤ 1 := pow_le_one₀ H.lam_pos.le H.lam_le_one
    have h3 : 0 ≤ H.lam ^ s.2.node.length := pow_nonneg H.lam_pos.le _
    have h4 := mul_le_mul h2 h1 (abs_nonneg _) zero_le_one
    have h5 := mul_nonneg H.A_nonneg hη0
    rw [pow_zero, one_mul]
    linarith
  | n + 1, s => by
    set Q := M.pricePath z₀ m₀ K
    set Q' := M.pricePath z₀ m₀ K'
    set len := s.2.node.length
    have hlam := H.lam_pos
    have hW : 0 < H.lam ^ len := pow_pos hlam _
    have hW1 : 0 < H.lam ^ (len + 1) := pow_pos hlam _
    set T := H.A * η + H.q ^ n * H.D with hT
    -- the children's gaps, from the induction hypothesis
    have hB : ∀ ze : Z × E, ∀ a' ∈ Icc 0 M.assetCap,
        |H.U.du (M.consumption z₀ Q (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩))
          - H.U.du (M.consumption z₀ Q' (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩))|
          ≤ T / H.lam ^ (len + 1) := by
      intro ze a' _
      have ih := weighted_du_gap_iter hη0 hη n (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
      rw [le_div_iff₀ hW1, mul_comm]
      exact ih
    have h1 := M.du_consumption_sub_le H.U z₀ (H.slack z₀ Q) (H.slack z₀ Q') H.floor_lt_cLo
      (H.cLo_le z₀ Q) H.du_lip H.Mdu_nonneg s (fun _ => T / H.lam ^ (len + 1)) hB
    -- the sum over children
    have hS : ∑ ze : Z × E, M.shockProb z₀ ze (s, 0)
          * (|M.returnAt z₀ Q (ze.1 :: s.2.node) - M.returnAt z₀ Q' (ze.1 :: s.2.node)|
              * H.U.du H.cLo
            + M.returnBound * (T / H.lam ^ (len + 1)))
        ≤ (H.ℓ * η * H.D + M.returnBound * T) / H.lam ^ (len + 1) := by
      have hterm : ∀ ze : Z × E,
          |M.returnAt z₀ Q (ze.1 :: s.2.node) - M.returnAt z₀ Q' (ze.1 :: s.2.node)| * H.U.du H.cLo
            + M.returnBound * (T / H.lam ^ (len + 1))
          ≤ (H.ℓ * η * H.D + M.returnBound * T) / H.lam ^ (len + 1) := by
        intro ze
        have hg := H.returnAt_gap z₀ m₀ K K' (ze.1 :: s.2.node)
        have hc := hη (ze.1 :: s.2.node)
        have hlen : (ze.1 :: s.2.node).length = len + 1 := rfl
        rw [hlen] at hc
        have hδ : |K (ze.1 :: s.2.node) - K' (ze.1 :: s.2.node)| ≤ η / H.lam ^ (len + 1) := by
          rw [le_div_iff₀ hW1, mul_comm]
          exact hc
        have hD := H.D_nonneg
        have hgap : |M.returnAt z₀ Q (ze.1 :: s.2.node) - M.returnAt z₀ Q' (ze.1 :: s.2.node)|
            ≤ H.ℓ * (η / H.lam ^ (len + 1)) :=
          hg.trans (mul_le_mul_of_nonneg_left hδ H.ℓ_nonneg)
        have : |M.returnAt z₀ Q (ze.1 :: s.2.node) - M.returnAt z₀ Q' (ze.1 :: s.2.node)|
            * H.U.du H.cLo ≤ H.ℓ * (η / H.lam ^ (len + 1)) * H.D :=
          mul_le_mul_of_nonneg_right hgap hD
        have e1 : H.ℓ * (η / H.lam ^ (len + 1)) * H.D = H.ℓ * η * H.D / H.lam ^ (len + 1) := by
          ring
        have e3 : (H.ℓ * η * H.D + M.returnBound * T) / H.lam ^ (len + 1)
            = H.ℓ * η * H.D / H.lam ^ (len + 1) + M.returnBound * T / H.lam ^ (len + 1) :=
          add_div _ _ _
        have e2 : M.returnBound * (T / H.lam ^ (len + 1))
            = M.returnBound * T / H.lam ^ (len + 1) := by ring
        linarith
      calc _ ≤ ∑ ze : Z × E, M.shockProb z₀ ze (s, 0)
            * ((H.ℓ * η * H.D + M.returnBound * T) / H.lam ^ (len + 1)) :=
            Finset.sum_le_sum fun ze _ =>
              mul_le_mul_of_nonneg_left (hterm ze) (M.shockProb_nonneg' z₀ ze (s, 0))
        _ = (H.ℓ * η * H.D + M.returnBound * T) / H.lam ^ (len + 1) := by
            rw [← Finset.sum_mul, M.shockProb_sum z₀, one_mul]
    -- the cash gap at the node
    have hX : |M.cash z₀ Q s - M.cash z₀ Q' s| ≤ H.ℓ * M.cashScale * η / H.lam ^ len := by
      have hc := H.cash_gap z₀ m₀ K K' s
      have hδ : |K s.2.node - K' s.2.node| ≤ η / H.lam ^ len := by
        rw [le_div_iff₀ hW, mul_comm]
        exact hη s.2.node
      calc _ ≤ H.ℓ * |K s.2.node - K' s.2.node| * M.cashScale := hc
        _ ≤ H.ℓ * (η / H.lam ^ len) * M.cashScale :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ H.ℓ_nonneg)
              M.cashScale_nonneg
        _ = H.ℓ * M.cashScale * η / H.lam ^ len := by ring
    -- assemble
    have hβ := M.discount_pos.le
    have hstep : H.lam ^ len * |H.U.du (M.consumption z₀ Q s) - H.U.du (M.consumption z₀ Q' s)|
        ≤ M.discount * (H.ℓ * η * H.D + M.returnBound * T) / H.lam
          + H.Mdu * (H.ℓ * M.cashScale * η) := by
      have hW' : H.lam ^ (len + 1) = H.lam ^ len * H.lam := pow_succ _ _
      have k1 := mul_le_mul_of_nonneg_left
        (h1.trans (add_le_add (mul_le_mul_of_nonneg_left hS hβ)
          (mul_le_mul_of_nonneg_left hX H.Mdu_nonneg))) hW.le
      calc _ ≤ H.lam ^ len * (M.discount * ((H.ℓ * η * H.D + M.returnBound * T)
              / H.lam ^ (len + 1)) + H.Mdu * (H.ℓ * M.cashScale * η / H.lam ^ len)) := k1
        _ = M.discount * (H.ℓ * η * H.D + M.returnBound * T) / H.lam
            + H.Mdu * (H.ℓ * M.cashScale * η) := by
            rw [hW']
            field_simp
    have hid : M.discount * (H.ℓ * η * H.D + M.returnBound * T) / H.lam
          + H.Mdu * (H.ℓ * M.cashScale * η)
        = H.A * η + H.q ^ (n + 1) * H.D := by
      have hA := H.A_eq
      have hq : H.q = M.discount * M.returnBound / H.lam := rfl
      have e : M.discount * (H.ℓ * η * H.D + M.returnBound * T) / H.lam
            + H.Mdu * (H.ℓ * M.cashScale * η)
          = (M.discount * H.ℓ * H.D / H.lam + H.Mdu * H.ℓ * M.cashScale) * η + H.q * T := by
        rw [hq]
        field_simp
        ring
      rw [e, ← hA, hT, pow_succ]
      ring
    linarith

/-- **Weighted marginal-utility gaps**: at depth `|h|`, the gap is at most `A η / λ^{|h|}`. -/
theorem weighted_du_gap (hη0 : 0 ≤ η) (hη : ∀ h : List Z, H.lam ^ h.length * |K h - K' h| ≤ η)
    (s : M.State) :
    H.lam ^ s.2.node.length * |H.U.du (M.consumption z₀ (M.pricePath z₀ m₀ K) s)
        - H.U.du (M.consumption z₀ (M.pricePath z₀ m₀ K') s)| ≤ H.A * η := by
  have hlim : Tendsto (fun n : ℕ => H.A * η + H.q ^ n * H.D) atTop (𝓝 (H.A * η + 0 * H.D)) :=
    tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one H.q_nonneg H.q_lt_one).mul tendsto_const_nhds)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim fun n => H.weighted_du_gap_iter z₀ m₀ K K' hη0 hη n s

/-! ### Saving-policy gaps -/

/-- **Weighted saving-policy gaps**: `|Δa'| ≤ |Δcash| + |Δu'(c)| / m`. -/
theorem weighted_policy_gap (hη0 : 0 ≤ η)
    (hη : ∀ h : List Z, H.lam ^ h.length * |K h - K' h| ≤ η) (s : M.State) :
    H.lam ^ s.2.node.length * |M.policy z₀ (M.pricePath z₀ m₀ K) s
        - M.policy z₀ (M.pricePath z₀ m₀ K') s|
      ≤ (H.ℓ * M.cashScale + H.A / H.m) * η := by
  set Q := M.pricePath z₀ m₀ K
  set Q' := M.pricePath z₀ m₀ K'
  set w := H.lam ^ s.2.node.length
  have hw : 0 ≤ w := pow_nonneg H.lam_pos.le _
  have hc := H.cash_gap z₀ m₀ K K' s
  have hdu := H.weighted_du_gap z₀ m₀ K K' hη0 hη s
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
      = (M.cash z₀ Q s - M.cash z₀ Q' s)
        - (M.consumption z₀ Q s - M.consumption z₀ Q' s) := by
    simp only [consumption]
    ring
  have h1 : w * |M.cash z₀ Q s - M.cash z₀ Q' s| ≤ H.ℓ * M.cashScale * η :=
    calc _ ≤ w * (H.ℓ * |K s.2.node - K' s.2.node| * M.cashScale) :=
          mul_le_mul_of_nonneg_left hc hw
      _ = H.ℓ * M.cashScale * (w * |K s.2.node - K' s.2.node|) := by ring
      _ ≤ H.ℓ * M.cashScale * η :=
          mul_le_mul_of_nonneg_left (hη _) (mul_nonneg H.ℓ_nonneg M.cashScale_nonneg)
  have h2 : w * |M.consumption z₀ Q s - M.consumption z₀ Q' s| ≤ H.A * η / H.m := by
    rw [le_div_iff₀ H.m_pos]
    calc _ = w * (H.m * |M.consumption z₀ Q s - M.consumption z₀ Q' s|) := by ring
      _ ≤ w * |H.U.du (M.consumption z₀ Q s) - H.U.du (M.consumption z₀ Q' s)| :=
          mul_le_mul_of_nonneg_left hcons hw
      _ ≤ H.A * η := hdu
  rw [e]
  calc _ ≤ w * (|M.cash z₀ Q s - M.cash z₀ Q' s|
          + |M.consumption z₀ Q s - M.consumption z₀ Q' s|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hw
    _ = w * |M.cash z₀ Q s - M.cash z₀ Q' s|
        + w * |M.consumption z₀ Q s - M.consumption z₀ Q' s| := by ring
    _ ≤ H.ℓ * M.cashScale * η + H.A * η / H.m := add_le_add h1 h2
    _ = (H.ℓ * M.cashScale + H.A / H.m) * η := by ring

end ContractionBase

namespace ContractionHyp

variable (H : M.ContractionHyp)
include H

variable (z₀ : Z) (m₀ : E → ℝ) (K K' : List Z → ℝ)

variable [Nonempty Z] {η : ℝ}

/-! ### Distribution gaps, weighted by depth -/

omit [Nonempty Z] in
theorem weighted_gapPath [Nonempty Z] {c : ℝ} (hc : 0 ≤ c) :
    ∀ h : List Z, H.lam ^ h.length * KSModel.gapPath M.returnBound
        (fun h : List Z => c / H.lam ^ h.length) h
      ≤ H.lam * c / (1 - H.lam * M.returnBound)
  | [] => by
    simp only [KSModel.gapPath, mul_zero]
    exact div_nonneg (mul_nonneg H.lam_pos.le hc) (sub_nonneg.2 H.lam_return_lt.le)
  | z :: h => by
    have ih := weighted_gapPath hc h
    set G := H.lam * c / (1 - H.lam * M.returnBound)
    have hG : G * (1 - H.lam * M.returnBound) = H.lam * c :=
      div_mul_cancel₀ _ (ne_of_gt (sub_pos.2 H.lam_return_lt))
    have hne : H.lam ^ h.length ≠ 0 := (pow_pos H.lam_pos _).ne'
    have e : H.lam ^ (z :: h).length * KSModel.gapPath M.returnBound
          (fun h : List Z => c / H.lam ^ h.length) (z :: h)
        = H.lam * M.returnBound * (H.lam ^ h.length * KSModel.gapPath M.returnBound
          (fun h : List Z => c / H.lam ^ h.length) h) + H.lam * c := by
      simp only [KSModel.gapPath, List.length_cons, pow_succ]
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left ih (mul_nonneg H.lam_pos.le M.returnBound_nonneg)
    linarith

/-! ### The equilibrium map is a contraction -/

omit [Nonempty Z] in
theorem κ_nonneg : 0 ≤ H.κ :=
  div_nonneg (mul_nonneg H.lam_pos.le (add_nonneg (mul_nonneg H.ℓ_nonneg M.cashScale_nonneg)
    (div_nonneg H.A_nonneg H.m_pos.le))) (sub_nonneg.2 H.lam_return_lt.le)

/-- **The equilibrium map is a `κ`-contraction** in the weighted norm `sup_h λ^{|h|} |K_h|`. -/
theorem weighted_equilibriumMap_gap (μ₀ : Measure M.AState) [IsProbabilityMeasure μ₀]
    (hη0 : 0 ≤ η) (hη : ∀ h : List Z, H.lam ^ h.length * |K h - K' h| ≤ η) (h : List Z) :
    H.lam ^ h.length * |M.equilibriumMap z₀ μ₀ K h - M.equilibriumMap z₀ μ₀ K' h|
      ≤ H.κ * η := by
  set c := (H.ℓ * M.cashScale + H.A / H.m) * η
  have hc : 0 ≤ c := mul_nonneg (add_nonneg (mul_nonneg H.ℓ_nonneg M.cashScale_nonneg)
    (div_nonneg H.A_nonneg H.m_pos.le)) hη0
  have hP : ∀ h (x : M.AState),
      |M.policy z₀ (M.pricePath z₀ (M.initMass μ₀) K) (x.1, ⟨x.2.idio, h⟩)
        - M.policy z₀ (M.pricePath z₀ (M.initMass μ₀) K') (x.1, ⟨x.2.idio, h⟩)|
        ≤ (fun h : List Z => c / H.lam ^ h.length) h := by
    intro h x
    rw [le_div_iff₀ (pow_pos H.lam_pos _), mul_comm]
    exact H.weighted_policy_gap z₀ (M.initMass μ₀) K K' hη0 hη (x.1, ⟨x.2.idio, h⟩)
  have hm := M.meanCapital_sub_le z₀ μ₀ _ _ _ hP h
  calc _ ≤ H.lam ^ h.length * KSModel.gapPath M.returnBound
          (fun h : List Z => c / H.lam ^ h.length) h :=
        mul_le_mul_of_nonneg_left hm (pow_nonneg H.lam_pos.le _)
    _ ≤ H.lam * c / (1 - H.lam * M.returnBound) := H.weighted_gapPath hc h
    _ = H.κ * η := by
        simp only [c, ContractionBase.κ]
        ring

omit [Nonempty Z] in
/-- **Uniqueness of sequential equilibrium.** If the contraction modulus `κ` is below one, then
from every initial shock and distribution there is at most one sequential equilibrium. -/
theorem uniqueSequentialEquilibrium (hκ : H.κ < 1) : M.UniqueSequentialEquilibrium := by
  intro z μ K K' hK hK'
  have : Nonempty Z := ⟨z⟩
  have hcap0 := M.meanCapital_mem z (μ : Measure M.AState)
    (M.pricePath z (M.initMass (μ : Measure M.AState)) K) []
  have hcap : 0 ≤ M.assetCap := hcap0.1.trans hcap0.2
  have hb : ∀ h, |K h - K' h| ≤ M.assetCap := by
    intro h
    have h1 := M.meanCapital_mem z (μ : Measure M.AState)
      (M.pricePath z (M.initMass (μ : Measure M.AState)) K) h
    have h2 := M.meanCapital_mem z (μ : Measure M.AState)
      (M.pricePath z (M.initMass (μ : Measure M.AState)) K') h
    rw [← hK h] at h1
    rw [← hK' h] at h2
    exact abs_sub_le_iff.2 ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩
  have hiter : ∀ n : ℕ, ∀ h : List Z,
      H.lam ^ h.length * |K h - K' h| ≤ H.κ ^ n * M.assetCap := by
    intro n
    induction n with
    | zero =>
      intro h
      rw [pow_zero, one_mul]
      calc _ ≤ 1 * |K h - K' h| :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ H.lam_pos.le H.lam_le_one) (abs_nonneg _)
        _ ≤ M.assetCap := by rw [one_mul]; exact hb h
    | succ n ih =>
      intro h
      have hm := H.weighted_equilibriumMap_gap z K K' (μ : Measure M.AState)
        (mul_nonneg (pow_nonneg H.κ_nonneg n) hcap) ih h
      have e1 : K h = M.equilibriumMap z (μ : Measure M.AState) K h := hK h
      have e2 : K' h = M.equilibriumMap z (μ : Measure M.AState) K' h := hK' h
      rw [e1, e2]
      calc _ ≤ H.κ * (H.κ ^ n * M.assetCap) := hm
        _ = H.κ ^ (n + 1) * M.assetCap := by ring
  funext h
  have hlim : Tendsto (fun n : ℕ => H.κ ^ n * M.assetCap) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one H.κ_nonneg hκ).mul_const M.assetCap
  have h0 : H.lam ^ h.length * |K h - K' h| ≤ 0 := ge_of_tendsto' hlim fun n => hiter n h
  have hw := pow_pos H.lam_pos h.length
  have habs : |K h - K' h| ≤ 0 := by
    by_contra hc
    replace hc := lt_of_not_ge hc
    have := mul_pos hw hc
    linarith
  exact sub_eq_zero.1 (abs_nonpos_iff.1 habs)

omit [Nonempty Z] in
/-- **Recursive equilibrium on the minimal state** `(z, μ)` when `κ < 1`: along the equilibrium
path, capital is mean assets, households save by `recursivePolicy`, and distributions move by
`lawOfMotion`, with no remaining hypothesis. -/
theorem isRecursive (hκ : H.κ < 1) (z : Z) (μ : ProbabilityMeasure M.AState) (h : List Z) :
    M.eqPath z μ h = ∫ x, M.assets x ∂(M.nodeProb z μ h : Measure M.AState) ∧
      (∀ x : M.AState,
        M.policy z (M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ))
            (x.1, ⟨x.2.idio, h⟩)
          = M.recursivePolicy (shockAt z h) (M.nodeProb z μ h) x) ∧
      ∀ z' : Z, M.nodeProb z μ (z' :: h) = M.lawOfMotion (shockAt z h) (M.nodeProb z μ h) z' :=
  M.isRecursive (H.uniqueSequentialEquilibrium hκ) z μ h

end ContractionHyp

end KSModel

end KrusellSmith

end LeanEconomics
