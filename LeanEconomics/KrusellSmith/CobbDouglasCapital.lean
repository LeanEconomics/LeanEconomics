/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CapitalBound
import LeanEconomics.KrusellSmith.CRRAContraction

/-!
# The capital clamp never binds

Milestone C4 of `CLAMP_PLAN.md`. For clamped Cobb–Douglas prices whose lower capital clamp
`capLo` is small enough (`CobbDouglas.CapLoOK`, explicit), the price condition of `capital_ge`
holds with `k = capLo` (`CobbDouglas.priceCondition`). So in the CRRA economy (any `γ > 0`, log
included), every sequential equilibrium starting from a distribution with mean assets at least
`capLo` keeps capital in `[capLo, capHi]` at every node (`crra_capital_mem`), and the prices are
the **unclamped** Cobb–Douglas marginal products at equilibrium capital and labour everywhere
(`crra_unclamped_prices`, `crra_exists_unclamped_equilibrium`).

**The condition on `capLo`** (with `α` the capital share, `z̲, z̄` the bounds on productivity,
`[L̲, L̄]` the labour clamp, equal to the range of efficiencies):

* `capLo ≤ 1` and `capLo · ē ≤ assetCap · L̲ / 2`;
* `capLo^{1−α} < D / 2`, with `D = (1 − α) z̲ L̄^{−α} L̲ / 2`;
* `C₁ (1 + C₂) capLo^{(1−α)/γ} < D / 2`, with `C₁ = (β π α z̲ L̲^{1−α})^{−1/γ}`, `C₂ = z̄ L̄^{1−α}`.

None of `D, C₁, C₂` depends on `capLo`, so the condition holds for every small enough `capLo`
(`exists_capLo`). The proof: the wage at capital `≥ capLo` is of order `capLo^α`; the return to
saving when capital is below `capLo` is of order `capLo^{α−1}`, so the Euler factor
`(β π R)^{−1/γ}` is of order `capLo^{(1−α)/γ}`, and the child's cash on hand is of order
`capLo^α`.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

namespace CobbDouglas

variable {Z : Type*} (T : CobbDouglas Z)

/-- The wage constant `D = (1 − α) z̲ L̄^{−α} L̲ / 2`. -/
noncomputable def wageConst : ℝ :=
  (1 - T.share) * T.tfpLo * T.labHi ^ (-T.share) * T.labLo / 2

/-- The Euler constant `C₁ = (β π α z̲ L̲^{1−α})^{−1/γ}`. -/
noncomputable def eulerConst (β π γ : ℝ) : ℝ :=
  (β * π * (T.share * T.tfpLo * T.labLo ^ (1 - T.share))) ^ (-1 / γ)

/-- The output constant `C₂ = z̄ L̄^{1−α}`. -/
noncomputable def outputConst : ℝ := T.tfpHi * T.labHi ^ (1 - T.share)

/-- **The explicit condition on a lower clamp `k`.** -/
def LowerClampOK (β π γ ē cap k : ℝ) : Prop :=
  k ≤ 1 ∧ k * ē ≤ cap * T.labLo / 2 ∧ k ^ (1 - T.share) < T.wageConst / 2 ∧
    T.eulerConst β π γ * (1 + T.outputConst) * k ^ ((1 - T.share) / γ) < T.wageConst / 2

/-- The condition for the clamp of `T` itself. -/
def CapLoOK (β π γ ē cap : ℝ) : Prop := T.LowerClampOK β π γ ē cap T.capLo

theorem wageConst_pos : 0 < T.wageConst := by
  have h1 : 0 < 1 - T.share := by linarith [T.share_lt_one]
  unfold wageConst
  have := Real.rpow_pos_of_pos (T.labLo_pos.trans_le T.labLo_le) (-T.share)
  have := T.labLo_pos
  have := T.tfpLo_pos
  positivity

theorem eulerConst_pos {β π γ : ℝ} (hβ : 0 < β) (hπ : 0 < π) : 0 < T.eulerConst β π γ :=
  Real.rpow_pos_of_pos (mul_pos (mul_pos hβ hπ) (mul_pos (mul_pos T.share_pos T.tfpLo_pos)
    (Real.rpow_pos_of_pos T.labLo_pos _))) _

theorem outputConst_nonneg [Nonempty Z] : 0 ≤ T.outputConst :=
  mul_nonneg (T.tfpHi_nonneg (Classical.arbitrary Z))
    (Real.rpow_nonneg (T.labLo_pos.trans_le T.labLo_le).le _)

theorem grossReturn_pos (z : Z) (K L : ℝ) : 0 < T.grossReturn z K L := by
  have h1 : 0 ≤ 1 - T.depreciation := sub_nonneg.2 T.depreciation_le_one
  have h2 : 0 < T.share * T.tfp z * T.clampCap K ^ (T.share - 1) * T.clampLab L ^ (1 - T.share) :=
    mul_pos (mul_pos (mul_pos T.share_pos (T.tfp_pos z))
      (Real.rpow_pos_of_pos (T.clampCap_pos K) _)) (Real.rpow_pos_of_pos (T.clampLab_pos L) _)
  unfold grossReturn
  linarith

theorem clampCap_of_lt {K : ℝ} (hK : K < T.capLo) : T.clampCap K = T.capLo :=
  max_eq_left ((min_le_right _ _).trans hK.le)

/-- **Cobb–Douglas prices satisfy the price condition of `capital_ge`** at `k = capLo`. -/
theorem priceCondition {β π γ ē cap : ℝ} (hβ : 0 < β) (hπ : 0 < π) (hγ : 0 < γ)
    (hcap : 0 < cap) (hok : T.CapLoOK β π γ ē cap) (z : Z) (Kh Kc L L' : ℝ)
    (hKc : Kc < T.capLo) (hL : L ∈ Icc T.labLo T.labHi)
    (hL' : L' ∈ Icc T.labLo T.labHi) :
    (β * π * T.grossReturn z Kc L') ^ (-1 / γ)
        * (T.grossReturn z Kc L' * T.capLo + T.wage z Kc L' * L')
      < T.wage z Kh L * (L - T.capLo * ē / cap) - T.capLo := by
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hok
  set k := T.capLo with hkdef
  set a := T.share with hadef
  have hk0 : 0 < k := T.capLo_pos
  have ha0 := T.share_pos
  have ha1 := T.share_lt_one
  have hL'0 : 0 < L' := T.labLo_pos.trans_le hL'.1
  have hz := T.tfp_pos z
  have hzlo := T.tfpLo_le z
  have hzhi := T.tfp_le z
  have hδ0 : 0 ≤ 1 - T.depreciation := sub_nonneg.2 T.depreciation_le_one
  have hδ1 : 1 - T.depreciation ≤ 1 := by linarith [T.depreciation_nonneg]
  -- prices at the child, where capital is below the clamp
  have hcl := T.clampCap_of_lt hKc
  have hR : T.grossReturn z Kc L'
      = 1 - T.depreciation + a * T.tfp z * k ^ (a - 1) * L' ^ (1 - a) := by
    rw [grossReturn, hcl, T.clampLab_of_mem hL']
  have hw : T.wage z Kc L' = (1 - a) * T.tfp z * k ^ a * L' ^ (-a) := by
    rw [wage, hcl, T.clampLab_of_mem hL']
  -- the child's cash on hand: `(1 − δ) k + z k^α L'^{1−α}`
  have e1 : k ^ (a - 1) * k = k ^ a := by
    rw [← Real.rpow_add_one hk0.ne']
    ring_nf
  have e2 : L' ^ (-a) * L' = L' ^ (1 - a) := by
    rw [← Real.rpow_add_one hL'0.ne']
    ring_nf
  have hsum : T.grossReturn z Kc L' * k + T.wage z Kc L' * L'
      = (1 - T.depreciation) * k + T.tfp z * k ^ a * L' ^ (1 - a) := by
    rw [hR, hw]
    linear_combination (a * T.tfp z * L' ^ (1 - a)) * e1 + ((1 - a) * T.tfp z * k ^ a) * e2
  have hka : k ≤ k ^ a := by
    have := Real.rpow_le_rpow_of_exponent_ge hk0 hk1 ha1.le
    rwa [Real.rpow_one] at this
  have hkapos : 0 < k ^ a := Real.rpow_pos_of_pos hk0 a
  have hLhi : L' ^ (1 - a) ≤ T.labHi ^ (1 - a) :=
    Real.rpow_le_rpow hL'0.le hL'.2 (by linarith)
  have hsum_le : T.grossReturn z Kc L' * k + T.wage z Kc L' * L'
      ≤ (1 + T.outputConst) * k ^ a := by
    rw [hsum, outputConst]
    have h1 : (1 - T.depreciation) * k ≤ k ^ a := (mul_le_of_le_one_left hk0.le hδ1).trans hka
    have h2 : T.tfp z * k ^ a * L' ^ (1 - a) ≤ T.tfpHi * T.labHi ^ (1 - a) * k ^ a := by
      have := mul_le_mul hzhi hLhi (Real.rpow_nonneg hL'0.le _) (hz.le.trans hzhi)
      nlinarith
    linarith
  -- the Euler factor: `(β π R)^{−1/γ} ≤ C₁ k^{(1−α)/γ}`
  have hRlo : a * T.tfpLo * T.labLo ^ (1 - a) * k ^ (a - 1) ≤ T.grossReturn z Kc L' := by
    rw [hR]
    have hLlo : T.labLo ^ (1 - a) ≤ L' ^ (1 - a) :=
      Real.rpow_le_rpow T.labLo_pos.le hL'.1 (by linarith)
    have hk' := Real.rpow_pos_of_pos hk0 (a - 1)
    have := mul_le_mul (mul_le_mul_of_nonneg_left hzlo ha0.le) hLlo
      (Real.rpow_nonneg T.labLo_pos.le _) (mul_nonneg ha0.le hz.le)
    nlinarith
  have hbase : 0 < β * π * (a * T.tfpLo * T.labLo ^ (1 - a) * k ^ (a - 1)) :=
    mul_pos (mul_pos hβ hπ) (mul_pos (mul_pos (mul_pos ha0 T.tfpLo_pos)
      (Real.rpow_pos_of_pos T.labLo_pos _)) (Real.rpow_pos_of_pos hk0 _))
  have hρ : (β * π * T.grossReturn z Kc L') ^ (-1 / γ)
      ≤ T.eulerConst β π γ * k ^ ((1 - a) / γ) := by
    have h1 := Real.rpow_le_rpow_of_nonpos hbase
      (mul_le_mul_of_nonneg_left hRlo (mul_nonneg hβ.le hπ.le))
      (show -1 / γ ≤ 0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) hγ.le)
    refine h1.trans (le_of_eq ?_)
    have hA : 0 ≤ β * π * (a * T.tfpLo * T.labLo ^ (1 - a)) :=
      (mul_pos (mul_pos hβ hπ) (mul_pos (mul_pos ha0 T.tfpLo_pos)
        (Real.rpow_pos_of_pos T.labLo_pos _))).le
    rw [show β * π * (a * T.tfpLo * T.labLo ^ (1 - a) * k ^ (a - 1))
        = β * π * (a * T.tfpLo * T.labLo ^ (1 - a)) * k ^ (a - 1) by ring,
      Real.mul_rpow hA (Real.rpow_nonneg hk0.le _), ← Real.rpow_mul hk0.le, eulerConst]
    congr 2
    field_simp
    ring
  -- left side `< (D/2) k^α`
  have hC1 := T.eulerConst_pos (γ := γ) hβ hπ
  have hlhs : (β * π * T.grossReturn z Kc L') ^ (-1 / γ)
        * (T.grossReturn z Kc L' * k + T.wage z Kc L' * L')
      < T.wageConst / 2 * k ^ a := by
    have hρ0 : 0 ≤ (β * π * T.grossReturn z Kc L') ^ (-1 / γ) :=
      Real.rpow_nonneg (mul_nonneg (mul_nonneg hβ.le hπ.le) (T.grossReturn_pos z Kc L').le) _
    calc _ ≤ T.eulerConst β π γ * k ^ ((1 - a) / γ) * ((1 + T.outputConst) * k ^ a) :=
          mul_le_mul hρ hsum_le (by rw [hsum]; positivity) (by positivity)
      _ = T.eulerConst β π γ * (1 + T.outputConst) * k ^ ((1 - a) / γ) * k ^ a := by ring
      _ < T.wageConst / 2 * k ^ a := mul_lt_mul_of_pos_right hk4 hkapos
  -- right side `≥ D k^α − k`
  have hwage := T.wageLo_le_wage z Kh L
  have hLk : T.labLo / 2 ≤ L - k * ē / cap := by
    have : k * ē / cap ≤ T.labLo / 2 := by
      rw [div_le_iff₀ hcap]
      linarith
    linarith [hL.1]
  have hwLo : T.wageLo * (T.labLo / 2) = T.wageConst * k ^ a := by
    simp only [wageLo, wageConst]
    ring
  have hrhs : T.wageConst * k ^ a - k ≤ T.wage z Kh L * (L - k * ē / cap) - k := by
    have hwLo0 : 0 ≤ T.wageLo := T.wageLo_pos.le
    have := mul_le_mul hwage hLk (by linarith [T.labLo_pos]) (hwLo0.trans hwage)
    linarith
  -- `k < (D/2) k^α`
  have hkk : k < T.wageConst / 2 * k ^ a := by
    have e3 : k = k ^ (1 - a) * k ^ a := by
      rw [← Real.rpow_add hk0, show 1 - a + a = 1 by ring, Real.rpow_one]
    calc k = k ^ (1 - a) * k ^ a := e3
      _ < T.wageConst / 2 * k ^ a := mul_lt_mul_of_pos_right hk3 hkapos
  linarith

/-- **Every small enough lower clamp satisfies the condition**, with an explicit threshold. -/
theorem exists_capLo [Nonempty Z] {β π γ ē cap : ℝ} (hβ : 0 < β) (hπ : 0 < π) (hγ : 0 < γ)
    (hē : 0 < ē) (hcap : 0 < cap) :
    ∃ k₀ > 0, ∀ k, 0 < k → k ≤ k₀ → T.LowerClampOK β π γ ē cap k := by
  set a := T.share
  have ha1 : 0 < 1 - a := by linarith [T.share_lt_one]
  have hD := T.wageConst_pos
  have hC1 := T.eulerConst_pos (γ := γ) hβ hπ
  have hC2 := T.outputConst_nonneg
  set t := (T.wageConst / 2) ^ (1 / (1 - a)) with ht
  set C := T.eulerConst β π γ * (1 + T.outputConst) with hC
  have hC0 : 0 < C := mul_pos hC1 (by linarith)
  set u := (T.wageConst / 2 / C) ^ (γ / (1 - a)) with hu
  have ht0 : 0 < t := Real.rpow_pos_of_pos (by linarith) _
  have hu0 : 0 < u := Real.rpow_pos_of_pos (div_pos (by linarith) hC0) _
  have hL0 := T.labLo_pos
  refine ⟨min (min 1 (cap * T.labLo / (2 * ē))) (min (t / 2) (u / 2)),
    lt_min (lt_min one_pos (by positivity)) (lt_min (by linarith) (by linarith)), ?_⟩
  intro k hk0 hk
  have hk1 : k ≤ 1 := hk.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hk2 : k ≤ cap * T.labLo / (2 * ē) := hk.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hkt : k < t := (hk.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt
    (by linarith)
  have hku : k < u := (hk.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt
    (by linarith)
  refine ⟨hk1, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)] at hk2
    linarith
  · have h := Real.rpow_lt_rpow hk0.le hkt ha1
    rwa [ht, ← Real.rpow_mul (by linarith), one_div_mul_cancel ha1.ne', Real.rpow_one] at h
  · have hp : 0 < (1 - a) / γ := div_pos ha1 hγ
    have h := Real.rpow_lt_rpow hk0.le hku hp
    rw [hu, ← Real.rpow_mul (div_pos (by linarith) hC0).le,
      show γ / (1 - a) * ((1 - a) / γ) = 1 by field_simp, Real.rpow_one] at h
    rw [← hC]
    calc C * k ^ ((1 - a) / γ) < C * (T.wageConst / 2 / C) := mul_lt_mul_of_pos_left h hC0
      _ = T.wageConst / 2 := by field_simp

end CobbDouglas

/-! ### The CRRA economy: capital stays inside the clamp -/

variable {Z E : Type*} [Fintype Z] [Fintype E]

variable (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)

/-- **Capital stays inside the clamp** along every sequential equilibrium of the CRRA economy,
from every distribution with mean assets at least `capLo`, when `capLo` satisfies the explicit
condition and the upper clamp is above the asset cap. -/
theorem crra_capital_mem {π : ℝ} (hπ0 : 0 < π) (hπ : ∀ z, π ≤ V.aggProb z z)
    (hlab : T.labLo = V.effLo ∧ T.labHi = V.effHi) (hcapHi : V.assetCap ≤ T.capHi)
    (hok : T.CapLoOK V.discount π γ V.effHi V.assetCap) (z₀ : Z)
    (μ₀ : Measure (crraModel V T hγ).AState) [IsProbabilityMeasure μ₀]
    (hμ : T.capLo ≤ ∫ x, (crraModel V T hγ).assets x ∂μ₀) {Kc : List Z → ℝ}
    (hK : (crraModel V T hγ).IsSequentialEquilibrium z₀ μ₀ Kc) :
    ∀ h, Kc h ∈ Icc T.capLo T.capHi := by
  have hē0 : 0 ≤ V.effHi := by
    rw [← hlab.2]
    exact (T.labLo_pos.trans_le T.labLo_le).le
  have hsl : (crraModel V T hγ).Slack z₀
      ((crraModel V T hγ).pricePath z₀ ((crraModel V T hγ).initMass μ₀) Kc) := fun s =>
    (half_lt_self (crraFloorLevel_pos V T hγ)).trans_le
      (crraFloorLevel_le_consumption V T hγ z₀ _ s)
  have hlab' : ∀ h, (crraModel V T hγ).labour z₀ ((crraModel V T hγ).initMass μ₀) h
      ∈ Icc T.labLo T.labHi := by
    intro h
    rw [hlab.1, hlab.2]
    exact (crraModel V T hγ).labour_mem z₀ μ₀ V.effLo_le V.le_effHi h
  have hlow := KSModel.capital_ge (crraSmoothUtility V T hγ) z₀ μ₀ hγ (fun _ _ => rfl) hK hsl
    hπ0 hπ (T.grossReturn_pos) V.le_effHi hē0 hlab'
    (fun z Kh Kc' L L' _ _ hKc hL hL' =>
      T.priceCondition V.discount_pos hπ0 hγ V.assetCap_pos hok z Kh Kc' L L' hKc hL hL')
    (by rw [hK []]; exact hμ)
  intro h
  refine ⟨hlow h, ?_⟩
  rw [hK h]
  exact ((crraModel V T hγ).meanCapital_mem z₀ μ₀ _ h).2.trans hcapHi

/-- **The prices are the unclamped Cobb–Douglas marginal products** at every node of every
sequential equilibrium of the CRRA economy (under the conditions of `crra_capital_mem`). -/
theorem crra_unclamped_prices {π : ℝ} (hπ0 : 0 < π) (hπ : ∀ z, π ≤ V.aggProb z z)
    (hlab : T.labLo = V.effLo ∧ T.labHi = V.effHi) (hcapHi : V.assetCap ≤ T.capHi)
    (hok : T.CapLoOK V.discount π γ V.effHi V.assetCap) (z₀ : Z)
    (μ₀ : Measure (crraModel V T hγ).AState) [IsProbabilityMeasure μ₀]
    (hμ : T.capLo ≤ ∫ x, (crraModel V T hγ).assets x ∂μ₀) {Kc : List Z → ℝ}
    (hK : (crraModel V T hγ).IsSequentialEquilibrium z₀ μ₀ Kc) (h : List Z) :
    (crraModel V T hγ).returnAt z₀
        ((crraModel V T hγ).pricePath z₀ ((crraModel V T hγ).initMass μ₀) Kc) h
      = 1 - T.depreciation + T.share * T.tfp (shockAt z₀ h) * Kc h ^ (T.share - 1)
          * (crraModel V T hγ).labour z₀ ((crraModel V T hγ).initMass μ₀) h ^ (1 - T.share) ∧
    (crraModel V T hγ).wageAt z₀
        ((crraModel V T hγ).pricePath z₀ ((crraModel V T hγ).initMass μ₀) Kc) h
      = (1 - T.share) * T.tfp (shockAt z₀ h) * Kc h ^ T.share
          * (crraModel V T hγ).labour z₀ ((crraModel V T hγ).initMass μ₀) h ^ (-T.share) := by
  have hKh := crra_capital_mem V T hγ hπ0 hπ hlab hcapHi hok z₀ μ₀ hμ hK h
  have hL : (crraModel V T hγ).labour z₀ ((crraModel V T hγ).initMass μ₀) h
      ∈ Icc T.labLo T.labHi := by
    rw [hlab.1, hlab.2]
    exact (crraModel V T hγ).labour_mem z₀ μ₀ V.effLo_le V.le_effHi h
  exact ⟨T.grossReturn_of_mem _ hKh hL, T.wage_of_mem _ hKh hL⟩

/-- **Existence of sequential equilibrium with unclamped Cobb–Douglas prices**, for CRRA utility
(any `γ > 0`, log included), from every distribution with mean assets at least `capLo`. -/
theorem crra_exists_unclamped_equilibrium {π : ℝ} (hπ0 : 0 < π) (hπ : ∀ z, π ≤ V.aggProb z z)
    (hlab : T.labLo = V.effLo ∧ T.labHi = V.effHi) (hcapHi : V.assetCap ≤ T.capHi)
    (hok : T.CapLoOK V.discount π γ V.effHi V.assetCap) (z₀ : Z)
    (μ₀ : Measure (crraModel V T hγ).AState) [IsProbabilityMeasure μ₀]
    (hμ : T.capLo ≤ ∫ x, (crraModel V T hγ).assets x ∂μ₀) :
    ∃ Kc, (crraModel V T hγ).IsSequentialEquilibrium z₀ μ₀ Kc ∧
      ∀ h, Kc h ∈ Icc T.capLo T.capHi ∧
        (crraModel V T hγ).returnAt z₀
            ((crraModel V T hγ).pricePath z₀ ((crraModel V T hγ).initMass μ₀) Kc) h
          = 1 - T.depreciation + T.share * T.tfp (shockAt z₀ h) * Kc h ^ (T.share - 1)
              * (crraModel V T hγ).labour z₀ ((crraModel V T hγ).initMass μ₀) h
                ^ (1 - T.share) ∧
        (crraModel V T hγ).wageAt z₀
            ((crraModel V T hγ).pricePath z₀ ((crraModel V T hγ).initMass μ₀) Kc) h
          = (1 - T.share) * T.tfp (shockAt z₀ h) * Kc h ^ T.share
              * (crraModel V T hγ).labour z₀ ((crraModel V T hγ).initMass μ₀) h
                ^ (-T.share) := by
  obtain ⟨Kc, -, hK⟩ := (crraModel V T hγ).exists_sequentialEquilibrium z₀ μ₀
  exact ⟨Kc, hK, fun h => ⟨crra_capital_mem V T hγ hπ0 hπ hlab hcapHi hok z₀ μ₀ hμ hK h,
    crra_unclamped_prices V T hγ hπ0 hπ hlab hcapHi hok z₀ μ₀ hμ hK h⟩⟩

end KrusellSmith

end LeanEconomics
