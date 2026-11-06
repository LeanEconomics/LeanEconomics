/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Contraction
import LeanEconomics.KrusellSmith.CobbDouglas

/-!
# Uniqueness for CRRA utility and clamped Cobb–Douglas prices

Milestone M5 of `UNIQUENESS_PLAN.md`: the hypotheses `ContractionHyp` of the contraction argument
hold, with explicit constants, for a Krusell–Smith economy with CRRA utility `c^{1-γ}/(1-γ)`
(log at `γ = 1`, any `γ > 0`) and clamped Cobb–Douglas prices.

* **Consumption floor** (`crraFloorLevel`). For CRRA the Inada radius is explicit:
  `r = (β S + 1)^{-1/γ}` with `S = slopeConst`, and optimal consumption is at least
  `c̲ = min r (incomeFloor / 4)` along every path (`KSInada.min_radius_le_consumption`). The model
  imposes the floor `c̲ / 2`, which never binds.
* **Marginal utility** `u'(c) = c^{-γ}` is `γ (c̲/2)^{-γ-1}`-Lipschitz above the floor and
  strongly decreasing with modulus `γ topCons^{-γ-1}` below the largest cash on hand
  (`crra_du_bounds`, by the mean value theorem).
* **Prices** (`CobbDouglas.cdLip`): the clamped gross return and wage are Lipschitz in capital with
  constants `α(1-α) z̄ L̄^{1-α} K̲^{α-2}` and `α(1-α) z̄ L̲^{-α} K̲^{α-1}`.

**Theorem** (`crra_existsUnique_sequentialEquilibrium`, `crra_isRecursive`): for weights `λ` with
`β R̄ < λ ≤ 1` and `λ R̄ < 1`, if the modulus `κ` of `crraContractionHyp` is below one, then from
every initial shock and distribution there is exactly one sequential equilibrium, and the
recursive equilibrium on the minimal state `(z, μ)` exists.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

/-! ### Mean value bounds for powers -/

/-- The mean value theorem for `t ↦ t ^ p`. -/
theorem exists_rpow_sub_eq (p : ℝ) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    ∃ ξ ∈ Ioo x y, y ^ p - x ^ p = p * ξ ^ (p - 1) * (y - x) := by
  obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ p)
    (fun t => p * t ^ (p - 1)) hxy
    (fun t ht =>
      (Real.continuousAt_rpow_const t p (Or.inl (hx.trans_le ht.1).ne')).continuousWithinAt)
    (fun t ht => Real.hasDerivAt_rpow_const (Or.inl (hx.trans ht.1).ne'))
  refine ⟨ξ, hξ, ?_⟩
  rw [e, div_mul_cancel₀ _ (sub_pos.2 hxy).ne']

/-- For `p ≤ 1`, `t ↦ t ^ p` is `|p| a^{p-1}`-Lipschitz on `[a, ∞)`. -/
theorem abs_rpow_sub_le {p a x y : ℝ} (hp : p ≤ 1) (ha : 0 < a) (hax : a ≤ x) (hay : a ≤ y) :
    |x ^ p - y ^ p| ≤ |p| * a ^ (p - 1) * |x - y| := by
  have key : ∀ x y, a ≤ x → x ≤ y → |y ^ p - x ^ p| ≤ |p| * a ^ (p - 1) * (y - x) := by
    intro x y hax hxy
    rcases hxy.eq_or_lt with rfl | hlt
    · simp
    obtain ⟨ξ, hξ, e⟩ := exists_rpow_sub_eq p (ha.trans_le hax) hlt
    have hξ0 : 0 < ξ := ha.trans_le (hax.trans hξ.1.le)
    rw [e, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hξ0 _),
      abs_of_pos (sub_pos.2 hlt)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha (hax.trans hξ.1.le) (by linarith)) (abs_nonneg p))
      (sub_pos.2 hlt).le
  rcases le_total x y with h | h
  · rw [abs_sub_comm (x ^ p), abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 h)]
    exact key x y hax h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact key y x hay h

/-- **CRRA marginal utility gaps**: for `0 < x ≤ y`,
`γ y^{-γ-1} (y - x) ≤ x^{-γ} - y^{-γ} ≤ γ x^{-γ-1} (y - x)`. -/
theorem crra_du_bounds {γ x y : ℝ} (hγ : 0 < γ) (hx : 0 < x) (hxy : x ≤ y) :
    γ * y ^ (-γ - 1) * (y - x) ≤ x ^ (-γ) - y ^ (-γ) ∧
      x ^ (-γ) - y ^ (-γ) ≤ γ * x ^ (-γ - 1) * (y - x) := by
  rcases hxy.eq_or_lt with rfl | hlt
  · simp
  obtain ⟨ξ, hξ, e⟩ := exists_rpow_sub_eq (-γ) hx hlt
  have hξ0 : 0 < ξ := hx.trans hξ.1
  have e' : x ^ (-γ) - y ^ (-γ) = γ * ξ ^ (-γ - 1) * (y - x) := by linarith
  have h1 : y ^ (-γ - 1) ≤ ξ ^ (-γ - 1) :=
    Real.rpow_le_rpow_of_nonpos hξ0 hξ.2.le (by linarith)
  have h2 : ξ ^ (-γ - 1) ≤ x ^ (-γ - 1) :=
    Real.rpow_le_rpow_of_nonpos hx hξ.1.le (by linarith)
  have hd : 0 ≤ y - x := (sub_pos.2 hlt).le
  rw [e']
  exact ⟨mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hγ.le) hd,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hγ.le) hd⟩

/-! ### Clamped Cobb–Douglas prices are Lipschitz in capital -/

namespace CobbDouglas

variable {Z : Type*} (T : CobbDouglas Z)

theorem abs_clampCap_sub_le (k k' : ℝ) : |T.clampCap k - T.clampCap k'| ≤ |k - k'| := by
  simp only [clampCap]
  rw [max_comm T.capLo, max_comm T.capLo]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

theorem abs_rpow_clampCap_sub_le {p : ℝ} (hp : p ≤ 1) (k k' : ℝ) :
    |T.clampCap k ^ p - T.clampCap k' ^ p| ≤ |p| * T.capLo ^ (p - 1) * |k - k'| :=
  (abs_rpow_sub_le hp T.capLo_pos (T.clampCap_mem k).1 (T.clampCap_mem k').1).trans
    (mul_le_mul_of_nonneg_left (T.abs_clampCap_sub_le k k')
      (mul_nonneg (abs_nonneg p) (Real.rpow_nonneg T.capLo_pos.le _)))

/-- The Lipschitz constant of the clamped gross return in capital. -/
noncomputable def returnLip : ℝ :=
  T.share * T.tfpHi * T.labHi ^ (1 - T.share) * ((1 - T.share) * T.capLo ^ (T.share - 1 - 1))

/-- The Lipschitz constant of the clamped wage in capital. -/
noncomputable def wageLip : ℝ :=
  (1 - T.share) * T.tfpHi * T.labLo ^ (-T.share) * (T.share * T.capLo ^ (T.share - 1))

/-- The Lipschitz constant of clamped Cobb–Douglas prices in capital. -/
noncomputable def cdLip : ℝ := max T.returnLip T.wageLip

theorem tfpHi_nonneg (z : Z) : 0 ≤ T.tfpHi := (T.tfp_pos z).le.trans (T.tfp_le z)

theorem returnLip_nonneg [Nonempty Z] : 0 ≤ T.returnLip := by
  have z : Z := Classical.arbitrary Z
  have hs := T.share_pos
  have hs1 : 0 ≤ 1 - T.share := by linarith [T.share_lt_one]
  exact mul_nonneg (mul_nonneg (mul_nonneg hs.le (T.tfpHi_nonneg z))
    (Real.rpow_nonneg (T.labLo_pos.trans_le T.labLo_le).le _))
    (mul_nonneg hs1 (Real.rpow_nonneg T.capLo_pos.le _))

theorem cdLip_nonneg [Nonempty Z] : 0 ≤ T.cdLip := T.returnLip_nonneg.trans (le_max_left _ _)

theorem abs_grossReturn_sub_le (z : Z) (k k' L : ℝ) :
    |T.grossReturn z k L - T.grossReturn z k' L| ≤ T.cdLip * |k - k'| := by
  have hs := T.share_pos
  have hs1 : T.share - 1 ≤ 0 := by linarith [T.share_lt_one]
  have e : T.grossReturn z k L - T.grossReturn z k' L
      = (T.share * T.tfp z * T.clampLab L ^ (1 - T.share))
        * (T.clampCap k ^ (T.share - 1) - T.clampCap k' ^ (T.share - 1)) := by
    simp only [grossReturn]
    ring
  have hL := Real.rpow_nonneg (T.clampLab_pos L).le (1 - T.share)
  have hcoef : 0 ≤ T.share * T.tfp z * T.clampLab L ^ (1 - T.share) :=
    mul_nonneg (mul_nonneg hs.le (T.tfp_pos z).le) hL
  have hcoefle : T.share * T.tfp z * T.clampLab L ^ (1 - T.share)
      ≤ T.share * T.tfpHi * T.labHi ^ (1 - T.share) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (T.tfp_le z) hs.le)
      (Real.rpow_le_rpow (T.clampLab_pos L).le (T.clampLab_mem L).2 (by linarith))
      hL (mul_nonneg hs.le (T.tfpHi_nonneg z))
  have hp := T.abs_rpow_clampCap_sub_le (p := T.share - 1) (by linarith) k k'
  rw [abs_of_nonpos hs1] at hp
  rw [e, abs_mul, abs_of_nonneg hcoef]
  calc _ ≤ (T.share * T.tfpHi * T.labHi ^ (1 - T.share))
          * (-(T.share - 1) * T.capLo ^ (T.share - 1 - 1) * |k - k'|) :=
        mul_le_mul hcoefle hp (abs_nonneg _) (hcoef.trans hcoefle)
    _ = T.returnLip * |k - k'| := by simp only [returnLip]; ring
    _ ≤ T.cdLip * |k - k'| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)

theorem abs_wage_sub_le (z : Z) (k k' L : ℝ) :
    |T.wage z k L - T.wage z k' L| ≤ T.cdLip * |k - k'| := by
  have hs := T.share_pos
  have hs1 : 0 ≤ 1 - T.share := by linarith [T.share_lt_one]
  have e : T.wage z k L - T.wage z k' L
      = ((1 - T.share) * T.tfp z * T.clampLab L ^ (-T.share))
        * (T.clampCap k ^ T.share - T.clampCap k' ^ T.share) := by
    simp only [wage]
    ring
  have hL := Real.rpow_nonneg (T.clampLab_pos L).le (-T.share)
  have hcoef : 0 ≤ (1 - T.share) * T.tfp z * T.clampLab L ^ (-T.share) :=
    mul_nonneg (mul_nonneg hs1 (T.tfp_pos z).le) hL
  have hcoefle : (1 - T.share) * T.tfp z * T.clampLab L ^ (-T.share)
      ≤ (1 - T.share) * T.tfpHi * T.labLo ^ (-T.share) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (T.tfp_le z) hs1)
      (Real.rpow_le_rpow_of_nonpos T.labLo_pos (T.clampLab_mem L).1 (by linarith))
      hL (mul_nonneg hs1 (T.tfpHi_nonneg z))
  have hp := T.abs_rpow_clampCap_sub_le (p := T.share) T.share_lt_one.le k k'
  rw [abs_of_pos hs] at hp
  rw [e, abs_mul, abs_of_nonneg hcoef]
  calc _ ≤ ((1 - T.share) * T.tfpHi * T.labLo ^ (-T.share))
          * (T.share * T.capLo ^ (T.share - 1) * |k - k'|) :=
        mul_le_mul hcoefle hp (abs_nonneg _) (hcoef.trans hcoefle)
    _ = T.wageLip * |k - k'| := by simp only [wageLip]; ring
    _ ≤ T.cdLip * |k - k'| := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)

end CobbDouglas

/-! ### The CRRA economy -/

variable {Z E : Type*} [Fintype Z] [Fintype E]

/-- **A Krusell–Smith economy with CRRA utility and clamped Cobb–Douglas prices.** -/
noncomputable def crraEconomy (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ) :
    KSInada Z E where
  aggProb := V.aggProb
  aggProb_nonneg := V.aggProb_nonneg
  aggProb_sum := V.aggProb_sum
  idioProb := V.idioProb
  idioProb_nonneg := V.idioProb_nonneg
  idioProb_sum := V.idioProb_sum
  efficiency := V.efficiency
  efficiency_nonneg e := V.effLo_pos.le.trans (V.effLo_le e)
  assetCap := V.assetCap
  assetCap_pos := V.assetCap_pos
  discount := V.discount
  discount_pos := V.discount_pos
  discount_lt_one := V.discount_lt_one
  grossReturn := T.grossReturn
  continuous_grossReturn := T.continuous_grossReturn
  grossReturn_nonneg := T.grossReturn_nonneg
  returnBound := T.returnBound
  grossReturn_le := T.grossReturn_le
  wage := T.wage
  continuous_wage := T.continuous_wage
  wage_nonneg := T.wage_nonneg
  wageBound := T.wageBound
  wage_le := T.wage_le
  incomeFloor := T.wageLo * V.effLo
  incomeFloor_pos := mul_pos T.wageLo_pos V.effLo_pos
  incomeFloor_le z K L e :=
    mul_le_mul (T.wageLo_le_wage z K L) (V.effLo_le e) V.effLo_pos.le (T.wage_nonneg z K L)
  utility := crraUtility γ
  continuousOn_utility := continuousOn_crraUtility γ
  strictConcaveOn_utility := strictConcaveOn_crraUtility hγ
  monotoneOn_utility := monotoneOn_crraUtility γ
  marginalInada := marginalInada_crraUtility hγ

variable (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)

/-- The explicit Inada radius for CRRA: below it, marginal utility exceeds `β · slopeConst + 1`. -/
noncomputable def crraRadius : ℝ :=
  ((crraEconomy V T hγ).discount * (crraEconomy V T hγ).slopeConst + 1) ^ (-1 / γ)

/-- **The explicit consumption floor** for CRRA: optimal consumption never goes below it. -/
noncomputable def crraFloorLevel : ℝ :=
  min (crraRadius V T hγ) ((crraEconomy V T hγ).incomeFloor / 4)

theorem crraRadius_pos : 0 < crraRadius V T hγ :=
  Real.rpow_pos_of_pos (by
    have := mul_nonneg (crraEconomy V T hγ).discount_pos.le (crraEconomy V T hγ).slopeConst_nonneg
    linarith) _

theorem crraFloorLevel_pos : 0 < crraFloorLevel V T hγ :=
  lt_min (crraRadius_pos V T hγ) (by linarith [(crraEconomy V T hγ).incomeFloor_pos])

theorem crraFloorLevel_half_pos : 0 < crraFloorLevel V T hγ / 2 :=
  half_pos (crraFloorLevel_pos V T hγ)

theorem crraFloorLevel_half_le : crraFloorLevel V T hγ / 2 ≤ (crraEconomy V T hγ).incomeFloor := by
  have h1 : crraFloorLevel V T hγ ≤ (crraEconomy V T hγ).incomeFloor / 4 := min_le_right _ _
  have h2 := (crraEconomy V T hγ).incomeFloor_pos
  linarith

/-- The radius property of `crraRadius`. -/
theorem crraRadius_spec (c₁ c₂ : ℝ) (h₁ : c₁ ∈ Ioi 0) (h₁₂ : c₁ < c₂)
    (h₂ : c₂ ≤ crraRadius V T hγ) :
    ((crraEconomy V T hγ).discount * (crraEconomy V T hγ).slopeConst + 1) * (c₂ - c₁)
      ≤ (crraEconomy V T hγ).utility c₂ - (crraEconomy V T hγ).utility c₁ := by
  set k := (crraEconomy V T hγ).discount * (crraEconomy V T hγ).slopeConst + 1 with hk
  have hk0 : 0 < k := by
    have := mul_nonneg (crraEconomy V T hγ).discount_pos.le (crraEconomy V T hγ).slopeConst_nonneg
    linarith
  have hc₁ : 0 < c₁ := h₁
  obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope (crraUtility γ) (fun t => t ^ (-γ)) h₁₂
    (fun t ht => ((hasDerivAt_crraUtility γ (hc₁.trans_le ht.1)).continuousAt).continuousWithinAt)
    (fun t ht => hasDerivAt_crraUtility γ (hc₁.trans ht.1))
  have hξ0 : 0 < ξ := hc₁.trans hξ.1
  -- `ξ ≤ r`, so `ξ^{-γ} ≥ r^{-γ} = k`
  have hr : crraRadius V T hγ ^ (-γ) = k := by
    rw [crraRadius, ← hk, ← Real.rpow_mul hk0.le]
    rw [show -1 / γ * -γ = 1 by field_simp, Real.rpow_one]
  have hle : k ≤ ξ ^ (-γ) := by
    rw [← hr]
    exact Real.rpow_le_rpow_of_nonpos hξ0 (hξ.2.le.trans h₂) (by linarith)
  have hd : 0 < c₂ - c₁ := sub_pos.2 h₁₂
  have e' : (crraEconomy V T hγ).utility c₂ - (crraEconomy V T hγ).utility c₁
      = ξ ^ (-γ) * (c₂ - c₁) := by
    change crraUtility γ c₂ - crraUtility γ c₁ = _
    rw [e, div_mul_cancel₀ _ hd.ne']
  rw [e']
  exact mul_le_mul_of_nonneg_right hle hd.le

/-- **The CRRA model**: the floored economy at half the explicit consumption floor. -/
noncomputable abbrev crraModel : KSModel Z E :=
  (crraEconomy V T hγ).toModel (crraFloorLevel V T hγ / 2) (crraFloorLevel_half_pos V T hγ)
    (crraFloorLevel_half_le V T hγ)

/-- Optimal consumption in the CRRA model is at least `crraFloorLevel`. -/
theorem crraFloorLevel_le_consumption (z₀ : Z) (K : List Z → ℝ × ℝ) (s : (crraModel V T hγ).State) :
    crraFloorLevel V T hγ ≤ (crraModel V T hγ).consumption z₀ K s :=
  (crraEconomy V T hγ).min_radius_le_consumption (crraFloorLevel_half_pos V T hγ)
    (crraFloorLevel_half_le V T hγ) z₀ K (crraRadius_spec V T hγ) s

/-- CRRA marginal utility, `c ↦ c^{-γ}`, as a `SmoothUtility` of the CRRA model. -/
noncomputable def crraSmoothUtility : (crraModel V T hγ).SmoothUtility where
  du c := c ^ (-γ)
  hasDerivAt _ hc := hasDerivAt_crraUtility γ ((crraFloorLevel_half_pos V T hγ).trans hc)
  continuousOn c hc :=
    (Real.continuousAt_rpow_const c (-γ)
      (Or.inl ((crraFloorLevel_half_pos V T hγ).trans hc).ne')).continuousWithinAt

/-- **The base hypotheses of the contraction argument hold for the CRRA model**, for any weight
`λ` with `β R̄ < λ ≤ 1`. -/
noncomputable def crraContractionBase [Nonempty Z] (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hdisc : V.discount * T.returnBound < lam) :
    (crraModel V T hγ).ContractionBase where
  U := crraSmoothUtility V T hγ
  cLo := crraFloorLevel V T hγ
  floor_lt_cLo := half_lt_self (crraFloorLevel_pos V T hγ)
  cLo_le := crraFloorLevel_le_consumption V T hγ
  Mdu := γ * (crraFloorLevel V T hγ / 2) ^ (-γ - 1)
  Mdu_nonneg := mul_nonneg hγ.le (Real.rpow_nonneg (crraFloorLevel_half_pos V T hγ).le _)
  du_lip x y hx hxy := by
    have hx0 : 0 < x := (crraFloorLevel_half_pos V T hγ).trans hx
    have h := (crra_du_bounds hγ hx0 hxy).2
    have h2 : x ^ (-γ - 1) ≤ (crraFloorLevel V T hγ / 2) ^ (-γ - 1) :=
      Real.rpow_le_rpow_of_nonpos (crraFloorLevel_half_pos V T hγ) hx.le (by linarith)
    have hd : 0 ≤ y - x := sub_nonneg.2 hxy
    calc x ^ (-γ) - y ^ (-γ) ≤ γ * x ^ (-γ - 1) * (y - x) := h
      _ ≤ γ * (crraFloorLevel V T hγ / 2) ^ (-γ - 1) * (y - x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hγ.le) hd
  m := γ * (crraEconomy V T hγ).topCons ^ (-γ - 1)
  m_pos := mul_pos hγ (Real.rpow_pos_of_pos
    ((crraEconomy V T hγ).incomeFloor_pos.trans_le (le_max_left _ _)) _)
  du_strong x y hx hxy hy := by
    have hx0 : 0 < x := (crraFloorLevel_half_pos V T hγ).trans hx
    have h := (crra_du_bounds hγ hx0 hxy).1
    have hyt : y ≤ (crraEconomy V T hγ).topCons := hy.trans (le_max_right _ _)
    have h2 : (crraEconomy V T hγ).topCons ^ (-γ - 1) ≤ y ^ (-γ - 1) :=
      Real.rpow_le_rpow_of_nonpos (hx0.trans_le hxy) hyt (by linarith)
    have hd : 0 ≤ y - x := sub_nonneg.2 hxy
    calc γ * (crraEconomy V T hγ).topCons ^ (-γ - 1) * (y - x)
        ≤ γ * y ^ (-γ - 1) * (y - x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hγ.le) hd
      _ ≤ x ^ (-γ) - y ^ (-γ) := h
  ℓ := T.cdLip
  ℓ_nonneg := T.cdLip_nonneg
  return_lip := T.abs_grossReturn_sub_le
  wage_lip := T.abs_wage_sub_le
  lam := lam
  lam_pos := hlam0
  lam_le_one := hlam1
  disc_lt := hdisc

/-- **The hypotheses of the contraction argument hold for the CRRA model**, for any weight `λ`
with `β R̄ < λ ≤ 1` and `λ R̄ < 1`. -/
noncomputable def crraContractionHyp [Nonempty Z] (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hdisc : V.discount * T.returnBound < lam) (hret : lam * T.returnBound < 1) :
    (crraModel V T hγ).ContractionHyp :=
  { crraContractionBase V T hγ lam hlam0 hlam1 hdisc with lam_return_lt := hret }

variable [Nonempty Z] {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
  (hdisc : V.discount * T.returnBound < lam) (hret : lam * T.returnBound < 1)

/-- **Existence and uniqueness of sequential equilibrium** with CRRA utility and clamped
Cobb–Douglas prices, when the contraction modulus is below one. -/
theorem crra_existsUnique_sequentialEquilibrium
    (hκ : (crraContractionHyp V T hγ lam hlam0 hlam1 hdisc hret).κ < 1) (z₀ : Z)
    (μ₀ : ProbabilityMeasure (crraModel V T hγ).AState) :
    ∃! K, (crraModel V T hγ).IsSequentialEquilibrium z₀ (μ₀ : Measure _) K := by
  obtain ⟨K, -, hK⟩ := (crraModel V T hγ).exists_sequentialEquilibrium z₀ (μ₀ : Measure _)
  exact ⟨K, hK, fun K' hK' =>
    (crraContractionHyp V T hγ lam hlam0 hlam1 hdisc hret).uniqueSequentialEquilibrium hκ
      z₀ μ₀ K' K hK' hK⟩

/-- **Recursive equilibrium on the minimal state** with CRRA utility and clamped Cobb–Douglas
prices, when the contraction modulus is below one. -/
theorem crra_isRecursive (hκ : (crraContractionHyp V T hγ lam hlam0 hlam1 hdisc hret).κ < 1)
    (z : Z) (μ : ProbabilityMeasure (crraModel V T hγ).AState) (h : List Z) :
    (crraModel V T hγ).eqPath z μ h
        = ∫ x, (crraModel V T hγ).assets x ∂((crraModel V T hγ).nodeProb z μ h : Measure _) ∧
      (∀ x : (crraModel V T hγ).AState,
        (crraModel V T hγ).policy z ((crraModel V T hγ).pricePath z
            ((crraModel V T hγ).initMass (μ : Measure _)) ((crraModel V T hγ).eqPath z μ))
            (x.1, ⟨x.2.idio, h⟩)
          = (crraModel V T hγ).recursivePolicy (shockAt z h)
              ((crraModel V T hγ).nodeProb z μ h) x) ∧
      ∀ z' : Z, (crraModel V T hγ).nodeProb z μ (z' :: h)
        = (crraModel V T hγ).lawOfMotion (shockAt z h) ((crraModel V T hγ).nodeProb z μ h) z' :=
  (crraContractionHyp V T hγ lam hlam0 hlam1 hdisc hret).isRecursive hκ z μ h

end KrusellSmith

end LeanEconomics
