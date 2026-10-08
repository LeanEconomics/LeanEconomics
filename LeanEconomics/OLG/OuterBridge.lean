/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EnclCert.Outer
import LeanEconomics.Models.OLG7Cap
import LeanEconomics.OLG.EnclBridge
import LeanEconomics.OLG.CapSlack
import LeanEconomics.OLG.Existence
import LeanEconomics.OLG.Reachable
import LeanEconomics.OLG.EnclFinal

/-!
# From the outer-range checker to the life-cycle economy

`EnclCert.Outer` verifies, on a cell of rates `[m₁/RD, m₂/RD]`, exact integer inequalities. This
file says what each of them means for an economy `P` of the seven-state calibration whose gross
rate lies in the cell (`InCell`): bounds on the patience factor, the finite-horizon propensity,
human wealth, risk-adjusted human wealth, the cohort slope, the affine ceiling and the clamped
floor; cap slack from impatience; and the two conclusions, capital supply below demand
(`olgCapital_lt_demand_of_cell`) and above it (`demand_lt_olgCapital_of_cell`).
-/

open Set

namespace LeanEconomics.EnclCert

open IncomeFluctuation

/-- The real number an integer over `D` stands for. -/
noncomputable def vI (n : Int) : ℝ := (n : ℝ) / D

theorem DI_cast : ((DI : Int) : ℝ) = (D : ℝ) := by simp [DI]
theorem RD_cast : ((RD : Int) : ℝ) = 1000000 := by norm_num [RD]
theorem RD_pos : (0 : ℝ) < ((RD : Int) : ℝ) := by rw [RD_cast]; norm_num
theorem vI_DI : vI DI = 1 := by rw [vI, DI_cast]; exact div_self D_pos.ne'
theorem vI_zero : vI 0 = 0 := by simp [vI]
theorem vI_nonneg {n : Int} (h : 0 ≤ n) : 0 ≤ vI n :=
  div_nonneg (by exact_mod_cast h) D_pos.le
theorem vI_pos {n : Int} (h : 0 < n) : 0 < vI n :=
  div_pos (by exact_mod_cast h) D_pos
theorem vI_le_vI {m n : Int} (h : m ≤ n) : vI m ≤ vI n :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) D_pos.le
theorem vI_le_one_of_le {n : Int} (h : n ≤ DI) : vI n ≤ 1 := by
  rw [← vI_DI]; exact vI_le_vI h

/-- `a ≤ b` when `b - a` is a quotient of a nonnegative numerator by a positive denominator. -/
theorem le_of_sub_eq_div {a b n d : ℝ} (h : b - a = n / d) (hn : 0 ≤ n) (hd : 0 < d) : a ≤ b := by
  have : 0 ≤ b - a := by rw [h]; exact div_nonneg hn hd.le
  linarith

theorem lt_of_sub_eq_div {a b n d : ℝ} (h : b - a = n / d) (hn : 0 < n) (hd : 0 < d) : a < b := by
  have : 0 < b - a := by rw [h]; exact div_pos hn hd
  linarith

/-- The gross rate `(RD + m)/RD` as a real. -/
noncomputable def rI (m : Int) : ℝ := ((Rn m : Int) : ℝ) / ((RD : Int) : ℝ)

theorem rI_pos {m : Int} (h : 0 < Rn m) : 0 < rI m := div_pos (by exact_mod_cast h) RD_pos

/-- The economy `P` carries the calibration's data and a gross rate inside the cell. -/
structure InCell {cap : ℝ} (P : IncomeFluctuation (Fin 7) 0 cap) (m1 m2 : Int) : Prop where
  income : ∀ z, P.income z = (yQ z : ℝ)
  trans : ∀ z z', P.transitionMatrix z z' = (piQ z z' : ℝ)
  disc : (P.discount : ℝ) = 24 / 25
  u : P.u = crraUtility 3
  unb : P.Unbounded
  minInc : P.minIncome = (19264 : ℝ) / 72101
  maxInc : P.maxIncome = (212480 : ℝ) / 72101
  rlo : rI m1 ≤ 1 + P.interest
  rhi : 1 + P.interest ≤ rI m2

theorem InCell.disc_pos {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 : Int}
    (hM : InCell P m1 m2) : 0 < (P.discount : ℝ) := by rw [hM.disc]; norm_num

/-! ### The patience factor -/

theorem tOK_unpack {m1 m2 tLo tHi : Int} (h : tOK m1 m2 tLo tHi = true) :
    0 < Rn m1 ∧ m1 ≤ m2 ∧ 0 < tLo ∧ 0 < tHi ∧ tLo ^ 3 * 25 * RD ≤ 24 * Rn m1 * DI ^ 3
      ∧ 24 * Rn m2 * DI ^ 3 ≤ tHi ^ 3 * 25 * RD := by
  simp only [tOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem le_patience_of_pow_le {cap : ℝ} (P : IncomeFluctuation (Fin 7) 0 cap) {t : ℝ}
    (ht : 0 ≤ t) (h : t ^ 3 ≤ (P.discount : ℝ) * (1 + P.interest)) : t ≤ P.patience 3 := by
  have h3 : t = (t ^ 3) ^ ((1 : ℝ) / 3) := by
    rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast ht (by norm_num)]
  show t ≤ ((P.discount : ℝ) * (1 + P.interest)) ^ ((1 : ℝ) / 3)
  rw [h3]
  exact Real.rpow_le_rpow (by positivity) h (by norm_num)

theorem patience_lo {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 tLo tHi : Int}
    (hM : InCell P m1 m2) (ht : tOK m1 m2 tLo tHi = true) : vI tLo ≤ P.patience 3 := by
  obtain ⟨hR1, -, htl, -, h5, -⟩ := tOK_unpack ht
  refine le_patience_of_pow_le P (vI_nonneg htl.le) ?_
  have hreal : ((tLo : ℝ)) ^ 3 * 25 * ((RD : Int) : ℝ) ≤ 24 * ((Rn m1 : Int) : ℝ) * (D : ℝ) ^ 3 := by
    have := h5
    rw [← DI_cast]; exact_mod_cast this
  have hD := D_pos; have hRD := RD_pos
  have h1 : vI tLo ^ 3 ≤ (24 / 25) * rI m1 := by
    refine le_of_sub_eq_div (n := 24 * ((Rn m1 : Int) : ℝ) * (D : ℝ) ^ 3
      - (tLo : ℝ) ^ 3 * 25 * ((RD : Int) : ℝ)) (d := 25 * ((RD : Int) : ℝ) * (D : ℝ) ^ 3) ?_
      (by linarith) (by positivity)
    unfold vI rI; field_simp
  calc vI tLo ^ 3 ≤ (24 / 25) * rI m1 := h1
    _ ≤ (P.discount : ℝ) * (1 + P.interest) := by
      rw [hM.disc]; exact mul_le_mul_of_nonneg_left hM.rlo (by norm_num)

theorem patience_hi {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 tLo tHi : Int}
    (hM : InCell P m1 m2) (ht : tOK m1 m2 tLo tHi = true) : P.patience 3 ≤ vI tHi := by
  obtain ⟨hR1, hm, -, hth, -, h6⟩ := tOK_unpack ht
  have hD := D_pos; have hRD := RD_pos
  refine P.patience_le_of_le_rpow (by norm_num) hM.disc_pos (vI_pos hth) ?_
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hreal : 24 * ((Rn m2 : Int) : ℝ) * (D : ℝ) ^ 3 ≤ ((tHi : ℝ)) ^ 3 * 25 * ((RD : Int) : ℝ) := by
    have := h6
    rw [← DI_cast]; exact_mod_cast this
  have h1 : (24 / 25) * rI m2 ≤ vI tHi ^ 3 := by
    refine le_of_sub_eq_div (n := (tHi : ℝ) ^ 3 * 25 * ((RD : Int) : ℝ)
      - 24 * ((Rn m2 : Int) : ℝ) * (D : ℝ) ^ 3) (d := 25 * ((RD : Int) : ℝ) * (D : ℝ) ^ 3) ?_
      (by linarith) (by positivity)
    unfold vI rI; field_simp
  calc (P.discount : ℝ) * (1 + P.interest) ≤ (24 / 25) * rI m2 := by
        rw [hM.disc]; exact mul_le_mul_of_nonneg_left hM.rhi (by norm_num)
    _ ≤ vI tHi ^ 3 := h1

/-! ### The finite-horizon propensity -/

theorem kapOK_unpack {m1 m2 tLo tHi : Int} {kLo kHi : Array Int}
    (h : kapOK m1 m2 tLo tHi kLo kHi = true) :
    kLo.size = J ∧ kHi.size = J ∧ kLo[0]! = DI ∧ kHi[0]! = DI ∧
      ∀ k < J - 1, 0 ≤ kLo[k+1]!
        ∧ kLo[k+1]! * (tHi * RD + kLo[k]! * Rn m1) ≤ kLo[k]! * Rn m1 * DI
        ∧ 0 < kHi[k+1]! ∧ kHi[k+1]! ≤ DI
        ∧ kHi[k]! * Rn m2 * DI ≤ kHi[k+1]! * (tLo * RD + kHi[k]! * Rn m2) := by
  simp only [kapOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun k hk => ?_⟩
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h5 k hk
  exact ⟨a, b, c, d, e⟩

/-- The step of the lower bound: `b ≤ κR/(Þ + κR)` from `b (Th + a R₁) ≤ a R₁` with `a ≤ κ`,
`R₁ ≤ R`, `Þ ≤ Th`. -/
theorem kapLo_step {κ R T a R1 Th b : ℝ} (hκ : a ≤ κ) (ha : 0 ≤ a) (hR : R1 ≤ R) (hR1 : 0 < R1)
    (hT : T ≤ Th) (hTpos : 0 < T) (hb : b * (Th + a * R1) ≤ a * R1) :
    b ≤ κ * R / (T + κ * R) := by
  have hx0 : 0 ≤ a * R1 := by positivity
  have hx : a * R1 ≤ κ * R := mul_le_mul hκ hR hR1.le (le_trans ha hκ)
  have hκR : 0 ≤ κ * R := le_trans hx0 hx
  have h1 : b ≤ a * R1 / (Th + a * R1) := by
    rw [le_div_iff₀ (by linarith)]; exact hb
  have h2 : a * R1 / (Th + a * R1) ≤ a * R1 / (T + a * R1) :=
    div_le_div_of_nonneg_left hx0 (by linarith) (by linarith)
  have h3 : a * R1 / (T + a * R1) ≤ κ * R / (T + κ * R) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  linarith

/-- The step of the upper bound: `κR/(Þ + κR) ≤ b` from `a R₂ ≤ b (Tl + a R₂)` with `κ ≤ a`,
`R ≤ R₂`, `Tl ≤ Þ`. -/
theorem kapHi_step {κ R T a R2 Tl b : ℝ} (hκ : κ ≤ a) (hκ0 : 0 ≤ κ) (hR : R ≤ R2) (hR0 : 0 < R)
    (hT : Tl ≤ T) (hTl : 0 < Tl) (hb : a * R2 ≤ b * (Tl + a * R2)) :
    κ * R / (T + κ * R) ≤ b := by
  have hx : κ * R ≤ a * R2 := mul_le_mul hκ hR hR0.le (le_trans hκ0 hκ)
  have hκR : 0 ≤ κ * R := by positivity
  have hx1 : 0 ≤ a * R2 := le_trans hκR hx
  have h1 : κ * R / (T + κ * R) ≤ a * R2 / (T + a * R2) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : a * R2 / (T + a * R2) ≤ a * R2 / (Tl + a * R2) :=
    div_le_div_of_nonneg_left hx1 (by linarith) (by linarith)
  have h3 : a * R2 / (Tl + a * R2) ≤ b := by
    rw [div_le_iff₀ (by linarith)]; exact hb
  linarith

/-- **The propensity is bracketed by the checker's bounds**, at every stage of the life. -/
theorem kap_bounds {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 tLo tHi : Int}
    {kLo kHi : Array Int} (hM : InCell P m1 m2) (ht : tOK m1 m2 tLo tHi = true)
    (hk : kapOK m1 m2 tLo tHi kLo kHi = true) :
    ∀ k < J, 0 ≤ kLo[k]! ∧ vI kLo[k]! ≤ P.stageMPC 3 k ∧ P.stageMPC 3 k ≤ vI kHi[k]! := by
  obtain ⟨hR1, hm, htl, hth, -, -⟩ := tOK_unpack ht
  obtain ⟨-, -, h0lo, h0hi, hstep⟩ := kapOK_unpack hk
  have hTlo := patience_lo hM ht
  have hThi := patience_hi hM ht
  have hTpos := P.patience_pos' (γ := 3) (by norm_num) hM.disc_pos
  have hRpos := P.interest_gt_neg_one
  have hD := D_pos; have hRD := RD_pos
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by rw [h0lo]; norm_num [DI, D], ?_, ?_⟩
    · rw [h0lo, vI_DI]; simp [stageMPC]
    · rw [h0hi, vI_DI]; simp [stageMPC]
  | succ k ih =>
    intro hk1
    obtain ⟨hlo0, hκlo, hκhi⟩ := ih (by omega)
    obtain ⟨hlo1, hlo, hhi1pos, hhi1le, hhi⟩ := hstep k (by omega)
    refine ⟨hlo1, ?_, ?_⟩
    · rw [stageMPC_succ]
      have hb : vI kLo[k+1]! * (vI tHi + vI kLo[k]! * rI m1) ≤ vI kLo[k]! * rI m1 := by
        have hreal : ((kLo[k+1]! : Int) : ℝ) * ((tHi : ℝ) * ((RD : Int) : ℝ)
            + ((kLo[k]! : Int) : ℝ) * ((Rn m1 : Int) : ℝ))
            ≤ ((kLo[k]! : Int) : ℝ) * ((Rn m1 : Int) : ℝ) * (D : ℝ) := by
          rw [← DI_cast]; exact_mod_cast hlo
        refine le_of_sub_eq_div (n := ((kLo[k]! : Int) : ℝ) * ((Rn m1 : Int) : ℝ) * (D : ℝ)
          - ((kLo[k+1]! : Int) : ℝ) * ((tHi : ℝ) * ((RD : Int) : ℝ)
            + ((kLo[k]! : Int) : ℝ) * ((Rn m1 : Int) : ℝ)))
          (d := (D : ℝ) ^ 2 * ((RD : Int) : ℝ)) ?_ (by linarith) (by positivity)
        unfold vI rI; field_simp
      exact kapLo_step hκlo (vI_nonneg hlo0) hM.rlo (rI_pos hR1) hThi hTpos hb
    · rw [stageMPC_succ]
      have hb : vI kHi[k]! * rI m2 ≤ vI kHi[k+1]! * (vI tLo + vI kHi[k]! * rI m2) := by
        have hreal : ((kHi[k]! : Int) : ℝ) * ((Rn m2 : Int) : ℝ) * (D : ℝ)
            ≤ ((kHi[k+1]! : Int) : ℝ) * ((tLo : ℝ) * ((RD : Int) : ℝ)
              + ((kHi[k]! : Int) : ℝ) * ((Rn m2 : Int) : ℝ)) := by
          rw [← DI_cast]; exact_mod_cast hhi
        refine le_of_sub_eq_div (n := ((kHi[k+1]! : Int) : ℝ) * ((tLo : ℝ) * ((RD : Int) : ℝ)
            + ((kHi[k]! : Int) : ℝ) * ((Rn m2 : Int) : ℝ))
          - ((kHi[k]! : Int) : ℝ) * ((Rn m2 : Int) : ℝ) * (D : ℝ))
          (d := (D : ℝ) ^ 2 * ((RD : Int) : ℝ)) ?_ (by linarith) (by positivity)
        unfold vI rI; field_simp
      exact kapHi_step hκhi (P.stageMPC_pos (by norm_num) hM.disc_pos k).le hM.rhi hRpos hTlo
        (vI_pos htl) hb

/-! ### Sums and data -/

theorem sumI_cast (f : ℕ → Int) :
    ((sumI f : Int) : ℝ) = ∑ w : Fin 7, ((f w : Int) : ℝ) := by
  simp only [sumI, Fin.sum_univ_seven, Fin.val_zero, Fin.val_one, Fin.val_two]
  push_cast
  rfl

theorem piI_cast (z w : Fin 7) : ((piI z w : Int) : ℝ) = (piQ z w : ℝ) * piDen := by
  rw [piI, Int.cast_natCast, ← piNum_div, div_mul_cancel₀ _ piDen_pos.ne']

theorem piDenI_cast : ((piDenI : Int) : ℝ) = (piDen : ℝ) := by simp [piDenI]

/-- `∑ π(z,w) g(w)/D` as the checker's integer sum. -/
theorem sum_piQ_vI (z : Fin 7) (g : ℕ → Int) :
    ∑ w : Fin 7, (piQ z w : ℝ) * vI (g w) = ((sumI fun w => piI z w * g w : Int) : ℝ) / (piDen * D) := by
  rw [sumI_cast]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hp : (piDen : ℝ) ≠ 0 := piDen_pos.ne'
  have hD : (D : ℝ) ≠ 0 := D_pos.ne'
  rw [piI_cast, vI]
  field_simp

theorem yDn_le (z : Fin 7) : vI (yDn z) ≤ (yQ z : ℝ) := by
  rw [vI, yDn, Int.cast_natCast, ← yN_div]
  have := (yN_pos z).2
  rw [div_le_div_iff₀ D_pos (by exact_mod_cast this)]
  have h := natDiv_le_real ((yN z).1 * D) (yN z).2
  rw [le_div_iff₀ (by exact_mod_cast this)] at h
  push_cast at h ⊢
  linarith

theorem le_yUp (z : Fin 7) : (yQ z : ℝ) ≤ vI (yUp z) := by
  rw [vI, yUp, Int.cast_natCast, ← yN_div]
  have := (yN_pos z).2
  rw [div_le_div_iff₀ (by exact_mod_cast this) D_pos]
  have h := le_ceilDiv_real (a := (yN z).1 * D) (b := (yN z).2) this
  rw [div_le_iff₀ (by exact_mod_cast this)] at h
  push_cast at h ⊢
  linarith

theorem yDn_nonneg (z : ℕ) : 0 ≤ yDn z := by unfold yDn; exact Int.natCast_nonneg _
theorem yUp_nonneg (z : ℕ) : 0 ≤ yUp z := by unfold yUp; exact Int.natCast_nonneg _

theorem yQ_pos (z : Fin 7) : (0 : ℝ) < (yQ z : ℝ) := by
  have := yQ_min z
  have h : (((19264 / 72101 : ℚ)) : ℝ) ≤ (yQ z : ℝ) := Rat.cast_le.mpr this
  push_cast at h
  linarith

theorem nuR_eq (z : Fin 7) : nuR z = ((nuI z : Int) : ℝ) / 64 := by
  rw [nuR, ← nuN_div, nuN_den, nuI, Int.cast_natCast]; push_cast; rfl

theorem sum_nuR_vI (g : ℕ → Int) :
    ∑ z : Fin 7, nuR z * vI (g z) = ((sumI fun z => nuI z * g z : Int) : ℝ) / (64 * D) := by
  rw [sumI_cast]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [nuR_eq, vI]
  field_simp

/-! ### Human wealth from above -/

theorem hHiOK_unpack {m1 : Int} {hHi : Array (Array Int)} (h : hHiOK m1 hHi = true) :
    hHi.size = J ∧ (∀ z < 7, (hHi[0]!)[z]! = 0) ∧ ∀ k < J - 1, ∀ z < 7,
      sumI (fun w => piI z w * (yUp w + (hHi[k]!)[w]!)) * RD ≤ (hHi[k+1]!)[z]! * piDenI * Rn m1 := by
  simp only [hHiOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem stageHumanWealth_le_hHi {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 : Int}
    {hHi : Array (Array Int)} (hM : InCell P m1 m2) (hR1 : 0 < Rn m1)
    (hh : hHiOK m1 hHi = true) :
    ∀ k < J, ∀ z : Fin 7, P.stageHumanWealth k z ≤ vI (hHi[k]!)[(z : ℕ)]! := by
  obtain ⟨-, h0, hstep⟩ := hHiOK_unpack hh
  have hD := D_pos; have hRD := RD_pos
  have hRpos := P.interest_gt_neg_one
  intro k
  induction k with
  | zero => intro _ z; rw [h0 (z : ℕ) z.isLt]; simp [vI, stageHumanWealth]
  | succ k ih =>
    intro hk z
    rw [stageHumanWealth_succ]
    have hsum : ∑ z', P.transitionMatrix z z' * (P.income z' + P.stageHumanWealth k z')
        ≤ ∑ w : Fin 7, (piQ z w : ℝ) * vI (yUp (w : ℕ) + (hHi[k]!)[(w : ℕ)]!) := by
      refine Finset.sum_le_sum fun w _ => ?_
      rw [hM.trans, hM.income]
      refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast piQ_nonneg z w)
      rw [vI, Int.cast_add, add_div]
      exact add_le_add (le_yUp w) (ih (by omega) w)
    have hs := sum_piQ_vI z (fun w => yUp w + (hHi[k]!)[w]!)
    beta_reduce at hs
    rw [hs] at hsum
    have hsum_nonneg : 0 ≤ ∑ z', P.transitionMatrix z z' * (P.income z' + P.stageHumanWealth k z') :=
      Finset.sum_nonneg fun w _ => mul_nonneg (P.transitionMatrix_nonneg z w)
        (add_nonneg (by rw [hM.income]; exact (yQ_pos w).le) (P.stageHumanWealth_nonneg k w))
    have hreal : ((sumI (fun w => piI z w * (yUp w + (hHi[k]!)[w]!)) : Int) : ℝ) * ((RD : Int) : ℝ)
        ≤ (((hHi[k+1]!)[z]! : Int) : ℝ) * (piDen : ℝ) * ((Rn m1 : Int) : ℝ) := by
      rw [← piDenI_cast]; exact_mod_cast hstep k (by omega) z z.isLt
    calc (∑ z', P.transitionMatrix z z' * (P.income z' + P.stageHumanWealth k z')) / (1 + P.interest)
        ≤ (((sumI fun w => piI z w * (yUp w + (hHi[k]!)[w]!) : Int) : ℝ) / (piDen * D)) / rI m1 := by
          exact div_le_div₀ (le_trans hsum_nonneg hsum) hsum (rI_pos hR1) hM.rlo
      _ ≤ vI (hHi[k+1]!)[z]! := by
          refine le_of_sub_eq_div (n := (((hHi[k+1]!)[z]! : Int) : ℝ) * (piDen : ℝ) * ((Rn m1 : Int) : ℝ)
            - ((sumI (fun w => piI z w * (yUp w + (hHi[k]!)[w]!)) : Int) : ℝ) * ((RD : Int) : ℝ))
            (d := (piDen : ℝ) * (D : ℝ) * ((Rn m1 : Int) : ℝ)) ?_ (by linarith)
            (mul_pos (mul_pos piDen_pos hD) (by exact_mod_cast hR1))
          have hRn : (0 : ℝ) < ((Rn m1 : Int) : ℝ) := by exact_mod_cast hR1
          have := piDen_pos
          unfold vI rI; field_simp

/-! ### Risk-adjusted human wealth from below: the power mean -/

theorem pmOK_unpack {xs : ℕ → Int} {z : ℕ} {m : Int} (h : pmOK xs z m = true) :
    0 ≤ m ∧ m ^ 3 * sUp xs z ≤ DI ^ 3 * Q ∧ ∀ w < 7, 0 < xs w ∧
      (piNum z w = 0 ∨ piI z w * DI ^ 3 * Q ≤ sTerm xs z w * (piDenI * xs w ^ 3)) := by
  simp only [pmOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem sTerm_nonneg_of_zero {xs : ℕ → Int} {z w : ℕ} (h : piNum z w = 0) : sTerm xs z w = 0 := by
  simp [sTerm, h]

/-- `m ≤ S^{-1/3}` from `m³ S ≤ 1`. -/
theorem le_rpow_neg_third {m S : ℝ} (hm : 0 ≤ m) (hS : 0 < S) (h : m ^ 3 * S ≤ 1) :
    m ≤ S ^ (1 / (-3 : ℝ)) := by
  have h1 : m ^ 3 ≤ S⁻¹ := by rw [← one_div, le_div_iff₀ hS]; linarith
  have h2 : (m ^ 3) ^ ((1 : ℝ) / 3) ≤ (S⁻¹) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hm (by norm_num),
    Real.inv_rpow hS.le, ← Real.rpow_neg hS.le] at h2
  rw [show (1 / (-3 : ℝ)) = -(((3 : ℕ) : ℝ)⁻¹) by norm_num]
  exact h2

theorem rpow_neg_three' {x : ℝ} (hx : 0 < x) : x ^ (-(3 : ℝ)) = (x ^ 3)⁻¹ := rpow_neg_three hx

/-- **The checker's `m` is below the power mean** of exponent `-3` of `xs/D` under `π(z, ·)`. -/
theorem vI_le_powerMean {xs : ℕ → Int} {z : Fin 7} {m : Int} (h : pmOK xs z m = true) :
    vI m ≤ powerMean (fun w : Fin 7 => (piQ z w : ℝ)) (-3) (fun w : Fin 7 => vI (xs w)) := by
  obtain ⟨hm, hmain, hw⟩ := pmOK_unpack h
  have hD := D_pos
  have hQ : ((Q : Int) : ℝ) = (D : ℝ) ^ 3 := by simp [Q, DI]
  have hxpos : ∀ w : Fin 7, 0 < vI (xs w) := fun w => vI_pos (hw w w.isLt).1
  -- the sum is below `sUp / Q`
  have hS : ∑ w : Fin 7, (piQ z w : ℝ) * vI (xs w) ^ (-3 : ℝ)
      ≤ ((sUp xs z : Int) : ℝ) / ((Q : Int) : ℝ) := by
    rw [sUp, sumI_cast, Finset.sum_div]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [rpow_neg_three' (hxpos w)]
    rcases (hw w w.isLt).2 with h0 | hle
    · rw [sTerm_nonneg_of_zero h0]
      have : (piQ z w : ℝ) = 0 := by
        rw [← piNum_div, h0]; simp
      rw [this]; simp
    · have hx := (hw w w.isLt).1
      have hxr : (0 : ℝ) < ((xs w : Int) : ℝ) := by exact_mod_cast hx
      have hQpos : (0 : ℝ) < ((Q : Int) : ℝ) := by rw [hQ]; positivity
      have hreal : ((piI z w : Int) : ℝ) * (D : ℝ) ^ 3 * ((Q : Int) : ℝ)
          ≤ ((sTerm xs z w : Int) : ℝ) * ((piDen : ℝ) * ((xs w : Int) : ℝ) ^ 3) := by
        rw [← piDenI_cast, ← DI_cast]; exact_mod_cast hle
      rw [piI_cast] at hreal
      refine le_of_sub_eq_div (n := ((sTerm xs z w : Int) : ℝ) * ((piDen : ℝ) * ((xs w : Int) : ℝ) ^ 3)
        - (piQ z w : ℝ) * (piDen : ℝ) * (D : ℝ) ^ 3 * ((Q : Int) : ℝ))
        (d := (piDen : ℝ) * ((xs w : Int) : ℝ) ^ 3 * ((Q : Int) : ℝ)) ?_ (by linarith)
        (mul_pos (mul_pos piDen_pos (pow_pos hxr 3)) hQpos)
      have := piDen_pos
      unfold vI; field_simp
  have hSpos : 0 < ∑ w : Fin 7, (piQ z w : ℝ) * vI (xs w) ^ (-3 : ℝ) :=
    sum_rpow_pos (fun w => by exact_mod_cast piQ_nonneg z w) (by exact_mod_cast piQ_row_sum z) hxpos
  unfold powerMean
  refine le_rpow_neg_third (vI_nonneg hm) hSpos ?_
  have hmain' : ((m : ℝ)) ^ 3 * ((sUp xs z : Int) : ℝ) ≤ (D : ℝ) ^ 3 * ((Q : Int) : ℝ) := by
    rw [← DI_cast]; exact_mod_cast hmain
  have hQpos : (0 : ℝ) < ((Q : Int) : ℝ) := by rw [hQ]; positivity
  have hsUp_nonneg : 0 ≤ ((sUp xs z : Int) : ℝ) := by
    have h := lt_of_lt_of_le hSpos hS
    rw [div_pos_iff_of_pos_right hQpos] at h
    exact h.le
  calc vI m ^ 3 * ∑ w : Fin 7, (piQ z w : ℝ) * vI (xs w) ^ (-3 : ℝ)
      ≤ vI m ^ 3 * (((sUp xs z : Int) : ℝ) / ((Q : Int) : ℝ)) :=
        mul_le_mul_of_nonneg_left hS (pow_nonneg (vI_nonneg hm) 3)
    _ ≤ 1 := by
        rw [vI, div_pow, div_mul_div_comm, div_le_one (mul_pos (pow_pos hD 3) hQpos)]
        linarith [hmain']

theorem hrOK_unpack {m2 : Int} {kHi : Array Int} {hr pm : Array (Array Int)}
    (h : hrOK m2 kHi hr pm = true) :
    hr.size = J ∧ pm.size = J ∧ (∀ z < 7, (hr[0]!)[z]! = 0) ∧ ∀ k < J - 1, ∀ z < 7,
      pmOK (fun w => yDn w + (hr[k]!)[w]!) z (pm[k+1]!)[z]! = true ∧ 0 ≤ (hr[k+1]!)[z]!
        ∧ (hr[k+1]!)[z]! * Rn m2 ≤ (pm[k+1]!)[z]! * RD
        ∧ (hr[k+1]!)[z]! * kHi[k+1]! ≤ (DI - kHi[k+1]!) * yDn z := by
  simp only [hrOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun k hk z hz => ?_⟩
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h4 k hk z hz
  exact ⟨a, b, c, d⟩

/-- **Risk-adjusted human wealth is above the checker's lower bound.** -/
theorem riskHumanWealth_ge_hr {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap}
    {m1 m2 tLo tHi : Int} {kLo kHi : Array Int} {hr pm : Array (Array Int)}
    (hM : InCell P m1 m2) (ht : tOK m1 m2 tLo tHi = true) (hk : kapOK m1 m2 tLo tHi kLo kHi = true)
    (hh : hrOK m2 kHi hr pm = true) :
    ∀ k < J, ∀ z : Fin 7, vI (hr[k]!)[(z : ℕ)]! ≤ P.riskHumanWealth 3 k z := by
  obtain ⟨hR1, hm, -, -, -, -⟩ := tOK_unpack ht
  have hκ := kap_bounds hM ht hk
  obtain ⟨-, -, -, -, hkstep⟩ := kapOK_unpack hk
  obtain ⟨-, -, h0, hstep⟩ := hrOK_unpack hh
  have hD := D_pos; have hRD := RD_pos; have hRpos := P.interest_gt_neg_one
  have hR2 : 0 < Rn m2 := by unfold Rn at hR1 ⊢; omega
  intro k
  induction k with
  | zero => intro _ z; rw [h0 (z : ℕ) z.isLt]; simp [vI, riskHumanWealth]
  | succ k ih =>
    intro hk1 z
    obtain ⟨hpm, hnn, hle1, hle2⟩ := hstep k (by omega) (z : ℕ) z.isLt
    obtain ⟨-, -, hκhi⟩ := hκ (k + 1) hk1
    obtain ⟨-, -, hk1pos, hk1le, -⟩ := hkstep k (by omega)
    have hκpos := P.stageMPC_pos (γ := 3) (by norm_num) hM.disc_pos (k + 1)
    rw [riskHumanWealth_succ]
    refine le_min ?_ ?_
    · have hPM := vI_le_powerMean (z := z) hpm
      have htr : P.transitionMatrix z = fun w => (piQ z w : ℝ) := funext (hM.trans z)
      have hxs : ∀ w : Fin 7, 0 < (fun w => yDn w + (hr[k]!)[w]!) (w : ℕ) :=
        fun w => ((pmOK_unpack hpm).2.2 w w.isLt).1
      have hmono : powerMean (fun w : Fin 7 => (piQ z w : ℝ)) (-3)
            (fun w : Fin 7 => vI ((fun w => yDn w + (hr[k]!)[w]!) (w : ℕ)))
          ≤ powerMean (P.transitionMatrix z) (-3)
            (fun w => P.income w + P.riskHumanWealth 3 k w) := by
        rw [htr]
        refine powerMean_mono (by norm_num) (fun w => by exact_mod_cast piQ_nonneg z w)
          (by exact_mod_cast piQ_row_sum z) (fun w => vI_pos (hxs w))
          (fun w => add_pos_of_pos_of_nonneg (by rw [hM.income]; exact yQ_pos w)
            (P.riskHumanWealth_nonneg (by norm_num) hM.disc_pos k w))
          (fun w => ?_)
        · show vI (yDn w + (hr[k]!)[(w : ℕ)]!) ≤ P.income w + P.riskHumanWealth 3 k w
          rw [vI, Int.cast_add, add_div, hM.income]
          exact add_le_add (yDn_le w) (ih (by omega) w)
      have hpm_nonneg : 0 ≤ vI (pm[k+1]!)[(z : ℕ)]! := vI_nonneg (pmOK_unpack hpm).1
      have h1 : vI (hr[k+1]!)[(z : ℕ)]! ≤ vI (pm[k+1]!)[(z : ℕ)]! / rI m2 := by
        have hreal : ((((hr[k+1]!)[(z : ℕ)]! : Int)) : ℝ) * ((Rn m2 : Int) : ℝ)
            ≤ (((pm[k+1]!)[(z : ℕ)]! : Int) : ℝ) * ((RD : Int) : ℝ) := by exact_mod_cast hle1
        have hRn : (0 : ℝ) < ((Rn m2 : Int) : ℝ) := by exact_mod_cast hR2
        refine le_of_sub_eq_div (n := (((pm[k+1]!)[(z : ℕ)]! : Int) : ℝ) * ((RD : Int) : ℝ)
          - ((((hr[k+1]!)[(z : ℕ)]! : Int)) : ℝ) * ((Rn m2 : Int) : ℝ))
          (d := (D : ℝ) * ((Rn m2 : Int) : ℝ)) ?_ (by linarith) (by positivity)
        unfold vI rI; field_simp
      calc vI (hr[k+1]!)[(z : ℕ)]! ≤ vI (pm[k+1]!)[(z : ℕ)]! / rI m2 := h1
        _ ≤ vI (pm[k+1]!)[(z : ℕ)]! / (1 + P.interest) :=
            div_le_div_of_nonneg_left hpm_nonneg hRpos hM.rhi
        _ ≤ powerMean (P.transitionMatrix z) (-3)
              (fun w => P.income w + P.riskHumanWealth 3 k w) / (1 + P.interest) :=
            div_le_div_of_nonneg_right (le_trans hPM hmono) hRpos.le
    · have hk1r : (0 : ℝ) < ((kHi[k+1]! : Int) : ℝ) := by exact_mod_cast hk1pos
      have hk1le' : ((kHi[k+1]! : Int) : ℝ) ≤ (D : ℝ) := by rw [← DI_cast]; exact_mod_cast hk1le
      have hreal : ((((hr[k+1]!)[(z : ℕ)]! : Int)) : ℝ) * ((kHi[k+1]! : Int) : ℝ)
          ≤ ((D : ℝ) - ((kHi[k+1]! : Int) : ℝ)) * ((yDn z : Int) : ℝ) := by
        rw [← DI_cast]; exact_mod_cast hle2
      have hA : vI (hr[k+1]!)[(z : ℕ)]! ≤ (1 / vI kHi[k+1]! - 1) * vI (yDn z) := by
        refine le_of_sub_eq_div (n := ((D : ℝ) - ((kHi[k+1]! : Int) : ℝ)) * ((yDn z : Int) : ℝ)
          - ((((hr[k+1]!)[(z : ℕ)]! : Int)) : ℝ) * ((kHi[k+1]! : Int) : ℝ))
          (d := ((kHi[k+1]! : Int) : ℝ) * (D : ℝ)) ?_ (by linarith) (by positivity)
        unfold vI; field_simp
      have hB : (1 / vI kHi[k+1]! - 1) * vI (yDn z) ≤ (1 / P.stageMPC 3 (k + 1) - 1) * P.income z := by
        have h1 : 1 / vI kHi[k+1]! ≤ 1 / P.stageMPC 3 (k + 1) :=
          one_div_le_one_div_of_le hκpos hκhi
        have h2 : (0 : ℝ) ≤ 1 / vI kHi[k+1]! - 1 := by
          have : vI kHi[k+1]! ≤ 1 := vI_le_one_of_le hk1le
          have hpos : 0 < vI kHi[k+1]! := vI_pos hk1pos
          rw [sub_nonneg]; exact one_le_one_div hpos this
        rw [hM.income]
        exact mul_le_mul (by linarith) (yDn_le z) (vI_nonneg (yDn_nonneg z)) (by linarith [h2, h1])
      exact le_trans hA hB

/-! ### The cohort slope -/

theorem gOK_unpack {m1 m2 : Int} {kLo kHi gLo gHi : Array Int}
    (h : gOK m1 m2 kLo kHi gLo gHi = true) :
    gLo.size = J ∧ gHi.size = J ∧ gLo[0]! = DI ∧ gHi[0]! = DI ∧ ∀ k < J - 1,
      0 ≤ gLo[k+1]! ∧ gLo[k+1]! * DI * RD ≤ DI * DI * RD + gLo[k]! * (DI - kHi[k+1]!) * Rn m1
        ∧ DI * DI * RD + gHi[k]! * (DI - kLo[k+1]!) * Rn m2 ≤ gHi[k+1]! * DI * RD := by
  simp only [gOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun k hk => ?_⟩
  obtain ⟨⟨a, b⟩, c⟩ := h5 k hk
  exact ⟨a, b, c⟩

/-- **The cohort slope is bracketed by the checker's bounds.** -/
theorem cohortSlope_bounds {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 tLo tHi : Int}
    {kLo kHi gLo gHi : Array Int} (hM : InCell P m1 m2) (ht : tOK m1 m2 tLo tHi = true)
    (hk : kapOK m1 m2 tLo tHi kLo kHi = true) (hg : gOK m1 m2 kLo kHi gLo gHi = true) :
    ∀ k < J, 0 ≤ gLo[k]! ∧ vI gLo[k]! ≤ P.cohortSlope 3 k ∧ P.cohortSlope 3 k ≤ vI gHi[k]! := by
  obtain ⟨hR1, hm, -, -, -, -⟩ := tOK_unpack ht
  have hκ := kap_bounds hM ht hk
  obtain ⟨-, -, -, -, hkstep⟩ := kapOK_unpack hk
  obtain ⟨-, -, h0lo, h0hi, hstep⟩ := gOK_unpack hg
  have hD := D_pos; have hRD := RD_pos; have hRpos := P.interest_gt_neg_one
  have hR1r : (0 : ℝ) < ((Rn m1 : Int) : ℝ) := by exact_mod_cast hR1
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by rw [h0lo]; norm_num [DI, D], ?_, ?_⟩
    · rw [h0lo, vI_DI]; simp [cohortSlope]
    · rw [h0hi, vI_DI]; simp [cohortSlope]
  | succ k ih =>
    intro hk1
    obtain ⟨hglo0, hGlo, hGhi⟩ := ih (by omega)
    obtain ⟨hglo1, hlo, hhi⟩ := hstep k (by omega)
    obtain ⟨hklo1, hκlo, hκhi⟩ := hκ (k + 1) hk1
    obtain ⟨-, -, -, hk1le, -⟩ := hkstep k (by omega)
    have hGpos := P.cohortSlope_pos (γ := 3) (by norm_num) hM.disc_pos k
    have hκle1 := P.stageMPC_le_one (γ := 3) (by norm_num) hM.disc_pos (k + 1)
    have hκpos := P.stageMPC_pos (γ := 3) (by norm_num) hM.disc_pos (k + 1)
    refine ⟨hglo1, ?_, ?_⟩
    · rw [cohortSlope_succ]
      have h1 : vI gLo[k]! * (1 - vI kHi[k+1]!) * rI m1
          ≤ P.cohortSlope 3 k * (1 - P.stageMPC 3 (k + 1)) * (1 + P.interest) := by
        have hk1 : 1 - vI kHi[k+1]! ≤ 1 - P.stageMPC 3 (k + 1) := by linarith
        have hk1n : 0 ≤ 1 - vI kHi[k+1]! := by linarith [vI_le_one_of_le hk1le]
        exact mul_le_mul (mul_le_mul hGlo hk1 hk1n hGpos.le) hM.rlo (rI_pos hR1).le
          (mul_nonneg hGpos.le (by linarith))
      have hreal : ((gLo[k+1]! : Int) : ℝ) * (D : ℝ) * ((RD : Int) : ℝ)
          ≤ (D : ℝ) * (D : ℝ) * ((RD : Int) : ℝ)
            + ((gLo[k]! : Int) : ℝ) * ((D : ℝ) - ((kHi[k+1]! : Int) : ℝ)) * ((Rn m1 : Int) : ℝ) := by
        rw [← DI_cast]; exact_mod_cast hlo
      have h2 : vI gLo[k+1]! ≤ 1 + vI gLo[k]! * (1 - vI kHi[k+1]!) * rI m1 := by
        refine le_of_sub_eq_div (n := (D : ℝ) * (D : ℝ) * ((RD : Int) : ℝ)
            + ((gLo[k]! : Int) : ℝ) * ((D : ℝ) - ((kHi[k+1]! : Int) : ℝ)) * ((Rn m1 : Int) : ℝ)
            - ((gLo[k+1]! : Int) : ℝ) * (D : ℝ) * ((RD : Int) : ℝ))
          (d := (D : ℝ) * (D : ℝ) * ((RD : Int) : ℝ)) ?_ (by linarith) (by positivity)
        unfold vI rI; field_simp
      linarith
    · rw [cohortSlope_succ]
      have hghi0 : 0 ≤ vI gHi[k]! := le_trans hGpos.le hGhi
      have h1 : P.cohortSlope 3 k * (1 - P.stageMPC 3 (k + 1)) * (1 + P.interest)
          ≤ vI gHi[k]! * (1 - vI kLo[k+1]!) * rI m2 := by
        have hk1 : 1 - P.stageMPC 3 (k + 1) ≤ 1 - vI kLo[k+1]! := by linarith
        exact mul_le_mul (mul_le_mul hGhi hk1 (by linarith) hghi0) hM.rhi hRpos.le
          (mul_nonneg hghi0 (by linarith))
      have hreal : (D : ℝ) * (D : ℝ) * ((RD : Int) : ℝ)
            + ((gHi[k]! : Int) : ℝ) * ((D : ℝ) - ((kLo[k+1]! : Int) : ℝ)) * ((Rn m2 : Int) : ℝ)
          ≤ ((gHi[k+1]! : Int) : ℝ) * (D : ℝ) * ((RD : Int) : ℝ) := by
        rw [← DI_cast]; exact_mod_cast hhi
      have h2 : 1 + vI gHi[k]! * (1 - vI kLo[k+1]!) * rI m2 ≤ vI gHi[k+1]! := by
        refine le_of_sub_eq_div (n := ((gHi[k+1]! : Int) : ℝ) * (D : ℝ) * ((RD : Int) : ℝ)
            - ((D : ℝ) * (D : ℝ) * ((RD : Int) : ℝ)
            + ((gHi[k]! : Int) : ℝ) * ((D : ℝ) - ((kLo[k+1]! : Int) : ℝ)) * ((Rn m2 : Int) : ℝ)))
          (d := (D : ℝ) * (D : ℝ) * ((RD : Int) : ℝ)) ?_ (by linarith) (by positivity)
        unfold vI rI; field_simp
      linarith

/-! ### The affine ceiling -/

theorem fcOK_unpack {kLo gLo gHi : Array Int} {hr fc : Array (Array Int)}
    (h : fcOK kLo gLo gHi hr fc = true) :
    fc.size = J ∧ (∀ z < 7, (fc[0]!)[z]! = 0) ∧ ∀ k < J - 1, ∀ z < 7,
      DI * DI * sumI (fun w => piI z w * (fc[k]!)[w]!)
        + (if 0 ≤ bTerm kLo[k+1]! hr[k+1]! z then gHi[k]! else gLo[k]!) * bTerm kLo[k+1]! hr[k+1]! z
          * piDenI
        ≤ (fc[k+1]!)[z]! * DI * DI * piDenI := by
  simp only [fcOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The affine ceiling intercept is below the checker's bound.** -/
theorem cohortCeil_le_fc {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 tLo tHi : Int}
    {kLo kHi gLo gHi : Array Int} {hr pm fc : Array (Array Int)} (hM : InCell P m1 m2)
    (ht : tOK m1 m2 tLo tHi = true) (hk : kapOK m1 m2 tLo tHi kLo kHi = true)
    (hh : hrOK m2 kHi hr pm = true) (hg : gOK m1 m2 kLo kHi gLo gHi = true)
    (hf : fcOK kLo gLo gHi hr fc = true) :
    ∀ k < J, ∀ z : Fin 7, P.cohortCeil 3 k z ≤ vI (fc[k]!)[(z : ℕ)]! := by
  have hκ := kap_bounds hM ht hk
  have hHr := riskHumanWealth_ge_hr hM ht hk hh
  have hG := cohortSlope_bounds hM ht hk hg
  obtain ⟨-, h0, hstep⟩ := fcOK_unpack hf
  have hD := D_pos
  have hpd := piDen_pos
  intro k
  induction k with
  | zero => intro _ z; rw [h0 (z : ℕ) z.isLt]; simp [vI, cohortCeil]
  | succ k ih =>
    intro hk1 z
    obtain ⟨hklo1, hκlo, hκhi⟩ := hκ (k + 1) hk1
    obtain ⟨hglo, hGlo, hGhi⟩ := hG k (by omega)
    have hGpos := P.cohortSlope_pos (γ := 3) (by norm_num) hM.disc_pos k
    have hκle1 := P.stageMPC_le_one (γ := 3) (by norm_num) hM.disc_pos (k + 1)
    have hκpos := P.stageMPC_pos (γ := 3) (by norm_num) hM.disc_pos (k + 1)
    have hHrz := hHr (k + 1) hk1 z
    have hHrnn := P.riskHumanWealth_nonneg (γ := 3) (by norm_num) hM.disc_pos (k + 1) z
    rw [cohortCeil_succ]
    -- the sum
    have hsum : ∑ z', P.transitionMatrix z z' * P.cohortCeil 3 k z'
        ≤ ((sumI fun w => piI z w * (fc[k]!)[w]! : Int) : ℝ) / (piDen * D) := by
      have hs := sum_piQ_vI z (fun w => (fc[k]!)[w]!)
      beta_reduce at hs
      rw [← hs]
      refine Finset.sum_le_sum fun w _ => ?_
      rw [hM.trans]
      exact mul_le_mul_of_nonneg_left (ih (by omega) w) (by exact_mod_cast piQ_nonneg z w)
    -- the bracket
    set b : Int := bTerm kLo[k+1]! hr[k+1]! z with hb
    have hbr : (1 - P.stageMPC 3 (k + 1)) * P.income z
        - P.stageMPC 3 (k + 1) * P.riskHumanWealth 3 (k + 1) z ≤ (b : ℝ) / (D * D) := by
      have h1 : (1 - P.stageMPC 3 (k + 1)) * P.income z ≤ (1 - vI kLo[k+1]!) * vI (yUp z) := by
        rw [hM.income]
        exact mul_le_mul (by linarith) (le_yUp z) (yQ_pos z).le (by linarith [vI_nonneg hklo1])
      have h2 : vI kLo[k+1]! * vI (hr[k+1]!)[(z : ℕ)]!
          ≤ P.stageMPC 3 (k + 1) * P.riskHumanWealth 3 (k + 1) z :=
        mul_le_mul hκlo hHrz (vI_nonneg ((hrOK_unpack hh).2.2.2 k (by omega) (z : ℕ) z.isLt).2.1)
          hκpos.le
      have heq : (b : ℝ) / (D * D) = (1 - vI kLo[k+1]!) * vI (yUp z) - vI kLo[k+1]! * vI (hr[k+1]!)[(z : ℕ)]! := by
        rw [hb, bTerm]; push_cast; rw [DI_cast]; unfold vI; field_simp
      rw [heq]; linarith
    -- the slope times the bracket
    set G : Int := if 0 ≤ b then gHi[k]! else gLo[k]! with hG'
    have hGb : P.cohortSlope 3 k * ((1 - P.stageMPC 3 (k + 1)) * P.income z
        - P.stageMPC 3 (k + 1) * P.riskHumanWealth 3 (k + 1) z) ≤ (G : ℝ) * (b : ℝ) / (D * D * D) := by
      have hbD : (G : ℝ) * (b : ℝ) / (D * D * D) = vI G * ((b : ℝ) / (D * D)) := by
        unfold vI; field_simp
      rw [hbD]
      by_cases hb0 : 0 ≤ b
      · have hGe : G = gHi[k]! := by rw [hG', if_pos hb0]
        rw [hGe]
        have hbn : (0 : ℝ) ≤ (b : ℝ) / (D * D) := by
          have : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb0
          positivity
        calc P.cohortSlope 3 k * ((1 - P.stageMPC 3 (k + 1)) * P.income z
              - P.stageMPC 3 (k + 1) * P.riskHumanWealth 3 (k + 1) z)
            ≤ P.cohortSlope 3 k * ((b : ℝ) / (D * D)) := mul_le_mul_of_nonneg_left hbr hGpos.le
          _ ≤ vI gHi[k]! * ((b : ℝ) / (D * D)) := mul_le_mul_of_nonneg_right hGhi hbn
      · have hGe : G = gLo[k]! := by rw [hG', if_neg hb0]
        rw [hGe]
        have hbn : (b : ℝ) / (D * D) ≤ 0 := by
          have : (b : ℝ) < 0 := by exact_mod_cast (not_le.mp hb0)
          exact div_nonpos_of_nonpos_of_nonneg this.le (by positivity)
        calc P.cohortSlope 3 k * ((1 - P.stageMPC 3 (k + 1)) * P.income z
              - P.stageMPC 3 (k + 1) * P.riskHumanWealth 3 (k + 1) z)
            ≤ P.cohortSlope 3 k * ((b : ℝ) / (D * D)) := mul_le_mul_of_nonneg_left hbr hGpos.le
          _ ≤ vI gLo[k]! * ((b : ℝ) / (D * D)) := mul_le_mul_of_nonpos_right hGlo hbn
    -- assemble
    have hreal : (D : ℝ) * (D : ℝ) * ((sumI fun w => piI z w * (fc[k]!)[w]! : Int) : ℝ)
        + (G : ℝ) * (b : ℝ) * (piDen : ℝ) ≤ (((fc[k+1]!)[(z : ℕ)]! : Int) : ℝ) * (D : ℝ) * (D : ℝ) * (piDen : ℝ) := by
      have := hstep k (by omega) (z : ℕ) z.isLt
      rw [← hb, ← hG'] at this
      rw [← DI_cast, ← piDenI_cast]; exact_mod_cast this
    have hfin : ((sumI fun w => piI z w * (fc[k]!)[w]! : Int) : ℝ) / (piDen * D)
        + (G : ℝ) * (b : ℝ) / (D * D * D) ≤ vI (fc[k+1]!)[(z : ℕ)]! := by
      refine le_of_sub_eq_div (n := (((fc[k+1]!)[(z : ℕ)]! : Int) : ℝ) * (D : ℝ) * (D : ℝ) * (piDen : ℝ)
          - ((D : ℝ) * (D : ℝ) * ((sumI fun w => piI z w * (fc[k]!)[w]! : Int) : ℝ)
            + (G : ℝ) * (b : ℝ) * (piDen : ℝ)))
        (d := (D : ℝ) * (D : ℝ) * (D : ℝ) * (piDen : ℝ)) ?_ (by linarith) (by positivity)
      unfold vI; field_simp
    linarith

/-! ### Cap slack from impatience, on the cell -/

theorem slackOK_unpack {m1 m2 tHi : Int} (h : slackOK m1 m2 tHi = true) :
    (tHi * RD < DI * Rn m1 ∧ (212480 * RD + 72101 * m2 * CAPC) * DI * Rn m1 * tHi
        < (DI * Rn m1 - tHi * RD) * (19264 * RD + 72101 * Rn m1 * CAPC) * DI)
      ∨ 212480 * RD + 72101 * m2 * CAPC ≤ 0 := by
  simp only [slackOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem CAPC_cast : ((CAPC : Int) : ℝ) = 1000000 := by norm_num [CAPC]

theorem interest_le_of_rhi {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 : Int}
    (hM : InCell P m1 m2) : P.interest ≤ (m2 : ℝ) / ((RD : Int) : ℝ) := by
  have := hM.rhi
  have hRD := RD_pos
  rw [rI, Rn] at this
  push_cast at this
  rw [add_div, div_self hRD.ne'] at this
  linarith

theorem le_interest_of_rlo {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 : Int}
    (hM : InCell P m1 m2) : (m1 : ℝ) / ((RD : Int) : ℝ) ≤ P.interest := by
  have := hM.rlo
  have hRD := RD_pos
  rw [rI, Rn] at this
  push_cast at this
  rw [add_div, div_self hRD.ne'] at this
  linarith

/-- **The cap is slack at every stage on the cell**: the impatience condition holds at every
stage, by the limiting propensity (route A) or because `y_max + r·cap ≤ 0` (route B). -/
theorem slack_of_cell {P : IncomeFluctuation (Fin 7) 0 1000000} {m1 m2 tLo tHi : Int}
    (hM : InCell P m1 m2) (ht : tOK m1 m2 tLo tHi = true) (hs : slackOK m1 m2 tHi = true) :
    ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) 1000000, ∀ w : Fin 7, P.stagePolicy j (b, w) < 1000000 := by
  obtain ⟨hR1, hm, -, hth, -, -⟩ := tOK_unpack ht
  have hThi := patience_hi hM ht
  have hTpos := P.patience_pos' (γ := 3) (by norm_num) hM.disc_pos
  have hRpos := P.interest_gt_neg_one
  have hD := D_pos; have hRD := RD_pos
  have hR1r : (0 : ℝ) < ((Rn m1 : Int) : ℝ) := by exact_mod_cast hR1
  have hthr : (0 : ℝ) < (tHi : ℝ) := by exact_mod_cast hth
  have hr2 := interest_le_of_rhi hM
  have hlhs : P.maxIncome + P.interest * 1000000
      ≤ (212480 * ((RD : Int) : ℝ) + 72101 * (m2 : ℝ) * 1000000) / (72101 * ((RD : Int) : ℝ)) := by
    rw [hM.maxInc]
    have : (212480 * ((RD : Int) : ℝ) + 72101 * (m2 : ℝ) * 1000000) / (72101 * ((RD : Int) : ℝ))
        = 212480 / 72101 + (m2 : ℝ) / ((RD : Int) : ℝ) * 1000000 := by field_simp
    rw [this]; nlinarith [hr2]
  have hcond : ∀ k, P.maxIncome + P.interest * (1000000 : ℝ)
      < P.stageMPC 3 k * (P.minIncome + (1 + P.interest) * 1000000) / P.patience 3 := by
    intro k
    have hκpos := P.stageMPC_pos (γ := 3) (by norm_num) hM.disc_pos k
    have hmin : (0 : ℝ) < P.minIncome + (1 + P.interest) * 1000000 := by
      rw [hM.minInc]; positivity
    rcases slackOK_unpack hs with ⟨hpos, hlt⟩ | hneg
    · have hκinf : 1 - vI tHi / rI m1 ≤ P.stageMPC 3 k := by
        have hmin' := P.minMPC_le_stageMPC (γ := 3) (by norm_num) hM.disc_pos k
        have heq : P.minMPC 3 = 1 - P.patience 3 / (1 + P.interest) := rfl
        rw [heq] at hmin'
        have : P.patience 3 / (1 + P.interest) ≤ vI tHi / rI m1 :=
          div_le_div₀ (vI_nonneg hth.le) hThi (rI_pos hR1) hM.rlo
        linarith
      have hlt' : vI tHi < rI m1 := by
        have hreal : (tHi : ℝ) * ((RD : Int) : ℝ) < (D : ℝ) * ((Rn m1 : Int) : ℝ) := by
          rw [← DI_cast]; exact_mod_cast hpos
        rw [vI, rI, div_lt_div_iff₀ hD hRD]; linarith
      have hκinf_pos : 0 < 1 - vI tHi / rI m1 := by
        rw [sub_pos, div_lt_one (rI_pos hR1)]; exact hlt'
      have hrhs : (1 - vI tHi / rI m1) * (((19264 : ℝ) / 72101) + rI m1 * 1000000) / vI tHi
          ≤ P.stageMPC 3 k * (P.minIncome + (1 + P.interest) * 1000000) / P.patience 3 := by
        rw [hM.minInc]
        have hy : (0 : ℝ) ≤ (19264 : ℝ) / 72101 + rI m1 * 1000000 :=
          add_nonneg (by norm_num) (mul_nonneg (rI_pos hR1).le (by norm_num))
        have h1 : (1 - vI tHi / rI m1) * ((19264 : ℝ) / 72101 + rI m1 * 1000000)
            ≤ P.stageMPC 3 k * ((19264 : ℝ) / 72101 + (1 + P.interest) * 1000000) :=
          mul_le_mul hκinf
            (by have := mul_le_mul_of_nonneg_right hM.rlo (by norm_num : (0 : ℝ) ≤ 1000000); linarith)
            hy hκpos.le
        exact div_le_div₀ (mul_nonneg hκpos.le (by rw [hM.minInc] at hmin; exact hmin.le)) h1 hTpos hThi
      have hreal : (212480 * ((RD : Int) : ℝ) + 72101 * (m2 : ℝ) * 1000000) * (D : ℝ)
            * ((Rn m1 : Int) : ℝ) * (tHi : ℝ)
          < ((D : ℝ) * ((Rn m1 : Int) : ℝ) - (tHi : ℝ) * ((RD : Int) : ℝ))
            * (19264 * ((RD : Int) : ℝ) + 72101 * ((Rn m1 : Int) : ℝ) * 1000000) * (D : ℝ) := by
        have := hlt; rw [← DI_cast, ← CAPC_cast]; exact_mod_cast this
      have hkey : (212480 * ((RD : Int) : ℝ) + 72101 * (m2 : ℝ) * 1000000) / (72101 * ((RD : Int) : ℝ))
          < (1 - vI tHi / rI m1) * (((19264 : ℝ) / 72101) + rI m1 * 1000000) / vI tHi := by
        refine lt_of_sub_eq_div (n := ((D : ℝ) * ((Rn m1 : Int) : ℝ) - (tHi : ℝ) * ((RD : Int) : ℝ))
            * (19264 * ((RD : Int) : ℝ) + 72101 * ((Rn m1 : Int) : ℝ) * 1000000) * (D : ℝ)
            - (212480 * ((RD : Int) : ℝ) + 72101 * (m2 : ℝ) * 1000000) * (D : ℝ)
              * ((Rn m1 : Int) : ℝ) * (tHi : ℝ))
          (d := 72101 * ((RD : Int) : ℝ) * (D : ℝ) * ((Rn m1 : Int) : ℝ) * (tHi : ℝ)) ?_
          (by linarith) (by positivity)
        unfold vI rI; field_simp
      linarith [hlhs, hkey, hrhs]
    · have h0 : (212480 * ((RD : Int) : ℝ) + 72101 * (m2 : ℝ) * 1000000) ≤ 0 := by
        have := hneg; rw [← CAPC_cast]; exact_mod_cast this
      have h1 : (212480 * ((RD : Int) : ℝ) + 72101 * (m2 : ℝ) * 1000000) / (72101 * ((RD : Int) : ℝ))
          ≤ 0 := div_nonpos_of_nonpos_of_nonneg h0 (by positivity)
      have h2 : 0 < P.stageMPC 3 k * (P.minIncome + (1 + P.interest) * 1000000) / P.patience 3 :=
        div_pos (mul_pos hκpos hmin) hTpos
      linarith
  intro j b hb w
  exact P.stagePolicy_lt_cap_of_impatience (γ := 3) (by norm_num) hM.u hM.disc_pos hM.unb
    (by norm_num) (j + 1) (fun k _ => hcond k) j (Nat.le_succ j) b hb w

/-! ### Demand -/

theorem ceilLtDemand_unpack {m2 : Int} {fc59 : Array Int} (h : ceilLtDemand m2 fc59 = true) :
    0 < 25 * m2 + 2 * RD
      ∧ sumI (fun z => nuI z * fc59[z]!) * 16 * (25 * m2 + 2 * RD) < 225 * RD * 3840 * DI := by
  simp only [ceilLtDemand, Bool.and_eq_true, decide_eq_true_eq] at h; exact h

theorem olgDemand_eq (m : Int) (h : 0 < 25 * m + 2 * RD) :
    olgDemand ((m : ℝ) / ((RD : Int) : ℝ))
      = 225 * ((RD : Int) : ℝ) / (16 * (25 * (m : ℝ) + 2 * ((RD : Int) : ℝ))) := by
  have hpos : (0 : ℝ) < 25 * (m : ℝ) + 2 * ((RD : Int) : ℝ) := by exact_mod_cast h
  have hRD := RD_pos
  unfold olgDemand; field_simp; ring

theorem olgDemand_anti {a b : ℝ} (ha : -2 / 25 < a) (hab : a ≤ b) : olgDemand b ≤ olgDemand a := by
  unfold olgDemand
  have h1 : (0 : ℝ) < (1 - 9 / 25) * (a + 2 / 25) := by nlinarith
  have h2 : (1 - 9 / 25) * (a + 2 / 25) ≤ (1 - 9 / 25) * (b + 2 / 25) := by nlinarith
  exact div_le_div_of_nonneg_left (by norm_num) h1 h2

/-- **Capital supply is below demand**, from the checks on abstract data. -/
theorem olgCapital_lt_demand_of_checks {P : IncomeFluctuation (Fin 7) 0 1000000}
    {m1 m2 tLo tHi : Int} {kLo kHi gLo gHi : Array Int} {hr pm fc : Array (Array Int)}
    (hM : InCell P m1 m2) (hr' : -2 / 25 < P.interest) (ht : tOK m1 m2 tLo tHi = true)
    (hk : kapOK m1 m2 tLo tHi kLo kHi = true) (hh : hrOK m2 kHi hr pm = true)
    (hg : gOK m1 m2 kLo kHi gLo gHi = true) (hf : fcOK kLo gLo gHi hr fc = true)
    (hs : slackOK m1 m2 tHi = true) (hd : ceilLtDemand m2 fc[J-1]! = true) :
    P.olgCapital 59 nuR < olgDemand P.interest := by
  have hslack := slack_of_cell hM ht hs
  have hceil := P.olgCapital_le_cohortCeil (γ := 3) (by norm_num) hM.u hM.disc_pos hM.unb hslack
    59 nuR_nonneg
  have hfc := cohortCeil_le_fc hM ht hk hh hg hf
  obtain ⟨hpos, hlt⟩ := ceilLtDemand_unpack hd
  have hJ : J - 1 = 59 := rfl
  rw [hJ] at hlt
  have hsum : ∑ z, nuR z * P.cohortCeil 3 59 z ≤ ∑ z : Fin 7, nuR z * vI (fc[59]!)[(z : ℕ)]! :=
    Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hfc 59 (by decide) z) (nuR_nonneg z)
  have hs' := sum_nuR_vI (fun z => (fc[59]!)[z]!)
  beta_reduce at hs'
  rw [hs'] at hsum
  have hD := D_pos; have hRD := RD_pos
  have hposr : (0 : ℝ) < 25 * (m2 : ℝ) + 2 * ((RD : Int) : ℝ) := by exact_mod_cast hpos
  have hltr : ((sumI fun z => nuI z * (fc[59]!)[z]! : Int) : ℝ) * 16
        * (25 * (m2 : ℝ) + 2 * ((RD : Int) : ℝ))
      < 225 * ((RD : Int) : ℝ) * 3840 * (D : ℝ) := by
    rw [← DI_cast]; exact_mod_cast hlt
  have hkey : ((sumI fun z => nuI z * (fc[59]!)[z]! : Int) : ℝ) / (64 * D) / ((59 : ℕ) + 1 : ℝ)
      < 225 * ((RD : Int) : ℝ) / (16 * (25 * (m2 : ℝ) + 2 * ((RD : Int) : ℝ))) := by
    rw [show ((59 : ℕ) : ℝ) + 1 = 60 by norm_num, div_div,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    push_cast at hltr ⊢
    nlinarith [hltr]
  have hdem : olgDemand ((m2 : ℝ) / ((RD : Int) : ℝ)) ≤ olgDemand P.interest :=
    olgDemand_anti hr' (interest_le_of_rhi hM)
  rw [olgDemand_eq m2 hpos] at hdem
  calc P.olgCapital 59 nuR ≤ (∑ z, nuR z * P.cohortCeil 3 59 z) / ((59 : ℕ) + 1 : ℝ) := hceil
    _ ≤ ((sumI fun z => nuI z * (fc[59]!)[z]! : Int) : ℝ) / (64 * D) / ((59 : ℕ) + 1 : ℝ) :=
        div_le_div_of_nonneg_right hsum (by norm_num)
    _ < 225 * ((RD : Int) : ℝ) / (16 * (25 * (m2 : ℝ) + 2 * ((RD : Int) : ℝ))) := hkey
    _ ≤ olgDemand P.interest := hdem

/-- **Capital supply is below demand at every rate of a certified ceiling cell.** -/
theorem olgCapital_lt_demand_of_cell {P : IncomeFluctuation (Fin 7) 0 1000000} {m1 m2 : Int}
    (hM : InCell P m1 m2) (hr : -2 / 25 < P.interest) (hc : cellCeilOK m1 m2 = true) :
    P.olgCapital 59 nuR < olgDemand P.interest := by
  simp only [cellCeilOK, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨ht, hk⟩, hh⟩, hg⟩, hf⟩, hs⟩, hd⟩ := hc
  exact olgCapital_lt_demand_of_checks hM hr ht hk hh hg hf hs hd

/-! ### The floor side: reach, the clamped saving floor, and accumulated assets -/

theorem reachOK_unpack {m2 : Int} {rc : Array Int} (h : reachOK m2 rc = true) :
    rc.size = J + 1 ∧ rc[0]! = 0 ∧ (∀ j < J, rc[j]! * Rn m2 + yUp 6 * RD ≤ rc[j+1]! * RD)
      ∧ rc[J]! < CAPC * DI := by
  simp only [reachOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem yQ_six : (yQ 6 : ℝ) = (212480 : ℝ) / 72101 := by
  rw [← yN_div]; simp [yN]

theorem reach_le_rc {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 : Int} {rc : Array Int}
    (hM : InCell P m1 m2) (hR2 : 0 < Rn m2) (hrc : reachOK m2 rc = true) :
    ∀ j ≤ J, P.reach j ≤ vI rc[j]! := by
  obtain ⟨-, h0, hstep, -⟩ := reachOK_unpack hrc
  have hD := D_pos; have hRD := RD_pos
  have hRpos := P.interest_gt_neg_one
  intro j
  induction j with
  | zero => intro _; rw [h0]; simp [vI]
  | succ j ih =>
    intro hj
    rw [reach_succ]
    have h1 : (1 + P.interest) * P.reach j + P.maxIncome ≤ rI m2 * vI rc[j]! + vI (yUp 6) := by
      refine add_le_add (mul_le_mul hM.rhi (ih (by omega)) (P.reach_nonneg j) (rI_pos hR2).le) ?_
      rw [hM.maxInc, ← yQ_six]; exact le_yUp 6
    have hreal : ((rc[j]! : Int) : ℝ) * ((Rn m2 : Int) : ℝ) + ((yUp 6 : Int) : ℝ) * ((RD : Int) : ℝ)
        ≤ ((rc[j+1]! : Int) : ℝ) * ((RD : Int) : ℝ) := by exact_mod_cast hstep j (by omega)
    have h2 : rI m2 * vI rc[j]! + vI (yUp 6) ≤ vI rc[j+1]! := by
      refine le_of_sub_eq_div (n := ((rc[j+1]! : Int) : ℝ) * ((RD : Int) : ℝ)
          - (((rc[j]! : Int) : ℝ) * ((Rn m2 : Int) : ℝ) + ((yUp 6 : Int) : ℝ) * ((RD : Int) : ℝ)))
        (d := (D : ℝ) * ((RD : Int) : ℝ)) ?_ (by linarith) (by positivity)
      unfold vI rI; field_simp
    linarith

theorem reach_lt_cap {P : IncomeFluctuation (Fin 7) 0 1000000} {m1 m2 : Int} {rc : Array Int}
    (hM : InCell P m1 m2) (hR2 : 0 < Rn m2) (hrc : reachOK m2 rc = true) :
    P.reach (59 + 1) < 1000000 := by
  obtain ⟨-, -, -, hlt⟩ := reachOK_unpack hrc
  have h := reach_le_rc hM hR2 hrc J le_rfl
  have hcap : vI rc[J]! < 1000000 := by
    have hreal : ((rc[J]! : Int) : ℝ) < 1000000 * (D : ℝ) := by
      rw [← DI_cast, ← CAPC_cast]; exact_mod_cast hlt
    rw [vI, div_lt_iff₀ D_pos]; exact hreal
  exact lt_of_le_of_lt h hcap

theorem gridFOK_unpack {gF : Array Int} (h : gridFOK gF = true) :
    0 < gF.size ∧ gF[0]! = 0 ∧ ∀ i < gF.size - 1, gF[i]! < gF[i+1]! := by
  simp only [gridFOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem gridF_nonneg {gF : Array Int} (h : gridFOK gF = true) : ∀ i < gF.size, 0 ≤ gF[i]! := by
  obtain ⟨-, h0, hinc⟩ := gridFOK_unpack h
  intro i
  induction i with
  | zero => intro _; rw [h0]
  | succ i ih => intro hi; exact le_trans (ih (by omega)) (hinc i (by omega)).le

theorem lamOK_unpack {gF : Array Int} {m1 : Int} {kHi : Array Int} {hHi : Array (Array Int)}
    {lam : Array (Array (Array Int))} (h : lamOK gF m1 kHi hHi lam = true) :
    lam.size = J ∧ (∀ z < 7, ∀ i < gF.size, ((lam[0]!)[z]!)[i]! = gF[i]!)
      ∧ ∀ k < J - 1, ∀ z < 7, ∀ i < gF.size,
        idxBelow gF (max 0 (phiLo gF m1 kHi[k+1]! (hHi[k+1]!)[z]! z i)) < gF.size
        ∧ (idxBelow gF (max 0 (phiLo gF m1 kHi[k+1]! (hHi[k+1]!)[z]! z i)) = 0
            ∨ gF[idxBelow gF (max 0 (phiLo gF m1 kHi[k+1]! (hHi[k+1]!)[z]! z i))]! * DI * RD
              ≤ (DI - kHi[k+1]!) * (yDn z * RD + gF[i]! * Rn m1) - kHi[k+1]! * (hHi[k+1]!)[z]! * RD)
        ∧ ((lam[k+1]!)[z]!)[i]! * piDenI ≤ gF[i]! * piDenI
            + sumI (fun w => piI z w * ((lam[k]!)[w]!)[idxBelow gF (max 0 (phiLo gF m1 kHi[k+1]! (hHi[k+1]!)[z]! z i))]!) := by
  simp only [lamOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun k hk z hz i hi => ?_⟩
  obtain ⟨⟨a, b⟩, c⟩ := h3 k hk z hz i hi
  exact ⟨a, b, c⟩

/-- The clamped saving floor at a grid point is above the checker's quotient. -/
theorem assetFloor_ge {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 : Int}
    (hM : InCell P m1 m2) (hR1 : 0 < Rn m1) {k1 : ℕ} {z : Fin 7} {kHi1 hHi1 : Int}
    (hκhi : P.stageMPC 3 k1 ≤ vI kHi1) (hk1le : kHi1 ≤ DI) (hκnn : 0 ≤ kHi1)
    (hH : P.stageHumanWealth k1 z ≤ vI hHi1) (hHnn : 0 ≤ hHi1) {g : Int} (hg : 0 ≤ g) :
    (((DI - kHi1) * (yDn z * RD + g * Rn m1) - kHi1 * hHi1 * RD : Int) : ℝ) / (D * D * ((RD : Int) : ℝ))
      ≤ P.assetFloor 3 k1 z (vI g) := by
  have hD := D_pos; have hRD := RD_pos
  have hκle1 := P.stageMPC_le_one (γ := 3) (by norm_num) hM.disc_pos k1
  have hκpos := P.stageMPC_pos (γ := 3) (by norm_num) hM.disc_pos k1
  have hHnn' := P.stageHumanWealth_nonneg k1 z
  unfold assetFloor
  refine le_trans ?_ (le_max_right _ _)
  have h1 : (1 - vI kHi1) * (vI (yDn z) + rI m1 * vI g)
      ≤ (1 - P.stageMPC 3 k1) * (P.income z + (1 + P.interest) * vI g) := by
    have hk1 : 1 - vI kHi1 ≤ 1 - P.stageMPC 3 k1 := by linarith
    have hk1n : 0 ≤ 1 - vI kHi1 := by linarith [vI_le_one_of_le hk1le]
    refine mul_le_mul hk1 ?_ ?_ (by linarith)
    · rw [hM.income]
      exact add_le_add (yDn_le z) (mul_le_mul_of_nonneg_right hM.rlo (vI_nonneg hg))
    · exact add_nonneg (vI_nonneg (yDn_nonneg z)) (mul_nonneg (rI_pos hR1).le (vI_nonneg hg))
  have h2 : P.stageMPC 3 k1 * P.stageHumanWealth k1 z ≤ vI kHi1 * vI hHi1 :=
    mul_le_mul hκhi hH hHnn' (vI_nonneg hκnn)
  have heq : (((DI - kHi1) * (yDn z * RD + g * Rn m1) - kHi1 * hHi1 * RD : Int) : ℝ)
      / (D * D * ((RD : Int) : ℝ))
      = (1 - vI kHi1) * (vI (yDn z) + rI m1 * vI g) - vI kHi1 * vI hHi1 := by
    push_cast; rw [DI_cast]; unfold vI rI; field_simp
  rw [heq]; linarith

/-- **Accumulated assets are above the checker's grid bounds.** -/
theorem cohortFloorAt_ge_lam {cap : ℝ} {P : IncomeFluctuation (Fin 7) 0 cap} {m1 m2 tLo tHi : Int}
    {gF kLo kHi : Array Int} {hHi : Array (Array Int)} {lam : Array (Array (Array Int))}
    (hM : InCell P m1 m2) (ht : tOK m1 m2 tLo tHi = true) (hk : kapOK m1 m2 tLo tHi kLo kHi = true)
    (hh : hHiOK m1 hHi = true) (hg0 : gridFOK gF = true) (hl : lamOK gF m1 kHi hHi lam = true) :
    ∀ k < J, ∀ z : Fin 7, ∀ i < gF.size, vI ((lam[k]!)[(z : ℕ)]!)[i]! ≤ P.cohortFloorAt 3 k z (vI gF[i]!) := by
  obtain ⟨hR1, -, -, -, -, -⟩ := tOK_unpack ht
  have hκ := kap_bounds hM ht hk
  obtain ⟨-, -, -, -, hkstep⟩ := kapOK_unpack hk
  have hH := stageHumanWealth_le_hHi hM hR1 hh
  obtain ⟨-, h0, hstep⟩ := lamOK_unpack hl
  have hgnn := gridF_nonneg hg0
  have hg00 := (gridFOK_unpack hg0).2.1
  have hD := D_pos; have hRD := RD_pos; have hpd := piDen_pos
  intro k
  induction k with
  | zero => intro _ z i hi; rw [h0 (z : ℕ) z.isLt i hi]; simp [cohortFloorAt]
  | succ k ih =>
    intro hk1 z i hi
    obtain ⟨hjlt, hjcase, hlam⟩ := hstep k (by omega) (z : ℕ) z.isLt i hi
    generalize hj : idxBelow gF (max 0 (phiLo gF m1 kHi[k+1]! (hHi[k+1]!)[(z : ℕ)]! (z : ℕ) i)) = j
      at hjlt hjcase hlam
    obtain ⟨-, -, hκhi⟩ := hκ (k + 1) hk1
    obtain ⟨-, -, hk1pos, hk1le, -⟩ := hkstep k (by omega)
    have hHz := hH (k + 1) hk1 z
    have hHnn : 0 ≤ (hHi[k+1]!)[(z : ℕ)]! := by
      have := hHz; have h2 := P.stageHumanWealth_nonneg (k + 1) z
      by_contra hneg; push_neg at hneg
      have : vI (hHi[k+1]!)[(z : ℕ)]! < 0 := by
        rw [vI]; exact div_neg_of_neg_of_pos (by exact_mod_cast hneg) hD
      linarith
    -- the grid point below the saving floor
    have hΦ : vI gF[j]! ≤ P.assetFloor 3 (k + 1) z (vI gF[i]!) := by
      rcases hjcase with hj0 | hjle
      · rw [hj0, hg00, vI_zero]; exact P.assetFloor_nonneg 3 (k + 1) z _
      · refine le_trans ?_ (assetFloor_ge hM hR1 hκhi hk1le hk1pos.le hHz hHnn (hgnn i hi))
        have hreal : ((gF[j]! : Int) : ℝ) * (D : ℝ) * ((RD : Int) : ℝ)
            ≤ (((DI - kHi[k+1]!) * (yDn z * RD + gF[i]! * Rn m1)
              - kHi[k+1]! * (hHi[k+1]!)[(z : ℕ)]! * RD : Int) : ℝ) := by
          rw [← DI_cast]; exact_mod_cast hjle
        rw [vI, div_le_div_iff₀ hD (by positivity)]
        nlinarith [hreal]
    rw [cohortFloorAt_succ]
    have hsum : ∑ w : Fin 7, (piQ z w : ℝ) * vI ((lam[k]!)[(w : ℕ)]!)[j]!
        ≤ ∑ z', P.transitionMatrix z z' * P.cohortFloorAt 3 k z' (P.assetFloor 3 (k + 1) z (vI gF[i]!)) := by
      refine Finset.sum_le_sum fun w _ => ?_
      rw [hM.trans]
      refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast piQ_nonneg z w)
      exact le_trans (ih (by omega) w j hjlt)
        (P.cohortFloorAt_mono (by norm_num) hM.disc_pos k w hΦ)
    have hs := sum_piQ_vI z (fun w => ((lam[k]!)[w]!)[j]!)
    beta_reduce at hs
    rw [hs] at hsum
    have hreal : (((lam[k+1]!)[(z : ℕ)]!)[i]! : ℝ) * (piDen : ℝ)
        ≤ ((gF[i]! : Int) : ℝ) * (piDen : ℝ)
          + ((sumI fun w => piI z w * ((lam[k]!)[w]!)[j]! : Int) : ℝ) := by
      rw [← piDenI_cast]; exact_mod_cast hlam
    have hfin : vI ((lam[k+1]!)[(z : ℕ)]!)[i]! ≤ vI gF[i]!
        + ((sumI fun w => piI z w * ((lam[k]!)[w]!)[j]! : Int) : ℝ) / (piDen * D) := by
      refine le_of_sub_eq_div (n := ((gF[i]! : Int) : ℝ) * (piDen : ℝ)
          + ((sumI fun w => piI z w * ((lam[k]!)[w]!)[j]! : Int) : ℝ)
          - (((lam[k+1]!)[(z : ℕ)]!)[i]! : ℝ) * (piDen : ℝ))
        (d := (piDen : ℝ) * (D : ℝ)) ?_ (by linarith) (by positivity)
      unfold vI; field_simp
    linarith

theorem demandLtFloor_unpack {m1 : Int} {lam59 : Array (Array Int)} (h : demandLtFloor m1 lam59 = true) :
    0 < 25 * m1 + 2 * RD
      ∧ 225 * RD * 3840 * DI < sumI (fun z => nuI z * (lam59[z]!)[0]!) * 16 * (25 * m1 + 2 * RD) := by
  simp only [demandLtFloor, Bool.and_eq_true, decide_eq_true_eq] at h; exact h

/-- **Capital supply is above demand**, from the checks on abstract data. -/
theorem demand_lt_olgCapital_of_checks {P : IncomeFluctuation (Fin 7) 0 1000000}
    {m1 m2 tLo tHi : Int} {gF kLo kHi rc : Array Int} {hHi : Array (Array Int)}
    {lam : Array (Array (Array Int))} (hM : InCell P m1 m2) (ht : tOK m1 m2 tLo tHi = true)
    (hk : kapOK m1 m2 tLo tHi kLo kHi = true) (hh : hHiOK m1 hHi = true)
    (hrc : reachOK m2 rc = true) (hg0 : gridFOK gF = true) (hl : lamOK gF m1 kHi hHi lam = true)
    (hd : demandLtFloor m1 lam[J-1]! = true) :
    olgDemand P.interest < P.olgCapital 59 nuR := by
  obtain ⟨hR1, hm, -, -, -, -⟩ := tOK_unpack ht
  have hR2 : 0 < Rn m2 := by unfold Rn at hR1 ⊢; omega
  have hcap := reach_lt_cap hM hR2 hrc
  have hfloor := P.le_olgCapital_at (γ := 3) (by norm_num) hM.u hM.disc_pos hM.unb
    (P.reachRegions 59 hcap) 59 (by
      show (0 : ℝ) ∈ P.reachRegion 59 59
      rw [P.reachRegion_of_le le_rfl]; simp [reach]) nuR_nonneg
  have hlam := cohortFloorAt_ge_lam hM ht hk hh hg0 hl
  obtain ⟨hpos, hlt⟩ := demandLtFloor_unpack hd
  have hJ : J - 1 = 59 := rfl
  rw [hJ] at hlt
  have hg00 := (gridFOK_unpack hg0).2.1
  have hgF.size : 0 < gF.size := (gridFOK_unpack hg0).1
  have hsum : ∑ z : Fin 7, nuR z * vI ((lam[59]!)[(z : ℕ)]!)[0]!
      ≤ ∑ z, nuR z * P.cohortFloorAt 3 59 z 0 := by
    refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (nuR_nonneg z)
    have := hlam 59 (by decide) z 0 hgF.size
    rwa [hg00, vI_zero] at this
  have hs' := sum_nuR_vI (fun z => ((lam[59]!)[z]!)[0]!)
  beta_reduce at hs'
  rw [hs'] at hsum
  have hD := D_pos; have hRD := RD_pos
  have hposr : (0 : ℝ) < 25 * (m1 : ℝ) + 2 * ((RD : Int) : ℝ) := by exact_mod_cast hpos
  have hltr : 225 * ((RD : Int) : ℝ) * 3840 * (D : ℝ)
      < ((sumI fun z => nuI z * ((lam[59]!)[z]!)[0]! : Int) : ℝ) * 16
        * (25 * (m1 : ℝ) + 2 * ((RD : Int) : ℝ)) := by
    rw [← DI_cast]; exact_mod_cast hlt
  have hkey : 225 * ((RD : Int) : ℝ) / (16 * (25 * (m1 : ℝ) + 2 * ((RD : Int) : ℝ)))
      < ((sumI fun z => nuI z * ((lam[59]!)[z]!)[0]! : Int) : ℝ) / (64 * D) / ((59 : ℕ) + 1 : ℝ) := by
    rw [show ((59 : ℕ) : ℝ) + 1 = 60 by norm_num, div_div,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    push_cast at hltr ⊢
    nlinarith [hltr]
  have hm1 : -2 / 25 < (m1 : ℝ) / ((RD : Int) : ℝ) := by
    rw [lt_div_iff₀ hRD]; linarith
  have hdem : olgDemand P.interest ≤ olgDemand ((m1 : ℝ) / ((RD : Int) : ℝ)) :=
    olgDemand_anti hm1 (le_interest_of_rlo hM)
  rw [olgDemand_eq m1 hpos] at hdem
  calc olgDemand P.interest ≤ 225 * ((RD : Int) : ℝ) / (16 * (25 * (m1 : ℝ) + 2 * ((RD : Int) : ℝ))) := hdem
    _ < ((sumI fun z => nuI z * ((lam[59]!)[z]!)[0]! : Int) : ℝ) / (64 * D) / ((59 : ℕ) + 1 : ℝ) := hkey
    _ ≤ (∑ z, nuR z * P.cohortFloorAt 3 59 z 0) / ((59 : ℕ) + 1 : ℝ) :=
        div_le_div_of_nonneg_right hsum (by norm_num)
    _ ≤ P.olgCapital 59 nuR := hfloor

/-- **Capital supply is above demand at every rate of a certified floor cell.** -/
theorem demand_lt_olgCapital_of_cell {P : IncomeFluctuation (Fin 7) 0 1000000} {m1 m2 : Int}
    (hM : InCell P m1 m2) (hc : cellFloorOK m1 m2 = true) :
    olgDemand P.interest < P.olgCapital 59 nuR := by
  simp only [cellFloorOK, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨ht, hk⟩, hh⟩, hrc⟩, hg0⟩, hl⟩, hd⟩ := hc
  exact demand_lt_olgCapital_of_checks hM ht hk hh hrc hg0 hl hd

end LeanEconomics.EnclCert
