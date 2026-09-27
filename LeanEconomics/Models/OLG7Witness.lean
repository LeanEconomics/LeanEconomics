/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.LifeCycle
import EnclCert.Check

/-!
# The rational life-cycle calibration, as a Lean object

The calibration of the enclosure certificate (`WriteUps/WriteUpOLG/numerics/rational/encl.py`):
seven earnings states on a Rouwenhorst chain with persistence `9/10`, whose transition
probabilities are rational and whose invariant law is binomial; rational earnings levels
normalised to mean one; `β = 24/25`; relative risk aversion `3`; the lower rate `r₁ = 1/25`
as the base economy, the higher one supplied by `withRate`. The asset cap is `2000`, above the
crude reach of a sixty-period life at either rate and large enough for the impatience test that
keeps the cap slack at every stage of that life.

All probabilities and incomes are stored as rationals (`piQ`, `yQ`, `nuQ`) so that the certificate
can compute with them exactly, and cast to `ℝ` for the economy.
-/

open Set

namespace LeanEconomics

/-- The Rouwenhorst transition matrix at `ρ = 9/10`, seven states: the certificate's natural
numerators over their common denominator. -/
def piQ (z z' : Fin 7) : ℚ := (EnclCert.piNum z z' : ℚ) / EnclCert.piDen

/-- Earnings levels, normalised to mean one under the invariant law. -/
def yQ (z : Fin 7) : ℚ := ((EnclCert.yN z).1 : ℚ) / (EnclCert.yN z).2

/-- The invariant law of the chain: binomial. -/
def nuQ (z : Fin 7) : ℚ := ((EnclCert.nuN z).1 : ℚ) / (EnclCert.nuN z).2

theorem piNum_row_sum (z : Fin 7) :
    EnclCert.piNum z ((0 : Fin 7) : ℕ) + EnclCert.piNum z ((1 : Fin 7) : ℕ)
      + EnclCert.piNum z ((2 : Fin 7) : ℕ) + EnclCert.piNum z ((3 : Fin 7) : ℕ)
      + EnclCert.piNum z ((4 : Fin 7) : ℕ) + EnclCert.piNum z ((5 : Fin 7) : ℕ)
      + EnclCert.piNum z ((6 : Fin 7) : ℕ) = EnclCert.piDen := by
  fin_cases z <;> decide

theorem piQ_row_sum (z : Fin 7) : ∑ z', piQ z z' = 1 := by
  simp only [Fin.sum_univ_seven, piQ]
  rw [← add_div, ← add_div, ← add_div, ← add_div, ← add_div, ← add_div,
    div_eq_one_iff_eq (by norm_num [EnclCert.piDen])]
  exact_mod_cast piNum_row_sum z

theorem piQ_nonneg (z z' : Fin 7) : 0 ≤ piQ z z' := by
  unfold piQ; positivity

theorem nuN_invariant (z' : Fin 7) :
    (EnclCert.nuN ((0 : Fin 7) : ℕ)).1 * EnclCert.piNum ((0 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((1 : Fin 7) : ℕ)).1 * EnclCert.piNum ((1 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((2 : Fin 7) : ℕ)).1 * EnclCert.piNum ((2 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((3 : Fin 7) : ℕ)).1 * EnclCert.piNum ((3 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((4 : Fin 7) : ℕ)).1 * EnclCert.piNum ((4 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((5 : Fin 7) : ℕ)).1 * EnclCert.piNum ((5 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((6 : Fin 7) : ℕ)).1 * EnclCert.piNum ((6 : Fin 7) : ℕ) z'
      = EnclCert.piDen * (EnclCert.nuN z').1 := by
  fin_cases z' <;> decide

theorem nuN_den (z : Fin 7) : (EnclCert.nuN z).2 = 64 := by
  fin_cases z <;> rfl

theorem nuQ_invariant (z' : Fin 7) : ∑ z, nuQ z * piQ z z' = nuQ z' := by
  simp only [Fin.sum_univ_seven, nuQ, piQ, nuN_den, div_mul_div_comm]
  rw [← add_div, ← add_div, ← add_div, ← add_div, ← add_div, ← add_div,
    div_eq_div_iff (by norm_num [EnclCert.piDen]) (by norm_num)]
  have hcast : ((EnclCert.nuN ((0 : Fin 7) : ℕ)).1 * EnclCert.piNum ((0 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((1 : Fin 7) : ℕ)).1 * EnclCert.piNum ((1 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((2 : Fin 7) : ℕ)).1 * EnclCert.piNum ((2 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((3 : Fin 7) : ℕ)).1 * EnclCert.piNum ((3 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((4 : Fin 7) : ℕ)).1 * EnclCert.piNum ((4 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((5 : Fin 7) : ℕ)).1 * EnclCert.piNum ((5 : Fin 7) : ℕ) z'
      + (EnclCert.nuN ((6 : Fin 7) : ℕ)).1 * EnclCert.piNum ((6 : Fin 7) : ℕ) z' : ℚ)
      = (EnclCert.piDen * (EnclCert.nuN z').1 : ℕ) := by exact_mod_cast nuN_invariant z'
  push_cast at hcast ⊢
  linear_combination (64 : ℚ) * hcast

theorem nuQ_nonneg (z : Fin 7) : 0 ≤ nuQ z := by
  unfold nuQ; positivity

theorem yQ_min (z : Fin 7) : (19264 : ℚ) / 72101 ≤ yQ z := by
  fin_cases z <;> norm_num [yQ, EnclCert.yN]

theorem yQ_max (z : Fin 7) : yQ z ≤ (212480 : ℚ) / 72101 := by
  fin_cases z <;> norm_num [yQ, EnclCert.yN]

/-- **The life-cycle economy of the certificate**, at the lower rate `1/25`. -/
noncomputable def olg7 : IncomeFluctuation (Fin 7) 0 2000 where
  income z := (yQ z : ℝ)
  transitionMatrix z z' := (piQ z z' : ℝ)
  interest := 1 / 25
  discount := 24 / 25
  u := crraUtility 3
  minIncome := (19264 : ℝ) / 72101
  maxIncome := (212480 : ℝ) / 72101
  minIncome_pos := by norm_num
  minIncome_le z := by
    have h := yQ_min z
    rw [show ((19264 : ℝ) / 72101) = ((19264 / 72101 : ℚ) : ℝ) by norm_num]
    exact Rat.cast_le.mpr h
  le_maxIncome z := by
    have h := yQ_max z
    rw [show ((212480 : ℝ) / 72101) = ((212480 / 72101 : ℚ) : ℝ) by norm_num]
    exact Rat.cast_le.mpr h
  transitionMatrix_nonneg z z' := by exact_mod_cast piQ_nonneg z z'
  transitionMatrix_sum z := by exact_mod_cast piQ_row_sum z
  interest_gt_neg_one := by norm_num
  assetFloor_le_assetCap := by norm_num
  assetCap_nonneg := by norm_num
  minConsumption_pos := by norm_num
  minConsumption_le_floor := le_rfl
  discount_lt_one := by norm_num
  dom := Ioi 0
  Ioi_subset_dom := subset_rfl
  dom_subset_Ici := Ioi_subset_Ici_self
  continuousOn_u_dom := continuousOn_crraUtility 3
  monotoneOn_u_dom := monotoneOn_crraUtility 3
  strictConcaveOn_u_dom := strictConcaveOn_crraUtility (by norm_num)
  continuousOn_extendDom :=
    continuousOn_extendDom_Ioi (continuousOn_crraUtility 3)
      (tendsto_atBot_crraUtility (by norm_num))

@[simp] theorem olg7_u : olg7.u = crraUtility 3 := rfl
@[simp] theorem olg7_income (z : Fin 7) : olg7.income z = (yQ z : ℝ) := rfl
@[simp] theorem olg7_transitionMatrix (z z' : Fin 7) :
    olg7.transitionMatrix z z' = (piQ z z' : ℝ) := rfl
@[simp] theorem olg7_interest : olg7.interest = 1 / 25 := rfl
@[simp] theorem olg7_discount : (olg7.discount : ℝ) = 24 / 25 := rfl
@[simp] theorem olg7_minIncome : olg7.minIncome = (19264 : ℝ) / 72101 := rfl
@[simp] theorem olg7_maxIncome : olg7.maxIncome = (212480 : ℝ) / 72101 := rfl

theorem olg7_unbounded : olg7.Unbounded := rfl

/-- The higher rate `23/500 = 4.6%` is admissible. -/
theorem olg7_rateOK_high : olg7.RateOK (23 / 500) :=
  IncomeFluctuation.rateOK_of_floor_zero (by norm_num)

theorem olg7_rateOK_low : olg7.RateOK (1 / 25) :=
  IncomeFluctuation.rateOK_of_floor_zero (by norm_num)

end LeanEconomics
