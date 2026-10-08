/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.OLG7Witness
import LeanEconomics.Models.IncomeFluctuationRate

/-!
# The rational life-cycle calibration with a cap of one million

`olg7` of `OLG7Witness` carries the cap `2000`, which is enough for the pairwise certificate at
`4%` and `4.6%` but not for the floor on capital supply at high rates, whose hypothesis is that a
lifetime of feasible saving stays under the cap: at `20%` that reach is about `834,000`. The
economy here is the same calibration with cap `10⁶`, at a rate supplied by `withRate`.
-/

open Set

namespace LeanEconomics

/-- **The life-cycle economy of the certificate with cap `10⁶`**, at the base rate `1/25`. -/
noncomputable def olg7cap : IncomeFluctuation (Fin 7) 0 1000000 where
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

@[simp] theorem olg7cap_u : olg7cap.u = crraUtility 3 := rfl
@[simp] theorem olg7cap_income (z : Fin 7) : olg7cap.income z = (yQ z : ℝ) := rfl
@[simp] theorem olg7cap_transitionMatrix (z z' : Fin 7) :
    olg7cap.transitionMatrix z z' = (piQ z z' : ℝ) := rfl
@[simp] theorem olg7cap_discount : (olg7cap.discount : ℝ) = 24 / 25 := rfl
@[simp] theorem olg7cap_minIncome : olg7cap.minIncome = (19264 : ℝ) / 72101 := rfl
@[simp] theorem olg7cap_maxIncome : olg7cap.maxIncome = (212480 : ℝ) / 72101 := rfl

theorem olg7cap_unbounded : olg7cap.Unbounded := rfl

/-- The economy at the rate `r`, for any `r > -1`. -/
noncomputable def olg7At (r : ℝ) (hr : 0 < 1 + r) : IncomeFluctuation (Fin 7) 0 1000000 :=
  olg7cap.withRate r (IncomeFluctuation.rateOK_of_floor_zero hr)

@[simp] theorem olg7At_interest (r : ℝ) (hr : 0 < 1 + r) : (olg7At r hr).interest = r := rfl
@[simp] theorem olg7At_income (r : ℝ) (hr : 0 < 1 + r) (z : Fin 7) :
    (olg7At r hr).income z = (yQ z : ℝ) := rfl
@[simp] theorem olg7At_transitionMatrix (r : ℝ) (hr : 0 < 1 + r) (z z' : Fin 7) :
    (olg7At r hr).transitionMatrix z z' = (piQ z z' : ℝ) := rfl
@[simp] theorem olg7At_discount (r : ℝ) (hr : 0 < 1 + r) :
    ((olg7At r hr).discount : ℝ) = 24 / 25 := rfl
@[simp] theorem olg7At_u (r : ℝ) (hr : 0 < 1 + r) : (olg7At r hr).u = crraUtility 3 := rfl
@[simp] theorem olg7At_minIncome (r : ℝ) (hr : 0 < 1 + r) :
    (olg7At r hr).minIncome = (19264 : ℝ) / 72101 := rfl
@[simp] theorem olg7At_maxIncome (r : ℝ) (hr : 0 < 1 + r) :
    (olg7At r hr).maxIncome = (212480 : ℝ) / 72101 := rfl
theorem olg7At_unbounded (r : ℝ) (hr : 0 < 1 + r) : (olg7At r hr).Unbounded := rfl

end LeanEconomics
