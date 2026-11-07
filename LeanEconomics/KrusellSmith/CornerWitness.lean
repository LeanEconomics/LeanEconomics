/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CornerPrimitives
import LeanEconomics.KrusellSmith.CRRAContraction

/-!
# A concrete corner economy

Milestone C4b of `CORNER_PLAN.md`: an explicit Krusell–Smith economy with heterogeneous households
in which `(z, K)` is a sufficient state.

* Two aggregate states (`Bool`, `true` good) with i.i.d. probabilities `1/2`, two employment states
  (`true` employed, efficiency `44`; `false` unemployed, efficiency `2`), cap `ā = 1`, `β = 9/10`,
  **log utility** (`γ = 1`).
* Clamped Cobb–Douglas with share `1/2`, no depreciation, TFP `1`, capital box `[1/4, 1]`, labour
  clamped at `1`: gross returns in `[3/2, 2]`, wages in `[1/4, 1/2]`.
* KS employment design: employed shares `3/5` (bad) and `13/20` (good), with job-loss
  probabilities `16/25, 167/300, 193/325, 168/325` and job-finding probability `24/25`.

**`cornerWitness`**: households who were employed hold `ā`, the others nothing; this is a
sequence-state equilibrium, `(z, K)` is sufficient, and a recursive equilibrium on `(z, K)`
represents it. Capital is `3/5` after a bad shock and `13/20` after a good one
(`capAt_witness`) — inside the capital box, so prices respond to capital. Labour is clamped, so
prices do not respond to labour.
-/

open MeasureTheory Set

namespace LeanEconomics

namespace KrusellSmith

namespace CornerWitness

/-- Job-loss probabilities, by yesterday's and today's aggregate shock. -/
noncomputable def peu : Bool → Bool → ℝ
  | false, false => 16 / 25
  | false, true => 167 / 300
  | true, false => 193 / 325
  | true, true => 168 / 325

/-- Employment transitions. -/
noncomputable def pIdio (z z' : Bool) (e e' : Bool) : ℝ :=
  if e then (if e' then 1 - peu z z' else peu z z') else (if e' then 24 / 25 else 1 / 25)

/-- The environment. -/
noncomputable def env : KSEnvironment Bool Bool where
  aggProb _ _ := 1 / 2
  aggProb_nonneg _ _ := by norm_num
  aggProb_sum _ := by norm_num [Fintype.sum_bool]
  idioProb := pIdio
  idioProb_nonneg z z' e e' := by
    cases z <;> cases z' <;> cases e <;> cases e' <;> norm_num [pIdio, peu]
  idioProb_sum z z' e := by
    cases z <;> cases z' <;> cases e <;> norm_num [pIdio, peu, Fintype.sum_bool]
  efficiency e := if e then 44 else 2
  effLo := 2
  effHi := 44
  effLo_pos := by norm_num
  effLo_le e := by cases e <;> norm_num
  le_effHi e := by cases e <;> norm_num
  assetCap := 1
  assetCap_pos := by norm_num
  discount := 9 / 10
  discount_pos := by norm_num
  discount_lt_one := by norm_num

/-- The technology. -/
noncomputable def tech : CobbDouglas Bool where
  tfp _ := 1
  tfpLo := 1
  tfpHi := 1
  tfpLo_pos := by norm_num
  tfpLo_le _ := le_rfl
  tfp_le _ := le_rfl
  share := 1 / 2
  share_pos := by norm_num
  share_lt_one := by norm_num
  depreciation := 0
  depreciation_nonneg := le_rfl
  depreciation_le_one := by norm_num
  capLo := 1 / 4
  capHi := 1
  capLo_pos := by norm_num
  capLo_le := by norm_num
  labLo := 1
  labHi := 1
  labLo_pos := by norm_num
  labLo_le := le_rfl

/-- The model: log utility (`γ = 1`). -/
noncomputable abbrev model : KSModel Bool Bool := crraModel env tech one_pos

/-- Savers are the employed. -/
def saver (e : Bool) : Prop := e = true

instance : DecidablePred saver := fun e => inferInstanceAs (Decidable (e = true))

/-- Employed shares. -/
noncomputable def share (z : Bool) : ℝ := if z then 13 / 20 else 3 / 5

/-- **The employment design.** -/
noncomputable def design : EmploymentDesign model.idioProb where
  m z e := if e then share z else 1 - share z
  m_nonneg z e := by cases z <;> cases e <;> norm_num [share]
  sum_m z := by cases z <;> norm_num [share, Fintype.sum_bool]
  consistent z z' e' := by
    change ∑ e, (if e then share z else 1 - share z) * pIdio z z' e e'
      = if e' then share z' else 1 - share z'
    cases z <;> cases z' <;> cases e' <;> norm_num [share, pIdio, peu, Fintype.sum_bool]
  ε := 1 / 25
  ε_pos := by norm_num
  minor z z' e e' := by
    change (1 / 25 : ℝ) ≤ pIdio z z' e e'
    cases z <;> cases z' <;> cases e <;> cases e' <;> norm_num [pIdio, peu]

theorem quarter_rpow_half : (1 / 4 : ℝ) ^ (1 / 2 : ℝ) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)]
  norm_num

theorem quarter_rpow_half_sub_one : (1 / 4 : ℝ) ^ ((1 / 2 : ℝ) - 1) = 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **Price bounds.** -/
theorem return_bounds (z : Bool) (K L : ℝ) :
    3 / 2 ≤ model.grossReturn z K L ∧ model.grossReturn z K L ≤ 2 := by
  have hlo : tech.returnLo = 3 / 2 := by
    change 1 - 0 + 1 / 2 * 1 * (1 : ℝ) ^ ((1 / 2 : ℝ) - 1) * (1 : ℝ) ^ (1 - (1 / 2 : ℝ)) = 3 / 2
    rw [Real.one_rpow, Real.one_rpow]
    norm_num
  have hhi : tech.returnBound = 2 := by
    change 1 - 0 + 1 / 2 * 1 * (1 / 4 : ℝ) ^ ((1 / 2 : ℝ) - 1) * (1 : ℝ) ^ (1 - (1 / 2 : ℝ)) = 2
    rw [quarter_rpow_half_sub_one, Real.one_rpow]
    norm_num
  exact ⟨hlo ▸ tech.returnLo_le_grossReturn z K L, hhi ▸ tech.grossReturn_le z K L⟩

theorem wage_bounds (z : Bool) (K L : ℝ) :
    1 / 4 ≤ model.wage z K L ∧ model.wage z K L ≤ 1 / 2 := by
  have hlo : tech.wageLo = 1 / 4 := by
    change (1 - 1 / 2) * 1 * (1 / 4 : ℝ) ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 4
    rw [quarter_rpow_half, Real.one_rpow]
    norm_num
  have hhi : tech.wageBound = 1 / 2 := by
    change (1 - 1 / 2) * 1 * (1 : ℝ) ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2
    rw [Real.one_rpow, Real.one_rpow]
    norm_num
  exact ⟨hlo ▸ tech.wageLo_le_wage z K L, hhi ▸ tech.wage_le z K L⟩

/-- The consumption floor is positive and at most `1/16`. -/
theorem floor_le : model.consFloor ≤ 1 / 16 := by
  have h1 : crraFloorLevel env tech one_pos ≤ (crraEconomy env tech one_pos).incomeFloor / 4 :=
    min_le_right _ _
  have h2 : (crraEconomy env tech one_pos).incomeFloor = tech.wageLo * 2 := rfl
  have h3 : tech.wageLo = 1 / 4 := by
    change (1 - 1 / 2) * 1 * (1 / 4 : ℝ) ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 4
    rw [quarter_rpow_half, Real.one_rpow]
    norm_num
  change crraFloorLevel env tech one_pos / 2 ≤ 1 / 16
  rw [h2, h3] at h1
  linarith

/-- Log marginal utility. -/
theorem du_eq (c : ℝ) : (crraSmoothUtility env tech one_pos).du c = c⁻¹ :=
  Real.rpow_neg_one c

theorem cornerSave_eq (e : Bool) :
    (KSModel.cornerSave model saver e : ℝ) = if e then 1 else 0 := by
  rw [KSModel.cornerSave_val]
  cases e
  · simp [saver]
  · simp [saver]
    rfl

theorem eff_eq (e : Bool) : model.efficiency e = if e then 44 else 2 := rfl

theorem disc_eq : model.discount = 9 / 10 := rfl

theorem agg_eq (z z' : Bool) : model.aggProb z z' = 1 / 2 := rfl

theorem idio_eq (z z' e e' : Bool) : model.idioProb z z' e e' = pIdio z z' e e' := rfl

theorem cap_eq : model.assetCap = 1 := rfl

theorem cornerConditions :
    KSModel.CornerConditions design saver (crraSmoothUtility env tech one_pos) := by
  refine KSModel.cornerConditions_of_bounds (Rlo := 3 / 2) (Rhi := 2) (wlo := 1 / 4) (whi := 1 / 2)
    (by norm_num) return_bounds wage_bounds ?_ design ?_ ?_
  · intro e
    have := floor_le
    rw [cornerSave_eq, eff_eq]
    cases e <;> norm_num <;> linarith
  · intro z e he
    change e = true at he
    subst he
    simp only [du_eq, cornerSave_eq, eff_eq, disc_eq, agg_eq, idio_eq, cap_eq,
      Fintype.sum_prod_type, Fintype.sum_bool]
    cases z <;> norm_num [pIdio, peu]
  · intro z e he
    have he' : e = false := by
      change ¬ e = true at he
      simpa using he
    subst he'
    simp only [du_eq, cornerSave_eq, eff_eq, disc_eq, agg_eq, idio_eq, cap_eq,
      Fintype.sum_prod_type, Fintype.sum_bool]
    cases z <;> norm_num [pIdio, peu]

/-- **Capital in the corner equilibrium**: `3/5` after a bad shock, `13/20` after a good one —
inside the capital box `[1/4, 1]`. -/
theorem capAt_witness (ω : History Bool) :
    KSModel.capAt (KSModel.μc design saver) ω = if ω 1 then 13 / 20 else 3 / 5 := by
  rw [KSModel.capAt_μc]
  change (1 : ℝ) * ∑ e, (if saver e then (if e then share (ω 1) else 1 - share (ω 1)) else 0) = _
  simp only [Fintype.sum_bool, saver, share]
  cases ω 1 <;> norm_num

/-- **A Krusell–Smith equilibrium with heterogeneous households in which `(z, K)` is a
sufficient state**: the corner candidate is a sequence-state equilibrium of the log-utility,
clamped Cobb–Douglas economy above, it satisfies `KSufficient`, and a recursive equilibrium on
`(z, K)` represents it. -/
theorem cornerWitness :
    model.IsSeqStateEquilibrium (KSModel.μc design saver) ∧
      KSModel.KSufficient (KSModel.μc design saver) ∧
      ∃ R : model.AggStateRecursiveEquilibrium, R.Represents (KSModel.μc design saver) :=
  ⟨KSModel.isSeqStateEquilibrium_μc cornerConditions, KSModel.kSufficient_μc design saver,
    KSModel.exists_represents_μc cornerConditions⟩

end CornerWitness

end KrusellSmith

end LeanEconomics
