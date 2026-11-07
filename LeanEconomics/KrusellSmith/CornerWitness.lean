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
  (`true` employed, efficiency `4`; `false` unemployed, efficiency `1/2`), cap `ā = 1/4`,
  `β = 1/2`, **log utility** (`γ = 1`).
* Cobb–Douglas with capital share `1/4`, full depreciation, TFP `1`, capital box
  `[(37/60)^4, (13/20)^4]` and labour box `[(19/15)^4, (13/10)^4]` (fourth powers, so the powers
  `1/4`, `3/4` are exact).
* KS employment design: employed shares `3/5` (bad) and `13/20` (good), with job-loss
  probabilities `16/25, 167/300, 193/325, 168/325` and job-finding probability `24/25`.

**`cornerWitness`**: households who were employed hold `ā`, the others nothing; this is a
sequence-state equilibrium, `(z, K)` is sufficient, and a recursive equilibrium on `(z, K)`
represents it. Capital is `3/20` after a bad shock and `13/80` after a good one
(`capAt_witness`); labour is `13/5` or `111/40`. Both lie inside the clamping boxes at every node
of the equilibrium price tree (`seqPrices_mem_box`), so **prices are the true Cobb–Douglas marginal
products** of capital and labour.
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
  efficiency e := if e then 4 else 1 / 2
  effLo := 1 / 2
  effHi := 4
  effLo_pos := by norm_num
  effLo_le e := by cases e <;> norm_num
  le_effHi e := by cases e <;> norm_num
  assetCap := 1 / 4
  assetCap_pos := by norm_num
  discount := 1 / 2
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
  share := 1 / 4
  share_pos := by norm_num
  share_lt_one := by norm_num
  depreciation := 1
  depreciation_nonneg := by norm_num
  depreciation_le_one := le_rfl
  capLo := (37 / 60) ^ 4
  capHi := (13 / 20) ^ 4
  capLo_pos := by norm_num
  capLo_le := by norm_num
  labLo := (19 / 15) ^ 4
  labHi := (13 / 10) ^ 4
  labLo_pos := by norm_num
  labLo_le := by norm_num

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

theorem pow4_rpow (x : ℝ) (hx : 0 ≤ x) (r : ℝ) : (x ^ (4 : ℕ)) ^ r = x ^ (4 * r) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- Exact powers at the box corners. -/
theorem rpow_neg_three_quarters (x : ℝ) (hx : 0 < x) :
    (x ^ (4 : ℕ)) ^ ((1 / 4 : ℝ) - 1) = (x ^ 3)⁻¹ := by
  rw [pow4_rpow x hx.le, show (4 : ℝ) * ((1 / 4 : ℝ) - 1) = -((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg hx.le, Real.rpow_natCast]

theorem rpow_three_quarters (x : ℝ) (hx : 0 < x) : (x ^ (4 : ℕ)) ^ (1 - (1 / 4 : ℝ)) = x ^ 3 := by
  rw [pow4_rpow x hx.le, show (4 : ℝ) * (1 - (1 / 4 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

theorem rpow_quarter (x : ℝ) (hx : 0 < x) : (x ^ (4 : ℕ)) ^ (1 / 4 : ℝ) = x := by
  rw [pow4_rpow x hx.le, show (4 : ℝ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one]

theorem rpow_neg_quarter (x : ℝ) (hx : 0 < x) : (x ^ (4 : ℕ)) ^ (-(1 / 4 : ℝ)) = x⁻¹ := by
  rw [pow4_rpow x hx.le, show (4 : ℝ) * -(1 / 4 : ℝ) = -1 by norm_num, Real.rpow_neg_one]

/-- The lowest gross return. -/
noncomputable def Rlo : ℝ := 1 / 4 * (20 / 13) ^ 3 * (19 / 15) ^ 3

/-- The highest gross return. -/
noncomputable def Rhi : ℝ := 1 / 4 * (60 / 37) ^ 3 * (13 / 10) ^ 3

/-- The lowest wage. -/
noncomputable def wlo : ℝ := 3 / 4 * (37 / 60) * (10 / 13)

/-- The highest wage. -/
noncomputable def whi : ℝ := 3 / 4 * (13 / 20) * (15 / 19)

theorem wageLo_eq : tech.wageLo = wlo := by
  change (1 - 1 / 4) * 1 * ((37 / 60 : ℝ) ^ 4) ^ (1 / 4 : ℝ) * ((13 / 10 : ℝ) ^ 4) ^ (-(1 / 4 : ℝ))
    = wlo
  rw [rpow_quarter _ (by norm_num), rpow_neg_quarter _ (by norm_num), wlo]
  norm_num

/-- **Price bounds.** -/
theorem return_bounds (z : Bool) (K L : ℝ) :
    Rlo ≤ model.grossReturn z K L ∧ model.grossReturn z K L ≤ Rhi := by
  have hlo : tech.returnLo = Rlo := by
    change 1 - 1 + 1 / 4 * 1 * ((13 / 20 : ℝ) ^ 4) ^ ((1 / 4 : ℝ) - 1)
      * ((19 / 15 : ℝ) ^ 4) ^ (1 - (1 / 4 : ℝ)) = Rlo
    rw [rpow_neg_three_quarters _ (by norm_num), rpow_three_quarters _ (by norm_num), Rlo]
    norm_num
  have hhi : tech.returnBound = Rhi := by
    change 1 - 1 + 1 / 4 * 1 * ((37 / 60 : ℝ) ^ 4) ^ ((1 / 4 : ℝ) - 1)
      * ((13 / 10 : ℝ) ^ 4) ^ (1 - (1 / 4 : ℝ)) = Rhi
    rw [rpow_neg_three_quarters _ (by norm_num), rpow_three_quarters _ (by norm_num), Rhi]
    norm_num
  exact ⟨hlo ▸ tech.returnLo_le_grossReturn z K L, hhi ▸ tech.grossReturn_le z K L⟩

theorem wage_bounds (z : Bool) (K L : ℝ) :
    wlo ≤ model.wage z K L ∧ model.wage z K L ≤ whi := by
  have hhi : tech.wageBound = whi := by
    change (1 - 1 / 4) * 1 * ((13 / 20 : ℝ) ^ 4) ^ (1 / 4 : ℝ)
      * ((19 / 15 : ℝ) ^ 4) ^ (-(1 / 4 : ℝ)) = whi
    rw [rpow_quarter _ (by norm_num), rpow_neg_quarter _ (by norm_num), whi]
    norm_num
  exact ⟨wageLo_eq ▸ tech.wageLo_le_wage z K L, hhi ▸ tech.wage_le z K L⟩

/-- The consumption floor is at most `wlo / 16`. -/
theorem floor_le : model.consFloor ≤ wlo / 16 := by
  have h1 : crraFloorLevel env tech one_pos ≤ (crraEconomy env tech one_pos).incomeFloor / 4 :=
    min_le_right _ _
  have h2 : (crraEconomy env tech one_pos).incomeFloor = tech.wageLo * (1 / 2) := rfl
  change crraFloorLevel env tech one_pos / 2 ≤ wlo / 16
  rw [h2, wageLo_eq] at h1
  linarith

/-- Log marginal utility. -/
theorem du_eq (c : ℝ) : (crraSmoothUtility env tech one_pos).du c = c⁻¹ :=
  Real.rpow_neg_one c

theorem cornerSave_eq (e : Bool) :
    (KSModel.cornerSave model saver e : ℝ) = if e then 1 / 4 else 0 := by
  rw [KSModel.cornerSave_val]
  cases e
  · simp [saver]
  · simp [saver]
    change (1 / 4 : ℝ) = 4⁻¹
    norm_num

theorem eff_eq (e : Bool) : model.efficiency e = if e then 4 else 1 / 2 := rfl

theorem disc_eq : model.discount = 1 / 2 := rfl

theorem agg_eq (z z' : Bool) : model.aggProb z z' = 1 / 2 := rfl

theorem idio_eq (z z' e e' : Bool) : model.idioProb z z' e e' = pIdio z z' e e' := rfl

theorem cap_eq : model.assetCap = 1 / 4 := rfl

/-- (Feas) for the witness. -/
theorem feas_w (e : Bool) :
    model.consFloor + (KSModel.cornerSave model saver e : ℝ) < wlo * model.efficiency e := by
  have := floor_le
  rw [cornerSave_eq, eff_eq]
  cases e <;> norm_num [wlo] at this ⊢ <;> linarith

/-- (Emp) for the witness. -/
theorem emp_w (z e : Bool) (he : saver e) :
    (crraSmoothUtility env tech one_pos).du (wlo * model.efficiency e
        - KSModel.cornerSave model saver e)
      ≤ model.discount * ∑ ze : Bool × Bool, model.aggProb z ze.1 * model.idioProb z ze.1 e ze.2
        * Rlo * (crraSmoothUtility env tech one_pos).du (Rhi * model.assetCap
          + whi * model.efficiency ze.2 - KSModel.cornerSave model saver ze.2) := by
  change e = true at he
  subst he
  simp only [du_eq, cornerSave_eq, eff_eq, disc_eq, agg_eq, idio_eq, cap_eq,
    Fintype.sum_prod_type, Fintype.sum_bool]
  cases z <;> norm_num [pIdio, peu, Rlo, Rhi, wlo, whi]

/-- (Unemp) for the witness. -/
theorem unemp_w (z e : Bool) (he : ¬ saver e) :
    model.discount * ∑ ze : Bool × Bool, model.aggProb z ze.1 * model.idioProb z ze.1 e ze.2
        * Rhi * (crraSmoothUtility env tech one_pos).du (wlo * model.efficiency ze.2
          - KSModel.cornerSave model saver ze.2)
      ≤ (crraSmoothUtility env tech one_pos).du (Rhi * model.assetCap
        + whi * model.efficiency e) := by
  have he' : e = false := by
    change ¬ e = true at he
    simpa using he
  subst he'
  simp only [du_eq, cornerSave_eq, eff_eq, disc_eq, agg_eq, idio_eq, cap_eq,
    Fintype.sum_prod_type, Fintype.sum_bool]
  cases z <;> norm_num [pIdio, peu, Rlo, Rhi, wlo, whi]

theorem Rlo_nonneg : 0 ≤ Rlo := by norm_num [Rlo]

theorem cornerConditions :
    KSModel.CornerConditions design saver (crraSmoothUtility env tech one_pos) :=
  KSModel.cornerConditions_of_bounds Rlo_nonneg return_bounds wage_bounds feas_w design emp_w
    unemp_w

/-- **The household saves by the corner policy along every price path.** -/
theorem policy_witness (z₀ : Bool) (P : List Bool → ℝ × ℝ) (s : model.State) :
    model.policy z₀ P s = KSModel.cornerPolicy model saver s :=
  KSModel.policy_eq_cornerPolicy (KSModel.cornerFeas_of_bounds wage_bounds feas_w z₀ P)
    (KSModel.cornerEmp_of_bounds Rlo_nonneg return_bounds wage_bounds feas_w emp_w z₀ P)
    (KSModel.cornerUnemp_of_bounds Rlo_nonneg return_bounds wage_bounds feas_w unemp_w z₀ P) s

/-- Capital after yesterday's shock `y`: the cap times the employed share. -/
noncomputable def capOf (y : Bool) : ℝ := if y then 13 / 80 else 3 / 20

theorem saverMass_eq (y : Bool) : KSModel.saverMass design saver y = share y := by
  change ∑ e, (if saver e then (if e then share y else 1 - share y) else 0) = share y
  simp [saver]

/-- **Capital in the corner equilibrium**: `3/20` after a bad shock, `13/80` after a good one. -/
theorem capAt_witness (ω : History Bool) :
    KSModel.capAt (KSModel.μc design saver) ω = capOf (ω 1) := by
  rw [KSModel.capAt_μc, saverMass_eq, cap_eq]
  cases ω 1 <;> norm_num [share, capOf]

theorem capOf_mem_box (y : Bool) : capOf y ∈ Icc tech.capLo tech.capHi := by
  change capOf y ∈ Icc ((37 / 60 : ℝ) ^ 4) ((13 / 20) ^ 4)
  cases y <;> norm_num [capOf]

theorem labourD_mem_box (z : Bool) : KSModel.labourD design z ∈ Icc tech.labLo tech.labHi := by
  change ∑ e : Bool, (if e = true then share z else 1 - share z)
      * (if e = true then (4 : ℝ) else 1 / 2)
    ∈ Icc ((19 / 15 : ℝ) ^ 4) ((13 / 10) ^ 4)
  cases z <;> norm_num [share, Fintype.sum_bool]

/-- **Prices are the true Cobb–Douglas marginal products**: at every node of the equilibrium price
tree, capital and labour lie inside the clamping boxes. -/
theorem seqPrices_mem_box (ω : History Bool) (g : List Bool) :
    (model.seqPrices (KSModel.μc design saver) ω g).1 ∈ Icc tech.capLo tech.capHi ∧
      (model.seqPrices (KSModel.μc design saver) ω g).2 ∈ Icc tech.labLo tech.labHi := by
  rw [KSModel.seqPrices_μc]
  cases g with
  | nil =>
    refine ⟨?_, labourD_mem_box _⟩
    change KSModel.capAt (KSModel.μc design saver) ω ∈ _
    rw [capAt_witness]
    exact capOf_mem_box _
  | cons z g =>
    refine ⟨?_, labourD_mem_box _⟩
    change model.assetCap * KSModel.saverMass design saver (shockAt (ω 0) g) ∈ _
    have h : ∀ y, model.assetCap * share y = capOf y := by
      intro y
      cases y <;> norm_num [cap_eq, share, capOf]
    rw [saverMass_eq, h]
    exact capOf_mem_box _

/-- **A Krusell–Smith equilibrium with heterogeneous households in which `(z, K)` is a
sufficient state**: the corner candidate is a sequence-state equilibrium of the log-utility,
Cobb–Douglas economy above (prices are true marginal products along it, `seqPrices_mem_box`), it
satisfies `KSufficient`, and a recursive equilibrium on `(z, K)` represents it. -/
theorem cornerWitness :
    model.IsSeqStateEquilibrium (KSModel.μc design saver) ∧
      KSModel.KSufficient (KSModel.μc design saver) ∧
      ∃ R : model.AggStateRecursiveEquilibrium, R.Represents (KSModel.μc design saver) :=
  ⟨KSModel.isSeqStateEquilibrium_μc cornerConditions, KSModel.kSufficient_μc design saver,
    KSModel.exists_represents_μc cornerConditions⟩

end CornerWitness

end KrusellSmith

end LeanEconomics
