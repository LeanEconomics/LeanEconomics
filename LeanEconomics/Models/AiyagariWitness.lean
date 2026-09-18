/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.AiyagariUniqueness
import LeanEconomics.Models.DispersedWitness

/-!
# An economy at Aiyagari's numbers

`aiyagari1994_log_equilibriumRate_unique` carries a dozen hypotheses. This file exhibits an
economy that satisfies all of them by `rfl` and `norm_num`, so that the theorem is visibly about
something: `β = 24/25`, log utility, no borrowing, two iid earnings states `{1/2, 3/2}` (mean
one, which is Aiyagari's normalisation of per-capita labour), and an asset cap of `10⁸`.

The cap is that large for one reason. The theorem covers `[0, rhi]` for every `rhi` below the
time-preference rate `1/24 = 4.1667%`, and the cap has to clear
`(48/25)·maxIncome / (1 - (24/25)(1+rhi))`. Aiyagari's highest reported `μ = 1` rate is
`4.1666%`, leaving room `1 - (24/25)(1.041666) ≈ 1.6 × 10⁻⁷`, so a cap of order `10⁷` is needed
to reach it. Nothing about the economics changes with the cap —
it is imposed for compactness and the proof shows it never binds — so it is set high enough that
every equilibrium rate he reports at `μ = 1` lies inside the interval.
-/

open Set MeasureTheory

namespace LeanEconomics

/-- **Aiyagari (1994) at `μ = 1`**: `β = 0.96`, log utility, `b = 0`, iid earnings `{1/2, 3/2}`. -/
noncomputable def aiyagariLog : IncomeFluctuation (Fin 2) 0 100000000 where
  income z := if z = 0 then 1 / 2 else 3 / 2
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 24 / 25
  u := crraUtility 1
  minIncome := 1 / 2
  maxIncome := 3 / 2
  minIncome_pos := by norm_num
  minIncome_le z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  assetFloor_le_assetCap := by norm_num
  assetCap_nonneg := by norm_num
  minConsumption_pos := by norm_num
  minConsumption_le_floor := le_rfl
  discount_lt_one := by norm_num
  dom := Ioi 0
  Ioi_subset_dom := subset_rfl
  dom_subset_Ici := Ioi_subset_Ici_self
  continuousOn_u_dom := continuousOn_crraUtility 1
  monotoneOn_u_dom := monotoneOn_crraUtility 1
  strictConcaveOn_u_dom := strictConcaveOn_crraUtility one_pos
  continuousOn_extendDom :=
    continuousOn_extendDom_Ioi (continuousOn_crraUtility 1) (tendsto_atBot_crraUtility le_rfl)

@[simp] theorem aiyagariLog_u : aiyagariLog.u = crraUtility 1 := rfl
@[simp] theorem aiyagariLog_income_zero : aiyagariLog.income 0 = 1 / 2 := rfl
@[simp] theorem aiyagariLog_income_one : aiyagariLog.income 1 = 3 / 2 := rfl
@[simp] theorem aiyagariLog_discount : (aiyagariLog.discount : ℝ) = 24 / 25 := rfl
@[simp] theorem aiyagariLog_minIncome : aiyagariLog.minIncome = 1 / 2 := rfl
@[simp] theorem aiyagariLog_maxIncome : aiyagariLog.maxIncome = 3 / 2 := rfl
@[simp] theorem aiyagariLog_transitionMatrix (z z' : Fin 2) :
    aiyagariLog.transitionMatrix z z' = 1 / 2 := rfl

theorem aiyagariLog_unbounded : aiyagariLog.Unbounded := rfl

theorem aiyagariLog_iid : aiyagariLog.IidIncome := fun _ _ _ => rfl

/-- The expected endowment is one. -/
theorem aiyagariLog_mean_income :
    (1 / 2 : ℝ) * aiyagariLog.income 0 + 1 / 2 * aiyagariLog.income 1 = 1 := by norm_num

/-- **The equilibrium rate is unique on `[0, 4.1666%]`** — an interval containing every
equilibrium rate Aiyagari reports at `μ = 1` (Table II: `4.1666%` and `4.0649%` for the iid
columns, and between `3.3%` and `4.0%` for the persistent ones). All hypotheses of
`aiyagari1994_log_equilibriumRate_unique` are discharged by `rfl` and `norm_num`. -/
theorem aiyagariLog_equilibriumRate_unique {r₁ r₂ : ℝ}
    (h₁ : r₁ ∈ Icc (0 : ℝ) (416665 / 10000000)) (h₂ : r₂ ∈ Icc (0 : ℝ) (416665 / 10000000))
    (hrr₁ : aiyagariLog.RateOK r₁) (hrr₂ : aiyagariLog.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure aiyagariLog.State}
    (hμ₁ : (aiyagariLog.withRate r₁ hrr₁).IsStationary μ₁)
    (hμ₂ : (aiyagariLog.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : aiyagariLog.aggregateCapital μ₁ = normalisedDemand (9 / 25) (2 / 25) r₁)
    (he₂ : aiyagariLog.aggregateCapital μ₂ = normalisedDemand (9 / 25) (2 / 25) r₂) :
    r₁ = r₂ :=
  aiyagariLog.aiyagari1994_log_equilibriumRate_unique rfl aiyagariLog_unbounded rfl
    (by norm_num) (by norm_num) (by norm_num)
    (IncomeFluctuation.monotoneTransitions_of_iid _ aiyagariLog_iid) (z₀ := 0)
    (fun z => by fin_cases z <;> norm_num) rfl (fun z => by norm_num)
    h₁ h₂ hrr₁ hrr₂ hμ₁ hμ₂ he₁ he₂

/-! ### Persistent income

The same economy with Huggett's persistence: employed households stay employed with probability
`9/10`, the unemployed find work with probability `1/2`. `π(h|h) = 9/10 ≥ 1/2 = π(h|l)`, so the
transitions are monotone, and everything else is unchanged. -/

/-- Aiyagari's preferences and technology with a persistent two-state earnings process. -/
noncomputable def aiyagariPersistent : IncomeFluctuation (Fin 2) 0 100000000 where
  income z := if z = 0 then 1 / 2 else 3 / 2
  transitionMatrix z z' := if z = 0 then (if z' = 0 then 1 / 2 else 1 / 2)
    else (if z' = 0 then 1 / 10 else 9 / 10)
  interest := 0
  discount := 24 / 25
  u := crraUtility 1
  minIncome := 1 / 2
  maxIncome := 3 / 2
  minIncome_pos := by norm_num
  minIncome_le z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg z z' := by fin_cases z <;> fin_cases z' <;> norm_num
  transitionMatrix_sum z := by fin_cases z <;> simp <;> norm_num
  interest_gt_neg_one := by norm_num
  assetFloor_le_assetCap := by norm_num
  assetCap_nonneg := by norm_num
  minConsumption_pos := by norm_num
  minConsumption_le_floor := le_rfl
  discount_lt_one := by norm_num
  dom := Ioi 0
  Ioi_subset_dom := subset_rfl
  dom_subset_Ici := Ioi_subset_Ici_self
  continuousOn_u_dom := continuousOn_crraUtility 1
  monotoneOn_u_dom := monotoneOn_crraUtility 1
  strictConcaveOn_u_dom := strictConcaveOn_crraUtility one_pos
  continuousOn_extendDom :=
    continuousOn_extendDom_Ioi (continuousOn_crraUtility 1) (tendsto_atBot_crraUtility le_rfl)

theorem aiyagariPersistent_unbounded : aiyagariPersistent.Unbounded := rfl

/-- Not iid: the rows differ. -/
theorem aiyagariPersistent_not_iid : ¬ aiyagariPersistent.IidIncome := by
  intro h
  have := h 0 1 1
  norm_num [aiyagariPersistent] at this

/-- Huggett's condition holds, so the transitions are monotone. -/
theorem aiyagariPersistent_monotone : aiyagariPersistent.MonotoneTransitions :=
  IncomeFluctuation.monotoneTransitions_of_two_states _ (by norm_num [aiyagariPersistent])
    (by norm_num [aiyagariPersistent])

/-- **The equilibrium rate is unique on `[0, 4.1666%]` with persistent income.** The first
uniqueness result in this development for an economy whose income process is not iid. -/
theorem aiyagariPersistent_equilibriumRate_unique {r₁ r₂ : ℝ}
    (h₁ : r₁ ∈ Icc (0 : ℝ) (416665 / 10000000)) (h₂ : r₂ ∈ Icc (0 : ℝ) (416665 / 10000000))
    (hrr₁ : aiyagariPersistent.RateOK r₁) (hrr₂ : aiyagariPersistent.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure aiyagariPersistent.State}
    (hμ₁ : (aiyagariPersistent.withRate r₁ hrr₁).IsStationary μ₁)
    (hμ₂ : (aiyagariPersistent.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : aiyagariPersistent.aggregateCapital μ₁ = normalisedDemand (9 / 25) (2 / 25) r₁)
    (he₂ : aiyagariPersistent.aggregateCapital μ₂ = normalisedDemand (9 / 25) (2 / 25) r₂) :
    r₁ = r₂ :=
  aiyagariPersistent.aiyagari1994_log_equilibriumRate_unique rfl aiyagariPersistent_unbounded rfl
    (by norm_num) (by norm_num) (by norm_num [aiyagariPersistent]) aiyagariPersistent_monotone
    (z₀ := 0)
    (fun z => by fin_cases z <;> norm_num [aiyagariPersistent]) rfl
    (fun z => by fin_cases z <;> norm_num [aiyagariPersistent])
    h₁ h₂ hrr₁ hrr₂ hμ₁ hμ₂ he₁ he₂

end LeanEconomics
