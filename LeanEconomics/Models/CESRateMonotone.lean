/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.CESConcaveConsumption
import LeanEconomics.Models.IncomeFluctuationRateStep

/-!
# Light's Theorem 1 at a concrete CES calibration

`policy_mono_withRate_crra` proves that a household facing a higher interest rate saves at least
as much, given four things about the economy: consumption positive at every optimum, the asset
cap slack along both iterations, the Carroll–Kimball concavity of the iterates' consumption
functions, and relative risk aversion at most one. `nearLog` has all four, at every rate in
`[0, 1/200]` — the range the equilibrium argument uses — so Theorem 1 holds there outright.

The one thing that has to be said twice is the cap-slack bound. Economy TWO's maximisation is run
against economy ONE's iterates as well as its own, so the bound on saving is needed for both
sequences; `nearLog_oscGap_le_uniform` covers both, because the oscillation bound is uniform in
the rate over `[0, 1/200]` and `OscOn` does not mention the economy.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

open IncomeFluctuation

/-- Positive consumption against EVERY continuation with concave slices, not just at the fixed
point: what the induction sees. -/
theorem nearLog_withRate_positiveConsumptionAll {r : ℝ} (hrr : nearLog.RateOK r) :
    (nearLog.withRate r hrr).PositiveConsumptionAll := by
  refine (nearLog.withRate r hrr).positiveConsumptionAll_of_marginalInada ?_
  rw [show (nearLog.withRate r hrr).dom = Ici 0 from nearLog_bounded,
    show (nearLog.withRate r hrr).u = crraUtility (15 / 16) from rfl]
  exact marginalInadaOn_Ici_crraUtility (by norm_num) (by norm_num)

/-- **The calibration inequality, for any oscillation bound at most `27/5`.** This is the
`hlt` of `crra_policyOf_lt_assetCap`, with the oscillation left as a parameter so that it can be
fed either economy's iterates. -/
theorem nearLog_calibration {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200)) (hrr : nearLog.RateOK r)
    {G : ℝ} (hG0 : 0 ≤ G) (hG : G ≤ 27 / 5) :
    (((nearLog.withRate r hrr).discount : ℝ) * G / (999 / 1000))
        * ((nearLog.withRate r hrr).maxIncome
          + (1 + (nearLog.withRate r hrr).interest - 999 / 1000) * 1
          - (1 - 999 / 1000) * 0) ^ ((15 : ℝ) / 16)
      < 1 - 0 := by
  have hcoef : ((nearLog.withRate r hrr).discount : ℝ) * G / (999 / 1000) ≤ 25 / 37 := by
    rw [show (((nearLog.withRate r hrr).discount : ℝ)) = 1 / 8 from rfl,
      div_le_iff₀ (by norm_num)]
    linarith
  have hcoef0 : (0 : ℝ) ≤ ((nearLog.withRate r hrr).discount : ℝ) * G / (999 / 1000) := by
    rw [show (((nearLog.withRate r hrr).discount : ℝ)) = 1 / 8 from rfl]; positivity
  have hbase : (nearLog.withRate r hrr).maxIncome
      + (1 + (nearLog.withRate r hrr).interest - 999 / 1000) * 1 - (1 - 999 / 1000) * 0
      ≤ 503 / 500 := by
    simp only [IncomeFluctuation.withRate_maxIncome, IncomeFluctuation.withRate_interest,
      nearLog_maxIncome]
    linarith [hr.2]
  have hbase0 : (0 : ℝ) ≤ (nearLog.withRate r hrr).maxIncome
      + (1 + (nearLog.withRate r hrr).interest - 999 / 1000) * 1 - (1 - 999 / 1000) * 0 := by
    simp only [IncomeFluctuation.withRate_maxIncome, IncomeFluctuation.withRate_interest,
      nearLog_maxIncome]
    linarith [hr.1]
  have hpow : ((nearLog.withRate r hrr).maxIncome
      + (1 + (nearLog.withRate r hrr).interest - 999 / 1000) * 1
      - (1 - 999 / 1000) * 0) ^ ((15 : ℝ) / 16) ≤ 503 / 500 := by
    refine le_trans (Real.rpow_le_rpow hbase0 hbase (by norm_num)) ?_
    exact rpow_le_of_pow_le (m := 15) (n := 16) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hpow0 : (0 : ℝ) ≤ ((nearLog.withRate r hrr).maxIncome
      + (1 + (nearLog.withRate r hrr).interest - 999 / 1000) * 1
      - (1 - 999 / 1000) * 0) ^ ((15 : ℝ) / 16) := Real.rpow_nonneg hbase0 _
  nlinarith [hcoef, hpow, hcoef0, hpow0]

/-- The cap is slack against any continuation whose oscillation is at most `27/5`. -/
theorem nearLog_policyOf_lt_cap {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : nearLog.RateOK r) {v : (ℝ × Fin 2) →ᵇ ℝ} (hv : ConcaveSlices (0 : ℝ) 1 v)
    (hosc : (nearLog.withRate r hrr).OscOn v (27 / 5)) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (z : Fin 2) : (nearLog.withRate r hrr).policyOf v (a, z) < 1 :=
  (nearLog.withRate r hrr).crra_policyOf_lt_assetCap (γ := 15 / 16) (θ := 999 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl
    (nearLog_withRate_positiveConsumptionAll hrr) hv (by norm_num) hosc
    (nearLog_calibration hr hrr (by norm_num) le_rfl) ha z

/-- **Light (2018) Theorem 1 for `nearLog`.** At every rate in `[0, 1/200]`, a household facing a
higher interest rate saves at least as much — at every asset level and every income state, with
nothing assumed. -/
theorem nearLog_policy_mono_interest {r₁ r₂ : ℝ} (hr₁ : r₁ ∈ Icc (0 : ℝ) (1 / 200))
    (hr₂ : r₂ ∈ Icc (0 : ℝ) (1 / 200)) (hr : r₁ ≤ r₂)
    (h₁ : nearLog.RateOK r₁) (h₂ : nearLog.RateOK r₂)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 2) :
    (nearLog.withRate r₁ h₁).policy (a, z) ≤ (nearLog.withRate r₂ h₂).policy (a, z) := by
  have hpc := nearLog_withRate_positiveConsumptionAll h₂
  -- concave slices of both iterate sequences
  have hslices : ∀ (r : ℝ) (hrr : nearLog.RateOK r) (n : ℕ), ConcaveSlices (0 : ℝ) 1
      (((nearLog.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Fin 2) →ᵇ ℝ)) := by
    intro r hrr n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (nearLog.withRate r hrr).concaveSlices_bellman ih
  -- the oscillation bound, uniform in the rate, so it covers both sequences
  have hosc : ∀ (r : ℝ) (hrq : r ∈ Icc (0 : ℝ) (1 / 200)) (hrr : nearLog.RateOK r) (n : ℕ),
      (nearLog.withRate r₂ h₂).OscOn
        (((nearLog.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Fin 2) →ᵇ ℝ)) (27 / 5) := by
    intro r hrq hrr n
    refine IncomeFluctuation.OscOn.mono (nearLog.withRate r₂ h₂)
      (G := (nearLog.withRate r hrr).oscSpread) ?_ ?_
    · exact (nearLog.withRate r hrr).oscOn_iterate n
    · exact le_trans (le_of_eq ((nearLog.withRate r hrr).oscSpread_eq_oscGap))
        (nearLog_oscGap_le_uniform hrq hrr)
  have hslackv : ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ z' : Fin 2, (nearLog.withRate r₂ h₂).policyOf
      (((nearLog.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Fin 2) →ᵇ ℝ)) (x, z') < 1 :=
    fun n x hx z' => nearLog_policyOf_lt_cap hr₂ h₂ (hslices r₁ h₁ n) (hosc r₁ hr₁ h₁ n) hx z'
  have hslackw : ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ z' : Fin 2, (nearLog.withRate r₂ h₂).policyOf
      (((nearLog.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Fin 2) →ᵇ ℝ)) (x, z') < 1 :=
    fun n x hx z' => nearLog_policyOf_lt_cap hr₂ h₂ (hslices r₂ h₂ n) (hosc r₂ hr₂ h₂ n) hx z'
  exact nearLog.policy_mono_withRate_crra (γ := 15 / 16) (by norm_num) (by norm_num) rfl h₁ h₂ hr
    hpc hslackv hslackw
    ((nearLog.withRate r₂ h₂).concaveOn_consumptionFnOf_iterates_of_crra hpc (by norm_num)
      (by rw [show (((nearLog.withRate r₂ h₂).discount : ℝ)) = 1 / 8 from rfl]; norm_num) rfl
      hslackw) ha z

end LeanEconomics
