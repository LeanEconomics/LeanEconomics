/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.CESRateMonotone
import LeanEconomics.Equilibrium.CapitalSupplyMonotone

/-!
# Uniqueness of the Aiyagari equilibrium rate, at a concrete CES economy

The chain is now complete for `nearLog`:

* Light Theorem 1 (`nearLog_policy_mono_interest`): every household saves at least as much at the
  higher rate. Proved outright — Carroll–Kimball for the consumption function, Clausen–Strub for
  the envelope, and the budget coincidence across rates for the induction.
* Light Theorem 2 (`monotoneOn_capitalSupply_of_policy_mono`): aggregate capital is therefore
  non-decreasing in the rate.
* Light Theorem 3 (`equilibriumRate_unique`): capital demand is strictly decreasing, so the two
  curves cross once.

What is still carried as a hypothesis is the CONVERGENCE of the forward iterates of the
distribution to the stationary one, rate by rate. That is the one piece of step 4 of the Aiyagari
roadmap never finished: `tendsto_pushProb_iterate` proves it from Doeblin data, and the data has
not been produced for this witness. It is a statement about the DISTRIBUTION, not about the
household problem — nothing of the household side is assumed here any more.
-/

open scoped NNReal
open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

open IncomeFluctuation

/-- The `nearLog` economy as a total function of the interest rate. Off the admissible range it
is the economy itself, which is never looked at. -/
noncomputable def nearLogAt (r : ℝ) : IncomeFluctuation (Fin 2) 0 1 :=
  if h : 0 < 1 + r then nearLog.withRate r (IncomeFluctuation.rateOK_of_floor_zero h) else nearLog

theorem nearLogAt_eq {r : ℝ} (h : nearLog.RateOK r) : nearLogAt r = nearLog.withRate r h := by
  rw [nearLogAt, dif_pos h.1]

theorem nearLogAt_transitionMatrix (r r' : ℝ) (z z' : Fin 2) :
    (nearLogAt r).transitionMatrix z z' = (nearLogAt r').transitionMatrix z z' := by
  unfold nearLogAt
  split <;> split <;> rfl

/-- **Light Theorem 1 for the rate family.** -/
theorem nearLogAt_policy_mono {r r' : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hr' : r' ∈ Icc (0 : ℝ) (1 / 200)) (hle : r ≤ r') (s : ℝ × Fin 2)
    (hs : s.1 ∈ Icc (0 : ℝ) 1) : (nearLogAt r).policy s ≤ (nearLogAt r').policy s := by
  have h : nearLog.RateOK r := IncomeFluctuation.rateOK_of_floor_zero (by linarith [hr.1])
  have h' : nearLog.RateOK r' := IncomeFluctuation.rateOK_of_floor_zero (by linarith [hr'.1])
  rw [nearLogAt_eq h, nearLogAt_eq h']
  exact nearLog_policy_mono_interest hr hr' hle h h' hs s.2

/-- **Light Theorem 2 for `nearLog`.** Capital supply is non-decreasing in the interest rate,
given only that the forward iterates of the distribution converge. -/
theorem nearLog_monotoneOn_capitalSupply (μ₀ : ProbabilityMeasure nearLog.State)
    (ν : ℝ → ProbabilityMeasure nearLog.State)
    (hconv : ∀ r ∈ Icc (0 : ℝ) (1 / 200),
      Tendsto (fun m => (nearLogAt r).pushProb^[m] μ₀) atTop (𝓝 (ν r))) :
    MonotoneOn (fun r => nearLog.aggregateCapital (ν r)) (Icc (0 : ℝ) (1 / 200)) :=
  nearLog.monotoneOn_capitalSupply_of_policy_mono nearLogAt nearLogAt_transitionMatrix
    (fun r hr r' hr' hle s hs => nearLogAt_policy_mono hr hr' hle s hs) μ₀ ν hconv

/-- **Uniqueness of the equilibrium interest rate for `nearLog`.** Two rates in `[0, 1/200]` at
which capital supply equals capital demand are equal.

Nothing about the household side is assumed: Light's Theorem 1 is proved for this economy. The
remaining hypothesis is the convergence of the distribution's forward iterates. -/
theorem nearLog_equilibriumRate_unique {A δ : ℝ} (hA : A ≠ 0) (hδ : 0 < δ)
    (μ₀ : ProbabilityMeasure nearLog.State) (ν : ℝ → ProbabilityMeasure nearLog.State)
    (hconv : ∀ r ∈ Icc (0 : ℝ) (1 / 200),
      Tendsto (fun m => (nearLogAt r).pushProb^[m] μ₀) atTop (𝓝 (ν r)))
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc (0 : ℝ) (1 / 200)) (h₂ : r₂ ∈ Icc (0 : ℝ) (1 / 200))
    (he₁ : nearLog.aggregateCapital (ν r₁) = capitalDemand A δ r₁)
    (he₂ : nearLog.aggregateCapital (ν r₂) = capitalDemand A δ r₂) : r₁ = r₂ :=
  equilibriumRate_unique hA (by linarith) (nearLog_monotoneOn_capitalSupply μ₀ ν hconv) h₁ h₂
    he₁ he₂

end LeanEconomics
