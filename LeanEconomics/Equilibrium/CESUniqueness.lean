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

/-- The `nearLog` economy as a function of the interest rate: the SAME family the existence
theorem `nearLog_exists_equilibrium` uses, so existence and uniqueness speak about one object. -/
noncomputable def nearLogAt : ℝ → IncomeFluctuation (Fin 2) 0 1 :=
  nearLog.rateFamily (by norm_num : (0:ℝ) < 1 + 0) (by norm_num : (0:ℝ) ≤ 1 / 200)

theorem nearLogAt_eq {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200)) (h : nearLog.RateOK r) :
    nearLogAt r = nearLog.withRate r h :=
  nearLog.rateFamily_eq _ _ hr h

theorem nearLogAt_transitionMatrix (r r' : ℝ) (z z' : Fin 2) :
    (nearLogAt r).transitionMatrix z z' = (nearLogAt r').transitionMatrix z z' := rfl

/-- **Light Theorem 1 for the rate family.** -/
theorem nearLogAt_policy_mono {r r' : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hr' : r' ∈ Icc (0 : ℝ) (1 / 200)) (hle : r ≤ r') (s : ℝ × Fin 2)
    (hs : s.1 ∈ Icc (0 : ℝ) 1) : (nearLogAt r).policy s ≤ (nearLogAt r').policy s := by
  have h : nearLog.RateOK r := IncomeFluctuation.rateOK_of_floor_zero (by linarith [hr.1])
  have h' : nearLog.RateOK r' := IncomeFluctuation.rateOK_of_floor_zero (by linarith [hr'.1])
  rw [nearLogAt_eq hr h, nearLogAt_eq hr' h']
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

/-! ### The stationary distribution, and convergence to it

The last hypothesis is now discharged. `nearLog_tendsto_pushProb_iterate` is Doeblin with the
atom at the borrowing constraint: at every rate in `[0, 1/200]` the low income state is drawn
with probability `1/2` from everywhere, and enough consecutive draws of it carry even the
richest household to zero assets (`nearLog_exhausts_uniform`, from the corner and decline
conditions of `CESNearLogWitness`). So the forward iterates of ANY initial distribution converge
weakly to the stationary one, and capital supply is a genuine function of the rate. -/

/-- The stationary distribution at each rate. Unique, by `nearLog_existsUnique_uniform`, for
every rate in `[0, 1/200]`. -/
noncomputable def nearLogStationary (r : ℝ) : ProbabilityMeasure nearLog.State :=
  Classical.choose ((nearLogAt r).exists_isStationary
    ⟨Measure.dirac (Classical.ofNonempty : nearLog.State), inferInstance⟩)

theorem nearLogStationary_isStationary (r : ℝ) :
    (nearLogAt r).IsStationary (nearLogStationary r) :=
  Classical.choose_spec ((nearLogAt r).exists_isStationary
    ⟨Measure.dirac (Classical.ofNonempty : nearLog.State), inferInstance⟩)

/-- **The economy finds its stationary distribution**, at every rate in `[0, 1/200]`. -/
theorem nearLog_tendsto_stationary (μ₀ : ProbabilityMeasure nearLog.State) :
    ∀ r ∈ Icc (0 : ℝ) (1 / 200),
      Tendsto (fun m => (nearLogAt r).pushProb^[m] μ₀) atTop (𝓝 (nearLogStationary r)) := by
  intro r hr
  have h : nearLog.RateOK r := IncomeFluctuation.rateOK_of_floor_zero (by linarith [hr.1])
  have hst := nearLogStationary_isStationary r
  rw [nearLogAt_eq hr h] at hst ⊢
  exact nearLog_tendsto_pushProb_iterate hr h μ₀ hst

/-- **Capital supply for `nearLog` is a genuine function of the rate, and it is monotone.**
Nothing is assumed. -/
theorem nearLog_monotoneOn_capitalSupply' :
    MonotoneOn (fun r => nearLog.aggregateCapital (nearLogStationary r)) (Icc (0 : ℝ) (1 / 200)) :=
  nearLog_monotoneOn_capitalSupply
    ⟨Measure.dirac (Classical.ofNonempty : nearLog.State), inferInstance⟩ nearLogStationary
    (nearLog_tendsto_stationary _)

/-- **Uniqueness of the Aiyagari equilibrium interest rate for `nearLog`, unconditionally.**

Two rates in `[0, 1/200]` at which capital supply equals capital demand are equal. Every
hypothesis of the chain is now a theorem about this economy: Light's Theorem 1 from
`CESRateMonotone`, Theorem 2 from `CapitalSupplyMonotone`, Theorem 3 from
`Equilibrium.Uniqueness`, and the convergence of the distribution from Doeblin. -/
theorem nearLog_equilibriumRate_unique' {A δ : ℝ} (hA : A ≠ 0) (hδ : 0 < δ)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc (0 : ℝ) (1 / 200)) (h₂ : r₂ ∈ Icc (0 : ℝ) (1 / 200))
    (he₁ : nearLog.aggregateCapital (nearLogStationary r₁) = capitalDemand A δ r₁)
    (he₂ : nearLog.aggregateCapital (nearLogStationary r₂) = capitalDemand A δ r₂) : r₁ = r₂ :=
  equilibriumRate_unique hA (by linarith) nearLog_monotoneOn_capitalSupply' h₁ h₂ he₁ he₂


/-! ### The capstone

Existence was proved in `CESNearLogWitness` for the same rate family. With uniqueness of the
stationary distribution identifying the measure in any equilibrium with `nearLogStationary`, the
two combine: the `nearLog` economy has EXACTLY ONE Aiyagari equilibrium rate. -/

/-- In any equilibrium the stationary distribution is the canonical one — there is only one. -/
theorem nearLog_eq_stationary_of_isStationary {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    {μ : ProbabilityMeasure nearLog.State} (hμ : (nearLogAt r).IsStationary μ) :
    μ = nearLogStationary r := by
  have h : nearLog.RateOK r := IncomeFluctuation.rateOK_of_floor_zero (by linarith [hr.1])
  obtain ⟨ν, -, huniq⟩ := nearLog_existsUnique_uniform hr h
  rw [nearLogAt_eq hr h] at hμ
  have hst := nearLogStationary_isStationary r
  rw [nearLogAt_eq hr h] at hst
  rw [huniq _ hμ, huniq _ hst]

/-- **Uniqueness of the Aiyagari equilibrium rate for `nearLog`.** -/
theorem nearLog_isAiyagariEquilibrium_unique {A δ : ℝ} (hA : A ≠ 0) (hδ : 0 < δ)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc (0 : ℝ) (1 / 200)) (h₂ : r₂ ∈ Icc (0 : ℝ) (1 / 200))
    (he₁ : IsAiyagariEquilibrium nearLogAt (capitalDemand A δ) r₁)
    (he₂ : IsAiyagariEquilibrium nearLogAt (capitalDemand A δ) r₂) : r₁ = r₂ := by
  obtain ⟨μ₁, hst₁, hcap₁⟩ := he₁
  obtain ⟨μ₂, hst₂, hcap₂⟩ := he₂
  rw [nearLog_eq_stationary_of_isStationary h₁ hst₁] at hcap₁
  rw [nearLog_eq_stationary_of_isStationary h₂ hst₂] at hcap₂
  exact nearLog_equilibriumRate_unique' hA hδ h₁ h₂ hcap₁ hcap₂

/-- **The `nearLog` economy has exactly one Aiyagari equilibrium rate.** Existence is
`nearLog_exists_equilibrium`; uniqueness is Light's three theorems, every hypothesis of which is
now a theorem about this economy. -/
theorem nearLog_existsUnique_equilibrium :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∃! r : ℝ, r ∈ Icc (0 : ℝ) (1 / 200)
        ∧ IsAiyagariEquilibrium nearLogAt (capitalDemand A δ) r := by
  obtain ⟨A, δ, hA, hδ, r, hr, heq⟩ := nearLog_exists_equilibrium
  refine ⟨A, δ, hA, by linarith, r, ⟨hr, heq⟩, ?_⟩
  rintro r' ⟨hr', heq'⟩
  exact nearLog_isAiyagariEquilibrium_unique (ne_of_gt hA) (by linarith) hr' hr heq' heq

end LeanEconomics
