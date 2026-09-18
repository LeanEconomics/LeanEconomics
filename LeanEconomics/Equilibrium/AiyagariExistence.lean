/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.AiyagariUniqueness

/-!
# Existence for Aiyagari (1994) at `μ = 1`, up to one number

`exists_equilibrium_of_ceiling_and_floor_of_demand` produces an equilibrium on `[rlo, rhi]` from
four inputs: a unique stationary distribution at each rate, a ceiling on capital supply at
`rlo` below demand there, a floor at `rhi` above demand there, and a continuous demand
schedule. For the log economy with Aiyagari's numbers three of the four are proved here:
uniqueness is the Doeblin chain of `AiyagariUniqueness`, the ceiling is the minimal-MPC ceiling
`β · maxIncome/(1 - β(1+rlo))` — which is BELOW Cobb--Douglas demand near `-δ`, where demand is
unbounded — and the demand schedule is `normalisedDemand`.

The floor is not proved, and this file says so in its hypotheses. What is needed is a number
`m ≥ k(rhi)/w(rhi)` with `m ≤ K(rhi)` for every stationary distribution at `rhi`; at the rates
where Aiyagari's equilibria sit, `k/w` is about `5`, and the analytic supply floors available
here (an atom at the cap, a positive saving from the corner) are nowhere near it. Below the
time-preference rate the household is impatient, and how much it accumulates before impatience
takes over is a quantitative question about the policy that the qualitative theory — decline
above a threshold, the Euler inequality — does not answer. Above `λ` the floor is available
(`log_aggregateCapital_ge_of_patient`) but uniqueness of the stationary distribution is not.

So: existence AND uniqueness of the equilibrium rate for Aiyagari's log calibration reduce to
one inequality on capital supply at the top of the interval.
-/

open Set MeasureTheory

namespace LeanEconomics

theorem normalisedDemand_continuousOn {α δ rlo rhi : ℝ} (hα1 : α < 1) (hδ : 0 < rlo + δ) :
    ContinuousOn (normalisedDemand α δ) (Icc rlo rhi) := by
  change ContinuousOn (fun r => α / ((1 - α) * (r + δ))) (Icc rlo rhi)
  refine ContinuousOn.div continuousOn_const ?_ fun r hr => ?_
  · exact (continuous_const.mul (continuous_id.add continuous_const)).continuousOn
  · have : 0 < r + δ := by linarith [hr.1]
    exact mul_ne_zero (by linarith) this.ne'

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **An equilibrium for the log economy on `[rlo, rhi]`, given a supply floor at `rhi`.**
Uniqueness of the stationary distribution at each rate and the ceiling at `rlo` are proved; the
floor `m` at `rhi` is the hypothesis. -/
theorem log_exists_equilibrium_of_floor {rlo rhi α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ : 0 < rlo + δ) (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ)) (hβ1 : (P.discount : ℝ) < 1) (hrlo : 0 < 1 + rlo)
    (hlt : rlo < rhi) (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hcap : 2 * (P.discount : ℝ) * P.maxIncome < (1 - (P.discount : ℝ) * (1 + rhi)) * assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hmin : P.income z₀ = P.minIncome) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    {m : ℝ} (hfloor : ∀ hrhi : P.RateOK rhi, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate rhi hrhi).IsStationary μ → m ≤ P.aggregateCapital μ)
    (hDlo : (P.discount : ℝ) * P.maxIncome / (1 - (P.discount : ℝ) * (1 + rlo))
      ≤ normalisedDemand α δ rlo)
    (hDhi : normalisedDemand α δ rhi ≤ m) :
    ∃ r ∈ Icc rlo rhi,
      IsAiyagariEquilibrium (P.rateFamily hrlo hlt.le) (normalisedDemand α δ) r := by
  set β : ℝ := (P.discount : ℝ) with hβdef
  set R : ℝ := 1 + rhi with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith
  have hroom : 0 < 1 - β * R := by rw [hβdef, hRdef]; linarith
  have hmaxpos : 0 < P.maxIncome := lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxIncome
  have hcap0 : 0 < assetCap := by
    by_contra h
    have h' : assetCap ≤ 0 := not_lt.mp h
    have : (1 - β * R) * assetCap ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hroom.le h'
    nlinarith [hcap, hβ, hmaxpos]
  have hminpos : 0 < P.minIncome := P.minIncome_pos
  have hcap' : β * (P.maxIncome + R * assetCap) < assetCap := by nlinarith [hcap]
  -- the corner level, as in `log_equilibriumRate_unique_of_cap`
  set A : ℝ := P.minIncome * (1 - β * R) / (2 * β * R ^ 2) with hAdef
  have hA : 0 < A := by rw [hAdef]; positivity
  set a₀ : ℝ := min assetCap A with ha₀def
  have ha₀ : 0 < a₀ := lt_min hcap0 hA
  have hle : a₀ ≤ assetCap := min_le_left _ _
  have ha₀A : a₀ ≤ A := min_le_right _ _
  have hcorn : β * R * (P.income z₀ + R * a₀) < P.minIncome := by
    rw [hmin]
    have hkey : β * R * (R * A) = P.minIncome * (1 - β * R) / 2 := by
      rw [hAdef]; field_simp; try ring
    have hmono' : β * R * (R * a₀) ≤ β * R * (R * A) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha₀A hR.le) (by positivity)
    have : β * R * (P.minIncome + R * a₀) = β * R * P.minIncome + β * R * (R * a₀) := by ring
    rw [this]
    nlinarith [hkey, hmono', hroom, hminpos]
  refine P.exists_equilibrium_of_ceiling_and_floor_of_demand hrlo hlt ?_ ?_ hfloor
    (normalisedDemand α δ) (normalisedDemand_continuousOn hα1 hδ) hDlo hDhi
  · intro r hr hrr
    exact P.log_existsUnique_isStationary hu hunb hβ hβ1 hβR hcap' hmono hz₀ hreach ha₀ hle hcorn
      hr hrr
  · intro hrlo' μ hμ
    refine P.log_aggregateCapital_le hu hunb hβ hβ1 hrlo' (by nlinarith [hβR, hlt, hβ]) ?_ hμ
    have : (1 + rlo) * assetCap ≤ R * assetCap :=
      mul_le_mul_of_nonneg_right (by rw [hRdef]; linarith) hcap0.le
    nlinarith [hcap']

/-- **Aiyagari (1994) at `μ = 1`: an equilibrium exists on `[rlo, rhi] ⊂ (-δ, λ)` given a
supply floor at `rhi`**, for any earnings process with monotone transitions. With
`aiyagari1994_log_equilibriumRate_unique`, it is then the only one. -/
theorem aiyagari1994_log_exists_equilibrium_of_floor {rlo rhi : ℝ}
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded) (hβ : (P.discount : ℝ) = 24 / 25)
    (hrlo : -2 / 25 < rlo) (hlt : rlo < rhi) (hlam : rhi < 1 / 24)
    (hcap : 2 * (24 / 25) * P.maxIncome < (1 - 24 / 25 * (1 + rhi)) * assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hmin : P.income z₀ = P.minIncome) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    {m : ℝ} (hfloor : ∀ hrhi : P.RateOK rhi, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate rhi hrhi).IsStationary μ → m ≤ P.aggregateCapital μ)
    (hDlo : 24 / 25 * P.maxIncome / (1 - 24 / 25 * (1 + rlo))
      ≤ normalisedDemand (9 / 25) (2 / 25) rlo)
    (hDhi : normalisedDemand (9 / 25) (2 / 25) rhi ≤ m) :
    ∃ r ∈ Icc rlo rhi, IsAiyagariEquilibrium
      (P.rateFamily (by linarith : (0 : ℝ) < 1 + rlo) hlt.le)
      (normalisedDemand (9 / 25) (2 / 25)) r :=
  P.log_exists_equilibrium_of_floor (by norm_num) (by norm_num) (by linarith) hu hunb
    (by rw [hβ]; norm_num) (by rw [hβ]; norm_num) (by linarith) hlt (by rw [hβ]; linarith)
    (by rw [hβ]; exact hcap) hmono hz₀ hmin hreach hfloor (by rw [hβ]; exact hDlo) hDhi

end IncomeFluctuation

end LeanEconomics
