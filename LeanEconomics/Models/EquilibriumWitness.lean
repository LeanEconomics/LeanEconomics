/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.DispersedWitness
import LeanEconomics.Models.UniformRate
import LeanEconomics.Equilibrium.SignChange

/-!
# An Aiyagari equilibrium, instantiated

`exists_equilibrium_of_uniqueness_and_floor` asks for two things of the households — a unique
stationary distribution at every rate in an interval, and a positive floor under capital supply —
and supplies the firm itself. This file checks both at concrete numbers, on the interval
`[0, 1/20]`, for the `dispersed` economy of `DispersedWitness`.

## Where the interval comes from

The three conditions bind at opposite ends, which is what makes the interval narrow rather than
the constants being crude.

* CORNER and DECLINE bind at the TOP (`UniformRate`), so both are checked at `r = 1/20`. They
  bracket the switching asset level `a₀`: the corner needs `a₀` small, the decline needs it large.
  At `r = 1/20` the window is `a₀ ∈ (0.0303, 0.0360)` and `a₀ = 1/30` sits inside it. By `r = 0.1`
  the window is empty, which is what caps `rhi`.
* The GAIN binds at the BOTTOM (`gain_term_mono`), so it is checked at `r = 0`, with `h = 1/50`.

## Three inequalities

Everything reduces to

* `log 2 < 139/189` — the corner, from `Real.log_two_lt_d9`;
* `log 100 < 5` — the decline, from `Real.exp_one_gt_d9`;
* `2 · 50^16 < 3 · 49^16` — the gain, an integer fact.

with margins of 6%, 33% and 9% respectively.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

/-! ### Two elementary bounds -/

theorem log_hundred_lt_five : Real.log 100 < 5 := by
  have h5 : Real.exp 1 ^ (5 : ℕ) = Real.exp 5 := by
    rw [Real.exp_one_pow]; norm_num
  have h1 : (100 : ℝ) < Real.exp 5 := by
    calc (100 : ℝ) < (2.7182818283 : ℝ) ^ (5 : ℕ) := by norm_num
      _ < Real.exp 1 ^ (5 : ℕ) := by
        have he := Real.exp_one_gt_d9
        have h0 : (0 : ℝ) ≤ 2.7182818283 := by norm_num
        gcongr
      _ = Real.exp 5 := h5
  exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr h1

theorem log_two_lt : Real.log 2 < 139 / 189 :=
  lt_trans Real.log_two_lt_d9 (by norm_num)

/-! ### The value function, bounded uniformly over the interval -/

theorem dispersed_norm_le_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 20))
    (hrr : dispersed.RateOK r) :
    ‖(dispersed.withRate r hrr).toExtended.valueFunction‖ ≤ 8 / 7 * Real.log 100 := by
  have h := (dispersed.withRate r hrr).toExtended.norm_valueFunction_le
  have hmin : (dispersed.withRate r hrr).toExtended.rewardMin
      = (dispersed.withRate r hrr).u (dispersed.withRate r hrr).minConsumption := rfl
  have hmax : (dispersed.withRate r hrr).toExtended.rewardMax
      = (dispersed.withRate r hrr).u (dispersed.withRate r hrr).maxConsumption := rfl
  have hdisc : ((dispersed.withRate r hrr).toExtended.discount : ℝ)
      = ((dispersed.withRate r hrr).discount : ℝ) := rfl
  have hmc : (dispersed.withRate r hrr).maxConsumption = 2 + r := by
    simp only [IncomeFluctuation.maxConsumption, IncomeFluctuation.withRate_maxIncome,
      IncomeFluctuation.withRate_interest, dispersed_maxIncome]
    ring
  rw [hmin, hmax, hdisc, hmc, IncomeFluctuation.withRate_u,
    IncomeFluctuation.withRate_minConsumption, IncomeFluctuation.withRate_discount, dispersed_u,
    dispersed_minConsumption, dispersed_discount] at h
  have h1 : |Real.log (1 / 100)| = Real.log 100 := by
    rw [show (1 : ℝ) / 100 = (100 : ℝ)⁻¹ by norm_num, Real.log_inv, abs_neg,
      abs_of_nonneg (Real.log_nonneg (by norm_num))]
  have hr2 : (1 : ℝ) ≤ 2 + r := by linarith [hr.1]
  have h2 : |Real.log (2 + r)| = Real.log (2 + r) :=
    abs_of_nonneg (Real.log_nonneg hr2)
  have h3 : Real.log (2 + r) ≤ Real.log 100 :=
    Real.log_le_log (by linarith) (by linarith [hr.2])
  rw [h1, h2, max_eq_left h3] at h
  calc ‖(dispersed.withRate r hrr).toExtended.valueFunction‖ ≤ Real.log 100 / (1 - 1 / 8) := h
    _ = 8 / 7 * Real.log 100 := by ring

/-! ### The consumption floor, decline and corner, uniformly -/

/-- Every rate variant of the witness still has log utility, hence the open domain, hence
positive consumption at the optimum. -/
theorem dispersed_withRate_unbounded {r : ℝ} (hrr : dispersed.RateOK r) :
    (dispersed.withRate r hrr).Unbounded := rfl

theorem dispersed_withRate_positiveConsumption {r : ℝ} (hrr : dispersed.RateOK r) :
    (dispersed.withRate r hrr).PositiveConsumption :=
  (dispersed.withRate r hrr).positiveConsumption_of_unbounded rfl

/-- The linear consumption bound holds with a single constant across the interval. -/
theorem dispersed_consumption_bound {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 20))
    (hrr : dispersed.RateOK r)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 2) :
    1 / (1 + 4 / 7 * Real.log 100) * (dispersed.withRate r hrr).resources (a, z)
      ≤ (dispersed.withRate r hrr).consumptionFn z a := by
  have hbd := (dispersed.withRate r hrr).log_consumption_lower_bound_of_norm
    (dispersed_withRate_positiveConsumption hrr) (by simp)
    (dispersed_norm_le_uniform hr hrr) ha z
  have he : (1 : ℝ) + 4 * ((dispersed.withRate r hrr).discount : ℝ) * (8 / 7 * Real.log 100)
      = 1 + 4 / 7 * Real.log 100 := by
    rw [IncomeFluctuation.withRate_discount, dispersed_discount]; ring
  rw [he] at hbd
  rwa [one_div, inv_mul_eq_div]

theorem dispersed_epsUniform_gt : 7 / 27 < 1 / (1 + 4 / 7 * Real.log 100) := by
  have h := log_hundred_lt_five
  have hpos : (0 : ℝ) < 1 + 4 / 7 * Real.log 100 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 100 by norm_num)
    linarith
  rw [lt_div_iff₀ hpos]
  linarith

/-- **Assets decline above `1/30`, at every rate in the interval.** -/
theorem dispersed_decline_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 20)) (hrr : dispersed.RateOK r)
    {a : ℝ} (ha : a ∈ Icc (1 / 30 : ℝ) 1) :
    (dispersed.withRate r hrr).policy (a, 0) < a := by
  have hmem : a ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ha.1], ha.2⟩
  have heps := dispersed_epsUniform_gt
  have hlogn : (0 : ℝ) ≤ Real.log 100 := Real.log_nonneg (by norm_num)
  have hε1 : 1 / (1 + 4 / 7 * Real.log 100) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  refine dispersed.policy_lt_self_of_rate_le hrr hr.2 hε1 hmem
    (by simpa using dispersed_consumption_bound hr hrr hmem 0) ?_
  simp only [dispersed_income_zero]
  set ε : ℝ := 1 / (1 + 4 / 7 * Real.log 100) with hεdef
  have hcoef : (0 : ℝ) < 1 - (1 - ε) * (1 + 1 / 20) := by nlinarith [heps]
  have hstep : (1 - (1 - ε) * (1 + 1 / 20)) * (1 / 30)
      ≤ (1 - (1 - ε) * (1 + 1 / 20)) * a := mul_le_mul_of_nonneg_left ha.1 hcoef.le
  nlinarith [heps, hstep]

/-- **The borrowing constraint binds below `1/30`, at every rate in the interval.** -/
theorem dispersed_corner_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 20)) (hrr : dispersed.RateOK r)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (1 / 30)) :
    (dispersed.withRate r hrr).policy (a, 0) = 0 := by
  have hmem : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
  have hrhi : dispersed.RateOK (1 / 20 : ℝ) :=
    IncomeFluctuation.rateOK_of_floor_zero (by norm_num)
  have hβ : ((dispersed.discount : ℝ)) * (1 + 1 / 20) < 1 := by
    rw [dispersed_discount]; norm_num
  refine dispersed.log_policy_eq_zero_uniform rfl (by simp) hrr hrhi hr.2 hβ hmem 0 ?_
  have hres : (dispersed.withRate (1 / 20) hrhi).resources (a, 0)
      = 1 / 100 + (21 / 20) * a := by
    simp only [IncomeFluctuation.resources, IncomeFluctuation.withRate_income,
      IncomeFluctuation.withRate_interest, dispersed_income_zero, max_eq_right ha.1]
    ring
  have hlip : (dispersed.withRate (1 / 20) hrhi).logLipschitz
      = 33600 * Real.log 2 / 139 := by
    simp only [IncomeFluctuation.logLipschitz, IncomeFluctuation.withRate_minConsumption,
      IncomeFluctuation.withRate_interest, IncomeFluctuation.withRate_discount,
      dispersed_minConsumption, dispersed_discount]
    norm_num
    ring
  rw [IncomeFluctuation.withRate_discount, dispersed_discount, hlip, hres]
  rw [lt_div_iff₀ (by linarith [ha.1])]
  nlinarith [log_two_lt, ha.1, ha.2, Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]

/-! ### Uniqueness, the floor, and the equilibrium -/

/-- **A unique stationary distribution at every rate in the interval.** -/
theorem dispersed_existsUnique_uniform {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 20))
    (hrr : dispersed.RateOK r) :
    ∃! μ : ProbabilityMeasure dispersed.State, (dispersed.withRate r hrr).IsStationary μ := by
  obtain ⟨N, hN⟩ := (dispersed.withRate r hrr).exists_exhaust_of_decline (z₀ := 0) (a₀ := 1 / 30)
    (by norm_num) (by norm_num)
    (fun a ha => dispersed_corner_uniform hr hrr ha)
    (fun a ha => dispersed_decline_uniform hr hrr ha)
  exact (dispersed.withRate r hrr).existsUnique_isStationary (z₀ := 0) (N := N)
    (fun z => by simp) hN

theorem dispersed_gain_top : Real.log (40 / 39) < 1 / 16 * Real.log (58 / 37) := by
  have e1 : (16 : ℝ) * Real.log (40 / 39) = Real.log ((40 / 39 : ℝ) ^ (16 : ℕ)) := by
    rw [Real.log_pow]; push_cast; ring
  have hlt : Real.log ((40 / 39 : ℝ) ^ (16 : ℕ)) < Real.log (58 / 37) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [← e1] at hlt
  linarith

/-- **A positive floor under capital supply at the top of the interval**, which is the only place
the equilibrium argument needs one. Taking `h` at `r = 1/20` rather than at `r = 0` — the gain
condition is easier at higher rates — raises the floor from `1/200` to `1/160`. -/
theorem dispersed_floor_top (hrr : dispersed.RateOK (1 / 20))
    (μ : ProbabilityMeasure dispersed.State)
    (hμ : (dispersed.withRate (1 / 20) hrr).IsStationary μ) :
    1 / 160 ≤ dispersed.aggregateCapital μ := by
  have hkey := (dispersed.withRate (1 / 20) hrr).le_aggregateCapital_of_gain
    (dispersed_withRate_positiveConsumption hrr) (by simp) hμ
    (z₁ := 1) (z₀ := 0) (p₀ := 1 / 2) (h := 1 / 40) (by norm_num) (by norm_num) (by norm_num)
    (fun z => by simp) ?_
  · have heq : (dispersed.withRate (1 / 20) hrr).aggregateCapital μ
        = dispersed.aggregateCapital μ := rfl
    rw [heq] at hkey
    norm_num at hkey
    linarith
  · simp only [IncomeFluctuation.withRate_income, IncomeFluctuation.withRate_interest,
      IncomeFluctuation.withRate_discount, IncomeFluctuation.withRate_transitionMatrix,
      dispersed_income_zero, dispersed_income_one, dispersed_discount,
      dispersed_transitionMatrix]
    norm_num
    linarith [dispersed_gain_top]

/-- **An Aiyagari equilibrium.** Every hypothesis discharged: a unique stationary agent
distribution at each rate in `[0, 1/20]`, capital supply bounded below by `1/200` there, and a
Cobb–Douglas firm chosen to meet it. -/
theorem dispersed_exists_equilibrium :
    ∃ A δ : ℝ, 0 < A ∧ 0 < 0 + δ ∧ ∃ r ∈ Icc (0 : ℝ) (1 / 20),
      IsAiyagariEquilibrium
        (dispersed.rateFamily (by norm_num : (0:ℝ) < 1 + 0) (by norm_num : (0:ℝ) ≤ 1 / 20))
        (capitalDemand A δ) r :=
  dispersed.exists_equilibrium_of_uniqueness_and_floor (by norm_num) (by norm_num)
    (fun r hr hrr => dispersed_existsUnique_uniform hr hrr) (by norm_num)
    (fun hrr μ hμ => dispersed_floor_top hrr μ hμ)

/-- **The same equilibrium in implied-rate form**: at the equilibrium rate, the capital the
households hold implies that rate back. -/
theorem dispersed_exists_equilibrium_impliedRate :
    ∃ A δ : ℝ, 0 < A ∧ ∃ r ∈ Icc (0 : ℝ) (1 / 20),
      ∃ μ : ProbabilityMeasure dispersed.State,
        ((dispersed.rateFamily (by norm_num : (0:ℝ) < 1 + 0)
          (by norm_num : (0:ℝ) ≤ 1 / 20)) r).IsStationary μ ∧
        0 < ((dispersed.rateFamily (by norm_num : (0:ℝ) < 1 + 0)
          (by norm_num : (0:ℝ) ≤ 1 / 20)) r).aggregateCapital μ ∧
        impliedRate A δ (((dispersed.rateFamily (by norm_num : (0:ℝ) < 1 + 0)
          (by norm_num : (0:ℝ) ≤ 1 / 20)) r).aggregateCapital μ) = r := by
  obtain ⟨A, δ, hA, hrδ, r, hr, heq⟩ := dispersed_exists_equilibrium
  refine ⟨A, δ, hA, r, hr, ?_⟩
  have hrpos : 0 < r + δ := by linarith [hr.1]
  exact (isAiyagariEquilibrium_iff_impliedRate hA hrpos).mp heq


end LeanEconomics
