/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.SignChange
import LeanEconomics.Equilibrium.UniquenessClass

/-!
# The minimal MPC at a witness

`crra_minMPC_mul_le_consumptionFn` bounds the consumption share below by `κ = 1 - Þ/R`. This file
evaluates it at `nearLog`, where `β = 1/8` and `γ = 15/16`, so

  `Þ = (β(1+r))^(16/15) ≈ 0.109`  and  `1 - κ ≤ 111/1000`

uniformly over the rate interval `[0, 1/200]`. The consequence is a ceiling on capital supply of
`1/8`, in place of the asset cap `1`.

That matters for the equilibrium: the asset cap is bookkeeping, imposed to make the state space
compact, and it appears in the technology band of `exists_equilibrium_of_technology` as the number
demand has to clear at the bottom of the rate interval. Replacing it by a number the calibration
determines makes the band eight times wider.

The two hypotheses of the bound — consumption positive at each iterate, and the saving cap slack
there — are exactly `Calibrated.positive_iterate` and `Calibrated.policyOf_iterate_lt_cap`, so
`nearLog_calibrated` supplies them.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

open IncomeFluctuation

/-- **`nearLog`'s minimal MPC is positive** on the rate band, from return impatience. -/
theorem nearLog_minMPC_pos {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200)) (hrr : nearLog.RateOK r) :
    0 < (nearLog.withRate r hrr).minMPC (15 / 16) :=
  IncomeFluctuation.minMPC_pos (P := nearLog.withRate r hrr) (by norm_num) hr.1
    (by
      rw [show ((nearLog.withRate r hrr).discount : ℝ) = 1 / 8 from rfl,
        show (nearLog.withRate r hrr).interest = r from rfl]
      linarith [hr.2])

/-- **The minimal-MPC bound for `nearLog`.** -/
theorem nearLog_minMPC_mul_le_consumptionFn {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : nearLog.RateOK r) (z : Fin 2) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    (nearLog.withRate r hrr).minMPC (15 / 16) * (nearLog.withRate r hrr).resources (a, z)
      ≤ (nearLog.withRate r hrr).consumptionFn z a :=
  (nearLog.withRate r hrr).crra_minMPC_mul_le_consumptionFn (by norm_num) rfl rfl
    (nearLog_minMPC_pos hr hrr)
    (by rw [show ((nearLog.withRate r hrr).discount : ℝ) = 1 / 8 from rfl]; norm_num)
    (by
      rw [show ((nearLog.withRate r hrr).discount : ℝ) = 1 / 8 from rfl,
        show (nearLog.withRate r hrr).interest = r from rfl]
      linarith [hr.2])
    (fun n z' b hb => nearLog_calibrated.positive_iterate hr hrr hr hrr n hb z')
    (fun n b hb z' => nearLog_calibrated.policyOf_iterate_lt_cap hr hrr hr hrr n hb z') z ha

/-- **Capital supply at `nearLog` never exceeds `1/8`** — eight times better than the asset cap,
and a number the calibration determines rather than one imposed for compactness. -/
theorem nearLog_aggregateCapital_le {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : nearLog.RateOK r) {μ : ProbabilityMeasure nearLog.State}
    (hμ : (nearLog.withRate r hrr).IsStationary μ) :
    nearLog.aggregateCapital μ ≤ 1 / 8 := by
  have hkey := (nearLog.withRate r hrr).crra_aggregateCapital_le_of_minMPC (γ := 15 / 16)
    (by norm_num) rfl (nearLog_minMPC_pos hr hrr)
    (by rw [show ((nearLog.withRate r hrr).discount : ℝ) = 1 / 8 from rfl]; norm_num)
    (by
      rw [show ((nearLog.withRate r hrr).discount : ℝ) = 1 / 8 from rfl,
        show (nearLog.withRate r hrr).interest = r from rfl]
      linarith [hr.2])
    (fun n z' b hb => nearLog_calibrated.positive_iterate hr hrr hr hrr n hb z')
    (fun n b hb z' => nearLog_calibrated.policyOf_iterate_lt_cap hr hrr hr hrr n hb z') hμ
  have heq : (nearLog.withRate r hrr).aggregateCapital μ = nearLog.aggregateCapital μ := rfl
  rw [heq] at hkey
  have hone : 1 - (nearLog.withRate r hrr).minMPC (15 / 16) ≤ 111 / 1000 :=
    nearLog_one_sub_minMPC_le hr hrr
  have hzero : (0 : ℝ) ≤ 1 - (nearLog.withRate r hrr).minMPC (15 / 16) := by
    have := IncomeFluctuation.minMPC_le_one (P := nearLog.withRate r hrr) (γ := 15 / 16)
      (by norm_num)
      (by rw [show ((nearLog.withRate r hrr).discount : ℝ) = 1 / 8 from rfl]; norm_num)
    linarith
  have hM : (nearLog.withRate r hrr).maxIncome = 1 := rfl
  have hint : (nearLog.withRate r hrr).interest = r := rfl
  rw [hM, hint] at hkey
  set x : ℝ := 1 - (nearLog.withRate r hrr).minMPC (15 / 16) with hxdef
  have hden : (0 : ℝ) < 1 - x * (1 + r) := by nlinarith [hr.1, hr.2]
  rw [le_div_iff₀ hden] at hkey
  nlinarith [hkey, hone, hzero, hr.1, hr.2]

/-- **An equilibrium for `nearLog` at a technology five times less extreme.** The ceiling `1/8`
in place of the asset cap `1` widens the band of admissible `A` by a factor of `√8`, and with it
the admissible depreciation: `δ = 1/2000` against the `1/10000` the asset-cap version allowed.

The two inequalities are the same as before — `4δ²·M ≤ A²` clears the ceiling at the bottom of
the interval and `A² ≤ 4(1/200+δ)²·m` falls under the floor at the top — but with `M = 1/8`
rather than `M = 1`. -/
theorem nearLog_exists_equilibrium_of_technology' :
    ∃ r ∈ Icc (0 : ℝ) (1 / 200),
      IsAiyagariEquilibrium
        (nearLog.rateFamily (by norm_num : (0:ℝ) < 1 + 0) (by norm_num : (0:ℝ) ≤ 1 / 200))
        (capitalDemand (1 / 2000) (1 / 2000)) r :=
  nearLog.exists_equilibrium_of_ceiling_and_floor (by norm_num) (by norm_num)
    (fun r hr hrr => nearLog_existsUnique_uniform hr hrr)
    (M := 1 / 8) (fun hrlo' μ hμ => nearLog_aggregateCapital_le (by norm_num) hrlo' hμ)
    (fun hrr μ hμ => nearLog_floor_top hrr μ hμ)
    (1 / 2000) (1 / 2000) (by norm_num)
    (le_capitalDemand_of_sq (by norm_num) (by norm_num))
    (capitalDemand_le_of_sq (by norm_num) (by norm_num))

/-! ### Exhaustion without the income process

`nearLog_calibrated.exhausts` gets the decline half from Açıkgöz Proposition 4, which compares
income states and therefore needs `IidIncome`. The minimal-MPC route compares nothing, so the
same data comes out with no assumption about the transition matrix at all — only the corner
condition and one threshold inequality.

At these numbers the threshold is `0.00111 < 0.0178`, clear by a factor of sixteen: the
household's consumption share is so high that assets fall from just above `1/800`, well below the
`1/50` the corner condition already covers. -/

/-- **The Doeblin exhaustion data for `nearLog`, with nothing assumed about the income process.**
-/
theorem nearLog_exists_exhaust_of_minMPC {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : nearLog.RateOK r) :
    ∃ N : ℕ, ((nearLog.withRate r hrr).gBad 0)^[N] (nearLog.withRate r hrr).topState
      = (nearLog.withRate r hrr).botState := by
  have hone : 1 - (nearLog.withRate r hrr).minMPC (15 / 16) ≤ 111 / 1000 :=
    nearLog_one_sub_minMPC_le hr hrr
  have hzero : (0 : ℝ) ≤ 1 - (nearLog.withRate r hrr).minMPC (15 / 16) := by
    have := IncomeFluctuation.minMPC_le_one (P := nearLog.withRate r hrr) (γ := 15 / 16)
      (by norm_num)
      (by rw [show ((nearLog.withRate r hrr).discount : ℝ) = 1 / 8 from rfl]; norm_num)
    linarith
  refine (nearLog.withRate r hrr).crra_exists_exhaust_of_minMPC (γ := 15 / 16) (z₀ := 0)
    (a₀ := 1 / 50) (by norm_num) rfl rfl (nearLog_minMPC_pos hr hrr)
    (by rw [show ((nearLog.withRate r hrr).discount : ℝ) = 1 / 8 from rfl]; norm_num)
    (by
      rw [show ((nearLog.withRate r hrr).discount : ℝ) = 1 / 8 from rfl,
        show (nearLog.withRate r hrr).interest = r from rfl]
      linarith [hr.2])
    (fun n z' b hb => nearLog_calibrated.positive_iterate hr hrr hr hrr n hb z')
    (fun n b hb z' => nearLog_calibrated.policyOf_iterate_lt_cap hr hrr hr hrr n hb z')
    (by norm_num) (by norm_num) (fun a ha => nearLog_corner_uniform hr hrr ha) ?_
  rw [show (nearLog.withRate r hrr).income 0 = 1 / 100 from rfl,
    show (nearLog.withRate r hrr).interest = r from rfl]
  nlinarith [hone, hzero, hr.1, hr.2]

/-- **A unique stationary distribution for `nearLog`, with the income process assumed only to
reach the worst state.** The class proves the same thing, but its route to the decline half runs
through Açıkgöz Proposition 4 and so needs the income process to be iid. Here the only thing
asked of the transition matrix is `0 < transitionMatrix z 0` — that the worst income state is
reachable from everywhere, which is what the Doeblin argument itself needs and cannot avoid. -/
theorem nearLog_existsUnique_of_minMPC {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 200))
    (hrr : nearLog.RateOK r) :
    ∃! μ : ProbabilityMeasure nearLog.State, (nearLog.withRate r hrr).IsStationary μ := by
  obtain ⟨N, hN⟩ := nearLog_exists_exhaust_of_minMPC hr hrr
  exact (nearLog.withRate r hrr).existsUnique_isStationary (z₀ := 0) (N := N)
    (fun z => by norm_num) hN

end LeanEconomics
