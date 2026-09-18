/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Integral
import LeanEconomics.Equilibrium.IncomeMarginal
import LeanEconomics.Equilibrium.RateRange

/-!
# Localising the equilibrium rate, for any risk aversion

Two bounds on capital supply that need nothing about the curvature of utility beyond what the
Euler inequality already carries, so that they apply at Aiyagari's `μ = 3` and `μ = 5` as well
as at `μ = 1`.

**Below zero: the budget ceiling.** Saving is at most cash on hand, `a' ≤ y + R a`, because
consumption is non-negative. Integrated against a stationary distribution this is
`K ≤ Ȳ + R K`, so at a negative rate `K ≤ Ȳ/(-r)` (`aggregateCapital_le_of_neg_rate`) — the
rigorous form of Walsh and Young's zero-consumption supply schedule `w/(δ - r)`. Against
Cobb--Douglas demand `α/((1-α)(r+δ))` it excludes every rate below `-(1-α)δ`, which at
Aiyagari's numbers is `-5.12%`; the theorem is stated for `r ≤ -5.2%`
(`aiyagari1994_no_equilibrium_of_budget`), for ANY period utility. Walsh and Young's third,
low-rate equilibrium sits, in the zero-consumption limit, exactly at `-(1-α)δ`, so this bound is
sharp against the branch they find and says it cannot occur below that point.

**Above the time-preference rate: the CRRA floor.** `integral_marginal_le_of_patient` is stated
for any marginal utility; with `u' = x^{-n}` and Jensen's inequality for the convex `x ↦ x^{-n}`,
`(1 - 1/βR)^{1/n} · (minIncome + r·assetCap) ≤ Ȳ + r K` (`crra_aggregateCapital_ge_of_patient`).
The mean income is exact here — consumption integrates to `Ȳ + r K` under stationarity — and
the floor is far stronger than at `n = 1`: with `βR = 1 + η` the factor is of order `η^{1/n}`,
so at `n = 3` a cap of a few thousand times income already puts the floor above demand for
every rate more than a thousandth above `λ`.

Together: for Aiyagari's calibration at any `μ ∈ {1, 3, 5}`, every equilibrium rate lies in
`(-5.2%, λ + ε)`.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### The budget ceiling at negative rates -/

/-- **Capital supply at a negative rate is at most mean income over the rate**, for any
utility: `a' ≤ y + R a` integrated against a stationary distribution. -/
theorem aggregateCapital_le_of_neg_rate (hr : P.interest < 0) {μ : ProbabilityMeasure P.State}
    (hμ : P.IsStationary μ) :
    P.aggregateCapital μ ≤ (∑ z, P.incomeMass μ z * P.income z) / (-P.interest) := by
  have h := P.aggregateCapital_le_of_consumption_bound_mean hμ (ε := 0) (by norm_num)
    (by linarith) (fun z a _ => by
      rw [zero_mul]
      change (0 : ℝ) ≤ P.consumption (a, z) (P.policy (a, z))
      exact P.consumption_nonneg (P.policy_mem _))
  rw [show (1 : ℝ) - (1 - 0) * (1 + P.interest) = -P.interest by ring, sub_zero, one_mul] at h
  exact h

/-- **Aiyagari (1994), any risk aversion: no equilibrium on `(-δ, -5.2%]`.** Nothing about
utility is used. The earnings process is normalised to stationary mean at most one and has a
state reached from everywhere in one step. -/
theorem aiyagari1994_no_equilibrium_of_budget {r : ℝ} (hr : r ∈ Ioc (-2 / 25 : ℝ) (-13 / 250))
    (hrr : P.RateOK r) {z₀ : Z} (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    {p : Z → ℝ} (hp1 : ∑ z, p z = 1) (hp : ∀ z', p z' = ∑ z, p z * P.transitionMatrix z z')
    (hmean : ∑ z, p z * P.income z ≤ 1)
    {μ : ProbabilityMeasure P.State} (hμ : (P.withRate r hrr).IsStationary μ) :
    P.aggregateCapital μ ≠ normalisedDemand (9 / 25) (2 / 25) r := by
  classical
  intro heq
  obtain ⟨z₁, -, hz₁⟩ := Finset.exists_min_image Finset.univ
    (fun z => P.transitionMatrix z z₀) Finset.univ_nonempty
  have hmarg : P.incomeMass μ = p :=
    invariant_eq_of_reach P.transitionMatrix_nonneg P.transitionMatrix_sum (hreach z₁)
      (fun z => hz₁ z (Finset.mem_univ z)) (P.sum_incomeMass μ) hp1
      (fun z' => (P.withRate r hrr).incomeMass_stationary hμ z') hp
  have hneg : 0 < -r := by linarith [hr.2]
  have hceil := (P.withRate r hrr).aggregateCapital_le_of_neg_rate
    (by rw [IncomeFluctuation.withRate_interest]; linarith [hr.2]) hμ
  rw [IncomeFluctuation.withRate_interest] at hceil
  change P.aggregateCapital μ ≤ (∑ z, P.incomeMass μ z * P.income z) / (-r) at hceil
  rw [hmarg] at hceil
  have hceil' : P.aggregateCapital μ ≤ 1 / (-r) :=
    le_trans hceil (div_le_div_of_nonneg_right hmean hneg.le)
  have hD : 1 / (-r) < normalisedDemand (9 / 25) (2 / 25) r := by
    simp only [normalisedDemand]
    have h2 : (0 : ℝ) < (1 - 9 / 25) * (r + 2 / 25) := by nlinarith [hr.1]
    rw [div_lt_div_iff₀ hneg h2]
    nlinarith [hr.2]
  linarith

/-! ### The CRRA floor above the time-preference rate -/

/-- **Capital supply under patience, CRRA with integer risk aversion `n`**: Jensen's inequality
for `x ↦ x^{-n}` turns the small integrated marginal utility into a floor on mean consumption,
which is `Ȳ + r K` under stationarity. -/
theorem crra_aggregateCapital_ge_of_patient {n : ℕ} (hn : 0 < n) (hu : P.u = crraUtility n)
    (hunb : P.Unbounded) (hβR : 1 < (P.discount : ℝ) * (1 + P.interest)) (hint : 0 ≤ P.interest)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    (1 - 1 / ((P.discount : ℝ) * (1 + P.interest))) ^ ((n : ℝ)⁻¹)
        * (P.minIncome + P.interest * assetCap)
      ≤ (∑ z, P.incomeMass μ z * P.income z) + P.interest * P.aggregateCapital μ := by
  classical
  have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hpc : P.PositiveConsumption := P.positiveConsumption_of_unbounded hunb
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := by linarith
  have hθ : (0 : ℝ) < 1 - 1 / ((P.discount : ℝ) * (1 + P.interest)) := by
    rw [sub_pos, div_lt_one hβR0]; exact hβR
  set θ : ℝ := 1 - 1 / ((P.discount : ℝ) * (1 + P.interest)) with hθdef
  set M : ℝ := P.minIncome + P.interest * assetCap with hMdef
  have hM : 0 < M := by
    have := P.minIncome_pos
    have := P.assetCap_nonneg
    rw [hMdef]; nlinarith
  -- marginal utility as an integer power
  set du : ℝ → ℝ := fun x => x ^ (-(n : ℤ)) with hdudef
  have hdu_eq : ∀ x : ℝ, du x = x ^ (-(n : ℝ)) := by
    intro x
    simp only [hdudef]
    rw [show (-(n : ℝ)) = ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
  have hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c := by
    intro c hc
    rw [hu, hdu_eq c]
    exact hasDerivAt_crraUtility (n : ℝ) hc
  have hanti : AntitoneOn du (Ioi (0 : ℝ)) := by
    intro x hx _ _ hxy
    simp only [hdudef, zpow_neg, zpow_natCast]
    exact inv_anti₀ (pow_pos hx n) (pow_le_pow_left₀ hx.le hxy n)
  have hdupos : ∀ c : ℝ, 0 < c → 0 < du c := fun c hc => zpow_pos hc _
  have hdcont : ContinuousOn du (Ioi (0 : ℝ)) :=
    continuousOn_id.zpow₀ _ (fun x hx => Or.inl (ne_of_gt hx))
  have hkey := P.integral_marginal_le_of_patient hβR hint hderiv hanti hdupos hdcont hpc hμ
  -- consumption integrates to mean income plus interest on capital
  set K : ℝ := P.aggregateCapital μ with hKdef
  have hcs : ∀ s : P.State, P.consumptionFn s.2 (s.1 : ℝ)
      = P.income s.2 + (1 + P.interest) * P.assetCoord s - P.policyCoord s := by
    intro s
    have hres : P.resources ((s.1 : ℝ), s.2) = P.income s.2 + (1 + P.interest) * (s.1 : ℝ) := by
      simp only [resources, max_eq_right s.1.2.1]
    simp only [consumptionFn, consumption, hres, policyCoord_apply, incl, assetCoord_apply]
  have hinc_int : Integrable (fun s : P.State => P.income s.2) (μ : Measure P.State) :=
    ((continuous_of_discreteTopology (f := P.income)).comp
      continuous_snd).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfg : Integrable (fun s : P.State => P.income s.2 + (1 + P.interest) * P.assetCoord s)
      (μ : Measure P.State) :=
    hinc_int.add ((P.assetCoord.integrable _).const_mul _)
  have hX : ∫ s, P.consumptionFn s.2 (s.1 : ℝ) ∂(μ : Measure P.State)
      = (∑ z, P.incomeMass μ z * P.income z) + P.interest * K := by
    simp_rw [hcs]
    rw [integral_sub (f := fun s => P.income s.2 + (1 + P.interest) * P.assetCoord s)
        (g := fun s => P.policyCoord s) hfg (P.policyCoord.integrable _),
      integral_add (f := fun s => P.income s.2) (g := fun s => (1 + P.interest) * P.assetCoord s)
        hinc_int ((P.assetCoord.integrable _).const_mul _),
      integral_const_mul, P.integral_incomeFn, ← P.aggregateCapital_eq_integral_policy hμ,
      ← hKdef, show ∫ s, P.assetCoord s ∂(μ : Measure P.State) = K from rfl]
    ring
  set X : ℝ := ∫ s, P.consumptionFn s.2 (s.1 : ℝ) ∂(μ : Measure P.State) with hXdef
  -- consumption is bounded below on the compact state space
  obtain ⟨s₀, -, hs₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    P.continuous_consumptionState.continuousOn
  set cmin : ℝ := P.consumptionFn s₀.2 (s₀.1 : ℝ) with hcmin
  have hcmin_pos : 0 < cmin := P.consumptionFn_pos hpc s₀.1.2 s₀.2
  have hmin : ∀ s : P.State, cmin ≤ P.consumptionFn s.2 (s.1 : ℝ) := fun s => hs₀ (mem_univ s)
  -- Jensen for the convex `x ↦ x^(-n)` on `[cmin, ∞)`
  have hconv : ConvexOn ℝ (Ici cmin) du :=
    (convexOn_zpow (-(n : ℤ))).subset (Ici_subset_Ioi.mpr hcmin_pos) (convex_Ici _)
  have hc_int : Integrable (fun s : P.State => P.consumptionFn s.2 (s.1 : ℝ))
      (μ : Measure P.State) :=
    P.continuous_consumptionState.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hdc_int : Integrable (fun s : P.State => du (P.consumptionFn s.2 (s.1 : ℝ)))
      (μ : Measure P.State) := by
    have hcont : Continuous fun s : P.State => du (P.consumptionFn s.2 (s.1 : ℝ)) :=
      hdcont.comp_continuous P.continuous_consumptionState
        fun s => mem_Ioi.mpr (P.consumptionFn_pos hpc s.1.2 s.2)
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hjensen : du X ≤ ∫ s, du (P.consumptionFn s.2 (s.1 : ℝ)) ∂(μ : Measure P.State) :=
    hconv.map_integral_le (hdcont.mono (Ici_subset_Ioi.mpr hcmin_pos)) isClosed_Ici
      (Eventually.of_forall fun s => hmin s) hc_int hdc_int
  have hXpos : 0 < X := by
    have : cmin ≤ X := by
      rw [hXdef]
      calc cmin = ∫ _s, cmin ∂(μ : Measure P.State) := by simp
        _ ≤ _ := integral_mono (integrable_const _) hc_int hmin
    linarith
  -- assemble: `θ · X^(-n) ≤ θ ∫ c^(-n) ≤ M^(-n)`
  have hcomb : θ * du X ≤ du M := le_trans (mul_le_mul_of_nonneg_left hjensen hθ.le) hkey
  have h1 : θ * M ^ n ≤ X ^ n := by
    simp only [hdudef, zpow_neg, zpow_natCast] at hcomb
    rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos hXpos n), inv_mul_eq_div,
      le_div_iff₀ (pow_pos hM n)] at hcomb
    linarith
  have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
  rw [Real.mul_rpow hθ.le (pow_nonneg hM.le n), Real.pow_rpow_inv_natCast hM.le hn.ne',
    Real.pow_rpow_inv_natCast hXpos.le hn.ne'] at h2
  rw [← hX]
  exact h2

/-- **No equilibrium above the time-preference rate, CRRA `n`, with income risk**: once the
floor exceeds `1 + r·D(r)` (mean income one), the market cannot clear at demand `D`. -/
theorem crra_no_equilibrium_of_patient_mean {n : ℕ} (hn : 0 < n) (hu : P.u = crraUtility n)
    (hunb : P.Unbounded) {r : ℝ} (hrr : P.RateOK r) (hβR : 1 < (P.discount : ℝ) * (1 + r))
    (hint : 0 ≤ r) {z₀ : Z} (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    {p : Z → ℝ} (hp1 : ∑ z, p z = 1) (hp : ∀ z', p z' = ∑ z, p z * P.transitionMatrix z z')
    (hmean : ∑ z, p z * P.income z ≤ 1) {D : ℝ}
    (hD : 1 + r * D < (1 - 1 / ((P.discount : ℝ) * (1 + r))) ^ ((n : ℝ)⁻¹)
      * (P.minIncome + r * assetCap))
    {μ : ProbabilityMeasure P.State} (hμ : (P.withRate r hrr).IsStationary μ) :
    P.aggregateCapital μ ≠ D := by
  classical
  intro heq
  obtain ⟨z₁, -, hz₁⟩ := Finset.exists_min_image Finset.univ
    (fun z => P.transitionMatrix z z₀) Finset.univ_nonempty
  have hmarg : P.incomeMass μ = p :=
    invariant_eq_of_reach P.transitionMatrix_nonneg P.transitionMatrix_sum (hreach z₁)
      (fun z => hz₁ z (Finset.mem_univ z)) (P.sum_incomeMass μ) hp1
      (fun z' => (P.withRate r hrr).incomeMass_stationary hμ z') hp
  have hfloor := (P.withRate r hrr).crra_aggregateCapital_ge_of_patient hn hu hunb
    (by simpa using hβR) (by simpa using hint) hμ
  simp only [IncomeFluctuation.withRate_discount, IncomeFluctuation.withRate_interest,
    IncomeFluctuation.withRate_minIncome] at hfloor
  change (1 - 1 / ((P.discount : ℝ) * (1 + r))) ^ ((n : ℝ)⁻¹) * (P.minIncome + r * assetCap)
    ≤ (∑ z, P.incomeMass μ z * P.income z) + r * P.aggregateCapital μ at hfloor
  rw [hmarg, heq] at hfloor
  linarith

end IncomeFluctuation

end LeanEconomics
