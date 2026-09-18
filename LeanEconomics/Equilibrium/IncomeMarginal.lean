/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.AiyagariUniqueness

/-!
# The income marginal of a stationary distribution, and the mean-income ceiling

The minimal-MPC ceiling on capital supply, `(1-κ) · maxIncome / (1 - (1-κ)R)`, pays for its
simplicity with `maxIncome`: it bounds every household's income by the highest state. But the
ceiling comes from integrating `a' ≤ (1-κ)(y + R a)` against the stationary distribution, and
the integral of `y` is the MEAN income under the distribution's income marginal — which is the
income chain's own invariant distribution, and so a primitive of the earnings process, not of
the equilibrium.

Three facts make that precise. `integral_incomeFn` writes the integral of any function of the
income state as a finite sum against the income marginal `incomeMass μ`. `incomeMass_stationary`
says the marginal of a stationary distribution is invariant for the chain. `invariant_eq_of_reach`
is the finite-chain uniqueness of invariant distributions when some state is reached from
everywhere in one step — the `L¹` contraction by the factor `1 - ε`, `ε` the least one-step
probability of that state. So the mean income in the ceiling is the chain's stationary mean.

For Aiyagari (1994) that mean is one by construction — he scales the endowment so — and the
ceiling becomes `β / (1 - β(1+r))` with no reference to the highest endowment. Against
Cobb--Douglas demand it excludes every rate in `(-δ, -4%]`, for every one of his earnings
processes at once (`aiyagari1994_log_no_equilibrium_below_mean`).
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

/-! ### Invariant distributions of a finite chain -/

/-- **A finite chain with a state reached from everywhere has one invariant distribution.** If
`ε ≤ π z z₀` for all `z`, the chain contracts `L¹` distance between distributions by `1 - ε`:
subtract `ε` from the `z₀` column, the remainder is a non-negative matrix with row sums `1 - ε`
that still maps the difference of two invariant distributions to itself. -/
theorem invariant_eq_of_reach {Z : Type*} [Fintype Z] {π : Z → Z → ℝ}
    (hπ : ∀ z z', 0 ≤ π z z') (hsum : ∀ z, ∑ z', π z z' = 1)
    {z₀ : Z} {ε : ℝ} (hε : 0 < ε) (hreach : ∀ z, ε ≤ π z z₀)
    {p q : Z → ℝ} (hp1 : ∑ z, p z = 1) (hq1 : ∑ z, q z = 1)
    (hp : ∀ z', p z' = ∑ z, p z * π z z') (hq : ∀ z', q z' = ∑ z, q z * π z z') : p = q := by
  classical
  set d : Z → ℝ := fun z => p z - q z with hd
  have hd0 : ∑ z, d z = 0 := by
    simp only [hd, Finset.sum_sub_distrib, hp1, hq1, sub_self]
  have hdinv : ∀ z', d z' = ∑ z, d z * π z z' := by
    intro z'
    simp only [hd]
    rw [hp z', hq z', ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  set π' : Z → Z → ℝ := fun z z' => π z z' - if z' = z₀ then ε else 0 with hπ'
  have hπ'nn : ∀ z z', 0 ≤ π' z z' := by
    intro z z'
    simp only [hπ']
    split_ifs with h
    · subst h; linarith [hreach z]
    · linarith [hπ z z']
  have hπ'sum : ∀ z, ∑ z', π' z z' = 1 - ε := by
    intro z
    simp only [hπ']
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_ite_eq']
    simp
  have hdinv' : ∀ z', d z' = ∑ z, d z * π' z z' := by
    intro z'
    simp only [hπ', mul_sub, Finset.sum_sub_distrib, ← hdinv]
    have : ∑ z, d z * (if z' = z₀ then ε else 0) = (if z' = z₀ then ε else 0) * ∑ z, d z := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => mul_comm _ _
    rw [this, hd0, mul_zero, sub_zero]
  have habs : ∑ z', |d z'| ≤ (1 - ε) * ∑ z, |d z| := by
    calc ∑ z', |d z'| = ∑ z', |∑ z, d z * π' z z'| :=
          Finset.sum_congr rfl fun z' _ => by rw [hdinv' z']
      _ ≤ ∑ z', ∑ z, |d z| * π' z z' := by
          refine Finset.sum_le_sum fun z' _ => ?_
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun z _ => by rw [abs_mul, abs_of_nonneg (hπ'nn z z')]
      _ = ∑ z, |d z| * ∑ z', π' z z' := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]
      _ = (1 - ε) * ∑ z, |d z| := by
          simp_rw [hπ'sum]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => mul_comm _ _
  have hnn : 0 ≤ ∑ z, |d z| := Finset.sum_nonneg fun z _ => abs_nonneg _
  have hsum0 : ∑ z, |d z| = 0 := by nlinarith
  funext z
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun z _ => abs_nonneg (d z)).mp hsum0 z
    (Finset.mem_univ z)
  simp only [hd] at hz
  linarith [abs_eq_zero.mp hz]

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### The income marginal -/

/-- The mass a distribution on the state space puts on income state `z`. -/
noncomputable def incomeMass (μ : ProbabilityMeasure P.State) (z : Z) : ℝ :=
  (μ : Measure P.State).real {s | s.2 = z}

theorem measurableSet_incomeState (z : Z) : MeasurableSet {s : P.State | s.2 = z} :=
  measurable_snd (measurableSet_singleton z)

omit [BorelSpace Z] in
theorem incomeMass_nonneg (μ : ProbabilityMeasure P.State) (z : Z) : 0 ≤ P.incomeMass μ z :=
  measureReal_nonneg

/-- **The integral of a function of the income state** is a finite sum against the marginal. -/
theorem integral_incomeFn (μ : ProbabilityMeasure P.State) (g : Z → ℝ) :
    ∫ s, g s.2 ∂(μ : Measure P.State) = ∑ z, P.incomeMass μ z * g z := by
  classical
  have hpt : ∀ s : P.State,
      g s.2 = ∑ z, ({s : P.State | s.2 = z}.indicator (fun _ => g z)) s := by
    intro s
    rw [Finset.sum_eq_single s.2]
    · simp [Set.indicator]
    · intro z _ hz
      simp [Set.indicator, Ne.symm hz]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [integral_indicator_const (g z) (P.measurableSet_incomeState z), smul_eq_mul]
    rfl
  · intro z _
    exact (integrable_const (g z)).indicator (P.measurableSet_incomeState z)

theorem sum_incomeMass (μ : ProbabilityMeasure P.State) : ∑ z, P.incomeMass μ z = 1 := by
  have h := P.integral_incomeFn μ (fun _ => 1)
  have h1 : ∫ _s : P.State, (1 : ℝ) ∂(μ : Measure P.State) = 1 := by simp
  rw [h1] at h
  simpa using h.symm

/-- **The income marginal of a stationary distribution is invariant for the chain.** -/
theorem incomeMass_stationary {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) (z' : Z) :
    P.incomeMass μ z' = ∑ z, P.incomeMass μ z * P.transitionMatrix z z' := by
  classical
  set h : P.State →ᵇ ℝ := mkOfCompact
    ⟨fun s => if s.2 = z' then (1 : ℝ) else 0,
      (continuous_of_discreteTopology (f := fun z : Z => if z = z' then (1 : ℝ) else 0)).comp
        continuous_snd⟩ with hhdef
  have hh : ∀ s : P.State, h s = if s.2 = z' then (1 : ℝ) else 0 := fun s => rfl
  have hstat : ∫ s, h s ∂(μ : Measure P.State) = ∫ s, P.markovOp h s ∂(μ : Measure P.State) := by
    calc ∫ s, h s ∂(μ : Measure P.State)
        = ∫ s, h s ∂((P.pushProb μ : ProbabilityMeasure P.State) : Measure P.State) := by
          rw [hμ]
      _ = ∫ s, P.markovOp h s ∂(μ : Measure P.State) := by rw [coe_pushProb, P.integral_push]
  have hmk : ∀ s : P.State, P.markovOp h s = P.transitionMatrix s.2 z' := by
    intro s
    rw [markovOp_apply]
    simp [prob, nextState, hh]
  have hl : ∫ s, h s ∂(μ : Measure P.State) = P.incomeMass μ z' := by
    have := P.integral_incomeFn μ (fun z => if z = z' then (1 : ℝ) else 0)
    simp only [hh]
    rw [this]
    simp
  have hr : ∫ s, P.markovOp h s ∂(μ : Measure P.State)
      = ∑ z, P.incomeMass μ z * P.transitionMatrix z z' := by
    simp_rw [hmk]
    exact P.integral_incomeFn μ (fun z => P.transitionMatrix z z')
  rw [← hl, hstat, hr]

/-! ### The mean-income ceiling -/

/-- **The capital ceiling with mean income in place of the highest income.** -/
theorem aggregateCapital_le_of_consumption_bound_mean {μ : ProbabilityMeasure P.State}
    (hμ : P.IsStationary μ) {ε : ℝ} (hε1 : ε ≤ 1)
    (hlt : (1 - ε) * (1 + P.interest) < 1)
    (hlb : ∀ (z : Z), ∀ a ∈ Icc (0 : ℝ) assetCap, ε * P.resources (a, z) ≤ P.consumptionFn z a) :
    P.aggregateCapital μ ≤ (1 - ε) * (∑ z, P.incomeMass μ z * P.income z)
      / (1 - (1 - ε) * (1 + P.interest)) := by
  have hε0 : (0 : ℝ) ≤ 1 - ε := by linarith
  have hr : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  set K : ℝ := P.aggregateCapital μ with hKdef
  have hK : K = ∫ s, P.policyCoord s ∂(μ : Measure P.State) :=
    P.aggregateCapital_eq_integral_policy hμ
  have hA : ∫ s, P.assetCoord s ∂(μ : Measure P.State) = K := rfl
  have hinc_int : Integrable (fun s : P.State => P.income s.2) (μ : Measure P.State) :=
    ((continuous_of_discreteTopology (f := P.income)).comp
      continuous_snd).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound : ∀ s : P.State, P.policyCoord s
      ≤ (1 - ε) * P.income s.2 + (1 - ε) * (1 + P.interest) * P.assetCoord s := by
    intro s
    have hmem : ((s.1 : ℝ)) ∈ Icc (0 : ℝ) assetCap := s.1.2
    have hlbs := hlb s.2 _ hmem
    have hres : P.resources ((s.1 : ℝ), s.2) = P.income s.2 + (1 + P.interest) * (s.1 : ℝ) := by
      simp only [resources, max_eq_right hmem.1]
    have hpol : P.policyCoord s
        = P.resources ((s.1 : ℝ), s.2) - P.consumptionFn s.2 (s.1 : ℝ) := by
      simp only [policyCoord_apply, incl, consumptionFn, consumption]; ring
    have hacoord : P.assetCoord s = (s.1 : ℝ) := rfl
    rw [hpol, hres, hacoord]
    rw [hres] at hlbs
    nlinarith [hlbs, hε0, hr, hmem.1]
  have hsplit : ∫ s, ((1 - ε) * P.income s.2 + (1 - ε) * (1 + P.interest) * P.assetCoord s)
        ∂(μ : Measure P.State)
      = (1 - ε) * (∑ z, P.incomeMass μ z * P.income z) + (1 - ε) * (1 + P.interest) * K := by
    rw [integral_add (hinc_int.const_mul _) ((P.assetCoord.integrable _).const_mul _),
      integral_const_mul, integral_const_mul, P.integral_incomeFn, hA]
  have hint : ∫ s, P.policyCoord s ∂(μ : Measure P.State)
      ≤ (1 - ε) * (∑ z, P.incomeMass μ z * P.income z) + (1 - ε) * (1 + P.interest) * K := by
    rw [← hsplit]
    exact integral_mono (P.policyCoord.integrable _)
      ((hinc_int.const_mul _).add ((P.assetCoord.integrable _).const_mul _)) hbound
  rw [← hK] at hint
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hint]

/-- **The log capital ceiling with mean income**, at any admissible rate with `β(1+r) < 1`. -/
theorem log_aggregateCapital_le_mean {r : ℝ} (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ)) (hβ1 : (P.discount : ℝ) < 1) (hrr : P.RateOK r)
    (hβR : (P.discount : ℝ) * (1 + r) < 1)
    (hthr : (P.discount : ℝ) * (P.maxIncome + (1 + r) * assetCap) < assetCap)
    {μ : ProbabilityMeasure P.State} (hμ : (P.withRate r hrr).IsStationary μ) :
    P.aggregateCapital μ ≤ (P.discount : ℝ) * (∑ z, P.incomeMass μ z * P.income z)
      / (1 - (P.discount : ℝ) * (1 + r)) := by
  have hκ : 1 - (P.withRate r hrr).minMPC 1 = (P.discount : ℝ) := by
    rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; ring
  have hκpos : 0 < (P.withRate r hrr).minMPC 1 := by
    rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; linarith
  have hβR' : ((P.withRate r hrr).discount : ℝ) * (1 + (P.withRate r hrr).interest) < 1 := hβR
  have hthr' : (1 - (P.withRate r hrr).minMPC 1)
      * ((P.withRate r hrr).maxIncome + (1 + (P.withRate r hrr).interest) * assetCap)
      < assetCap := by
    rw [hκ]; exact hthr
  have hpc : (P.withRate r hrr).PositiveConsumptionAll :=
    (P.withRate r hrr).positiveConsumptionAll_of_unbounded hunb
  have hposIt : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < (P.withRate r hrr).consumptionFnOf
        (((P.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a :=
    fun n z a ha => hpc _ ((P.withRate r hrr).concaveSlices_iterate_zero n) z a ha
  have hslackIt : ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r hrr).policyOf
        (((P.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (x, z) < assetCap :=
    fun n x hx z => ((P.withRate r hrr).crra_minMPC_of_cap one_pos hu rfl hκpos hβ hβR'
      hposIt hthr' n).2 x hx z
  have hkey := (P.withRate r hrr).aggregateCapital_le_of_consumption_bound_mean hμ
    (IncomeFluctuation.minMPC_le_one (P := P.withRate r hrr) one_pos hβ)
    (by
      rw [IncomeFluctuation.one_sub_minMPC_mul (P := P.withRate r hrr)]
      exact IncomeFluctuation.patience_lt_one (P := P.withRate r hrr) one_pos hβR')
    (fun z a ha => (P.withRate r hrr).crra_minMPC_mul_le_consumptionFn one_pos hu rfl hκpos hβ
      hβR' hposIt hslackIt z ha)
  rw [hκ] at hkey
  exact hkey

/-- **Aiyagari (1994) at `μ = 1`: no equilibrium on `(-δ, -4%]`, for every one of his earnings
processes.** The endowment is scaled so that its stationary mean is one; the chain reaches some
state from everywhere in one step (a Tauchen chain reaches its lowest state so). Then the
stationary distribution's income marginal is the chain's invariant distribution, mean income is
one, and the ceiling `β/(1 - β(1+r))` is below Cobb--Douglas demand for `r ≤ -1/25`. No
hypothesis on the highest endowment. -/
theorem aiyagari1994_log_no_equilibrium_below_mean {r : ℝ}
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded) (hβ : (P.discount : ℝ) = 24 / 25)
    (hcap : 24 * P.maxIncome < assetCap) (hr : r ∈ Ioc (-2 / 25 : ℝ) (-1 / 25))
    (hrr : P.RateOK r) {z₀ : Z} (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    {p : Z → ℝ} (hp1 : ∑ z, p z = 1) (hp : ∀ z', p z' = ∑ z, p z * P.transitionMatrix z z')
    (hmean : ∑ z, p z * P.income z ≤ 1)
    {μ : ProbabilityMeasure P.State} (hμ : (P.withRate r hrr).IsStationary μ) :
    P.aggregateCapital μ ≠ normalisedDemand (9 / 25) (2 / 25) r := by
  classical
  intro heq
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hmax : 0 < P.maxIncome := lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxIncome
  -- the least one-step probability of `z₀`
  obtain ⟨z₁, -, hz₁⟩ := Finset.exists_min_image Finset.univ
    (fun z => P.transitionMatrix z z₀) Finset.univ_nonempty
  have hε : 0 < P.transitionMatrix z₁ z₀ := hreach z₁
  -- the income marginal is `p`
  have hmarg : P.incomeMass μ = p :=
    invariant_eq_of_reach P.transitionMatrix_nonneg P.transitionMatrix_sum hε
      (fun z => hz₁ z (Finset.mem_univ z)) (P.sum_incomeMass μ) hp1
      (fun z' => (P.withRate r hrr).incomeMass_stationary hμ z') hp
  -- the ceiling
  have hceil := P.log_aggregateCapital_le_mean hu hunb (by rw [hβ]; norm_num)
    (by rw [hβ]; norm_num) hrr (by rw [hβ]; linarith [hr.2])
    (by
      rw [hβ]
      have := mul_nonneg (neg_nonneg.mpr (le_trans hr.2 (by norm_num))) hcap0
      nlinarith)
    hμ
  rw [hmarg, hβ] at hceil
  have hden : (0 : ℝ) < 1 - 24 / 25 * (1 + r) := by linarith [hr.2]
  have hceil' : P.aggregateCapital μ ≤ 24 / 25 / (1 - 24 / 25 * (1 + r)) := by
    refine le_trans hceil (div_le_div_of_nonneg_right ?_ hden.le)
    nlinarith [hmean]
  -- against demand
  have hD : 24 / 25 / (1 - 24 / 25 * (1 + r)) < normalisedDemand (9 / 25) (2 / 25) r := by
    simp only [normalisedDemand]
    have h2 : (0 : ℝ) < (1 - 9 / 25) * (r + 2 / 25) := by nlinarith [hr.1]
    rw [div_lt_div_iff₀ hden h2]
    nlinarith [hr.2]
  linarith

end IncomeFluctuation

end LeanEconomics
