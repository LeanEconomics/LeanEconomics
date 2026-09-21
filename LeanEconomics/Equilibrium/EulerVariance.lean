/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.LasryLionsIteration
import LeanEconomics.Equilibrium.PositiveCapital

/-!
# The stationary Euler identities: corner slack, and the variance of marginal utility

Two identities hold at every stationary distribution `μ` of a household with cap slack, and both
are exact consequences of the Euler inequality `u'(c) ≥ βR E[u'(c') | s]` and stationarity.

Write `M(s) = u'(c(s))` and `slack(s) = M(s) - βR E[M(s') | s] ≥ 0`, which vanishes at interior
choices. Integrating the Euler identity against `μ`, and using that `∫ E[M(s')|s] dμ = ∫ M dμ`,

  `∫ slack dμ = (1 - βR) ∫ M dμ`   (`integral_slack`):

the corner activity of the population, weighted by the marginal utility it forgoes, is exactly the
impatience rate times average marginal utility. Doing the same with `M²` and the conditional
variance `Var(s) = E[M(s')² | s] - E[M(s') | s]²`,

  `∫ Var dμ ≤ 2 (1 - βR) ‖M‖²`   (`integral_condVar_le`):

the expected conditional variance of next period's marginal utility vanishes as `βR → 1`. With a
borrowing constraint that is the whole precautionary channel: a household at low wealth cannot
smooth an income shock, so its next-period marginal utility varies with the shock, and the
identity says the stationary distribution cannot keep much mass where that happens once the
household is nearly patient.

## What this reduces the existence floor to

`aggregateCapital_ge_of_condVar` turns it into a floor on capital: if every household that saves at
most `A₀` faces conditional variance at least `v₀`, then

  `K(μ) ≥ A₀ (1 - 2(1 - βR)‖M‖² / v₀)`.

So a variance floor at low wealth, uniform as `βR → 1`, gives a capital floor that approaches `A₀`
as `r → λ`, for any `A₀` — the divergence of capital supply at the rate of time preference, in a
form that stays inside the capped model and needs no martingale convergence or uncapped limit.
The variance floor itself is `condVar_ge_pair`: it is at least `min(π₁, π₂)/2` times the squared
gap in marginal utility between two income states at tomorrow's assets. What is NOT proved is a
quantitative gap `u'(c(A, z_min)) - u'(c(A, z_max))` at low `A` uniform in the rate: it needs a
lower bound on consumption of high-income households beyond the minimal-MPC share, which the
present development does not have. That is the remaining input to existence at `μ = 1`.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]

section General

variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem continuous_consumptionFn_state :
    Continuous fun s : P.State => P.consumptionFn s.2 (s.1 : ℝ) := by
  change Continuous fun s : P.State => P.resources (P.incl s) - P.policy (P.incl s)
  exact (P.continuous_resources.comp P.continuous_incl).sub
    (continuous_subtype_val.comp P.continuous_nextAssets)

/-- **Marginal utility of consumption on the region**, as a bounded continuous function. -/
noncomputable def marginalState (du : ℝ → ℝ) (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption) : P.State →ᵇ ℝ :=
  mkOfCompact ⟨fun s => du (P.consumptionFn s.2 (s.1 : ℝ)),
    hdu.comp_continuous P.continuous_consumptionFn_state
      fun s => mem_Ioi.mpr (P.consumptionFn_pos hpc s.1.2 s.2)⟩

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem marginalState_apply (du : ℝ → ℝ) (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption) (s : P.State) :
    P.marginalState du hdu hpc s = du (P.consumptionFn s.2 (s.1 : ℝ)) := rfl

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem markovOp_marginalState (du : ℝ → ℝ) (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption) (s : P.State) :
    P.markovOp (P.marginalState du hdu hpc) s
      = ∑ z', P.transitionMatrix s.2 z' * du (P.consumptionFn z' (P.policy (P.incl s))) := rfl

/-- **The corner slack**: marginal utility today less the discounted expected marginal utility
tomorrow. Nonnegative by the Euler inequality; zero at interior choices. -/
noncomputable def slack (du : ℝ → ℝ) (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption) : P.State →ᵇ ℝ :=
  P.marginalState du hdu hpc
    - ((P.discount : ℝ) * (1 + P.interest)) • P.markovOp (P.marginalState du hdu hpc)

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem slack_apply (du : ℝ → ℝ) (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption) (s : P.State) :
    P.slack du hdu hpc s = P.marginalState du hdu hpc s
      - (P.discount : ℝ) * (1 + P.interest) * P.markovOp (P.marginalState du hdu hpc) s := rfl

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The slack is nonnegative**: the Euler inequality with room under the cap. -/
theorem slack_nonneg {du : ℝ → ℝ} (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c) (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s < assetCap)
    (s : P.State) : 0 ≤ P.slack du hdu hpc s := by
  rw [slack_apply, markovOp_marginalState, marginalState_apply]
  set a : ℝ := (s.1 : ℝ) with ha
  have hs : a ∈ Icc assetFloor assetCap := s.1.2
  set A : ℝ := P.policy (P.incl s) with hA
  have hAmem : A ∈ Icc assetFloor assetCap := P.policy_mem_region _
  have hc0 : 0 < P.consumptionFn s.2 a := P.consumptionFn_pos hpc hs s.2
  have hc' : ∀ z' : Z, 0 < P.consumptionFn z' A := fun z' => P.consumptionFn_pos hpc hAmem z'
  have hroom : A < P.maxSaving (a, s.2) := by
    rw [maxSaving_eq]
    refine lt_min (hslack _ hs) ?_
    have := hc0
    change 0 < P.resources (a, s.2) - P.policy (a, s.2) at this
    have hAeq : A = P.policy (a, s.2) := rfl
    linarith
  have hbv := P.toExtended.bellman_valueFunction
  have hE := P.euler_le (v := P.toExtended.valueFunction) (z := s.2) (a := a) (A := A)
    (du := du (P.consumptionFn s.2 a)) (du' := fun z' => du (P.consumptionFn z' A))
    hs (by rw [hbv]; exact congrFun P.policyOf_valueFunction _) hroom
    (by rw [hbv]; exact hc0) (by rw [hbv]; exact hderiv _ hc0)
    hc' (fun z' => hderiv _ (hc' z'))
  beta_reduce at hE
  linarith [hE]

/-- **The conditional variance of next period's marginal utility**, as a function of today's
state. -/
noncomputable def condVar (du : ℝ → ℝ) (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption) : P.State →ᵇ ℝ :=
  P.markovOp (P.marginalState du hdu hpc * P.marginalState du hdu hpc)
    - P.markovOp (P.marginalState du hdu hpc) * P.markovOp (P.marginalState du hdu hpc)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- The conditional variance is the weighted sum of squared deviations from the conditional
mean. -/
theorem condVar_eq_sum (du : ℝ → ℝ) (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption) (s : P.State) :
    P.condVar du hdu hpc s = ∑ z', P.prob s z'
      * (P.marginalState du hdu hpc (P.nextState s z')
        - P.markovOp (P.marginalState du hdu hpc) s) ^ 2 := by
  set M := P.marginalState du hdu hpc with hM
  have hsum := P.prob_sum s
  have hmean : ∑ z', P.prob s z' * M (P.nextState s z') = P.markovOp M s := by
    rw [markovOp_apply]
  have h1 : ∑ z', P.prob s z' * (M (P.nextState s z') - P.markovOp M s) ^ 2
      = ∑ z', (P.prob s z' * (M (P.nextState s z') * M (P.nextState s z'))
        - 2 * P.markovOp M s * (P.prob s z' * M (P.nextState s z'))
        + (P.markovOp M s) ^ 2 * P.prob s z') :=
    Finset.sum_congr rfl fun z' _ => by ring
  rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hmean, hsum]
  simp only [condVar, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.mul_apply,
    markovOp_apply]
  ring

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem condVar_nonneg (du : ℝ → ℝ) (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption) (s : P.State) : 0 ≤ P.condVar du hdu hpc s := by
  rw [condVar_eq_sum]
  exact Finset.sum_nonneg fun z' _ => mul_nonneg (P.prob_nonneg s z') (sq_nonneg _)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **A two-state lower bound on the conditional variance**: at least `min(π₁, π₂)/2` times the
squared gap in marginal utility between two income states at tomorrow's assets. -/
theorem condVar_ge_pair (du : ℝ → ℝ) (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption) (s : P.State) (z₁ z₂ : Z) :
    min (P.prob s z₁) (P.prob s z₂) / 2
      * (P.marginalState du hdu hpc (P.nextState s z₁)
        - P.marginalState du hdu hpc (P.nextState s z₂)) ^ 2
      ≤ P.condVar du hdu hpc s := by
  classical
  rw [condVar_eq_sum]
  have hnn : ∀ z' ∈ Finset.univ, 0 ≤ P.prob s z'
      * (P.marginalState du hdu hpc (P.nextState s z')
        - P.markovOp (P.marginalState du hdu hpc) s) ^ 2 :=
    fun z' _ => mul_nonneg (P.prob_nonneg s z') (sq_nonneg _)
  by_cases h12 : z₁ = z₂
  · subst h12
    simp only [sub_self, zero_pow two_ne_zero, mul_zero]
    exact Finset.sum_nonneg hnn
  set M := P.marginalState du hdu hpc with hM
  set m : ℝ := P.markovOp M s with hm
  set x₁ := M (P.nextState s z₁) with hx₁
  set x₂ := M (P.nextState s z₂) with hx₂
  have hπ₁ := P.prob_nonneg s z₁
  have hπ₂ := P.prob_nonneg s z₂
  have hsub : ∑ z' ∈ {z₁, z₂}, P.prob s z' * (M (P.nextState s z') - m) ^ 2
      ≤ ∑ z', P.prob s z' * (M (P.nextState s z') - m) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun z' _ _ => hnn z' (by simp)
  rw [Finset.sum_pair h12] at hsub
  have hmin₁ : min (P.prob s z₁) (P.prob s z₂) ≤ P.prob s z₁ := min_le_left _ _
  have hmin₂ : min (P.prob s z₁) (P.prob s z₂) ≤ P.prob s z₂ := min_le_right _ _
  have hmin0 : 0 ≤ min (P.prob s z₁) (P.prob s z₂) := le_min hπ₁ hπ₂
  have hkey : (x₁ - x₂) ^ 2 ≤ 2 * ((x₁ - m) ^ 2 + (x₂ - m) ^ 2) := by
    nlinarith [sq_nonneg (x₁ + x₂ - 2 * m)]
  have h1 : min (P.prob s z₁) (P.prob s z₂) * (x₁ - m) ^ 2 ≤ P.prob s z₁ * (x₁ - m) ^ 2 :=
    mul_le_mul_of_nonneg_right hmin₁ (sq_nonneg _)
  have h2 : min (P.prob s z₁) (P.prob s z₂) * (x₂ - m) ^ 2 ≤ P.prob s z₂ * (x₂ - m) ^ 2 :=
    mul_le_mul_of_nonneg_right hmin₂ (sq_nonneg _)
  have h3 := mul_le_mul_of_nonneg_left hkey hmin0
  nlinarith [hsub, h1, h2, h3]

/-! ### At a stationary distribution -/

/-- Stationarity as duality: the operator can be dropped under the integral. -/
theorem integral_markovOp_of_stationary {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ)
    (h : P.State →ᵇ ℝ) :
    ∫ s, P.markovOp h s ∂(μ : Measure P.State) = ∫ s, h s ∂(μ : Measure P.State) := by
  have h1 := P.integral_push (μ : Measure P.State) h
  have h2 : P.push (μ : Measure P.State) = (μ : Measure P.State) := by
    rw [← P.coe_pushProb, hμ]
  rw [h2] at h1
  exact h1.symm

/-- **The corner-slack identity**: `∫ slack dμ = (1 - βR) ∫ u'(c) dμ`. -/
theorem integral_slack {du : ℝ → ℝ} (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption) {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    ∫ s, P.slack du hdu hpc s ∂(μ : Measure P.State)
      = (1 - (P.discount : ℝ) * (1 + P.interest))
        * ∫ s, P.marginalState du hdu hpc s ∂(μ : Measure P.State) := by
  set M := P.marginalState du hdu hpc with hM
  have hint : ∀ h : P.State →ᵇ ℝ, Integrable (fun s => h s) (μ : Measure P.State) :=
    fun h => h.integrable _
  have : ∫ s, P.slack du hdu hpc s ∂(μ : Measure P.State)
      = ∫ s, (M s - (P.discount : ℝ) * (1 + P.interest) * P.markovOp M s) ∂(μ : Measure P.State) :=
    rfl
  rw [this, integral_sub (hint M) ((hint (P.markovOp M)).const_mul _), integral_const_mul,
    P.integral_markovOp_of_stationary hμ]
  ring

/-- **The variance bound**: `∫ Var(u'(c') | s) dμ ≤ 2 (1 - βR) ‖u'(c)‖²`. -/
theorem integral_condVar_le {du : ℝ → ℝ} (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c) (hdupos : ∀ c : ℝ, 0 < c → 0 ≤ du c)
    (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s < assetCap)
    (hβR0 : 0 < (P.discount : ℝ) * (1 + P.interest))
    (hβR : (P.discount : ℝ) * (1 + P.interest) ≤ 1)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    ∫ s, P.condVar du hdu hpc s ∂(μ : Measure P.State)
      ≤ 2 * (1 - (P.discount : ℝ) * (1 + P.interest)) * ‖P.marginalState du hdu hpc‖ ^ 2 := by
  set M := P.marginalState du hdu hpc with hM
  set S := P.slack du hdu hpc with hS
  set β : ℝ := (P.discount : ℝ) * (1 + P.interest) with hβ
  have hint : ∀ h : P.State →ᵇ ℝ, Integrable (fun s => h s) (μ : Measure P.State) :=
    fun h => h.integrable _
  have hM0 : ∀ s, 0 ≤ M s := fun s => hdupos _ (P.consumptionFn_pos hpc s.1.2 s.2)
  have hMle : ∀ s, M s ≤ ‖M‖ := fun s => by
    have := M.norm_coe_le_norm s
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hS0 : ∀ s, 0 ≤ S s := fun s => P.slack_nonneg hdu hderiv hpc hslack s
  -- the conditional mean is `(M - S)/β`
  have hmean : ∀ s, P.markovOp M s = (M s - S s) / β := fun s => by
    have hSs : S s = M s - β * P.markovOp M s := rfl
    rw [hSs, eq_div_iff hβR0.ne']
    ring
  have hMM : Integrable (fun s => M s * M s) (μ : Measure P.State) := hint (M * M)
  have hmm : Integrable (fun s => P.markovOp M s * P.markovOp M s) (μ : Measure P.State) :=
    hint (P.markovOp M * P.markovOp M)
  have hSS : Integrable (fun s => (M s - S s) * (M s - S s)) (μ : Measure P.State) :=
    hint ((M - S) * (M - S))
  -- `∫ condVar = ∫ M² - ∫ (markovOp M)²`
  have h1 : ∫ s, P.condVar du hdu hpc s ∂(μ : Measure P.State)
      = ∫ s, (M s * M s) ∂(μ : Measure P.State)
        - ∫ s, (P.markovOp M s * P.markovOp M s) ∂(μ : Measure P.State) := by
    have : ∫ s, P.condVar du hdu hpc s ∂(μ : Measure P.State)
        = ∫ s, (P.markovOp (M * M) s - (P.markovOp M * P.markovOp M) s)
          ∂(μ : Measure P.State) := rfl
    rw [this, integral_sub (hint _) (hint _), P.integral_markovOp_of_stationary hμ]
    rfl
  -- `(markovOp M)² ≥ (M - S)²` since `β ≤ 1`
  have h2 : ∫ s, ((M s - S s) * (M s - S s)) ∂(μ : Measure P.State)
      ≤ ∫ s, (P.markovOp M s * P.markovOp M s) ∂(μ : Measure P.State) := by
    refine integral_mono hSS hmm fun s => ?_
    simp only
    rw [hmean s, div_mul_div_comm, le_div_iff₀ (mul_pos hβR0 hβR0)]
    have hsq : 0 ≤ (M s - S s) * (M s - S s) := mul_self_nonneg _
    have hβ1 : β * β ≤ 1 := by nlinarith
    nlinarith
  -- `M² - (M - S)² = 2 S M - S² ≤ 2 ‖M‖ S`
  have h3 : ∫ s, (M s * M s - (M s - S s) * (M s - S s)) ∂(μ : Measure P.State)
      ≤ ∫ s, (2 * ‖M‖ * S s) ∂(μ : Measure P.State) := by
    refine integral_mono (hMM.sub hSS) ((hint S).const_mul _) fun s => ?_
    simp only
    have := mul_le_mul_of_nonneg_left (hMle s) (hS0 s)
    nlinarith [sq_nonneg (S s), hS0 s]
  rw [integral_sub hMM hSS, integral_const_mul, P.integral_slack hdu hpc hμ] at h3
  have h4 : ∫ s, M s ∂(μ : Measure P.State) ≤ ‖M‖ := by
    have := P.abs_integral_le_norm μ M
    exact (le_abs_self _).trans this
  have h5 : 0 ≤ 1 - β := by linarith
  have h6 : 0 ≤ ‖M‖ := norm_nonneg _
  rw [h1]
  nlinarith [h2, h3, mul_le_mul_of_nonneg_left h4 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h6),
    mul_nonneg h5 h6]

end General

/-! ### From a variance floor to a capital floor -/

section Floor

variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **A variance floor at low saving is a capital floor.** If every household saving at most `A₀`
faces conditional variance at least `v₀ > 0`, then
`K(μ) ≥ A₀ (1 - 2(1 - βR) ‖u'(c)‖² / v₀)` at every stationary `μ`. As `βR → 1` with `v₀` uniform,
the floor tends to `A₀`. -/
theorem aggregateCapital_ge_of_condVar {du : ℝ → ℝ} (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c) (hdupos : ∀ c : ℝ, 0 < c → 0 ≤ du c)
    (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → P.policy s < assetCap)
    (hβR0 : 0 < (P.discount : ℝ) * (1 + P.interest))
    (hβR : (P.discount : ℝ) * (1 + P.interest) ≤ 1)
    {A₀ v₀ : ℝ} (hA₀ : 0 ≤ A₀) (hv₀ : 0 < v₀)
    (hfloor : ∀ s : P.State, P.policyCoord s ≤ A₀ → v₀ ≤ P.condVar du hdu hpc s)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    A₀ - A₀ / v₀ * (2 * (1 - (P.discount : ℝ) * (1 + P.interest))
      * ‖P.marginalState du hdu hpc‖ ^ 2) ≤ P.aggregateCapital μ := by
  have hint : ∀ h : P.State →ᵇ ℝ, Integrable (fun s => h s) (μ : Measure P.State) :=
    fun h => h.integrable _
  have hpt : ∀ s : P.State, A₀ - A₀ / v₀ * P.condVar du hdu hpc s ≤ P.policyCoord s := by
    intro s
    have hpol0 : 0 ≤ P.policyCoord s := (P.policy_mem_region _).1
    have hV0 := P.condVar_nonneg du hdu hpc s
    have hq : 0 ≤ A₀ / v₀ := div_nonneg hA₀ hv₀.le
    rcases le_or_gt (P.policyCoord s) A₀ with h | h
    · have := hfloor s h
      have : A₀ ≤ A₀ / v₀ * P.condVar du hdu hpc s := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hv₀]
        exact mul_le_mul_of_nonneg_left this hA₀
      linarith
    · nlinarith [mul_nonneg hq hV0]
  have hI : ∫ s, (A₀ - A₀ / v₀ * P.condVar du hdu hpc s) ∂(μ : Measure P.State)
      ≤ ∫ s, P.policyCoord s ∂(μ : Measure P.State) :=
    integral_mono ((integrable_const _).sub ((hint _).const_mul _)) (hint _) hpt
  rw [integral_sub (integrable_const _) ((hint _).const_mul _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at hI
  rw [P.aggregateCapital_eq_integral_policy hμ]
  have hV := P.integral_condVar_le hdu hderiv hdupos hpc hslack hβR0 hβR hμ
  have hq : 0 ≤ A₀ / v₀ := div_nonneg hA₀ hv₀.le
  nlinarith [mul_le_mul_of_nonneg_left hV hq]

end Floor

end IncomeFluctuation

end LeanEconomics
