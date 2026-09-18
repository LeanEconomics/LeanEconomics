/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.Impatience
import LeanEconomics.Models.ImpatientDecline
import LeanEconomics.Equilibrium.SignChange
import LeanEconomics.Distribution.UniquenessTop

/-!
# Capital supply at or above the time-preference rate

Aiyagari's Figure IIb: capital supply tends to infinity as the rate approaches the
time-preference rate `λ` from below, so no equilibrium can lie at or above it. In a capped economy
"infinity" is the cap, and what can be proved is that at `β(1+r) > 1` every stationary
distribution holds capital comparable to the cap.

## Two results, and an honest gap

**Deterministic income.** Nobody runs assets down (`le_policy_of_patient`), so `policy - a ≥ 0`
pointwise; stationarity makes its integral zero, so `policy = a` almost everywhere; and a
household with room under the cap strictly accumulates (`lt_policy_of_patient`), so almost every
household is AT the cap. Capital supply IS the cap (`aggregateCapital_eq_assetCap_of_patient`).

**Income risk, given an atom at the cap.** If from the borrowing limit the richest income state
reaches the cap in `N` steps, then `N + 1` consecutive draws of that state — probability at least
`p₀^(N+1)` from anywhere — put the household at the cap, and the minorisation bound
`iterate_lower` turns that into `assetCap · p₀^(N+1) ≤ K` at every stationary distribution
(`assetCap_mul_le_aggregateCapital_of_atom`).

What is NOT proved is that patience delivers the atom with income risk. Patience gives strict
accumulation at the richest-consumption state wherever there is room, but strict accumulation
can approach the cap without reaching it — `a ↦ (a + cap)/2` does — and the finite-step atom is
exactly what the Doeblin argument needs. Closing that gap needs a QUANTITATIVE accumulation
bound under patience, the mirror image of the minimal MPC, and that is not here.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### Iterating the operator against a stationary distribution -/

theorem integral_markovOp_iterate_eq (h : P.State →ᵇ ℝ) (n : ℕ) :
    ∀ μ : ProbabilityMeasure P.State,
      ∫ s, (P.markovOp^[n] h) s ∂(μ : Measure P.State)
        = ∫ s, h s ∂((P.pushProb^[n] μ : ProbabilityMeasure P.State) : Measure P.State) := by
  induction n with
  | zero => intro μ; simp
  | succ k ih =>
    intro μ
    have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
    calc ∫ s, (P.markovOp^[k + 1] h) s ∂(μ : Measure P.State)
        = ∫ s, P.markovOp (P.markovOp^[k] h) s ∂(μ : Measure P.State) := by
          rw [Function.iterate_succ_apply']
      _ = ∫ s, (P.markovOp^[k] h) s ∂(P.push (μ : Measure P.State)) := (P.integral_push _ _).symm
      _ = ∫ s, (P.markovOp^[k] h) s
            ∂((P.pushProb μ : ProbabilityMeasure P.State) : Measure P.State) := rfl
      _ = ∫ s, h s ∂((P.pushProb^[k] (P.pushProb μ) : ProbabilityMeasure P.State)
            : Measure P.State) := ih (P.pushProb μ)
      _ = ∫ s, h s ∂((P.pushProb^[k + 1] μ : ProbabilityMeasure P.State) : Measure P.State) := by
          rw [Function.iterate_succ_apply]

/-- Against a stationary distribution, iterating the operator changes nothing. -/
theorem integral_markovOp_iterate_of_stationary (h : P.State →ᵇ ℝ) (n : ℕ)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    ∫ s, (P.markovOp^[n] h) s ∂(μ : Measure P.State) = ∫ s, h s ∂(μ : Measure P.State) := by
  rw [P.integral_markovOp_iterate_eq h n μ, Function.iterate_fixed hμ]

/-! ### Income risk, given an atom at the cap -/

/-- **Capital is at least `assetCap · p₀^(N+1)`** whenever `N` consecutive draws of the state `z₁`
carry the borrowing limit to the cap. -/
theorem assetCap_mul_le_aggregateCapital_of_atom {z₁ : Z} {N : ℕ}
    (hgro : (P.gBad z₁)^[N] P.botState = P.topState)
    {p₀ : ℝ} (hp0 : 0 ≤ p₀) (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    assetCap * p₀ ^ (N + 1) ≤ P.aggregateCapital μ := by
  have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
  have hp' : ∀ s : P.State, p₀ ≤ P.prob s z₁ := fun s => hp s.2
  have hinf : (0 : ℝ) ≤ P.infF P.assetCoord := by
    refine le_ciInf fun s => ?_
    exact s.1.2.1
  have hpow1 : p₀ ^ (N + 1) ≤ 1 := by
    have hz : Z := Classical.ofNonempty
    have h1 : p₀ ≤ 1 := by
      have hsum := P.transitionMatrix_sum hz
      have hsingle := Finset.single_le_sum (fun z' _ => P.transitionMatrix_nonneg hz z')
        (Finset.mem_univ z₁)
      linarith [hp hz]
    exact pow_le_one₀ hp0 h1
  -- pointwise: the iterated operator on assets is at least `p₀^(N+1) · cap`
  have hpt : ∀ s : P.State, assetCap * p₀ ^ (N + 1) ≤ (P.markovOp^[N + 1] P.assetCoord) s := by
    intro s
    have hlow := P.iterate_lower hp0 hp' P.assetCoord (N + 1) s
    rw [P.badStep_iterate_eq_top hgro s] at hlow
    have htop : P.assetCoord (P.topState, z₁) = assetCap := rfl
    rw [htop] at hlow
    have : 0 ≤ (1 - p₀ ^ (N + 1)) * P.infF P.assetCoord :=
      mul_nonneg (by linarith) hinf
    linarith
  calc assetCap * p₀ ^ (N + 1)
      = ∫ _s, assetCap * p₀ ^ (N + 1) ∂(μ : Measure P.State) := by simp
    _ ≤ ∫ s, (P.markovOp^[N + 1] P.assetCoord) s ∂(μ : Measure P.State) :=
        integral_mono (integrable_const _) ((P.markovOp^[N + 1] P.assetCoord).integrable _) hpt
    _ = P.aggregateCapital μ := P.integral_markovOp_iterate_of_stationary _ _ hμ

/-! ### Income risk: the supermartingale bound

Under `β(1+r) > 1` the Euler inequality `βR · E[u'(c')] ≤ u'(c)` holds wherever there is room
under the cap (`euler_le`), and where there is none the household is AT the cap and consumes at
least `minIncome + r · cap` next period. Integrating against a stationary distribution,

  `(1 - 1/βR) · ∫ u'(c) dμ ≤ u'(minIncome + r · cap)`,

which is small when the cap is large. Since `c ≤ maxIncome + R a`, a tangent-line bound turns a
small integrated marginal utility into a large integrated asset holding. No iid assumption, no
knowledge of which state consumes most, and no atom: only positivity and the Euler inequality. -/

/-- Consumption, as a continuous function of the state. -/
theorem continuous_consumptionState :
    Continuous (fun s : P.State => P.consumptionFn s.2 (s.1 : ℝ)) := by
  have hpol : Continuous (fun s : P.State => P.policy (P.incl s)) :=
    P.continuousOn_policy.comp_continuous P.continuous_incl P.incl_mem
  have hres : Continuous (fun s : P.State => P.resources (P.incl s)) := by
    change Continuous (fun s : P.State => P.income s.2 + (1 + P.interest) * max 0 (s.1 : ℝ))
    exact ((continuous_of_discreteTopology (f := P.income)).comp continuous_snd).add
      (continuous_const.mul (continuous_const.max (continuous_subtype_val.comp continuous_fst)))
  exact hres.sub hpol

/-- **The integrated marginal utility is small under patience.** With `βR > 1` the Euler
inequality `βR · E u'(c') ≤ u'(c)` holds wherever the cap has room, and at the cap tomorrow's
consumption is at least `minIncome + r · assetCap`; integrating against a stationary
distribution, where `∫ u'(c) = ∫ markovOp u'(c)`, gives
`(1 - 1/βR) · ∫ u'(c) ≤ u'(minIncome + r · assetCap)`. No differentiability of the policy
and no atom are needed: the argument is a supermartingale bound on marginal utility. -/
theorem integral_marginal_le_of_patient
    (hβR : 1 < (P.discount : ℝ) * (1 + P.interest)) (hint : 0 ≤ P.interest)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hdcont : ContinuousOn du (Ioi (0 : ℝ))) (hpc : P.PositiveConsumption)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    (1 - 1 / ((P.discount : ℝ) * (1 + P.interest)))
        * ∫ s, du (P.consumptionFn s.2 (s.1 : ℝ)) ∂(μ : Measure P.State)
      ≤ du (P.minIncome + P.interest * assetCap) := by
  classical
  have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hpos : ∀ (z : Z), ∀ x ∈ Icc (0 : ℝ) assetCap, 0 < P.consumptionFn z x :=
    fun z x hx => P.consumptionFn_pos hpc hx z
  set c : P.State → ℝ := fun s => P.consumptionFn s.2 (s.1 : ℝ) with hcdef
  have hc_cont : Continuous c := P.continuous_consumptionState
  have hc_pos : ∀ s, 0 < c s := fun s => hpos s.2 _ s.1.2
  -- the minimum of consumption, which bounds marginal utility
  obtain ⟨s₀, -, hs₀⟩ := isCompact_univ.exists_isMinOn (univ_nonempty (α := P.State))
    hc_cont.continuousOn
  have hmin : ∀ s, c s₀ ≤ c s := fun s => hs₀ (mem_univ s)
  set M : P.State →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (fun s => du (c s))
    (hdcont.comp_continuous hc_cont fun s => mem_Ioi.mpr (hc_pos s)) (du (c s₀))
    (fun s => by
      rw [Real.norm_eq_abs, abs_of_pos (hdupos _ (hc_pos s))]
      exact hanti (mem_Ioi.mpr (hc_pos s₀)) (mem_Ioi.mpr (hc_pos s)) (hmin s)) with hMdef
  have hMapp : ∀ s, M s = du (c s) := fun s => rfl
  -- the stationarity identity for `M`
  have hstat : ∫ s, M s ∂(μ : Measure P.State) = ∫ s, P.markovOp M s ∂(μ : Measure P.State) := by
    calc ∫ s, M s ∂(μ : Measure P.State)
        = ∫ s, M s ∂((P.pushProb μ : ProbabilityMeasure P.State) : Measure P.State) := by
          rw [show P.pushProb μ = μ from hμ]
      _ = ∫ s, P.markovOp M s ∂(μ : Measure P.State) := by rw [coe_pushProb, P.integral_push]
  -- the pointwise bound on the operator
  set ε : ℝ := du (P.minIncome + P.interest * assetCap) with hεdef
  have hεpos : 0 < ε := hdupos _ (by have := P.minIncome_pos; nlinarith)
  have hpt : ∀ s : P.State, P.markovOp M s
      ≤ M s / ((P.discount : ℝ) * (1 + P.interest)) + ε := by
    intro s
    have hbv := P.toExtended.bellman_valueFunction
    have hmem : ((s.1 : ℝ)) ∈ Icc (0 : ℝ) assetCap := s.1.2
    set A : ℝ := P.policy ((s.1 : ℝ), s.2) with hA
    have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.feasible_subset_region (P.policy_mem _)
    have hcs : 0 < P.consumptionFn s.2 (s.1 : ℝ) := hpos s.2 _ hmem
    have hop : P.markovOp M s
        = ∑ z' : Z, P.transitionMatrix s.2 z' * du (P.consumptionFn z' A) := by
      simp only [markovOp_apply, hMapp]
      rfl
    have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := by linarith
    by_cases hroom : A < P.maxSaving ((s.1 : ℝ), s.2)
    · -- room under the cap: the Euler inequality
      have hE := P.euler_le (v := P.toExtended.valueFunction) (z := s.2) (a := (s.1 : ℝ)) (A := A)
        (du := du (P.consumptionFn s.2 (s.1 : ℝ))) (du' := fun z' => du (P.consumptionFn z' A))
        hmem (by rw [hbv, hA]; exact congrFun P.policyOf_valueFunction _) hroom
        (by rw [hbv]; exact hcs) (by rw [hbv]; exact hderiv _ hcs) (fun z' => hpos z' A hAmem)
        (fun z' => hderiv _ (hpos z' A hAmem))
      rw [hop, hMapp]
      have h2 : ∑ z' : Z, P.transitionMatrix s.2 z' * du (P.consumptionFn z' A)
          ≤ du (P.consumptionFn s.2 (s.1 : ℝ)) / ((P.discount : ℝ) * (1 + P.interest)) := by
        rw [le_div_iff₀ hβR0]; linarith [hE]
      linarith [hεpos.le]
    · -- no room: the household is at the cap, and tomorrow consumes at least `minIncome + r cap`
      push_neg at hroom
      have hAcap : A = assetCap := by
        have hle := (P.policy_mem_region ((s.1 : ℝ), s.2)).2
        have hms : P.maxSaving ((s.1 : ℝ), s.2) = min assetCap (P.resources ((s.1 : ℝ), s.2)) :=
          P.maxSaving_eq _
        have hcpos : A < P.resources ((s.1 : ℝ), s.2) := by
          have := hcs
          simp only [consumptionFn, consumption] at this
          linarith
        rw [hms] at hroom
        rcases le_total assetCap (P.resources ((s.1 : ℝ), s.2)) with h | h
        · rw [min_eq_left h] at hroom; linarith
        · rw [min_eq_right h] at hroom; linarith
      have hnext : ∀ z' : Z, P.minIncome + P.interest * assetCap ≤ P.consumptionFn z' A := by
        intro z'
        rw [hAcap]
        have hres : P.resources (assetCap, z') = P.income z' + (1 + P.interest) * assetCap := by
          simp only [resources, max_eq_right hcap0]
        have hpol := (P.policy_mem_region (assetCap, z')).2
        have hinc := P.minIncome_le z'
        simp only [consumptionFn, consumption, hres]
        nlinarith
      have hterm : ∀ z' : Z, du (P.consumptionFn z' A) ≤ ε := fun z' =>
        hanti (mem_Ioi.mpr (by have := P.minIncome_pos; nlinarith)) (mem_Ioi.mpr (hpos z' A hAmem))
          (hnext z')
      have hsum : ∑ z' : Z, P.transitionMatrix s.2 z' * du (P.consumptionFn z' A) ≤ ε := by
        calc ∑ z' : Z, P.transitionMatrix s.2 z' * du (P.consumptionFn z' A)
            ≤ ∑ z' : Z, P.transitionMatrix s.2 z' * ε :=
              Finset.sum_le_sum fun z' _ =>
                mul_le_mul_of_nonneg_left (hterm z') (P.transitionMatrix_nonneg _ _)
          _ = ε := by rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]
      rw [hop]
      have h0 : 0 ≤ M s / ((P.discount : ℝ) * (1 + P.interest)) :=
        div_nonneg (hdupos _ (hc_pos s)).le hβR0.le
      exact le_trans hsum (by linarith)
  -- integrate the pointwise bound
  have hint' : ∫ s, P.markovOp M s ∂(μ : Measure P.State)
      ≤ ∫ s, (M s / ((P.discount : ℝ) * (1 + P.interest)) + ε) ∂(μ : Measure P.State) :=
    integral_mono ((P.markovOp M).integrable _)
      (((M.integrable _).div_const _).add (integrable_const _)) hpt
  have hconst : ∫ _s, ε ∂(μ : Measure P.State) = ε := by simp
  rw [integral_add ((M.integrable _).div_const _) (integrable_const _), integral_div, hconst]
    at hint'
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := by linarith
  have hM : ∫ s, du (P.consumptionFn s.2 (s.1 : ℝ)) ∂(μ : Measure P.State)
      = ∫ s, M s ∂(μ : Measure P.State) := rfl
  rw [hM, hstat]
  rw [hstat] at hint'
  have hlin : (1 - 1 / ((P.discount : ℝ) * (1 + P.interest)))
      * ∫ s, P.markovOp M s ∂(μ : Measure P.State)
      = (∫ s, P.markovOp M s ∂(μ : Measure P.State))
        - (∫ s, P.markovOp M s ∂(μ : Measure P.State)) / ((P.discount : ℝ) * (1 + P.interest)) := by
    ring
  rw [hlin]
  linarith [hint']

/-- **Capital supply under patience, with income risk**, for log utility: an explicit floor that
grows with the cap. Since `c ≤ maxIncome + R a` and `x ↦ 1/x` is convex, the small integrated
marginal utility forces a large integrated asset holding. -/
theorem log_aggregateCapital_ge_of_patient (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβR : 1 < (P.discount : ℝ) * (1 + P.interest)) (hint : 0 ≤ P.interest)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    (1 - 1 / ((P.discount : ℝ) * (1 + P.interest))) * (P.minIncome + P.interest * assetCap)
      ≤ P.maxIncome + (1 + P.interest) * P.aggregateCapital μ := by
  classical
  have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hpc : P.PositiveConsumption := P.positiveConsumption_of_unbounded hunb
  have hmaxpos : 0 < P.maxIncome := lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxIncome
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := by linarith
  have hroom : (0 : ℝ) < 1 - 1 / ((P.discount : ℝ) * (1 + P.interest)) := by
    rw [sub_pos, div_lt_one hβR0]; exact hβR
  have hy : 0 < P.minIncome + P.interest * assetCap := by
    have := P.minIncome_pos; nlinarith
  -- the marginal-utility bound with `u' = 1/c`
  have hkey := P.integral_marginal_le_of_patient hβR hint (du := fun x => x⁻¹)
    (fun x hx => by
      have := hasDerivAt_crraUtility 1 hx
      rw [Real.rpow_neg_one] at this
      rw [hu]; exact this)
    (fun x hx y hy hxy => inv_anti₀ hx hxy)
    (fun x hx => inv_pos.mpr hx) (continuousOn_inv₀.mono fun x hx => ne_of_gt hx) hpc hμ
  -- consumption is at most cash on hand, so `1/c ≥ 1/(maxIncome + R a)`
  set K : ℝ := P.aggregateCapital μ with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef, aggregateCapital]
    exact integral_nonneg fun s => s.1.2.1
  set Y : ℝ := P.maxIncome + (1 + P.interest) * K with hYdef
  have hY : 0 < Y := by rw [hYdef]; exact add_pos_of_pos_of_nonneg hmaxpos (mul_nonneg hR.le hK0)
  -- the tangent line of `1/x` at `Y`, integrated
  have hpt : ∀ s : P.State,
      Y⁻¹ - (1 + P.interest) * (P.assetCoord s - K) / Y ^ 2
        ≤ (P.consumptionFn s.2 (s.1 : ℝ))⁻¹ := by
    intro s
    have hcs : 0 < P.consumptionFn s.2 (s.1 : ℝ) := P.consumptionFn_pos hpc s.1.2 s.2
    have hres : P.resources ((s.1 : ℝ), s.2) = P.income s.2 + (1 + P.interest) * (s.1 : ℝ) := by
      simp only [resources, max_eq_right s.1.2.1]
    have hcle : P.consumptionFn s.2 (s.1 : ℝ) ≤ P.maxIncome + (1 + P.interest) * (s.1 : ℝ) := by
      have := (P.policy_mem_region ((s.1 : ℝ), s.2)).1
      have := P.le_maxIncome s.2
      simp only [consumptionFn, consumption, hres]
      linarith
    set X : ℝ := P.maxIncome + (1 + P.interest) * (s.1 : ℝ) with hX
    have hX0 : 0 < X := by
      rw [hX]; exact add_pos_of_pos_of_nonneg hmaxpos (mul_nonneg hR.le s.1.2.1)
    have h1 : X⁻¹ ≤ (P.consumptionFn s.2 (s.1 : ℝ))⁻¹ := inv_anti₀ hcs hcle
    have h2 : Y⁻¹ - (1 + P.interest) * (P.assetCoord s - K) / Y ^ 2 ≤ X⁻¹ := by
      have hXY : X - Y = (1 + P.interest) * (P.assetCoord s - K) := by
        rw [hX, hYdef, assetCoord_apply]; ring
      rw [← hXY]
      have hY2 : 0 < Y ^ 2 := pow_pos hY 2
      have hkey : X⁻¹ - Y⁻¹ + (X - Y) / Y ^ 2 = (X - Y) ^ 2 / (X * Y ^ 2) := by
        field_simp
        ring
      have hnn : 0 ≤ (X - Y) ^ 2 / (X * Y ^ 2) := div_nonneg (sq_nonneg _) (by positivity)
      linarith
    exact le_trans h2 h1
  have hint2 : ∫ s, (Y⁻¹ - (1 + P.interest) * (P.assetCoord s - K) / Y ^ 2) ∂(μ : Measure P.State)
      ≤ ∫ s, (P.consumptionFn s.2 (s.1 : ℝ))⁻¹ ∂(μ : Measure P.State) := by
    refine integral_mono ?_ ?_ hpt
    · exact (integrable_const _).sub
        ((((P.assetCoord.integrable _).sub (integrable_const _)).const_mul _).div_const _)
    · -- `1/c` is continuous on the compact state space
      have hcont : Continuous fun s : P.State => (P.consumptionFn s.2 (s.1 : ℝ))⁻¹ :=
        (continuousOn_inv₀.mono fun x hx => ne_of_gt hx).comp_continuous
          P.continuous_consumptionState fun s => mem_Ioi.mpr (P.consumptionFn_pos hpc s.1.2 s.2)
      exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlin : ∫ s, (Y⁻¹ - (1 + P.interest) * (P.assetCoord s - K) / Y ^ 2) ∂(μ : Measure P.State)
      = Y⁻¹ := by
    have hc1 : ∫ _s, Y⁻¹ ∂(μ : Measure P.State) = Y⁻¹ := by simp
    have hc2 : ∫ _s, K ∂(μ : Measure P.State) = K := by simp
    have hg : Integrable (fun s : P.State => (1 + P.interest) * (P.assetCoord s - K) / Y ^ 2)
        (μ : Measure P.State) :=
      (((P.assetCoord.integrable _).sub (integrable_const _)).const_mul _).div_const _
    have hg' : Integrable (fun s : P.State => P.assetCoord s - K) (μ : Measure P.State) :=
      (P.assetCoord.integrable _).sub (integrable_const _)
    rw [integral_sub (f := fun _ => Y⁻¹)
      (g := fun s => (1 + P.interest) * (P.assetCoord s - K) / Y ^ 2) (integrable_const _) hg,
      hc1, integral_div, integral_const_mul,
      integral_sub (f := fun s => P.assetCoord s) (g := fun _ => K) (P.assetCoord.integrable _)
        (integrable_const _), hc2,
      show ∫ s, P.assetCoord s ∂(μ : Measure P.State) = K from rfl]
    ring
  rw [hlin] at hint2
  -- assemble: `Y⁻¹ ≤ ∫ 1/c ≤ ε/(1 - 1/βR)`
  have hfinal : (1 - 1 / ((P.discount : ℝ) * (1 + P.interest))) * Y⁻¹
      ≤ (P.minIncome + P.interest * assetCap)⁻¹ := by
    calc (1 - 1 / ((P.discount : ℝ) * (1 + P.interest))) * Y⁻¹
        ≤ (1 - 1 / ((P.discount : ℝ) * (1 + P.interest)))
            * ∫ s, (P.consumptionFn s.2 (s.1 : ℝ))⁻¹ ∂(μ : Measure P.State) :=
          mul_le_mul_of_nonneg_left hint2 hroom.le
      _ ≤ (P.minIncome + P.interest * assetCap)⁻¹ := hkey
  rw [show (1 - 1 / ((P.discount : ℝ) * (1 + P.interest))) * Y⁻¹
      = (1 - 1 / ((P.discount : ℝ) * (1 + P.interest))) / Y from (div_eq_mul_inv _ _).symm,
    div_le_iff₀ hY, inv_mul_eq_div, le_div_iff₀ hy] at hfinal
  exact hfinal

/-! ### Deterministic income -/

/-- **No equilibrium above the time-preference rate, with income risk**, log utility: once the
floor `[(1 - 1/βR)(minIncome + r · assetCap) - maxIncome] / (1 + r)` on capital supply exceeds
the demand `D`, the market cannot clear. With a large cap the floor is of order `(1 - 1/βR)·r·cap`,
so only a band of rates just above `λ` escapes, of width shrinking like `1/assetCap`. -/
theorem log_no_equilibrium_of_patient_risk (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβR : 1 < (P.discount : ℝ) * (1 + P.interest)) (hint : 0 ≤ P.interest)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) {D : ℝ}
    (hD : P.maxIncome + (1 + P.interest) * D
      < (1 - 1 / ((P.discount : ℝ) * (1 + P.interest))) * (P.minIncome + P.interest * assetCap)) :
    P.aggregateCapital μ ≠ D := by
  intro h
  have := P.log_aggregateCapital_ge_of_patient hu hunb hβR hint hμ
  rw [h] at this
  linarith

section Deterministic

variable [Subsingleton Z]

/-- **Under patience, capital supply is the cap**, with deterministic income. -/
theorem aggregateCapital_eq_assetCap_of_patient
    (hβR : 1 < (P.discount : ℝ) * (1 + P.interest))
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpc : P.PositiveConsumption)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    P.aggregateCapital μ = assetCap := by
  have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
  have hpos : ∀ (z : Z), ∀ x ∈ Icc (0 : ℝ) assetCap, 0 < P.consumptionFn z x :=
    fun z x hx => P.consumptionFn_pos hpc hx z
  -- `policy - a ≥ 0` everywhere, and its integral vanishes
  have hge : ∀ s : P.State, 0 ≤ P.policyCoord s - P.assetCoord s := fun s => by
    have hle : (s.1 : ℝ) ≤ P.policy ((s.1 : ℝ), s.2) :=
      P.le_policy_of_patient hpc hβR.le (a := (s.1 : ℝ)) s.1.2 s.2
    have hpc' : P.policyCoord s = P.policy ((s.1 : ℝ), s.2) := rfl
    have hac : P.assetCoord s = (s.1 : ℝ) := rfl
    rw [hpc', hac]
    linarith
  have hzero : ∫ s, (P.policyCoord s - P.assetCoord s) ∂(μ : Measure P.State) = 0 := by
    rw [integral_sub (P.policyCoord.integrable _) (P.assetCoord.integrable _),
      ← P.aggregateCapital_eq_integral_policy hμ]
    simp [aggregateCapital]
  have hae : (fun s => P.policyCoord s - P.assetCoord s) =ᵐ[(μ : Measure P.State)] 0 :=
    (integral_eq_zero_iff_of_nonneg hge
      ((P.policyCoord.integrable _).sub (P.assetCoord.integrable _))).mp hzero
  -- so almost every household sits at the cap
  have hatcap : (fun s => P.assetCoord s) =ᵐ[(μ : Measure P.State)] fun _ => assetCap := by
    filter_upwards [hae] with s hs
    have hs' : P.policy ((s.1 : ℝ), s.2) - (s.1 : ℝ) = 0 := hs
    have hfix : P.policy ((s.1 : ℝ), s.2) = (s.1 : ℝ) := by linarith
    by_contra hne
    have hne' : (s.1 : ℝ) ≠ assetCap := hne
    have hlt : (s.1 : ℝ) < assetCap := lt_of_le_of_ne s.1.2.2 hne'
    have hroom : P.policy ((s.1 : ℝ), s.2) < P.maxSaving ((s.1 : ℝ), s.2) := by
      rw [P.maxSaving_eq]
      refine lt_min (by rw [hfix]; exact hlt) ?_
      have := hpos s.2 _ s.1.2
      simp only [consumptionFn, consumption] at this
      linarith
    have := P.lt_policy_of_patient hβR hderiv hanti hdupos hpos s.1.2 (z := s.2) hroom
      (fun z' => by rw [Subsingleton.elim z' s.2])
    linarith
  calc P.aggregateCapital μ = ∫ s, P.assetCoord s ∂(μ : Measure P.State) := rfl
    _ = ∫ _s, assetCap ∂(μ : Measure P.State) := integral_congr_ae hatcap
    _ = assetCap := by simp

/-- **No equilibrium above the time-preference rate**, deterministic income, log utility:
capital supply is the cap, so any demand below the cap is unmet. -/
theorem log_no_equilibrium_of_patient (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβR : 1 < (P.discount : ℝ) * (1 + P.interest))
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) {D : ℝ} (hD : D < assetCap) :
    P.aggregateCapital μ ≠ D := by
  rw [P.aggregateCapital_eq_assetCap_of_patient hβR (du := fun c => c ^ (-(1 : ℝ)))
    (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility 1 hc)
    (fun _ hx _ _ hxy => Real.rpow_le_rpow_of_nonpos hx hxy (by norm_num))
    (fun c hc => Real.rpow_pos_of_pos hc _) (P.positiveConsumption_of_unbounded hunb) hμ]
  exact ne_of_gt hD

end Deterministic

end IncomeFluctuation

end LeanEconomics
