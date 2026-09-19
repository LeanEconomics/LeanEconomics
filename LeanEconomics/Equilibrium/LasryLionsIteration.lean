/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.ShiftedDominance
import LeanEconomics.Models.UniformRate

/-!
# Lasry–Lions with the initial distribution supplied by the iteration

`Equilibrium/LasryLions` records why the Lasry–Lions argument does not reach stationary
discounted equilibria: it cancels `∫ (u₁ - u₂) d(m₁(0) - m₂(0))` by a COMMON initial
distribution, and two stationary equilibria carry two different distributions. But the stationary
distribution of a Bewley economy is the limit of the iteration `T^n μ₀` from ANY `μ₀`, so a
common start is available after all: run both economies from the same `μ₀` with their own
stationary policies, and compare along the iteration rather than at the limit.

## The inequality

Two admissible rates `r₁ ≤ r₂` of the same household economy, with stationary policies
`g₁, g₂`, value functions `V₁, V₂`, and distribution operators `T₁, T₂`. Each value function
satisfies its Bellman identity along its own policy, and a household at either rate may follow the
OTHER economy's policy for `T` periods and then behave optimally, which bounds its value from
below. Adding the two inequalities, integrating against `μ₀`, and pushing the iteration through
the Markov operators, the initial terms cancel and

  `∑_{t<T} β^t [ ∫ Δ(·, g₁) d(T₁^t μ₀) - ∫ Δ(·, g₂) d(T₂^t μ₀) ]
     ≤ β^T [ ∫ (V₁ - V₂) d(T₁^T μ₀) - ∫ (V₁ - V₂) d(T₂^T μ₀) ]`,

where `Δ(a, a') = u(y + R₂ a - a') - u(y + R₁ a - a') ≥ 0` is the utility gain from facing the
higher rate at a given saving decision (`lasryLions_iteration_sum_le`). The right side is at most
`2 β^T ‖V₁ - V₂‖`, so the discounted series is at most zero
(`lasryLions_iteration_tsum_nonpos`). This is the Lasry–Lions pairing inequality for two
stationary equilibria, valid for every `μ₀`.

## What it is and is not

The pairing is not aggregate capital: it is marginal-utility weighted and policy dependent, and
Lasry–Lions monotonicity — the pairing nonnegative — is exactly the elasticity condition
(`Δ` increasing in `a` is `R₂ u'(c₂) ≥ R₁ u'(c₁)`), which Graber and Matter (2024) observe fails
for price coupling in general. So the inequality does not give uniqueness by itself. What it adds
is an INTEGRATED and DISCOUNTED constraint between two equilibria, where the pointwise Euler chain
of `ElasticityReduction` needs the condition at every pivot state; whether the integrated form
tolerates the failure of the pointwise one on a thin tail is the question it is here to pose.

The one hypothesis beyond the standing ones is that the higher-rate policy is affordable at the
lower rate: `0 < y + R₁ a - g₂(a, z)`. It holds for rates close together, since `c₂ ≥ κ₂ m₂` gives
`g₂ ≤ (1 - κ₂) m₂`, and `(1 - κ₂)(y + R₂ a) < y + R₁ a` whenever `(r₂ - r₁) a < κ₂ m₂`.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]

/-! ### The Markov operator is linear, and so are its iterates -/

section Operator

variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem markovOp_add (h k : P.State →ᵇ ℝ) : P.markovOp (h + k) = P.markovOp h + P.markovOp k := by
  ext s
  simp only [markovOp_apply, BoundedContinuousFunction.add_apply, mul_add, Finset.sum_add_distrib]

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem markovOp_smul (c : ℝ) (h : P.State →ᵇ ℝ) : P.markovOp (c • h) = c • P.markovOp h := by
  ext s
  simp only [markovOp_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z' _ => by ring

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem markovOp_neg (h : P.State →ᵇ ℝ) : P.markovOp (-h) = -P.markovOp h := by
  ext s
  simp only [markovOp_apply, BoundedContinuousFunction.neg_apply, mul_neg, Finset.sum_neg_distrib]

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem markovOp_sub (h k : P.State →ᵇ ℝ) : P.markovOp (h - k) = P.markovOp h - P.markovOp k := by
  rw [sub_eq_add_neg, P.markovOp_add, P.markovOp_neg, sub_eq_add_neg]

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem markovOp_iterate_add (n : ℕ) (h k : P.State →ᵇ ℝ) :
    (P.markovOp)^[n] (h + k) = (P.markovOp)^[n] h + (P.markovOp)^[n] k := by
  induction n generalizing h k with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply, P.markovOp_add, ih, Function.iterate_succ_apply,
      Function.iterate_succ_apply]

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem markovOp_iterate_smul (n : ℕ) (c : ℝ) (h : P.State →ᵇ ℝ) :
    (P.markovOp)^[n] (c • h) = c • (P.markovOp)^[n] h := by
  induction n generalizing h with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply, P.markovOp_smul, ih, Function.iterate_succ_apply]

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem markovOp_iterate_neg (n : ℕ) (h : P.State →ᵇ ℝ) :
    (P.markovOp)^[n] (-h) = -(P.markovOp)^[n] h := by
  induction n generalizing h with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply, P.markovOp_neg, ih, Function.iterate_succ_apply]

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem markovOp_iterate_mono (n : ℕ) {h k : P.State →ᵇ ℝ} (hk : ⇑h ≤ ⇑k) :
    ⇑((P.markovOp)^[n] h) ≤ ⇑((P.markovOp)^[n] k) := by
  induction n generalizing h k with
  | zero => simpa using hk
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (P.markovOp_mono hk)

/-- **Duality along the iteration**: the `n`-fold operator against `μ₀` is the test function
against the `n`-th iterate of the distribution. -/
theorem integral_iterate_markovOp (μ₀ : ProbabilityMeasure P.State) (n : ℕ) (h : P.State →ᵇ ℝ) :
    ∫ s, ((P.markovOp)^[n] h) s ∂(μ₀ : Measure P.State)
      = ∫ s, h s ∂((P.pushProb^[n] μ₀ : ProbabilityMeasure P.State) : Measure P.State) := by
  induction n generalizing h with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih (P.markovOp h)]
    exact P.integral_markovOp_iterate μ₀ m h

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The recursion unrolled.** If `D ≤ -G + β M D` pointwise, then
`D ≤ -∑_{t<T} β^t M^t G + β^T M^T D` for every `T`. -/
theorem le_iterate_of_le_markovOp {D G : P.State →ᵇ ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hrec : ∀ s, D s ≤ -G s + β * P.markovOp D s) (T : ℕ) (s : P.State) :
    D s ≤ -(∑ t ∈ Finset.range T, β ^ t * ((P.markovOp)^[t] G) s)
      + β ^ T * ((P.markovOp)^[T] D) s := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h1 : ⇑D ≤ ⇑(-G + β • P.markovOp D) := fun x => by
      simpa only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.neg_apply,
        BoundedContinuousFunction.smul_apply, smul_eq_mul] using hrec x
    have h2 := P.markovOp_iterate_mono T h1 s
    rw [P.markovOp_iterate_add, P.markovOp_iterate_neg, P.markovOp_iterate_smul,
      ← Function.iterate_succ_apply] at h2
    simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.neg_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul] at h2
    rw [Finset.sum_range_succ, pow_succ]
    have h3 := mul_le_mul_of_nonneg_left h2 (pow_nonneg hβ T)
    linarith [ih, h3]

end Operator

/-! ### Two rates, one household, and the value functions on the state space -/

section TwoRates

variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- A bounded continuous function on `ℝ × Z`, restricted to the region. -/
noncomputable def restrictState (Q : IncomeFluctuation Z 0 assetCap) (v : (ℝ × Z) →ᵇ ℝ) :
    Q.State →ᵇ ℝ :=
  v.compContinuous ⟨Q.incl, Q.continuous_incl⟩

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem restrictState_apply (Q : IncomeFluctuation Z 0 assetCap) (v : (ℝ × Z) →ᵇ ℝ)
    (s : Q.State) : Q.restrictState v s = v (Q.incl s) := rfl

/-- The value function of `Q`, on the region. -/
noncomputable def valueState (Q : IncomeFluctuation Z 0 assetCap) : Q.State →ᵇ ℝ :=
  Q.restrictState Q.toExtended.valueFunction

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- The Markov operator of `Q` applied to a restricted function is the expectation over
tomorrow's income of `v` at `Q`'s saving decision. -/
theorem markovOp_restrictState (Q : IncomeFluctuation Z 0 assetCap) (v : (ℝ × Z) →ᵇ ℝ)
    (s : Q.State) :
    Q.markovOp (Q.restrictState v) s
      = ∑ z', Q.transitionMatrix s.2 z' * v (Q.policy (Q.incl s), z') := rfl

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The Bellman identity on the region.** -/
theorem valueState_eq (Q : IncomeFluctuation Z 0 assetCap) (s : Q.State) :
    Q.valueState s = Q.u (Q.consumption (Q.incl s) (Q.policy (Q.incl s)))
      + Q.discount * Q.markovOp Q.valueState s := by
  unfold valueState
  rw [markovOp_restrictState]
  exact Q.valueFunction_eq_policy (Q.incl_mem s)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **Following another policy is no better.** If the saving decision `a'` is feasible for `Q` at
`s` and leaves positive consumption, then `Q`'s value is at least the utility of that consumption
plus the discounted expected value of continuing optimally from `a'`. -/
theorem valueFunction_ge_of_feasible (Q : IncomeFluctuation Z 0 assetCap) {s : ℝ × Z}
    (hs : s.1 ∈ Icc (0 : ℝ) assetCap) {a' : ℝ} (ha' : a' ∈ Q.toExtended.feasible s)
    (hc : 0 < Q.consumption s a') :
    Q.u (Q.consumption s a')
      + Q.discount * ∑ z', Q.transitionMatrix s.2 z' * Q.toExtended.valueFunction (a', z')
        ≤ Q.toExtended.valueFunction s := by
  have h := Q.toExtended.le_bellmanFn Q.toExtended.valueFunction ha'
  have hfix : Q.toExtended.bellmanFn Q.toExtended.valueFunction s
      = Q.toExtended.valueFunction s := by
    have := congrArg (fun w => w s) Q.toExtended.bellman_valueFunction
    simpa using this
  rw [hfix, ExtendedStochasticProgram.objectiveE, Q.reward_eq_coe hs ha' hc, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h
  exact h

/-- **The utility gain from facing economy `Q'` while following economy `Q`'s policy**, as a
bounded continuous function on the region. Positivity of both consumptions is what makes it
continuous. -/
noncomputable def crossGain (Q Q' : IncomeFluctuation Z 0 assetCap)
    (hpos : ∀ s : Q.State, 0 < Q.consumption (Q.incl s) (Q.policy (Q.incl s)))
    (hpos' : ∀ s : Q.State, 0 < Q'.consumption (Q.incl s) (Q.policy (Q.incl s))) :
    Q.State →ᵇ ℝ :=
  mkOfCompact ⟨fun s => Q'.u (Q'.consumption (Q.incl s) (Q.policy (Q.incl s)))
      - Q.u (Q.consumption (Q.incl s) (Q.policy (Q.incl s))), by
    have hpol : Continuous fun s : Q.State => Q.policy (Q.incl s) :=
      continuous_subtype_val.comp Q.continuous_nextAssets
    have hc : Continuous fun s : Q.State => Q.consumption (Q.incl s) (Q.policy (Q.incl s)) :=
      (Q.continuous_resources.comp Q.continuous_incl).sub hpol
    have hc' : Continuous fun s : Q.State => Q'.consumption (Q.incl s) (Q.policy (Q.incl s)) :=
      (Q'.continuous_resources.comp Q.continuous_incl).sub hpol
    exact (Q'.continuousOn_u_dom.comp_continuous hc' fun s => Q'.mem_dom_of_pos (hpos' s)).sub
      (Q.continuousOn_u_dom.comp_continuous hc fun s => Q.mem_dom_of_pos (hpos s))⟩

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem crossGain_apply (Q Q' : IncomeFluctuation Z 0 assetCap)
    (hpos : ∀ s : Q.State, 0 < Q.consumption (Q.incl s) (Q.policy (Q.incl s)))
    (hpos' : ∀ s : Q.State, 0 < Q'.consumption (Q.incl s) (Q.policy (Q.incl s))) (s : Q.State) :
    Q.crossGain Q' hpos hpos' s
      = Q'.u (Q'.consumption (Q.incl s) (Q.policy (Q.incl s)))
        - Q.u (Q.consumption (Q.incl s) (Q.policy (Q.incl s))) := rfl

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The one-period recursion for the value gap.** With `D = V_Q - V_{Q'}` on the region,
`D ≤ -crossGain + β M_Q D`, provided `Q`'s policy is feasible for `Q'` with positive consumption
and the two economies share the discount factor and transitions. -/
theorem valueGap_le_of_feasible (Q Q' : IncomeFluctuation Z 0 assetCap)
    (hβ : (Q'.discount : ℝ) = Q.discount)
    (hprob : ∀ z z' : Z, Q'.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpos : ∀ s : Q.State, 0 < Q.consumption (Q.incl s) (Q.policy (Q.incl s)))
    (hpos' : ∀ s : Q.State, 0 < Q'.consumption (Q.incl s) (Q.policy (Q.incl s)))
    (hfeas : ∀ s : Q.State, Q.policy (Q.incl s) ∈ Q'.toExtended.feasible (Q.incl s))
    (s : Q.State) :
    (Q.valueState - Q'.valueState) s
      ≤ -Q.crossGain Q' hpos hpos' s
        + Q.discount * Q.markovOp (Q.valueState - Q'.valueState) s := by
  have h1 := Q.valueState_eq s
  have h2 := Q'.valueFunction_ge_of_feasible (Q.incl_mem s) (hfeas s) (hpos' s)
  have hexp : ∑ z', Q'.transitionMatrix (Q.incl s).2 z'
      * Q'.toExtended.valueFunction (Q.policy (Q.incl s), z')
      = Q.markovOp Q'.valueState s := by
    simp only [markovOp_apply]
    exact Finset.sum_congr rfl fun z' _ => by rw [hprob]; rfl
  rw [hexp, hβ] at h2
  rw [Q.markovOp_sub, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.sub_apply,
    crossGain_apply]
  have h3 : Q'.valueState s = Q'.toExtended.valueFunction (Q.incl s) := rfl
  linarith [h1, h2, h3]

end TwoRates

/-! ### The inequality along the iteration from a common start -/

section Main

variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- At a zero borrowing limit, the lower-rate policy is feasible at the higher rate. -/
theorem policy_withRate_mem_feasible_of_le {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    (hr : r₁ ≤ r₂) {s : ℝ × Z} (hs : s.1 ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).policy s ∈ (P.withRate r₂ h₂).toExtended.feasible s := by
  have hmem := (P.withRate r₁ h₁).policy_mem s
  rw [feasible_eq] at hmem ⊢
  refine ⟨hmem.1, le_trans hmem.2 ?_⟩
  rw [maxSaving_eq, maxSaving_eq]
  obtain ⟨a, z⟩ := s
  have := P.resources_le_of_le h₁ h₂ hr hs.1 z
  exact min_le_min le_rfl this

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- A policy with positive consumption at the lower rate is feasible there. -/
theorem mem_feasible_of_consumption_pos (Q : IncomeFluctuation Z 0 assetCap) {s : ℝ × Z}
    {a' : ℝ} (ha' : a' ∈ Icc (0 : ℝ) assetCap) (hc : 0 < Q.consumption s a') :
    a' ∈ Q.toExtended.feasible s := by
  rw [feasible_eq, maxSaving_eq]
  refine ⟨ha'.1, le_min ha'.2 ?_⟩
  simp only [consumption] at hc
  linarith

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- At a zero borrowing limit, the lower-rate policy leaves positive consumption at the higher
rate. -/
theorem cross_consumption_pos {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption) (s : P.State) :
    0 < (P.withRate r₂ h₂).consumption ((P.withRate r₁ h₁).incl s)
      ((P.withRate r₁ h₁).policy ((P.withRate r₁ h₁).incl s)) := by
  have h0 : 0 < (P.withRate r₁ h₁).consumption ((P.withRate r₁ h₁).incl s)
      ((P.withRate r₁ h₁).policy ((P.withRate r₁ h₁).incl s)) := hpc₁ _ (incl_mem _ s)
  have hres : (P.withRate r₁ h₁).resources ((P.withRate r₁ h₁).incl s)
      ≤ (P.withRate r₂ h₂).resources ((P.withRate r₁ h₁).incl s) :=
    P.resources_le_of_le h₁ h₂ hr (incl_mem _ s).1 s.2
  simp only [consumption] at h0 ⊢
  linarith

/-- **The Lasry–Lions inequality along the iteration** (finite horizon `T`). Both economies are
run from the common start `μ₀` with their stationary policies; `G₁` is the gain from the higher
rate along the lower-rate policy, `G₂` the (negative) gain from the lower rate along the
higher-rate policy, and `D = V₁ - V₂` on the region. -/
theorem lasryLions_iteration_sum_le {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    (hr : r₁ ≤ r₂)
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hfeas : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap →
      0 < (P.withRate r₁ h₁).consumption s ((P.withRate r₂ h₂).policy s))
    (μ₀ : ProbabilityMeasure P.State) (T : ℕ) :
    ∑ t ∈ Finset.range T, (P.discount : ℝ) ^ t
      * (∫ s, (P.withRate r₁ h₁).crossGain (P.withRate r₂ h₂)
            (fun s => hpc₁ _ (incl_mem _ s)) (P.cross_consumption_pos h₁ h₂ hr hpc₁) s
          ∂(((P.withRate r₁ h₁).pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
        + ∫ s, (P.withRate r₂ h₂).crossGain (P.withRate r₁ h₁)
            (fun s => hpc₂ _ (incl_mem _ s)) (fun s => hfeas _ (incl_mem _ s)) s
          ∂(((P.withRate r₂ h₂).pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State))
      ≤ (P.discount : ℝ) ^ T
        * (∫ s, ((P.withRate r₁ h₁).valueState - (P.withRate r₂ h₂).valueState) s
            ∂(((P.withRate r₁ h₁).pushProb^[T] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
          - ∫ s, ((P.withRate r₁ h₁).valueState - (P.withRate r₂ h₂).valueState) s
            ∂(((P.withRate r₂ h₂).pushProb^[T] μ₀ : ProbabilityMeasure P.State)
              : Measure P.State)) := by
  classical
  set Q₁ := P.withRate r₁ h₁ with hQ₁
  set Q₂ := P.withRate r₂ h₂ with hQ₂
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  set D : P.State →ᵇ ℝ := Q₁.valueState - Q₂.valueState with hD
  set G₁ := Q₁.crossGain Q₂ (fun s => hpc₁ _ (incl_mem _ s)) (P.cross_consumption_pos h₁ h₂ hr hpc₁)
    with hG₁
  set G₂ := Q₂.crossGain Q₁ (fun s => hpc₂ _ (incl_mem _ s)) (fun s => hfeas _ (incl_mem _ s))
    with hG₂
  -- the two recursions
  have hrec₁ : ∀ s, D s ≤ -G₁ s + (P.discount : ℝ) * Q₁.markovOp D s := fun s =>
    Q₁.valueGap_le_of_feasible Q₂ rfl (fun _ _ => rfl) _ _
      (fun s => P.policy_withRate_mem_feasible_of_le h₁ h₂ hr (incl_mem _ s)) s
  have hrec₂ : ∀ s, (-D) s ≤ -G₂ s + (P.discount : ℝ) * Q₂.markovOp (-D) s := fun s => by
    have := Q₂.valueGap_le_of_feasible Q₁ rfl (fun _ _ => rfl)
      (fun s => hpc₂ _ (incl_mem _ s)) (fun s => hfeas _ (incl_mem _ s))
      (fun s => Q₁.mem_feasible_of_consumption_pos (Q₂.policy_mem_region _)
        (hfeas _ (incl_mem _ s))) s
    have hneg : Q₂.valueState - Q₁.valueState = -D := by rw [hD]; abel
    rwa [hneg] at this
  -- unrolled, pointwise
  have hun₁ := Q₁.le_iterate_of_le_markovOp hβ hrec₁ T
  have hun₂ := Q₂.le_iterate_of_le_markovOp hβ hrec₂ T
  -- integrate against `μ₀`
  set β : ℝ := (P.discount : ℝ) with hβdef
  have hint : ∀ (Q : IncomeFluctuation Z 0 assetCap) (h : P.State →ᵇ ℝ) (t : ℕ),
      Integrable (fun s => β ^ t * ((Q.markovOp)^[t] h) s) (μ₀ : Measure P.State) :=
    fun Q h t => (((Q.markovOp)^[t] h).integrable _).const_mul _
  have hsumInt : ∀ (Q : IncomeFluctuation Z 0 assetCap) (h : P.State →ᵇ ℝ),
      Integrable (fun s => -∑ t ∈ Finset.range T, β ^ t * ((Q.markovOp)^[t] h) s)
        (μ₀ : Measure P.State) :=
    fun Q h => (integrable_finsetSum _ fun t _ => hint Q h t).neg
  have hI₁ : ∫ s, D s ∂(μ₀ : Measure P.State)
      ≤ ∫ s, (-∑ t ∈ Finset.range T, β ^ t * ((Q₁.markovOp)^[t] G₁) s
          + β ^ T * ((Q₁.markovOp)^[T] D) s) ∂(μ₀ : Measure P.State) :=
    integral_mono (D.integrable _) ((hsumInt Q₁ G₁).add (hint Q₁ D T)) fun s => hun₁ s
  have hI₂ : ∫ s, (-D) s ∂(μ₀ : Measure P.State)
      ≤ ∫ s, (-∑ t ∈ Finset.range T, β ^ t * ((Q₂.markovOp)^[t] G₂) s
          + β ^ T * ((Q₂.markovOp)^[T] (-D)) s) ∂(μ₀ : Measure P.State) :=
    integral_mono ((-D).integrable _) ((hsumInt Q₂ G₂).add (hint Q₂ (-D) T)) fun s => hun₂ s
  have hR : ∀ (Q : IncomeFluctuation Z 0 assetCap) (h k : P.State →ᵇ ℝ),
      ∫ s, (-∑ t ∈ Finset.range T, β ^ t * ((Q.markovOp)^[t] h) s
          + β ^ T * ((Q.markovOp)^[T] k) s) ∂(μ₀ : Measure P.State)
        = -∑ t ∈ Finset.range T, β ^ t
            * ∫ s, h s ∂((Q.pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
          + β ^ T
            * ∫ s, k s ∂((Q.pushProb^[T] μ₀ : ProbabilityMeasure P.State) : Measure P.State) := by
    intro Q h k
    rw [integral_add (hsumInt Q h) (hint Q k T), integral_neg,
      integral_finsetSum _ fun t _ => hint Q h t]
    simp only [integral_const_mul, Q.integral_iterate_markovOp]
  rw [hR Q₁ G₁ D] at hI₁
  rw [hR Q₂ G₂ (-D)] at hI₂
  have hnegD : ∀ ν : Measure P.State, ∫ s, (-D) s ∂ν = -∫ s, D s ∂ν := fun ν => by
    simp only [BoundedContinuousFunction.neg_apply]
    exact integral_neg _
  rw [hnegD, hnegD] at hI₂
  have hsum : ∑ t ∈ Finset.range T, β ^ t
      * (∫ s, G₁ s ∂((Q₁.pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
        + ∫ s, G₂ s ∂((Q₂.pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State))
      = ∑ t ∈ Finset.range T, β ^ t
          * ∫ s, G₁ s ∂((Q₁.pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
        + ∑ t ∈ Finset.range T, β ^ t
          * ∫ s, G₂ s ∂((Q₂.pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hsum]
  linarith [hI₁, hI₂]

omit [BorelSpace Z] in
/-- A bounded continuous function integrates to at most its norm against a probability measure. -/
theorem abs_integral_le_norm (ν : ProbabilityMeasure P.State) (h : P.State →ᵇ ℝ) :
    |∫ s, h s ∂(ν : Measure P.State)| ≤ ‖h‖ := by
  have := norm_integral_le_of_norm_le_const (μ := (ν : Measure P.State)) (f := fun s => h s)
    (C := ‖h‖) (Filter.Eventually.of_forall fun s => h.norm_coe_le_norm s)
  simpa [Real.norm_eq_abs] using this

/-- **The discounted Lasry–Lions series is at most zero.** The finite-horizon inequality has right
side at most `2 β^T ‖V₁ - V₂‖`, which vanishes; the series converges absolutely. -/
theorem lasryLions_iteration_tsum_nonpos {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    (hr : r₁ ≤ r₂)
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hfeas : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap →
      0 < (P.withRate r₁ h₁).consumption s ((P.withRate r₂ h₂).policy s))
    (μ₀ : ProbabilityMeasure P.State) :
    ∑' t : ℕ, (P.discount : ℝ) ^ t
      * (∫ s, (P.withRate r₁ h₁).crossGain (P.withRate r₂ h₂)
            (fun s => hpc₁ _ (incl_mem _ s)) (P.cross_consumption_pos h₁ h₂ hr hpc₁) s
          ∂(((P.withRate r₁ h₁).pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
        + ∫ s, (P.withRate r₂ h₂).crossGain (P.withRate r₁ h₁)
            (fun s => hpc₂ _ (incl_mem _ s)) (fun s => hfeas _ (incl_mem _ s)) s
          ∂(((P.withRate r₂ h₂).pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State))
      ≤ 0 := by
  set Q₁ := P.withRate r₁ h₁ with hQ₁
  set Q₂ := P.withRate r₂ h₂ with hQ₂
  set G₁ := Q₁.crossGain Q₂ (fun s => hpc₁ _ (incl_mem _ s)) (P.cross_consumption_pos h₁ h₂ hr hpc₁)
    with hG₁
  set G₂ := Q₂.crossGain Q₁ (fun s => hpc₂ _ (incl_mem _ s)) (fun s => hfeas _ (incl_mem _ s))
    with hG₂
  set D : P.State →ᵇ ℝ := Q₁.valueState - Q₂.valueState with hD
  set β : ℝ := (P.discount : ℝ) with hβdef
  have hβ0 : 0 ≤ β := P.discount.coe_nonneg
  have hβ1 : β < 1 := by
    rw [hβdef]
    exact_mod_cast P.discount_lt_one
  set f : ℕ → ℝ := fun t => β ^ t
    * (∫ s, G₁ s ∂((Q₁.pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
      + ∫ s, G₂ s ∂((Q₂.pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State)) with hf
  -- absolute convergence
  have hsumm : Summable f := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (‖G₁‖ + ‖G₂‖)) fun t => ?_
    rw [hf, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
    calc |∫ s, G₁ s ∂((Q₁.pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
          + ∫ s, G₂ s ∂((Q₂.pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State)|
        ≤ |∫ s, G₁ s ∂((Q₁.pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State)|
          + |∫ s, G₂ s ∂((Q₂.pushProb^[t] μ₀ : ProbabilityMeasure P.State) : Measure P.State)| :=
          abs_add_le _ _
      _ ≤ ‖G₁‖ + ‖G₂‖ := add_le_add (P.abs_integral_le_norm _ G₁) (P.abs_integral_le_norm _ G₂)
  -- the partial sums are bounded by a vanishing sequence
  have hpartial : ∀ T : ℕ, ∑ t ∈ Finset.range T, f t ≤ β ^ T * (2 * ‖D‖) := by
    intro T
    refine le_trans (P.lasryLions_iteration_sum_le h₁ h₂ hr hpc₁ hpc₂ hfeas μ₀ T) ?_
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 T)
    have a1 := P.abs_integral_le_norm (Q₁.pushProb^[T] μ₀) D
    have a2 := P.abs_integral_le_norm (Q₂.pushProb^[T] μ₀) D
    rw [abs_le] at a1 a2
    linarith [a1.2, a2.1]
  have hlim : Tendsto (fun T : ℕ => ∑ t ∈ Finset.range T, f t) atTop (𝓝 (∑' t, f t)) :=
    hsumm.tendsto_sum_tsum_nat
  have hzero : Tendsto (fun T : ℕ => β ^ T * (2 * ‖D‖)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (2 * ‖D‖)
    simpa using this
  exact le_of_tendsto_of_tendsto' hlim hzero hpartial

end Main

end IncomeFluctuation

end LeanEconomics
