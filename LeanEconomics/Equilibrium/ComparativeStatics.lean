/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.MeanField
import LeanEconomics.Models.IncomeFluctuationRate
import LeanEconomics.Models.CRRA

/-!
# Comparative statics

Two kinds of comparison, and they cost very different amounts.

**Comparisons of VALUE** are cheap. `Blackwell.valueFunction_le` says a dominated operator has a
dominated fixed point, so comparing two economies reduces to comparing their Bellman operators at
a COMMON continuation value -- a one-period calculation. `valueFunction_le_of_income_le` is the
first instance: a household with weakly more income in every state is weakly better off. No
policy comparison, no differentiability, nothing about argmaxes.

**Comparisons of POLICY** are expensive, and that is where Carroll and Kimball sits. Nothing in
this file proves one; policy comparisons are taken as hypotheses, which is the honest division of
labour -- they are what a modeller supplies about their application, and the results here say what
follows for aggregates.

## Acemoglu and Jensen

`mfe_aggregateCapital_le` is the mean-field comparative static: a change that raises every
household's saving, at every level of the aggregate, raises the equilibrium aggregate. The proof
is the one `mfe_aggregateCapital_eq` uses for uniqueness, run in one direction instead of two --
stochastic dominance plus ergodicity, with no continuity and no fixed-point theorem on the
aggregate.

The subtlety worth noting is that the hypothesis has to hold at EVERY aggregate, not just at
equilibrium. The equilibrium aggregate of the perturbed economy is not known in advance, so the
argument needs the comparison wherever it might land; and it needs the unperturbed economy's own
policy to fall in the aggregate, which is the general-equilibrium feedback that makes these
statements harder than their partial-equilibrium versions.
-/

open scoped NNReal
open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P Q : IncomeFluctuation Z assetCap)

/-! ### A wider budget set is better

Three comparisons share one proof. Whatever moves -- income, the interest rate -- the content is
that the second economy's budget set contains the first's and its consumption at each action is
at least as large. `BudgetDominates` isolates that, and the two economic hypotheses reduce to it.
-/

/-- The second economy offers weakly more resources at every state, everything else equal. -/
structure BudgetDominates : Prop where
  resources_le : ∀ s : ℝ × Z, P.resources s ≤ Q.resources s
  maxConsumption_le : P.maxConsumption ≤ Q.maxConsumption
  same_transition : ∀ z z', P.transitionMatrix z z' = Q.transitionMatrix z z'
  same_discount : (P.discount : ℝ) = (Q.discount : ℝ)
  same_u : P.u = Q.u
  same_dom : P.dom = Q.dom

variable {P Q}

theorem BudgetDominates.maxSaving_le (h : P.BudgetDominates Q) (s : ℝ × Z) :
    P.maxSaving s ≤ Q.maxSaving s := by
  simp only [maxSaving]
  exact max_le_max le_rfl (min_le_min le_rfl (h.resources_le s))

theorem BudgetDominates.clampedConsumption_le (h : P.BudgetDominates Q) (p : (ℝ × Z) × ℝ) :
    P.clampedConsumption p ≤ Q.clampedConsumption p := by
  simp only [clampedConsumption, consumption]
  refine min_le_min h.maxConsumption_le (max_le_max le_rfl ?_)
  linarith [h.resources_le p.1]

/-- The wider economy's one-period reward is never smaller. -/
theorem BudgetDominates.reward_le (h : P.BudgetDominates Q) (p : (ℝ × Z) × ℝ) :
    P.toExtended.reward p ≤ Q.toExtended.reward p := by
  by_cases hmem : P.clampedConsumption p ∈ P.dom
  · have hmemQ : Q.clampedConsumption p ∈ Q.dom := by
      rw [← h.same_dom]
      exact P.dom_upward hmem (h.clampedConsumption_le p)
    change extendDom P.dom P.u (P.clampedConsumption p)
      ≤ extendDom Q.dom Q.u (Q.clampedConsumption p)
    rw [extendDom_of_mem hmem, extendDom_of_mem hmemQ, EReal.coe_le_coe_iff, h.same_u]
    exact Q.monotoneOn_u_dom (h.same_dom ▸ hmem) hmemQ (h.clampedConsumption_le p)
  · change extendDom P.dom P.u (P.clampedConsumption p) ≤ _
    rw [extendDom_of_not_mem hmem]
    exact bot_le

theorem BudgetDominates.expect_eq (h : P.BudgetDominates Q) (v : (ℝ × Z) →ᵇ ℝ)
    (p : (ℝ × Z) × ℝ) : P.toExtended.expect v p = Q.toExtended.expect v p := by
  simp only [ExtendedStochasticProgram.expect]
  exact Finset.sum_congr rfl fun z' _ => by
    rw [show P.toExtended.prob z' p = P.transitionMatrix p.1.2 z' from rfl,
      show Q.toExtended.prob z' p = Q.transitionMatrix p.1.2 z' from rfl, h.same_transition]
    rfl

/-- The wider economy's Bellman operator dominates, at every continuation value. -/
theorem BudgetDominates.bellman_le (h : P.BudgetDominates Q) (v : (ℝ × Z) →ᵇ ℝ) :
    ⇑(P.toExtended.bellman v) ≤ ⇑(Q.toExtended.bellman v) := by
  intro s
  refine P.toExtended.bellmanFn_le v fun a ha => ?_
  have haQ : a ∈ Q.toExtended.feasible s := ⟨ha.1, le_trans ha.2 (h.maxSaving_le s)⟩
  refine le_trans ?_ (Q.toExtended.le_bellmanFn v haQ)
  simp only [ExtendedStochasticProgram.objectiveE]
  refine add_le_add (h.reward_le (s, a)) (le_of_eq ?_)
  rw [h.expect_eq v (s, a), show ((P.toExtended.discount : ℝ)) = (P.discount : ℝ) from rfl,
    show ((Q.toExtended.discount : ℝ)) = (Q.discount : ℝ) from rfl, h.same_discount]

/-- **A wider budget set is better.** Unconditional: no comparison of policies is needed, only
of the operators at a common continuation value. -/
theorem BudgetDominates.valueFunction_le (h : P.BudgetDominates Q) (s : ℝ × Z) :
    P.toExtended.valueFunction s ≤ Q.toExtended.valueFunction s :=
  ExtendedStochasticProgram.valueFunction_le_of_bellman_le P.toExtended Q.toExtended
    h.bellman_le s

variable (P Q)

/-- Two economies differing only in income, the second weakly richer in every state. -/
structure RicherThan : Prop where
  income_le : ∀ z, P.income z ≤ Q.income z
  maxIncome_le : P.maxIncome ≤ Q.maxIncome
  same_interest : P.interest = Q.interest
  same_transition : ∀ z z', P.transitionMatrix z z' = Q.transitionMatrix z z'
  same_discount : (P.discount : ℝ) = (Q.discount : ℝ)
  same_u : P.u = Q.u
  same_dom : P.dom = Q.dom

/-- Two economies differing only in the interest rate, the second paying weakly more. Assets are
nonnegative, so a higher rate can only widen the budget set -- there is no wealth effect of the
wrong sign to worry about here, which is why the comparison is unconditional. -/
structure HigherRateThan : Prop where
  interest_le : P.interest ≤ Q.interest
  same_income : ∀ z, P.income z = Q.income z
  same_maxIncome : P.maxIncome = Q.maxIncome
  same_transition : ∀ z z', P.transitionMatrix z z' = Q.transitionMatrix z z'
  same_discount : (P.discount : ℝ) = (Q.discount : ℝ)
  same_u : P.u = Q.u
  same_dom : P.dom = Q.dom

variable {P Q}

theorem RicherThan.budgetDominates (h : P.RicherThan Q) : P.BudgetDominates Q where
  resources_le s := by
    simp only [resources, h.same_interest]
    linarith [h.income_le s.2]
  maxConsumption_le := by
    simp only [maxConsumption, h.same_interest]
    linarith [h.maxIncome_le]
  same_transition := h.same_transition
  same_discount := h.same_discount
  same_u := h.same_u
  same_dom := h.same_dom

theorem HigherRateThan.budgetDominates (h : P.HigherRateThan Q) : P.BudgetDominates Q where
  resources_le s := by
    simp only [resources, h.same_income s.2]
    have hnn : (0 : ℝ) ≤ max 0 s.1 := le_max_left _ _
    nlinarith [h.interest_le, hnn]
  maxConsumption_le := by
    simp only [maxConsumption, h.same_maxIncome]
    nlinarith [h.interest_le, P.assetCap_nonneg]
  same_transition := h.same_transition
  same_discount := h.same_discount
  same_u := h.same_u
  same_dom := h.same_dom

/-- **More income is better.** -/
theorem RicherThan.valueFunction_le (h : P.RicherThan Q) (s : ℝ × Z) :
    P.toExtended.valueFunction s ≤ Q.toExtended.valueFunction s :=
  h.budgetDominates.valueFunction_le s

/-- **A higher interest rate is better**, with no restriction on preferences. -/
theorem HigherRateThan.valueFunction_le (h : P.HigherRateThan Q) (s : ℝ × Z) :
    P.toExtended.valueFunction s ≤ Q.toExtended.valueFunction s :=
  h.budgetDominates.valueFunction_le s

/-! ### Patience

The one comparison where the class of continuation values matters. A more patient agent's
operator does NOT dominate at every continuation value -- with a continuation worth less than
nothing, weighting it more is worse. It dominates on NONNEGATIVE continuations, and when utility
is bounded below by zero -- CES with `γ < 1`, where `u 0 = 0` -- that is the class value function
iteration from `0` stays in. So this is a comparative static that the unbounded structure could
not have stated, never mind proved. -/

variable (P Q)

/-- Two economies differing only in the discount factor, the second more patient. -/
structure MorePatientThan : Prop where
  discount_le : (P.discount : ℝ) ≤ (Q.discount : ℝ)
  same_income : ∀ z, P.income z = Q.income z
  same_maxIncome : P.maxIncome = Q.maxIncome
  same_minIncome : P.minIncome = Q.minIncome
  same_interest : P.interest = Q.interest
  same_transition : ∀ z z', P.transitionMatrix z z' = Q.transitionMatrix z z'
  same_u : P.u = Q.u
  same_dom : P.dom = Q.dom

variable {P Q}

theorem MorePatientThan.feasible_eq (h : P.MorePatientThan Q) (s : ℝ × Z) :
    P.toExtended.feasible s = Q.toExtended.feasible s := by
  have hres : P.resources s = Q.resources s := by
    simp only [resources, h.same_income s.2, h.same_interest]
  simp only [P.feasible_eq, Q.feasible_eq, maxSaving, hres]

theorem MorePatientThan.reward_eq (h : P.MorePatientThan Q) (p : (ℝ × Z) × ℝ) :
    P.toExtended.reward p = Q.toExtended.reward p := by
  have hres : P.resources p.1 = Q.resources p.1 := by
    simp only [resources, h.same_income p.1.2, h.same_interest]
  have hmax : P.maxConsumption = Q.maxConsumption := by
    simp only [maxConsumption, h.same_maxIncome, h.same_interest]
  change extendDom P.dom P.u (P.clampedConsumption p) = extendDom Q.dom Q.u _
  simp only [clampedConsumption, consumption, hres, hmax, h.same_u, h.same_dom]

/-- **More patience is better**, when utility is bounded below by zero. -/
theorem MorePatientThan.valueFunction_le (h : P.MorePatientThan Q) (hmin : 0 ≤ P.u P.minIncome)
    (s : ℝ × Z) : P.toExtended.valueFunction s ≤ Q.toExtended.valueFunction s := by
  refine ExtendedStochasticProgram.valueFunction_le_of_bellman_le_on P.toExtended Q.toExtended
    (fun v => 0 ≤ ⇑v) (by intro _; simp) ?_ ?_ s
  · exact fun v hv => P.toExtended.zero_le_bellman hmin hv
  · intro v hv t
    refine P.toExtended.bellmanFn_le v fun a ha => ?_
    have haQ : a ∈ Q.toExtended.feasible t := (h.feasible_eq t) ▸ ha
    refine le_trans ?_ (Q.toExtended.le_bellmanFn v haQ)
    simp only [ExtendedStochasticProgram.objectiveE]
    refine add_le_add (le_of_eq (h.reward_eq (t, a))) ?_
    have hexp : P.toExtended.expect v (t, a) = Q.toExtended.expect v (t, a) := by
      simp only [ExtendedStochasticProgram.expect]
      exact Finset.sum_congr rfl fun z' _ => by
        rw [show P.toExtended.prob z' (t, a) = P.transitionMatrix t.2 z' from rfl,
          show Q.toExtended.prob z' (t, a) = Q.transitionMatrix t.2 z' from rfl,
          h.same_transition]
        rfl
    have hexp0 : 0 ≤ P.toExtended.expect v (t, a) := by
      refine Finset.sum_nonneg fun z _ => ?_
      exact mul_nonneg (P.toExtended.prob_nonneg z _) (hv _)
    rw [EReal.coe_le_coe_iff, hexp]
    rw [show ((P.toExtended.discount : ℝ)) = (P.discount : ℝ) from rfl,
      show ((Q.toExtended.discount : ℝ)) = (Q.discount : ℝ) from rfl]
    rw [hexp] at hexp0
    nlinarith [h.discount_le, hexp0]

/-- CES with `γ < 1` has nonnegative utility, so `MorePatientThan.valueFunction_le` applies to
exactly the family the bounded structure was built for -- `sqrtCES`, `cesWitness`, `nearLog`. For
log and CRRA with `γ ≥ 1` utility is unbounded below and the comparison is unavailable by this
route. -/
theorem crraUtility_nonneg {γ : ℝ} (hγ1 : γ < 1) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ crraUtility γ c := by
  rw [crraUtility_of_ne (by linarith)]
  exact div_nonneg (Real.rpow_nonneg hc _) (by linarith)

end IncomeFluctuation

/-! ### Acemoglu and Jensen: the equilibrium aggregate -/

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z assetCap)

/-- **A change that raises saving raises the equilibrium aggregate.**

`hPQ` is the partial-equilibrium content: at every level of the aggregate, the perturbed economy
saves at least as much. `hdecP` is the general-equilibrium feedback: in the unperturbed economy a
larger aggregate depresses saving. Neither is proved here -- `hdecP` is Light's Theorem 1 and
`hPQ` is whatever the perturbation is -- and together they give the comparison of equilibria. -/
theorem mfe_aggregateCapital_le (Pf Qf : ℝ → IncomeFluctuation Z assetCap)
    (hprob : ∀ K₁ K₂ : ℝ, ∀ z z' : Z,
      (Qf K₁).transitionMatrix z z' = (Pf K₂).transitionMatrix z z')
    (hdecP : ∀ {K₁ K₂ : ℝ}, K₁ ≤ K₂ → ∀ s : ℝ × Z, s.1 ∈ Icc 0 assetCap →
      (Pf K₂).policy s ≤ (Pf K₁).policy s)
    (hPQ : ∀ K : ℝ, ∀ s : ℝ × Z, s.1 ∈ Icc 0 assetCap → (Pf K).policy s ≤ (Qf K).policy s)
    (hconvP : ∀ (K : ℝ) (μ₀ μ : ProbabilityMeasure P.State), (Pf K).IsStationary μ →
      Tendsto (fun n => (Pf K).pushProb^[n] μ₀) atTop (𝓝 μ))
    (hconvQ : ∀ (K : ℝ) (μ₀ μ : ProbabilityMeasure P.State), (Qf K).IsStationary μ →
      Tendsto (fun n => (Qf K).pushProb^[n] μ₀) atTop (𝓝 μ))
    {μ ν : ProbabilityMeasure P.State}
    (hμ : P.IsMeanFieldEquilibrium Pf μ) (hν : P.IsMeanFieldEquilibrium Qf ν) :
    P.aggregateCapital μ ≤ P.aggregateCapital ν := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨s₀⟩ : Nonempty P.State := inferInstance
  set μ₀ : ProbabilityMeasure P.State := ⟨Measure.dirac s₀, inferInstance⟩ with hμ₀
  set Kμ : ℝ := P.aggregateCapital μ with hKμ
  set Kν : ℝ := P.aggregateCapital ν with hKν
  -- at the smaller aggregate the perturbed economy saves at least as much as the
  -- unperturbed one does at the larger
  have hchain : ∀ s : ℝ × Z, s.1 ∈ Icc 0 assetCap → (Pf Kμ).policy s ≤ (Qf Kν).policy s := by
    intro s hs
    exact le_trans (hdecP hcon.le s hs) (hPQ Kν s hs)
  have hdom := dominates_of_policy_le (Pf Kμ) (Qf Kν) (fun z z' => (hprob Kν Kμ z z').symm)
    hchain (μ₀ := μ₀) (hconvP _ μ₀ μ hμ) (hconvQ _ μ₀ ν hν)
  have := hdom P.assetCoord (monoAsset_assetCoord P)
  exact absurd this (not_le.mpr hcon)

end IncomeFluctuation

end LeanEconomics
