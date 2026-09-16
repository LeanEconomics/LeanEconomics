/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.MeanField
import LeanEconomics.Models.IncomeFluctuationRate

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

/-! ### More income is better

The only unconditional comparative static in the file, and the pattern for any other: bound the
two operators against each other at a common continuation value. -/

/-- Two economies differing only in income, the second weakly richer in every state. -/
structure RicherThan : Prop where
  income_le : ∀ z, P.income z ≤ Q.income z
  same_transition : ∀ z z', P.transitionMatrix z z' = Q.transitionMatrix z z'
  same_interest : P.interest = Q.interest
  same_discount : (P.discount : ℝ) = (Q.discount : ℝ)
  same_u : P.u = Q.u
  same_dom : P.dom = Q.dom
  maxIncome_le : P.maxIncome ≤ Q.maxIncome

variable {P Q}

theorem RicherThan.resources_le (h : P.RicherThan Q) (s : ℝ × Z) :
    P.resources s ≤ Q.resources s := by
  simp only [resources, h.same_interest]
  linarith [h.income_le s.2]

theorem RicherThan.maxSaving_le (h : P.RicherThan Q) (s : ℝ × Z) :
    P.maxSaving s ≤ Q.maxSaving s := by
  simp only [maxSaving]
  exact max_le_max le_rfl (min_le_min le_rfl (h.resources_le s))

theorem RicherThan.maxConsumption_le (h : P.RicherThan Q) :
    P.maxConsumption ≤ Q.maxConsumption := by
  simp only [maxConsumption, h.same_interest]
  linarith [h.maxIncome_le]

theorem RicherThan.clampedConsumption_le (h : P.RicherThan Q) (p : (ℝ × Z) × ℝ) :
    P.clampedConsumption p ≤ Q.clampedConsumption p := by
  simp only [clampedConsumption, consumption]
  refine min_le_min h.maxConsumption_le (max_le_max le_rfl ?_)
  linarith [h.resources_le p.1]

/-- The richer economy's one-period reward is never smaller. -/
theorem RicherThan.reward_le (h : P.RicherThan Q) (p : (ℝ × Z) × ℝ) :
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

/-- The richer economy's Bellman operator dominates, at every continuation value. -/
theorem RicherThan.bellman_le (h : P.RicherThan Q) (v : (ℝ × Z) →ᵇ ℝ) :
    ⇑(P.toExtended.bellman v) ≤ ⇑(Q.toExtended.bellman v) := by
  intro s
  refine P.toExtended.bellmanFn_le v fun a ha => ?_
  have haQ : a ∈ Q.toExtended.feasible s := ⟨ha.1, le_trans ha.2 (h.maxSaving_le s)⟩
  refine le_trans ?_ (Q.toExtended.le_bellmanFn v haQ)
  simp only [ExtendedStochasticProgram.objectiveE]
  refine add_le_add (h.reward_le (s, a)) (le_of_eq ?_)
  have hexp : P.toExtended.expect v (s, a) = Q.toExtended.expect v (s, a) := by
    simp only [ExtendedStochasticProgram.expect]
    exact Finset.sum_congr rfl fun z' _ => by
      rw [show P.toExtended.prob z' (s, a) = P.transitionMatrix s.2 z' from rfl,
        show Q.toExtended.prob z' (s, a) = Q.transitionMatrix s.2 z' from rfl,
        h.same_transition]
      rfl
  rw [hexp, show ((P.toExtended.discount : ℝ)) = (P.discount : ℝ) from rfl,
    show ((Q.toExtended.discount : ℝ)) = (Q.discount : ℝ) from rfl, h.same_discount]

/-- **More income is better.** Unconditional: no comparison of policies is needed, only of the
operators at a common continuation value. -/
theorem RicherThan.valueFunction_le (h : P.RicherThan Q) (s : ℝ × Z) :
    P.toExtended.valueFunction s ≤ Q.toExtended.valueFunction s :=
  ExtendedStochasticProgram.valueFunction_le_of_bellman_le P.toExtended Q.toExtended
    h.bellman_le s

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
