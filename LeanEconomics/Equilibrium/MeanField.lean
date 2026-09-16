/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.CapitalSupplyMonotone

/-!
# Light and Weintraub (2022), Theorem 2: uniqueness without continuity

`Equilibrium.Uniqueness` gets a unique equilibrium rate from SINGLE CROSSING: capital supply is
monotone, demand is strictly decreasing, so the curves meet once. That route needs supply to be a
genuine FUNCTION of the rate, hence unique stationary distributions, hence — for the intermediate
value theorem — CONTINUITY of supply, which is what `AiyagariContinuity` is for.

Light and Weintraub give a different argument that needs no continuity and no intermediate value
theorem. It is order-theoretic. Suppose two equilibria with aggregates `K₁ ≤ K₂`. The household
facing the larger aggregate faces the lower rate and so saves less, so its Markov operator is
dominated; running both from a common initial distribution they stay ordered, and ergodicity
carries the order to the two stationary distributions. Testing against the asset coordinate gives
`K₂ ≤ K₁`, and the two aggregates coincide.

Their Theorem 1 asks the transition to be increasing in the WHOLE state; that fails here, because
the policy need not rise with the income shock. Theorem 2 asks only for monotonicity in one
coordinate. `MonoAsset`, introduced in `CapitalSupplyMonotone` for the supply-monotonicity proof,
is exactly that condition — increasing in assets at each fixed income state — so the ingredients
were already in place:

* `Dominates.pushProb` — a dominated policy gives a dominated operator (their `Q` decreasing in
  the aggregate, combined with `Q` increasing in `x₁`);
* `dominates_of_policy_le` — running from a common start and passing to the limit, which is the
  body of their proof;
* `monoAsset_assetCoord` — the aggregator agrees with stochastic dominance.

## What it does not do

It does not weaken the economics. The hypothesis `hdec` — a larger aggregate means a smaller
policy — is Light's Theorem 1 composed with the firm's downward-sloping demand, the same
condition the single-crossing route needs, and Light and Weintraub say so: for Bewley–Aiyagari
"one needs to prove that `g̃` is decreasing in the aggregator". Nor does it escape ergodicity,
which here is still the atom at the borrowing constraint.

What it removes is `continuousOn_capitalSupply` from the dependency chain of uniqueness.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

omit [BorelSpace Z] in
/-- Aggregate capital does not depend on which household problem is posed on the region: the
asset coordinate is the asset coordinate. -/
theorem aggregateCapital_congr (Q : IncomeFluctuation Z assetFloor assetCap)
    (μ : ProbabilityMeasure P.State) : P.aggregateCapital μ = Q.aggregateCapital μ := rfl

/-- **A mean-field equilibrium**: a distribution stationary for the household problem posed at
its OWN aggregate capital. `P` names the region and the aggregator, both of which are the same
for every member of the family. -/
def IsMeanFieldEquilibrium (Pf : ℝ → IncomeFluctuation Z assetFloor assetCap)
    (μ : ProbabilityMeasure P.State) : Prop :=
  (Pf (P.aggregateCapital μ)).IsStationary μ

/-- **Light and Weintraub (2022), Theorem 2**, for the Bewley–Aiyagari model: two mean-field
equilibria carry the same aggregate capital.

No continuity and no intermediate value theorem: the argument is stochastic dominance plus
ergodicity. -/
theorem mfe_aggregateCapital_eq (Pf : ℝ → IncomeFluctuation Z assetFloor assetCap)
    (hprob : ∀ K₁ K₂ : ℝ, ∀ z z' : Z,
      (Pf K₁).transitionMatrix z z' = (Pf K₂).transitionMatrix z z')
    (hdec : ∀ {K₁ K₂ : ℝ}, K₁ ≤ K₂ → ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (Pf K₂).policy s ≤ (Pf K₁).policy s)
    (hconv : ∀ (K : ℝ) (μ₀ μ : ProbabilityMeasure P.State), (Pf K).IsStationary μ →
      Tendsto (fun n => (Pf K).pushProb^[n] μ₀) atTop (𝓝 μ))
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (h₁ : P.IsMeanFieldEquilibrium Pf μ₁) (h₂ : P.IsMeanFieldEquilibrium Pf μ₂) :
    P.aggregateCapital μ₁ = P.aggregateCapital μ₂ := by
  obtain ⟨s₀⟩ : Nonempty P.State := inferInstance
  set μ₀ : ProbabilityMeasure P.State := ⟨Measure.dirac s₀, inferInstance⟩ with hμ₀
  -- the comparison, in whichever direction the aggregates happen to fall
  have key : ∀ {ν₁ ν₂ : ProbabilityMeasure P.State},
      P.IsMeanFieldEquilibrium Pf ν₁ → P.IsMeanFieldEquilibrium Pf ν₂ →
      P.aggregateCapital ν₁ ≤ P.aggregateCapital ν₂ →
      P.aggregateCapital ν₂ ≤ P.aggregateCapital ν₁ := by
    intro ν₁ ν₂ hν₁ hν₂ hle
    have hdom := dominates_of_policy_le (Pf (P.aggregateCapital ν₂))
      (Pf (P.aggregateCapital ν₁)) (fun z z' => hprob _ _ z z')
      (hdec hle) (μ₀ := μ₀)
      (hconv _ μ₀ ν₂ hν₂) (hconv _ μ₀ ν₁ hν₁)
    exact hdom P.assetCoord (monoAsset_assetCoord P)
  rcases le_total (P.aggregateCapital μ₁) (P.aggregateCapital μ₂) with h | h
  · exact le_antisymm h (key h₁ h₂ h)
  · exact le_antisymm (key h₂ h₁ h) h

/-- **Uniqueness of the mean-field equilibrium.** Equal aggregates mean the two distributions are
stationary for the SAME household problem, and ergodicity finishes. -/
theorem mfe_unique (Pf : ℝ → IncomeFluctuation Z assetFloor assetCap)
    (hprob : ∀ K₁ K₂ : ℝ, ∀ z z' : Z,
      (Pf K₁).transitionMatrix z z' = (Pf K₂).transitionMatrix z z')
    (hdec : ∀ {K₁ K₂ : ℝ}, K₁ ≤ K₂ → ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (Pf K₂).policy s ≤ (Pf K₁).policy s)
    (hconv : ∀ (K : ℝ) (μ₀ μ : ProbabilityMeasure P.State), (Pf K).IsStationary μ →
      Tendsto (fun n => (Pf K).pushProb^[n] μ₀) atTop (𝓝 μ))
    (huniq : ∀ (K : ℝ) (μ ν : ProbabilityMeasure P.State),
      (Pf K).IsStationary μ → (Pf K).IsStationary ν → μ = ν)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (h₁ : P.IsMeanFieldEquilibrium Pf μ₁) (h₂ : P.IsMeanFieldEquilibrium Pf μ₂) :
    μ₁ = μ₂ := by
  have hK := P.mfe_aggregateCapital_eq Pf hprob hdec hconv h₁ h₂
  refine huniq (P.aggregateCapital μ₂) μ₁ μ₂ ?_ h₂
  have : (Pf (P.aggregateCapital μ₁)).IsStationary μ₁ := h₁
  rwa [hK] at this

end IncomeFluctuation

end LeanEconomics
