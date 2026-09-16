/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Analysis.HARA
import LeanEconomics.Equilibrium.MeanField
import LeanEconomics.Models.IncomeFluctuationRateMonotone
import LeanEconomics.Models.BoundedIncomeFluctuation

/-!
# Equilibrium uniqueness under HARA

Light's uniqueness argument needs two things of the utility function: relative risk aversion at
most one, and concavity of the consumption function. Toda (2021) shows the second forces HARA,
so HARA is the class to specialise to.

## What the domain refactor bought

`crra_pinch` recorded a dead end. The old structure required utility to fall to `-∞` at zero
consumption, which forces `γ ≥ 1`; Light's condition forces `γ ≤ 1`; so CRRA was pinched to log,
and Light's programme had exactly one instance. That divergence requirement was never economics --
it was the price of the reward being continuous into `EReal`. With the utility domain a field it
is gone, and `crra_admissible_of_lt_one` below records the consequence: the whole of `0 < γ ≤ 1`
is now available, with `sqrtCES`, `cesWitness` and `nearLog` as realised instances. Light's
programme is no longer a theorem about one utility function.

## The assembly, and the one gap

`mfe_unique` (Light and Weintraub Theorem 2) needs the policy to FALL in aggregate capital.
`hdec_of_rate_antitone` supplies that from Light's Theorem 1 whenever the family's interest rate
falls in aggregate capital -- which is what a downward-sloping capital demand means -- so the
chain is complete down to `ContIncreasingDifferences`, and `mfe_unique_of_rate_family` states it.

`ContIncreasingDifferences` is where Carroll and Kimball sits, and it is NOT proved here. Two
things stand in the way, and they are different in kind.

* Carroll and Kimball's argument runs through risk tolerances adding across the optimisation,
  `T_V (m) = T_u (c) + T_W (m - c)`, which needs the value function twice differentiable. We have
  one-sided first derivatives, conditionally (`IncomeFluctuationEnvelope`), and no more. HARA is
  necessary for the conclusion but it is not sufficient for this route to be available.
* Worse, and specific to this development: `not_concaveOn_consumptionFn_of_cap_binds` proves the
  conclusion FALSE whenever the asset cap binds. The cap is forced by compactness of the state
  space, which the whole distribution layer rests on. So HARA alone cannot discharge the
  hypothesis here at any level of effort -- the cap has to go first, or the hypothesis has to be
  localised to the region where saving stays strictly inside it.

That second point is the useful finding: the obstruction to unconditional uniqueness is the
COMPACT STATE SPACE, not the utility class. Specialising to HARA was necessary and is now done;
it was not sufficient, and the next move is the cap rather than more work on preferences.
-/

open scoped NNReal
open Set Filter Topology MeasureTheory

namespace LeanEconomics

/-! ### The pinch, broken -/

/-- **CRRA with `0 < γ < 1` meets Light's condition and needs no divergence at zero.** Against
`crra_pinch`, which shows the two OLD requirements leave only `γ = 1`. -/
theorem crra_admissible_of_lt_one {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    RelativeRiskAversionLeOne (crraUtility γ)
      ∧ ¬ Tendsto (crraUtility γ) (𝓝[>] 0) atBot
      ∧ IsHARA (crraUtility γ) :=
  ⟨relativeRiskAversionLeOne_crraUtility_iff.mpr hγ1.le,
    not_tendsto_atBot_crraUtility hγ1, isHARA_crraUtility hγ0⟩

/-- Light's condition holds for exactly `γ ≤ 1`, and the bounded structure realises all of it:
`sqrtCES` and `cesWitness` at `γ = 1/2`, `nearLog` at `γ = 15/16`, `dispersed` at `γ = 1`. -/
theorem light_condition_iff {γ : ℝ} : RelativeRiskAversionLeOne (crraUtility γ) ↔ γ ≤ 1 :=
  relativeRiskAversionLeOne_crraUtility_iff

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
-- Stated at a zero borrowing limit: the quantitative saving bounds and Light's rescaling
-- that these results rest on are proved there.
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The policy falls in aggregate capital**, given Light's Theorem 1 and a family whose
interest rate falls in aggregate capital. This is the hypothesis `mfe_unique` asks for, and the
only economics in it is that capital demand slopes down. -/
theorem hdec_of_rate_antitone (Pf : ℝ → IncomeFluctuation Z (0 : ℝ) assetCap)
    (hu : ∀ K₁ K₂ : ℝ, (Pf K₁).u = (Pf K₂).u)
    (hdom : ∀ K₁ K₂ : ℝ, (Pf K₁).dom = (Pf K₂).dom)
    (hβ : ∀ K₁ K₂ : ℝ, ((Pf K₁).discount : ℝ) = ((Pf K₂).discount : ℝ))
    (hinc : ∀ K₁ K₂ : ℝ, (Pf K₁).income = (Pf K₂).income)
    (hrate : ∀ K₁ K₂ : ℝ, K₁ ≤ K₂ → (Pf K₂).interest ≤ (Pf K₁).interest)
    (hid : ∀ K₁ K₂ : ℝ, K₁ ≤ K₂ → ContIncreasingDifferences (Pf K₂) (Pf K₁))
    {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) (s : ℝ × Z) (hs : s.1 ∈ Icc (0 : ℝ) assetCap) :
    (Pf K₂).policy s ≤ (Pf K₁).policy s := by
  have h := policy_mono_interest (Pf K₂) (Pf K₁) (hu K₂ K₁) (hdom K₂ K₁) (hβ K₂ K₁)
    (hinc K₂ K₁) (hrate K₁ K₂ hK) (hid K₁ K₂ hK) (a := s.1) hs s.2
  simpa using h

/-- **Uniqueness of the mean-field equilibrium for a rate family.** Every hypothesis is either
supplied by the existing development or is `ContIncreasingDifferences`, which is Carroll and
Kimball; see the module docstring for why HARA does not discharge it in a capped model. -/
theorem mfe_unique_of_rate_family (Pf : ℝ → IncomeFluctuation Z (0 : ℝ) assetCap)
    (hu : ∀ K₁ K₂ : ℝ, (Pf K₁).u = (Pf K₂).u)
    (hdom : ∀ K₁ K₂ : ℝ, (Pf K₁).dom = (Pf K₂).dom)
    (hβ : ∀ K₁ K₂ : ℝ, ((Pf K₁).discount : ℝ) = ((Pf K₂).discount : ℝ))
    (hinc : ∀ K₁ K₂ : ℝ, (Pf K₁).income = (Pf K₂).income)
    (hprob : ∀ K₁ K₂ : ℝ, ∀ z z' : Z,
      (Pf K₁).transitionMatrix z z' = (Pf K₂).transitionMatrix z z')
    (hrate : ∀ K₁ K₂ : ℝ, K₁ ≤ K₂ → (Pf K₂).interest ≤ (Pf K₁).interest)
    (hid : ∀ K₁ K₂ : ℝ, K₁ ≤ K₂ → ContIncreasingDifferences (Pf K₂) (Pf K₁))
    (hconv : ∀ (K : ℝ) (μ₀ μ : ProbabilityMeasure P.State), (Pf K).IsStationary μ →
      Tendsto (fun n => (Pf K).pushProb^[n] μ₀) atTop (𝓝 μ))
    (huniq : ∀ (K : ℝ) (μ ν : ProbabilityMeasure P.State),
      (Pf K).IsStationary μ → (Pf K).IsStationary ν → μ = ν)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (h₁ : P.IsMeanFieldEquilibrium Pf μ₁) (h₂ : P.IsMeanFieldEquilibrium Pf μ₂) :
    μ₁ = μ₂ :=
  P.mfe_unique Pf hprob
    (fun {_ _} hK s hs => hdec_of_rate_antitone Pf hu hdom hβ hinc hrate hid hK s hs)
    hconv huniq h₁ h₂

end IncomeFluctuation

end LeanEconomics
