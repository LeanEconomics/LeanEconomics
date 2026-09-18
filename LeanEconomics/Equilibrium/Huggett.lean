/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.CapitalSupplyMonotone
import LeanEconomics.Equilibrium.PositiveCapital
import LeanEconomics.Equilibrium.DebtorRate

/-!
# Huggett (1993): market clearing against a constant supply

In Huggett's exchange economy households trade a bond in zero net supply at price `q`, so the
rate is `r = 1/q - 1` and the equilibrium condition is that mean asset holdings equal the bond
supply — a constant, zero. Against a constant, a MONOTONE supply schedule gives nothing: two
rates with `K = 0` are compatible with `K ≡ 0` between them. Single crossing needs supply to be
STRICTLY increasing, and this file supplies the strictness.

`aggregateCapital_lt_of_policy_lt`: if the higher-rate policy dominates the lower-rate one
everywhere and strictly on a set the lower-rate stationary distribution charges, then aggregate
capital is strictly larger at the higher rate. The proof splits `K₂ - K₁` into a dominance term
(the coupling of `CapitalSupplyMonotone`, applied to the higher-rate policy, which rises with
assets) and the integral of the policy gap against the lower-rate distribution, which is
positive on the charged set. `huggett_equilibriumRate_unique` is then the single crossing:
two stationary equilibria with the same bond supply have the same rate.

The pointwise hypotheses are the ones `DebtorRate` proves for creditors — weak monotonicity
for `a ≥ 0`, strict for `a > 0` at an interior choice — and leaves open for debtors, where the
loss term `(r₂ - r₁)·max 0 (-a)` stands in the way. So for Huggett's calibration, with its
negative credit limits, uniqueness reduces to policy monotonicity on the debtor side.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetFloor assetCap : ℝ}

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- The saving policy rises with assets, so `policyCoord` is a test function for dominance. -/
theorem monoAsset_policyCoord (P : IncomeFluctuation Z assetFloor assetCap) :
    MonoAsset P.policyCoord := fun _ a b hab => P.policy_mono a.2 b.2 hab

/-- **Strictly larger capital from a strictly larger policy on a charged set.** -/
theorem aggregateCapital_lt_of_policy_lt (P Q : IncomeFluctuation Z assetFloor assetCap)
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s ≤ Q.policy s)
    {μ₀ μ ν : ProbabilityMeasure P.State}
    (hP : Tendsto (fun m => P.pushProb^[m] μ₀) atTop (𝓝 μ))
    (hQ : Tendsto (fun m => Q.pushProb^[m] μ₀) atTop (𝓝 ν))
    (hμ : P.IsStationary μ) (hν : Q.IsStationary ν)
    (hstrict : 0 < (μ : Measure P.State) {s | P.policyCoord s < Q.policyCoord s}) :
    P.aggregateCapital μ < Q.aggregateCapital ν := by
  have hdom : Dominates μ ν := dominates_of_policy_le P Q hprob hpol hP hQ
  have h1 : ∫ s, Q.policyCoord s ∂(μ : Measure P.State)
      ≤ ∫ s, Q.policyCoord s ∂(ν : Measure P.State) :=
    hdom _ (monoAsset_policyCoord Q)
  -- the policy gap has positive integral against `μ`
  have hnn : 0 ≤ fun s : P.State => Q.policyCoord s - P.policyCoord s :=
    fun s => sub_nonneg.mpr (hpol (P.incl s) (P.incl_mem s))
  have hint : Integrable (fun s : P.State => Q.policyCoord s - P.policyCoord s)
      (μ : Measure P.State) :=
    (Q.policyCoord.integrable _).sub (P.policyCoord.integrable _)
  have hsupp : Function.support (fun s : P.State => Q.policyCoord s - P.policyCoord s)
      = {s | P.policyCoord s < Q.policyCoord s} := by
    ext s
    simp only [Function.mem_support, mem_ofPred_eq, ne_eq, sub_eq_zero]
    constructor
    · intro h
      exact lt_of_le_of_ne (hpol (P.incl s) (P.incl_mem s)) (Ne.symm h)
    · intro h; exact ne_of_gt h
  have hpos : 0 < ∫ s, (Q.policyCoord s - P.policyCoord s) ∂(μ : Measure P.State) := by
    rw [integral_pos_iff_support_of_nonneg hnn hint, hsupp]
    exact hstrict
  rw [integral_sub (Q.policyCoord.integrable _) (P.policyCoord.integrable _)] at hpos
  rw [P.aggregateCapital_eq_integral_policy hμ, Q.aggregateCapital_eq_integral_policy hν]
  linarith

/-- **Huggett's single crossing: two stationary equilibria against the same bond supply have
the same rate**, given a policy that rises with the rate everywhere and strictly on a set the
stationary distribution charges, and convergence to the stationary distribution from a common
start at every rate. -/
theorem huggett_equilibriumRate_unique (P : IncomeFluctuation Z assetFloor assetCap)
    {rlo rhi B : ℝ}
    (hpol : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r < r' →
      ∀ hr : P.RateOK r, ∀ hr' : P.RateOK r', ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
        (P.withRate r hr).policy s ≤ (P.withRate r' hr').policy s)
    (hstrict : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r < r' →
      ∀ hr : P.RateOK r, ∀ hr' : P.RateOK r', ∀ μ : ProbabilityMeasure P.State,
        (P.withRate r hr).IsStationary μ →
          0 < (μ : Measure P.State)
            {s | (P.withRate r hr).policyCoord s < (P.withRate r' hr').policyCoord s})
    (μ₀ : ProbabilityMeasure P.State)
    (htend : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate r hrr).IsStationary μ →
        Tendsto (fun m => (P.withRate r hrr).pushProb^[m] μ₀) atTop (𝓝 μ))
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (hμ₁ : (P.withRate r₁ hrr₁).IsStationary μ₁) (hμ₂ : (P.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : P.aggregateCapital μ₁ = B) (he₂ : P.aggregateCapital μ₂ = B) : r₁ = r₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := aggregateCapital_lt_of_policy_lt (P.withRate r₁ hrr₁) (P.withRate r₂ hrr₂)
      (fun _ _ => rfl) (hpol r₁ h₁ r₂ h₂ hlt hrr₁ hrr₂) (htend r₁ h₁ hrr₁ μ₁ hμ₁)
      (htend r₂ h₂ hrr₂ μ₂ hμ₂) hμ₁ hμ₂ (hstrict r₁ h₁ r₂ h₂ hlt hrr₁ hrr₂ μ₁ hμ₁)
    change P.aggregateCapital μ₁ < P.aggregateCapital μ₂ at this
    linarith
  · have := aggregateCapital_lt_of_policy_lt (P.withRate r₂ hrr₂) (P.withRate r₁ hrr₁)
      (fun _ _ => rfl) (hpol r₂ h₂ r₁ h₁ hlt hrr₂ hrr₁) (htend r₂ h₂ hrr₂ μ₂ hμ₂)
      (htend r₁ h₁ hrr₁ μ₁ hμ₁) hμ₂ hμ₁ (hstrict r₂ h₂ r₁ h₁ hlt hrr₂ hrr₁ μ₂ hμ₂)
    change P.aggregateCapital μ₂ < P.aggregateCapital μ₁ at this
    linarith

end IncomeFluctuation

end LeanEconomics
