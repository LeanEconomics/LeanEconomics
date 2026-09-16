/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.Firm
import LeanEconomics.Equilibrium.PositiveCapital

/-!
# The sign change, both ends

`Equilibrium.Firm` proved the LOW end of the sign change — capital demand diverges as the rate
approaches `-δ`, while capital supply can never exceed the asset cap — and recorded that the HIGH
end was open, needing `capitalDemand δ rhi ≤ S rhi` and hence `S rhi > 0`, which it called
"obvious economically and unproved here".

That is now proved. `PositiveCapital` gives strictly positive capital supply, and what remains is
to make the bound QUANTITATIVE: the sign change needs a number, not merely positivity, because
`rhi` has to be chosen from it. `le_aggregateCapital` supplies the number from a uniform lower
bound on saving, and `exists_capitalDemand_le` is the mirror of `exists_capitalDemand_ge` —
Cobb–Douglas demand vanishes at high rates, so any positive supply floor is eventually met.

`exists_sign_change` then brackets the equilibrium from two-sided bounds on capital supply, and
`exists_equilibrium_of_bounds` hands the bracket to `exists_aiyagari_equilibrium`.

## What is still assumed, and it is no longer the demand side

The bounds `m ≤ S r ≤ M` are required at every rate. The upper one is free, from
`aggregateCapital_le`.
The lower one is the live hypothesis: `PositiveCapital` proves it at a rate, and making it uniform
over an interval wide enough for the curves to cross is what the crude constants make hard — the
decline condition alone needs `ε > r/(1+r)`, and with `ε ≈ 0.27` that caps the interval near
`r = 0.37`. So the remaining obstruction is a QUANTITATIVE one about the household side, not a
structural gap in the equilibrium argument.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

/-- **Capital demand vanishes at high rates.** The mirror of `exists_capitalDemand_ge`, and what
makes the high end of the sign change a theorem. -/
theorem exists_capitalDemand_le (δ : ℝ) {m : ℝ} (hm : 0 < m) (r₀ : ℝ) :
    ∃ rhi : ℝ, r₀ ≤ rhi ∧ 0 < rhi + δ ∧ capitalDemand δ rhi ≤ m := by
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  set t : ℝ := 1 / (2 * Real.sqrt m) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  refine ⟨max r₀ (t - δ), le_max_left _ _, ?_, ?_⟩
  · have := le_max_right r₀ (t - δ)
    linarith
  · have hge : t ≤ max r₀ (t - δ) + δ := by
      have := le_max_right r₀ (t - δ); linarith
    have hpos : 0 < max r₀ (t - δ) + δ := lt_of_lt_of_le ht0 hge
    have hts : t ^ 2 * (4 * m) = 1 := by
      rw [ht]
      field_simp
      rw [Real.sq_sqrt hm.le]
      ring
    have hsqle : t ^ 2 ≤ (max r₀ (t - δ) + δ) ^ 2 := by nlinarith [hge, ht0.le]
    simp only [capitalDemand]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsqle, hm, hts]

/-- **The sign change, from two-sided bounds on capital supply.** -/
theorem exists_sign_change (δ : ℝ) {S : ℝ → ℝ} {m M : ℝ} (hm : 0 < m)
    (hlb : ∀ r, m ≤ S r) (hub : ∀ r, S r ≤ M) :
    ∃ rlo rhi : ℝ, 0 < rlo + δ ∧ rlo ≤ rhi ∧ S rlo ≤ capitalDemand δ rlo
      ∧ capitalDemand δ rhi ≤ S rhi := by
  have hM : 0 ≤ M := le_trans hm.le (le_trans (hlb 0) (hub 0))
  obtain ⟨rlo, hrlo, hD⟩ := exists_capitalDemand_ge δ hM
  obtain ⟨rhi, hge, _, hD'⟩ := exists_capitalDemand_le δ hm rlo
  exact ⟨rlo, rhi, hrlo, hge, le_trans (hub rlo) hD, le_trans hD' (hlb rhi)⟩

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z assetCap)

/-- **A quantitative lower bound on capital supply.** Households in income state `z₁` save at
least `ε`, the stationary distribution puts at least `p₀` of its mass there, and capital is mean
saving — so capital is at least `ε p₀`. Positivity alone would not do: the sign change needs a
number from which to choose `rhi`. -/
theorem le_aggregateCapital {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ)
    {z₁ : Z} {p₀ ε : ℝ} (hε : 0 ≤ ε) (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    (hpol : ∀ a ∈ Icc (0 : ℝ) assetCap, ε ≤ P.policy (a, z₁)) :
    ε * p₀ ≤ P.aggregateCapital μ := by
  rw [P.aggregateCapital_eq_integral_policy hμ]
  have hbound : ∀ s : P.State, ε * P.incomeIndicator z₁ s ≤ P.policyCoord s := by
    intro s
    by_cases hz : s.2 = z₁
    · have hge := hpol _ (s.1.2 : ((s.1 : ℝ)) ∈ Icc (0 : ℝ) assetCap)
      have hind : P.incomeIndicator z₁ s = 1 := by simp [hz]
      have hpc : P.policyCoord s = P.policy ((s.1 : ℝ), s.2) := rfl
      rw [hind, mul_one, hpc, hz]
      exact hge
    · have hind : P.incomeIndicator z₁ s = 0 := by simp [hz]
      rw [hind, mul_zero]
      exact (P.policy_mem_region (P.incl s)).1
  calc ε * p₀ ≤ ε * ∫ s, P.incomeIndicator z₁ s ∂(μ : Measure P.State) :=
        mul_le_mul_of_nonneg_left (P.le_integral_incomeIndicator hμ hp) hε
    _ = ∫ s, ε * P.incomeIndicator z₁ s ∂(μ : Measure P.State) := (integral_const_mul _ _).symm
    _ ≤ ∫ s, P.policyCoord s ∂(μ : Measure P.State) :=
        integral_mono (((P.incomeIndicator z₁).integrable _).const_mul ε)
          (P.policyCoord.integrable _) hbound

end IncomeFluctuation

/-- **An Aiyagari equilibrium with the Cobb–Douglas firm**, from two-sided bounds on capital
supply. Both ends of the sign change are now theorems; what is assumed is a positive floor under
capital supply, uniform in the rate. -/
theorem exists_equilibrium_of_bounds {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z]
    [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z] {assetCap : ℝ}
    {Pf : ℝ → IncomeFluctuation Z assetCap} {S : ℝ → ℝ} (δ : ℝ) {m M : ℝ} (hm : 0 < m)
    (hlb : ∀ r, m ≤ S r) (hub : ∀ r, S r ≤ M)
    (hS : ∀ r, ∃ μ : ProbabilityMeasure (Pf r).State,
      (Pf r).IsStationary μ ∧ (Pf r).aggregateCapital μ = S r)
    (hScont : ∀ rlo rhi : ℝ, ContinuousOn S (Icc rlo rhi)) :
    ∃ rlo rhi : ℝ, rlo ≤ rhi ∧ ∃ r ∈ Icc rlo rhi,
      IsAiyagariEquilibrium Pf (capitalDemand δ) r := by
  obtain ⟨rlo, rhi, hrlo, hle, hloS, hhiS⟩ := exists_sign_change δ hm hlb hub
  refine ⟨rlo, rhi, hle, exists_aiyagari_equilibrium hle hS (hScont rlo rhi)
    (continuousOn_capitalDemand hrlo) hloS hhiS⟩

end LeanEconomics
