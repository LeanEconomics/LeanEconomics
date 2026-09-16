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
theorem exists_capitalDemand_le (A δ : ℝ) {m : ℝ} (hm : 0 < m) (r₀ : ℝ) :
    ∃ rhi : ℝ, r₀ ≤ rhi ∧ 0 < rhi + δ ∧ capitalDemand A δ rhi ≤ m := by
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  set t : ℝ := (|A| + 1) / (2 * Real.sqrt m) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  refine ⟨max r₀ (t - δ), le_max_left _ _, ?_, ?_⟩
  · have := le_max_right r₀ (t - δ)
    linarith
  · have hge : t ≤ max r₀ (t - δ) + δ := by
      have := le_max_right r₀ (t - δ); linarith
    have hpos : 0 < max r₀ (t - δ) + δ := lt_of_lt_of_le ht0 hge
    have hts : t ^ 2 * (4 * m) = (|A| + 1) ^ 2 := by
      rw [ht]
      field_simp
      rw [Real.sq_sqrt hm.le]
      ring
    have hsqle : t ^ 2 ≤ (max r₀ (t - δ) + δ) ^ 2 := by nlinarith [hge, ht0.le]
    have hA : A ^ 2 ≤ (|A| + 1) ^ 2 := by nlinarith [abs_nonneg A, sq_abs A]
    simp only [capitalDemand]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsqle, hm, hts, hA]

/-- **The sign change, from two-sided bounds on capital supply.** -/
theorem exists_sign_change (δ : ℝ) {S : ℝ → ℝ} {m M : ℝ} (hm : 0 < m)
    (hlb : ∀ r, m ≤ S r) (hub : ∀ r, S r ≤ M) :
    ∃ rlo rhi : ℝ, 0 < rlo + δ ∧ rlo ≤ rhi ∧ S rlo ≤ capitalDemand 1 δ rlo
      ∧ capitalDemand 1 δ rhi ≤ S rhi := by
  have hM : 0 ≤ M := le_trans hm.le (le_trans (hlb 0) (hub 0))
  obtain ⟨rlo, hrlo, hD⟩ := exists_capitalDemand_ge δ hM
  obtain ⟨rhi, hge, _, hD'⟩ := exists_capitalDemand_le 1 δ hm rlo
  exact ⟨rlo, rhi, hrlo, hge, le_trans (hub rlo) hD, le_trans hD' (hlb rhi)⟩

/-- **The firm can be calibrated to the households**, rather than the other way round. Given any
rate interval and any two-sided bound on capital supply, some productivity and depreciation put
capital demand above supply at the low end and below it at the high end.

This is what the productivity parameter buys. With `A` fixed at one the demand schedule carries a
scale of its own, and the household economy has to be stretched — in practice to absurd
depreciation rates — for the curves to meet. Here `A` sets the scale and `δ` the curvature, and
the construction is explicit: `η = d √m / (√M + √m)` with `d = rhi - rlo`, then `δ = η - rlo` and
`A = 2 η √M`, at which the low end holds with EQUALITY. -/
theorem exists_firm_of_bounds {rlo rhi m M : ℝ} (hlt : rlo < rhi) (hm : 0 < m) (hmM : m ≤ M) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < rlo + δ ∧ M ≤ capitalDemand A δ rlo ∧ capitalDemand A δ rhi ≤ m := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  set sm : ℝ := Real.sqrt m with hsmdef
  set sM : ℝ := Real.sqrt M with hsMdef
  have hsm0 : 0 < sm := Real.sqrt_pos.mpr hm
  have hsM0 : 0 < sM := Real.sqrt_pos.mpr hM
  have hsm2 : sm ^ 2 = m := Real.sq_sqrt hm.le
  have hsM2 : sM ^ 2 = M := Real.sq_sqrt hM.le
  set d : ℝ := rhi - rlo with hddef
  have hd0 : 0 < d := by rw [hddef]; linarith
  set η : ℝ := d * sm / (sM + sm) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hηkey : η * (sM + sm) = d * sm := by rw [hηdef]; field_simp
  refine ⟨2 * η * sM, η - rlo, by positivity, by linarith, ?_, ?_⟩
  · have hr : rlo + (η - rlo) = η := by ring
    simp only [capitalDemand, hr]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hsM2, hη0]
  · have hr : rhi + (η - rlo) = d + η := by rw [hddef]; ring
    have hkey : η * sM ≤ sm * (d + η) := by nlinarith [hηkey, hη0, hsm0]
    have hsq : (η * sM) ^ 2 ≤ (sm * (d + η)) ^ 2 := by
      nlinarith [hkey, mul_pos hη0 hsM0, mul_pos hsm0 (by linarith : (0 : ℝ) < d + η)]
    simp only [capitalDemand, hr]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsq, hsM2, hsm2]


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
      IsAiyagariEquilibrium Pf (capitalDemand 1 δ) r := by
  obtain ⟨rlo, rhi, hrlo, hle, hloS, hhiS⟩ := exists_sign_change δ hm hlb hub
  refine ⟨rlo, rhi, hle, exists_aiyagari_equilibrium hle hS (hScont rlo rhi)
    (continuousOn_capitalDemand hrlo) hloS hhiS⟩

end LeanEconomics
