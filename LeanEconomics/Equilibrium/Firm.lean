/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.AiyagariContinuity

/-!
# The firm side

`exists_aiyagari_equilibrium` takes any continuous capital demand schedule. This file supplies
one that is DERIVED from a production function rather than posited, so the equilibrium theorem
becomes a statement about a model rather than about a schedule.

The technology is Cobb–Douglas with `α = 1/2`, one unit of labour and total factor
productivity `A`, so output is `A √K` and the marginal product of capital is `A / (2√K)`.
Setting the net marginal product equal to the interest rate,

  A / (2√K) - δ = r,

and solving gives `K = A² / (4(r+δ)²)`. `capitalDemand_marginalProduct` checks that the
solution really does satisfy the first-order condition, which is what stops the formula from
being an arbitrary decreasing function with a suggestive name.

Productivity is a PARAMETER rather than fixed at one because the demand schedule otherwise
carries a scale the household side has to be stretched to meet. `exists_firm_of_bounds` is what
that buys: given any rate interval and any two-sided bound on capital supply, some firm meets it
there. The firm can be calibrated to the households rather than the other way round.

`α = 1/2` is chosen so the inversion is algebraic. A general exponent would need `rpow` and
would change nothing conceptually.

## What this does and does not close

Equilibrium needs excess demand to change sign across `[rlo, rhi]`. The LOW end is now a
theorem: capital demand diverges as `r` approaches `-δ`, while capital supply can never exceed
the asset cap, so `capitalDemand δ rlo ≥ assetCap ≥ S rlo` for `rlo` close enough to `-δ`.

The HIGH end is not, and the obstruction is economic rather than technical. It needs
`capitalDemand δ rhi ≤ S rhi`, and since Cobb–Douglas demand is strictly positive that forces
`S rhi > 0` -- households must hold capital at high interest rates. That is obvious
economically and unproved here. Worse, it is in tension with the only calibration whose
Doeblin hypotheses are verified: the impatient household of `NonVacuity` is driven to the
borrowing constraint at EVERY asset level, so its stationary distribution sits at zero assets
and its capital supply is identically zero. A calibration with a genuine equilibrium needs the
constraint to bind at the bad income state but not the good one, which the uniform corner
condition of `policy_eq_zero_of_corner` cannot express.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

/-- Capital demand from a Cobb–Douglas firm with `α = 1/2`, unit labour and unit productivity:
the capital stock at which the net marginal product equals `r`. -/
noncomputable def capitalDemand (A δ r : ℝ) : ℝ := A ^ 2 / (4 * (r + δ) ^ 2)

/-- **The demand schedule solves the firm's first-order condition.** -/
theorem capitalDemand_marginalProduct {A δ r : ℝ} (hA : 0 < A) (h : 0 < r + δ) :
    A / (2 * Real.sqrt (capitalDemand A δ r)) - δ = r := by
  have hsq : capitalDemand A δ r = (A / (2 * (r + δ))) ^ 2 := by
    simp only [capitalDemand]; field_simp; ring
  rw [hsq, Real.sqrt_sq (by positivity)]
  field_simp
  ring

theorem capitalDemand_pos {A δ r : ℝ} (hA : 0 < A) (h : 0 < r + δ) :
    0 < capitalDemand A δ r := by
  simp only [capitalDemand]; positivity

theorem continuousOn_capitalDemand {A δ rlo rhi : ℝ} (h : 0 < rlo + δ) :
    ContinuousOn (capitalDemand A δ) (Icc rlo rhi) := by
  refine ContinuousOn.div continuousOn_const ?_ fun r hr => ?_
  · exact (continuous_const.mul ((continuous_id.add continuous_const).pow 2)).continuousOn
  · have : 0 < r + δ := lt_of_lt_of_le h (by linarith [hr.1])
    positivity

/-- Capital demand falls as the interest rate rises. -/
theorem capitalDemand_antitoneOn {A δ : ℝ} {rlo rhi : ℝ} (h : 0 < rlo + δ) :
    AntitoneOn (capitalDemand A δ) (Icc rlo rhi) := by
  intro a ha b hb hab
  have ha' : 0 < a + δ := lt_of_lt_of_le h (by linarith [ha.1])
  have hb' : 0 < b + δ := lt_of_lt_of_le h (by linarith [hb.1])
  simp only [capitalDemand]
  gcongr

/-- **Capital demand diverges as the rate approaches `-δ`.** Given any bound -- in particular
the asset cap, which capital supply can never exceed -- some admissible rate demands more. -/
theorem exists_capitalDemand_ge (δ : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ rlo : ℝ, 0 < rlo + δ ∧ M ≤ capitalDemand 1 δ rlo := by
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  refine ⟨(1 / (2 * (M + 1))) - δ, by simp only [sub_add_cancel]; positivity, ?_⟩
  have hrw : (1 / (2 * (M + 1)) - δ) + δ = 1 / (2 * (M + 1)) := by ring
  simp only [capitalDemand, hrw, one_pow]
  rw [le_div_iff₀ (by positivity)]
  have hexp : 4 * (1 / (2 * (M + 1))) ^ 2 = 1 / (M + 1) ^ 2 := by field_simp; ring
  rw [hexp, mul_one_div, div_le_one (by positivity)]
  nlinarith

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z assetCap)

/-- **Capital supply never exceeds the asset cap**, because every household's assets are
capped. This is what makes the low end of the sign change a theorem. -/
theorem aggregateCapital_le (μ : ProbabilityMeasure P.State) :
    P.aggregateCapital μ ≤ assetCap := by
  have hle : ∀ s : P.State, P.assetCoord s ≤ assetCap := fun s => s.1.2.2
  calc P.aggregateCapital μ ≤ ∫ _s, assetCap ∂(μ : Measure P.State) :=
        integral_mono (P.assetCoord.integrable _) (integrable_const _) hle
    _ = assetCap := by simp

/-- Capital supply is nonnegative. -/
theorem aggregateCapital_nonneg (μ : ProbabilityMeasure P.State) :
    0 ≤ P.aggregateCapital μ := by
  have hle : ∀ s : P.State, (0 : ℝ) ≤ P.assetCoord s := fun s => s.1.2.1
  calc (0 : ℝ) = ∫ _s, (0 : ℝ) ∂(μ : Measure P.State) := by simp
    _ ≤ P.aggregateCapital μ :=
        integral_mono (integrable_const _) (P.assetCoord.integrable _) hle

/-- **The low end of the sign change is a theorem.** -/
theorem exists_rate_capitalDemand_ge (δ : ℝ) (μ : ProbabilityMeasure P.State) :
    ∃ rlo : ℝ, 0 < rlo + δ ∧ P.aggregateCapital μ ≤ capitalDemand 1 δ rlo := by
  obtain ⟨rlo, hrlo, hge⟩ := exists_capitalDemand_ge δ P.assetCap_nonneg
  exact ⟨rlo, hrlo, le_trans (P.aggregateCapital_le μ) hge⟩

end IncomeFluctuation

end LeanEconomics
