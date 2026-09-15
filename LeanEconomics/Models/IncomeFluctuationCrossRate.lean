/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationBounds

/-!
# Comparing two interest rates

Estimates relating two household problems that share an income process and an asset cap but
differ in the interest rate. These are the cross-rate ingredients of the sup-norm estimate on
the Bellman operator; they are stated for two programs rather than for a family, which is
more flexible and needs no indexing.

They are only expressible at all because `assetCap` is a structure PARAMETER: `P` and `Q`
below have the same type, so their state spaces and feasible sets are directly comparable.

## The trap

The obvious estimate is false as stated. Resources differ by

  resources_P s - resources_Q s = (P.interest - Q.interest) * max 0 s.1

which is UNBOUNDED in the state: a household with enormous assets sees an enormous change in
income from a small change in the rate. A sup-norm estimate over all states cannot come from
this quantity directly.

What rescues it is that the difference is only visible through a clamp. Maximum feasible
saving is `min assetCap resources`, so once resources exceed the cap at BOTH rates the
difference is exactly zero. The difference can be nonzero only where some rate leaves
resources below the cap, and that confines the state: `(1 + r) * max 0 s.1 < assetCap`. So
wherever the estimate is not trivially zero, the offending factor is bounded — by
`assetCap / (1 + rlo)`, with `rlo` any lower bound on the rates considered.

That is the shape every cross-rate estimate here takes: a case split on whether the clamp
binds, trivial on one side, and bounded on the other precisely because the clamp failing to
bind confines the state.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ}

/-- `min c ·` is 1-Lipschitz. -/
theorem abs_min_sub_min_le (c x y : ℝ) : |min c x - min c y| ≤ |x - y| := by
  have key : ∀ a b : ℝ, min c a - min c b ≤ |a - b| := by
    intro a b
    rcases le_total c b with h | h
    · have h1 : min c a ≤ c := min_le_left _ _
      have h2 : min c b = c := min_eq_left h
      have h3 := abs_nonneg (a - b)
      linarith
    · have h1 : min c a ≤ a := min_le_right _ _
      have h2 : min c b = b := min_eq_right h
      have h3 : a ≤ b + |a - b| := by cases abs_cases (a - b) <;> linarith
      linarith
  refine abs_le.mpr ⟨?_, key x y⟩
  have h := key y x
  rw [abs_sub_comm] at h
  linarith

/-- Resources differ by the rate gap times assets — a quantity unbounded in the state. -/
theorem resources_sub {P Q : IncomeFluctuation Z assetCap} (hinc : P.income = Q.income)
    (s : ℝ × Z) :
    P.resources s - Q.resources s = (P.interest - Q.interest) * max 0 s.1 := by
  simp only [resources, hinc]
  ring

/-- **Where the cap fails to bind, the state is confined.** This is what tames the unbounded
factor above. -/
theorem max_zero_le_of_resources_lt {P : IncomeFluctuation Z assetCap} {rlo : ℝ}
    (hr : 0 < 1 + rlo) (hP : rlo ≤ P.interest) {s : ℝ × Z} (hlt : P.resources s < assetCap) :
    max 0 s.1 ≤ assetCap / (1 + rlo) := by
  have hm : (0 : ℝ) ≤ max 0 s.1 := le_max_left _ _
  have hy : 0 < P.income s.2 := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le s.2)
  have hres : P.resources s = P.income s.2 + (1 + P.interest) * max 0 s.1 := rfl
  rw [le_div_iff₀ hr]
  nlinarith [hres, hlt, hy, hm, hP]

/-- **The maximum feasible saving moves little when the interest rate does.**

The bound is uniform over the whole state space, which the raw resources gap is not. -/
theorem abs_maxSaving_sub_le {P Q : IncomeFluctuation Z assetCap} (hinc : P.income = Q.income)
    {rlo : ℝ} (hr : 0 < 1 + rlo) (hP : rlo ≤ P.interest) (hQ : rlo ≤ Q.interest) (s : ℝ × Z) :
    |P.maxSaving s - Q.maxSaving s|
      ≤ |P.interest - Q.interest| * (assetCap / (1 + rlo)) := by
  rw [P.maxSaving_eq, Q.maxSaving_eq]
  rcases lt_or_ge (P.resources s) assetCap with hPlt | hPge
  · -- the cap fails to bind at `P`, so the state is confined
    refine le_trans (abs_min_sub_min_le _ _ _) ?_
    rw [resources_sub hinc, abs_mul, abs_of_nonneg (le_max_left 0 s.1)]
    exact mul_le_mul_of_nonneg_left (P.max_zero_le_of_resources_lt hr hP hPlt) (abs_nonneg _)
  · rcases lt_or_ge (Q.resources s) assetCap with hQlt | hQge
    · -- symmetrically at `Q`
      refine le_trans (abs_min_sub_min_le _ _ _) ?_
      rw [resources_sub hinc, abs_mul, abs_of_nonneg (le_max_left 0 s.1)]
      exact mul_le_mul_of_nonneg_left (Q.max_zero_le_of_resources_lt hr hQ hQlt) (abs_nonneg _)
    · -- the cap binds at both rates: the difference is exactly zero
      rw [min_eq_left hPge, min_eq_left hQge, sub_self, abs_zero]
      exact mul_nonneg (abs_nonneg _) (div_nonneg P.assetCap_nonneg hr.le)

end IncomeFluctuation

end LeanEconomics
