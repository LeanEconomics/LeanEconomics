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

open Set BoundedContinuousFunction

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

/-! ### The clamped consumption gap

Harder than the saving bound in two ways. The clamp LEVEL `maxConsumption` now moves with the
rate too, since it is `maxIncome + (1 + r) * assetCap`; and the chosen saving has to be
carried along, which is where the `θ` reparametrisation earns its place — with the choice
written as a fraction of maximum feasible saving, the same `θ` can be fed to both programs. -/

/-- `min` is 1-Lipschitz in both arguments at once. -/
theorem abs_min_sub_min_le_max (A B x y : ℝ) :
    |min A x - min B y| ≤ max |A - B| |x - y| := by
  set D := max |A - B| |x - y| with hD
  have key : ∀ a b u v : ℝ, |a - b| ≤ D → |u - v| ≤ D → min a u - min b v ≤ D := by
    intro a b u v hab huv
    have h1 : a ≤ b + D := by cases abs_cases (a - b) <;> linarith
    have h2 : u ≤ v + D := by cases abs_cases (u - v) <;> linarith
    have h3 : min a u ≤ min (b + D) (v + D) := min_le_min h1 h2
    rw [min_add_add_right] at h3
    linarith
  have hAB : |A - B| ≤ D := le_max_left _ _
  have hxy : |x - y| ≤ D := le_max_right _ _
  refine abs_le.mpr ⟨?_, key A B x y hAB hxy⟩
  have h := key B A y x (by rwa [abs_sub_comm]) (by rwa [abs_sub_comm])
  linarith

/-- The clamp level itself moves with the rate, but only by a bounded amount. -/
theorem abs_maxConsumption_sub {P Q : IncomeFluctuation Z assetCap}
    (hmax : P.maxIncome = Q.maxIncome) :
    |P.maxConsumption - Q.maxConsumption| = |P.interest - Q.interest| * assetCap := by
  have hexp : P.maxConsumption - Q.maxConsumption
      = (P.interest - Q.interest) * assetCap := by
    simp only [maxConsumption, hmax]; ring
  rw [hexp, abs_mul, abs_of_nonneg P.assetCap_nonneg]

/-- **Where the consumption clamp fails to bind, the state is confined.** The same move as
`max_zero_le_of_resources_lt`, one clamp further along. -/
theorem max_zero_le_of_consumption_lt {P : IncomeFluctuation Z assetCap} {rlo : ℝ}
    (hr : 0 < 1 + rlo) (hP : rlo ≤ P.interest) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) {s : ℝ × Z}
    (hlt : P.consumption s (θ * P.maxSaving s) < P.maxConsumption) :
    max 0 s.1 ≤ (P.maxIncome + assetCap) / (1 + rlo) + assetCap := by
  have hp1 : 0 < 1 + P.interest := P.interest_gt_neg_one
  have hcap := P.assetCap_nonneg
  have hnum : 0 ≤ P.maxIncome + assetCap := by
    have := le_trans P.minIncome_pos.le (P.minIncome_le_maxIncome)
    linarith
  have hy : 0 ≤ P.income s.2 := le_trans P.minIncome_pos.le (P.minIncome_le s.2)
  have hms0 := P.maxSaving_nonneg s
  have hmsle : P.maxSaving s ≤ assetCap := P.maxSaving_le_assetCap s
  have hres : P.resources s = P.income s.2 + (1 + P.interest) * max 0 s.1 := rfl
  have hmc : P.maxConsumption = P.maxIncome + (1 + P.interest) * assetCap := rfl
  have hcons : P.consumption s (θ * P.maxSaving s)
      = P.resources s - θ * P.maxSaving s := rfl
  -- saving at most the cap, so consumption is at least resources minus the cap
  have hsav : θ * P.maxSaving s ≤ assetCap := by nlinarith [hθ.1, hθ.2]
  have hstep : (max 0 s.1 - assetCap) * (1 + P.interest) < P.maxIncome + assetCap := by
    rw [hcons, hres] at hlt; rw [hmc] at hlt; nlinarith
  have hlt' : max 0 s.1 - assetCap < (P.maxIncome + assetCap) / (1 + P.interest) :=
    (lt_div_iff₀ hp1).mpr hstep
  have hdiv : (P.maxIncome + assetCap) / (1 + P.interest)
      ≤ (P.maxIncome + assetCap) / (1 + rlo) := by gcongr
  linarith

/-- **The clamped consumption gap.** Uniform over the state space and over the choice `θ`. -/
theorem abs_clamped_consumption_sub_le {P Q : IncomeFluctuation Z assetCap}
    (hinc : P.income = Q.income) (hmax : P.maxIncome = Q.maxIncome)
    {rlo : ℝ} (hr : 0 < 1 + rlo) (hP : rlo ≤ P.interest) (hQ : rlo ≤ Q.interest)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (s : ℝ × Z) :
    |min P.maxConsumption (P.consumption s (θ * P.maxSaving s))
        - min Q.maxConsumption (Q.consumption s (θ * Q.maxSaving s))|
      ≤ |P.interest - Q.interest|
          * ((P.maxIncome + assetCap) / (1 + rlo) + assetCap + assetCap / (1 + rlo)) := by
  have hcap := P.assetCap_nonneg
  have hgap : (0 : ℝ) ≤ |P.interest - Q.interest| := abs_nonneg _
  set M : ℝ := (P.maxIncome + assetCap) / (1 + rlo) + assetCap with hM
  -- the gap in unclamped consumption, given a bound on the state
  have hcons : ∀ B : ℝ, max 0 s.1 ≤ B →
      |P.consumption s (θ * P.maxSaving s) - Q.consumption s (θ * Q.maxSaving s)|
        ≤ |P.interest - Q.interest| * (B + assetCap / (1 + rlo)) := by
    intro B hB
    have hms := abs_maxSaving_sub_le hinc hr hP hQ s
    have hres := resources_sub hinc s
    have hexp : P.consumption s (θ * P.maxSaving s) - Q.consumption s (θ * Q.maxSaving s)
        = (P.resources s - Q.resources s) - θ * (P.maxSaving s - Q.maxSaving s) := by
      simp only [consumption]; ring
    rw [hexp, hres]
    have h1 : |(P.interest - Q.interest) * max 0 s.1| ≤ |P.interest - Q.interest| * B := by
      rw [abs_mul, abs_of_nonneg (le_max_left 0 s.1)]
      exact mul_le_mul_of_nonneg_left hB hgap
    have h2 : |θ * (P.maxSaving s - Q.maxSaving s)|
        ≤ |P.interest - Q.interest| * (assetCap / (1 + rlo)) := by
      rw [abs_mul, abs_of_nonneg hθ.1]
      calc θ * |P.maxSaving s - Q.maxSaving s|
          ≤ 1 * |P.maxSaving s - Q.maxSaving s| :=
            mul_le_mul_of_nonneg_right hθ.2 (abs_nonneg _)
        _ = |P.maxSaving s - Q.maxSaving s| := one_mul _
        _ ≤ _ := hms
    have h3 := abs_sub (((P.interest - Q.interest) * max 0 s.1))
      (θ * (P.maxSaving s - Q.maxSaving s))
    nlinarith [h1, h2, h3]
  have hnum : 0 ≤ P.maxIncome + assetCap := by
    have := le_trans P.minIncome_pos.le P.minIncome_le_maxIncome
    linarith
  have hMcap : assetCap ≤ M := by
    have : 0 ≤ (P.maxIncome + assetCap) / (1 + rlo) := by positivity
    rw [hM]; linarith
  have hdivnn : 0 ≤ assetCap / (1 + rlo) := by positivity
  -- the clamp-level gap is always available as a bound
  have hlevel : |P.maxConsumption - Q.maxConsumption|
      ≤ |P.interest - Q.interest| * (M + assetCap / (1 + rlo)) := by
    rw [abs_maxConsumption_sub hmax]
    exact mul_le_mul_of_nonneg_left (by linarith) hgap
  rcases le_or_gt P.maxConsumption (P.consumption s (θ * P.maxSaving s)) with hPge | hPlt
  · rcases le_or_gt Q.maxConsumption (Q.consumption s (θ * Q.maxSaving s)) with hQge | hQlt
    · -- BOTH clamps bind, so the two operators see the same clamped value and the
      -- unclamped gap -- which may be enormous -- is invisible
      rw [min_eq_left hPge, min_eq_left hQge]
      exact hlevel
    · -- `Q`'s clamp fails to bind, which confines the state
      refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le hlevel ?_)
      refine hcons M ?_
      have := Q.max_zero_le_of_consumption_lt hr hQ hθ hQlt
      rw [hM, hmax]; exact this
  · -- `P`'s clamp fails to bind, which confines the state
    refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le hlevel ?_)
    exact hcons M (P.max_zero_le_of_consumption_lt hr hP hθ hPlt)

/-! ### Assembling: from pointwise bounds to a bound on the supremum

The sup-norm estimate compares two suprema, and the reparametrisation has already made them
suprema over the SAME set `[0,1]`. What remains is to get from a bound on the objectives to a
bound on their suprema.

A naive pointwise bound would not do, and the reason is worth stating. Where consumption is
tiny but positive, `u` of the two consumptions can differ by an arbitrary amount however close
the rates are, because `u` falls to `-∞`; so

  ∀ θ, objective_P θ ≤ objective_Q θ + ε

is FALSE. Those actions are dominated -- consuming almost nothing is far worse than the
always-available choice `θ = 0` -- so they cannot affect either supremum, but a pointwise
statement cannot see that.

The cutoff `L` is what encodes it. The hypothesis is only required at actions worth at least
`L`, and `L` is separately known to sit below the other program's supremum. Actions below `L`
are then bounded by `L` itself and need no comparison at all. In use, `L` will be the value of
`θ = 0`, which both programs have available. -/

theorem maxE_le_of_pointwise {P Q : IncomeFluctuation Z assetCap} (v : (ℝ × Z) →ᵇ ℝ)
    (s : ℝ × Z) (L : EReal) (ε : EReal)
    (hL : L ≤ Q.toExtended.maxE v s + ε)
    (h : ∀ θ ∈ Icc (0 : ℝ) 1, L ≤ P.toExtended.objectiveE v s (θ * P.maxSaving s) →
      P.toExtended.objectiveE v s (θ * P.maxSaving s)
        ≤ Q.toExtended.objectiveE v s (θ * Q.maxSaving s) + ε) :
    P.toExtended.maxE v s ≤ Q.toExtended.maxE v s + ε := by
  rw [P.maxE_eq_sSup_unit]
  refine sSup_le ?_
  rintro x ⟨θ, hθ, rfl⟩
  rcases le_or_gt L (P.toExtended.objectiveE v s (θ * P.maxSaving s)) with hge | hlt
  · -- worth at least the cutoff: the pointwise hypothesis applies
    refine le_trans (h θ hθ hge) ?_
    have hmem : θ * Q.maxSaving s ∈ Q.toExtended.feasible s := by
      rw [Q.feasible_eq_image]; exact ⟨θ, hθ, rfl⟩
    gcongr
    exact le_maxValueE hmem
  · -- below the cutoff: dominated, and bounded by the cutoff itself
    exact le_trans hlt.le hL

end IncomeFluctuation

end LeanEconomics
