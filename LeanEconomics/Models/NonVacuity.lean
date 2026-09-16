/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Distribution.Uniqueness
import LeanEconomics.Models.IncomeFluctuationLipschitz

/-!
# The uniqueness hypotheses are satisfiable

`existsUnique_isStationary` assumes that the worst income state is always reachable and that
the richest household is driven to the borrowing constraint by `N` consecutive bad draws. A
theorem with unsatisfiable hypotheses proves nothing, so this file exhibits a model where both
hold and the conclusion is therefore a real statement.

## Why not the existing calibration

`calibrated` does NOT satisfy the exhaustion hypothesis, and the reason is economic rather
than technical: it has `β(1+r) = (24/25)(21/20) = 1.008 > 1`. Such a household is patient
relative to the interest rate, accumulates towards the asset cap and stays there, so repeated
bad draws never drive it to the constraint. Aiyagari economies satisfy `β(1+r) < 1` in
equilibrium, which is exactly what makes the constraint bind.

## What is verified here

The household below is myopic, `β = 0`. It consumes its resources and saves nothing, so one
bad draw exhausts any asset position and `N = 1` works. The asset space is NOT degenerate --
the cap is 10 and the state space is the full `[0,10] × Fin 2` -- so the chain being exercised
is the real one, and the resulting stationary distribution is a genuine object.

An honest limitation: verifying the hypothesis for a household with `0 < β(1+r) < 1`, which is
the economically interesting case, needs quantitative control of the policy function. There is
no closed form for CRRA with a cap, so it would need bounds on the policy that this
development does not have. What is established here is satisfiability, not that the natural
calibrations satisfy it.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

/-- A myopic household: the calibration, with the discount factor set to zero. -/
noncomputable def myopic : IncomeFluctuation (Fin 2) 10 :=
  { calibrated with discount := 0, discount_lt_one := by norm_num }

@[simp] theorem myopic_discount : (myopic.discount : ℝ) = 0 := rfl

/-- With no discounting the continuation value drops out and the objective is the reward. -/
theorem myopic_objectiveE (v : (ℝ × Fin 2) →ᵇ ℝ) (s : ℝ × Fin 2) (a : ℝ) :
    myopic.toExtended.objectiveE v s a = myopic.toExtended.reward (s, a) := by
  have hd : (myopic.toExtended.discount : ℝ) = 0 := rfl
  simp only [ExtendedStochasticProgram.objectiveE, hd, zero_mul, EReal.coe_zero, add_zero]

/-- **A myopic household saves nothing.** -/
theorem myopic_policy_eq_zero {s : ℝ × Fin 2} (hs : s.1 ∈ Icc (0 : ℝ) 10) :
    myopic.policy s = 0 := by
  set V := myopic.toExtended.valueFunction with hV
  have hmem : (0 : ℝ) ∈ myopic.toExtended.feasible s := ⟨le_rfl, le_max_left _ _⟩
  have hc0 : 0 < myopic.consumption s 0 := by
    simpa only [consumption, sub_zero] using myopic.resources_pos s
  -- the reward at zero saving is the utility of all resources
  have hrew0 := myopic.reward_eq_coe hs hmem hc0
  -- and nothing feasible beats it
  have hdom : ∀ a ∈ myopic.toExtended.feasible s,
      myopic.toExtended.objectiveE V s a
        ≤ ((myopic.u (myopic.consumption s 0) : ℝ) : EReal) := by
    intro a ha
    rw [myopic_objectiveE]
    change extendDom myopic.dom myopic.u (myopic.clampedConsumption (s, a)) ≤ _
    by_cases h : myopic.clampedConsumption (s, a) ∈ myopic.dom
    · rw [extendDom_of_mem h, EReal.coe_le_coe_iff]
      refine myopic.monotoneOn_u_dom h (myopic.mem_dom_of_pos hc0) ?_
      refine le_trans (min_le_right _ _) (max_le ?_ ?_)
      · simpa only [consumption, sub_zero] using (myopic.resources_pos s).le
      · simp only [consumption, sub_zero]
        linarith [ha.1]
    · rw [extendDom_of_not_mem h]; exact bot_le
  have hle : myopic.toExtended.bellmanFn V s ≤ myopic.u (myopic.consumption s 0) :=
    myopic.toExtended.bellmanFn_le V hdom
  have hge : ((myopic.u (myopic.consumption s 0) : ℝ) : EReal)
      ≤ ((myopic.toExtended.bellmanFn V s : ℝ) : EReal) := by
    have h := myopic.toExtended.le_bellmanFn V hmem
    rwa [myopic_objectiveE, hrew0] at h
  rw [EReal.coe_le_coe_iff] at hge
  -- so zero saving is optimal, and the optimal action is unique
  refine (myopic.eq_policy_of_optimal hs hmem ?_).symm
  rw [myopic_objectiveE, hrew0, EReal.coe_eq_coe_iff]
  linarith

/-- One bad draw exhausts any asset position. -/
theorem myopic_gBad (z₀ : Fin 2) (x : ↥(Icc (0 : ℝ) 10)) :
    myopic.gBad z₀ x = myopic.botState :=
  Subtype.ext (myopic_policy_eq_zero x.2)

/-- **Both hypotheses of `existsUnique_isStationary` hold for the myopic household**, so the
theorem is not vacuous. -/
theorem myopic_hexh (z₀ : Fin 2) : (myopic.gBad z₀)^[1] myopic.topState = myopic.botState :=
  myopic_gBad z₀ myopic.topState

theorem myopic_hreach (z₀ : Fin 2) : ∀ z : Fin 2, 0 < myopic.transitionMatrix z z₀ := by
  intro z; norm_num [myopic, calibrated]

/-- **A unique stationary agent distribution exists for the myopic household.** -/
theorem myopic_existsUnique_isStationary :
    ∃! μ : ProbabilityMeasure myopic.State, myopic.IsStationary μ :=
  myopic.existsUnique_isStationary (z₀ := 0) (N := 1) (myopic_hreach 0) (myopic_hexh 0)

/-! ### An impatient household, where the constraint genuinely binds

The myopic example above has `β = 0`, which settles satisfiability but not much else. This
one has `β(1+r) = 1/100 < 1`: the household does value the future, and the borrowing
constraint binds because it is impatient relative to the interest rate, which is the actual
economics of the Doeblin argument.

Nothing here is a new theorem. Every constant is explicit, so the hypotheses of
`policy_eq_zero_of_corner` reduce to arithmetic:

  maxConsumption = 2 + 1·1 = 3,  K = 2/minIncome² = 2,  m = 1/maxConsumption² = 1/9

`L = 3` satisfies `(K + βL)(1+r) = 2.03 ≤ 3`, and `βL = 0.03 < 1/9 = m`.
-/

/-- An impatient household: `β = 1/100`, `r = 0`, income in `{1, 2}`, cap `1`. -/
noncomputable def impatient : IncomeFluctuation (Fin 2) 1 where
  income z := if z = 0 then 1 else 2
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 100
  u := fun c => -c⁻¹
  minIncome := 1
  maxIncome := 2
  minIncome_pos := by norm_num
  minIncome_le z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  assetCap_nonneg := by norm_num
  discount_lt_one := by norm_num
  dom := Ioi 0
  Ioi_subset_dom := subset_rfl
  dom_subset_Ici := Ioi_subset_Ici_self
  continuousOn_u_dom := (continuousOn_id.inv₀ fun x hx => ne_of_gt hx).neg
  monotoneOn_u_dom := by
    intro x hx y _ hxy
    have : (0 : ℝ) < x := hx
    simp only [neg_le_neg_iff]
    gcongr
  strictConcaveOn_u_dom := strictConcaveOn_neg_inv
  continuousOn_extendDom :=
    continuousOn_extendDom_Ioi ((continuousOn_id.inv₀ fun x hx => ne_of_gt hx).neg)
      (tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero)

@[simp] theorem impatient_u (c : ℝ) : impatient.u c = -c⁻¹ := rfl
@[simp] theorem impatient_minIncome : impatient.minIncome = 1 := rfl
@[simp] theorem impatient_maxIncome : impatient.maxIncome = 2 := rfl
@[simp] theorem impatient_interest : impatient.interest = 0 := rfl
@[simp] theorem impatient_discount : (impatient.discount : ℝ) = 1 / 100 := rfl
@[simp] theorem impatient_transitionMatrix (z z' : Fin 2) :
    impatient.transitionMatrix z z' = 1 / 2 := rfl

theorem impatient_maxConsumption : impatient.maxConsumption = 3 := by
  simp only [maxConsumption, impatient_maxIncome, impatient_interest]; norm_num

theorem impatient_slopeBoundU : impatient.slopeBoundU = 2 := by
  simp only [slopeBoundU, slopeBound, impatient_minIncome, impatient_u]
  norm_num

/-- The marginal utility of consumption is at least `1/9` on the relevant range. -/
theorem impatient_marginal (c d : ℝ) (hd : 0 < d) (hdc : d ≤ c)
    (hc3 : c ≤ impatient.maxConsumption) :
    (1 / 9 : ℝ) * (c - d) ≤ impatient.u c - impatient.u d := by
  rw [impatient_maxConsumption] at hc3
  have hc : 0 < c := lt_of_lt_of_le hd hdc
  have hkey : -c⁻¹ - -d⁻¹ = (c - d) / (c * d) := by field_simp; ring
  rw [impatient_u, impatient_u, hkey, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hdc) (show (0 : ℝ) ≤ 9 - c * d by nlinarith)]

/-- **The impatient household saves nothing at any asset level.** -/
theorem impatient_policy_eq_zero {s : ℝ × Fin 2} (hs : s.1 ∈ Icc (0 : ℝ) 1) :
    impatient.policy s = 0 := by
  refine impatient.policy_eq_zero_of_corner (L := 3) (m := 1 / 9) ?_ ?_ ?_ hs
  · refine impatient.valueFunction_lipschitz (by norm_num) ?_
    rw [impatient_slopeBoundU, impatient_discount, impatient_interest]
    norm_num
  · exact impatient_marginal
  · rw [impatient_discount]; norm_num

theorem impatient_gBad (z₀ : Fin 2) (x : ↥(Icc (0 : ℝ) 1)) :
    impatient.gBad z₀ x = impatient.botState :=
  Subtype.ext (impatient_policy_eq_zero x.2)

theorem impatient_hexh (z₀ : Fin 2) :
    (impatient.gBad z₀)^[1] impatient.topState = impatient.botState :=
  impatient_gBad z₀ impatient.topState

theorem impatient_hreach (z₀ : Fin 2) : ∀ z : Fin 2, 0 < impatient.transitionMatrix z z₀ := by
  intro z; norm_num

/-- **A unique stationary agent distribution exists for an IMPATIENT household**, one that
discounts the future at a positive rate and is driven to the borrowing constraint because
`β(1+r) < 1`. -/
theorem impatient_existsUnique_isStationary :
    ∃! μ : ProbabilityMeasure impatient.State, impatient.IsStationary μ :=
  impatient.existsUnique_isStationary (z₀ := 0) (N := 1) (impatient_hreach 0) (impatient_hexh 0)

end IncomeFluctuation

end LeanEconomics
