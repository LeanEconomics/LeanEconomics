/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.LargeBetaLight
import LeanEconomics.Models.EulerCorner
import LeanEconomics.Distribution.Uniqueness

/-!
# The Doeblin chain at large `β`

At each rate, the uniqueness of the stationary distribution and the convergence to it come from
the same three facts as always — a corner at the worst income state, decline above it, and the
worst state reachable from everywhere — but at Aiyagari's `β = 0.96` each has to come from a
route that does not carry `1/(1-β)` or `1/(1-βR)` in a constant.

* The corner from the Euler inequality (`crra_policy_eq_zero_of_euler`), whose test is
  `βR · minIncome^(-γ) < (income z₀ + R a₀)^(-γ)` — one inequality, no Lipschitz constant.
* Decline from Açıkgöz Proposition 4 (`policy_lt_self_of_impatient_iid`), which holds at every
  asset level above the constraint given `βR < 1` and iid income.
* Cap slack at the fixed point from the minimal MPC (`crra_policy_lt_cap_of_minMPC`).

Nothing in this file mentions an oscillation bound.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **The exhaustion data at large `β`**, for CRRA with iid income. -/
theorem crra_exists_exhaust_of_euler_corner {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hint : 0 ≤ P.interest) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hiid : P.IidIncome)
    (hpc : P.PositiveConsumptionAll)
    (hthr : (1 - P.minMPC γ) * (P.maxIncome + (1 + P.interest) * assetCap) < assetCap)
    {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hcorner : (P.discount : ℝ) * (1 + P.interest) * P.minIncome ^ (-γ)
      < (P.income z₀ + (1 + P.interest) * a₀) ^ (-γ)) :
    ∃ N : ℕ, (P.gBad z₀)^[N] P.topState = P.botState := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  -- positivity, at the iterates and at the fixed point
  have hposIt : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a :=
    fun n z a ha => hpc _ (P.concaveSlices_iterate_zero n) z a ha
  have hpos : ∀ z : Z, ∀ x ∈ Icc (0 : ℝ) assetCap, 0 < P.consumptionFn z x :=
    fun z x hx => hpc _ P.concaveSlices_valueFunction z x hx
  -- cap slack at the fixed point, from the minimal MPC
  have hslack : ∀ z : Z, ∀ x ∈ Icc (0 : ℝ) assetCap, P.policy (x, z) < P.maxSaving (x, z) :=
    fun z x hx => P.policyOf_lt_maxSaving_of_pos (hpos z x hx)
      (P.crra_policy_lt_cap_of_minMPC hγ0 hu rfl hint hβ hβR hposIt hthr hx z)
  -- the corner below `a₀`, from the Euler inequality
  have hzero : ∀ a ∈ Icc (0 : ℝ) a₀, P.policy (a, z₀) = 0 := by
    intro a ha
    have hmem : a ∈ Icc (0 : ℝ) assetCap := ⟨ha.1, le_trans ha.2 hle⟩
    refine P.crra_policy_eq_zero_of_euler hγ0 hu rfl hβR hpos hslack hmem z₀ ?_
    have hres : P.resources (a, z₀) = P.income z₀ + (1 + P.interest) * a := by
      simp only [resources, max_eq_right ha.1]
    have hres0 : 0 < P.income z₀ + (1 + P.interest) * a := by
      have := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z₀)
      nlinarith [ha.1]
    have hle' : P.income z₀ + (1 + P.interest) * a ≤ P.income z₀ + (1 + P.interest) * a₀ := by
      nlinarith [ha.2]
    rw [hres]
    exact lt_of_lt_of_le hcorner (rpow_neg_antitone hγ0 hres0 hle')
  -- and decline above it, from impatience
  refine P.exists_exhaust_of_decline ha₀ hle hzero fun a ha => ?_
  exact P.policy_lt_self_of_impatient_iid hβR hiid (du := fun c => c ^ (-γ))
    (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility γ hc)
    (fun _ hx _ _ hxy => Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
    (fun c hc => Real.rpow_pos_of_pos hc _) hpos hslack hz₀
    ⟨le_trans ha₀.le ha.1, ha.2⟩ (lt_of_lt_of_le ha₀ ha.1)

section Measure

variable [MeasurableSpace Z] [BorelSpace Z]

/-- **A unique stationary distribution at large `β`.** -/
theorem crra_existsUnique_isStationary_of_euler_corner {γ : ℝ} (hγ0 : 0 < γ)
    (hu : P.u = crraUtility γ) (hint : 0 ≤ P.interest) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hiid : P.IidIncome)
    (hpc : P.PositiveConsumptionAll)
    (hthr : (1 - P.minMPC γ) * (P.maxIncome + (1 + P.interest) * assetCap) < assetCap)
    {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hcorner : (P.discount : ℝ) * (1 + P.interest) * P.minIncome ^ (-γ)
      < (P.income z₀ + (1 + P.interest) * a₀) ^ (-γ)) :
    ∃! μ : ProbabilityMeasure P.State, P.IsStationary μ := by
  obtain ⟨N, hN⟩ := P.crra_exists_exhaust_of_euler_corner hγ0 hu hint hβ hβR hiid hpc hthr hz₀
    ha₀ hle hcorner
  exact P.existsUnique_isStationary hreach hN

/-- **Convergence to it from any start**, Doeblin with the atom at the constraint. -/
theorem crra_tendsto_pushProb_of_euler_corner {γ : ℝ} (hγ0 : 0 < γ)
    (hu : P.u = crraUtility γ) (hint : 0 ≤ P.interest) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hiid : P.IidIncome)
    (hpc : P.PositiveConsumptionAll)
    (hthr : (1 - P.minMPC γ) * (P.maxIncome + (1 + P.interest) * assetCap) < assetCap)
    {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hcorner : (P.discount : ℝ) * (1 + P.interest) * P.minIncome ^ (-γ)
      < (P.income z₀ + (1 + P.interest) * a₀) ^ (-γ))
    (μ₀ : ProbabilityMeasure P.State) {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    Tendsto (fun m => P.pushProb^[m] μ₀) atTop (𝓝 μ) := by
  classical
  obtain ⟨N, hN⟩ := P.crra_exists_exhaust_of_euler_corner hγ0 hu hint hβ hβR hiid hpc hthr hz₀
    ha₀ hle hcorner
  obtain ⟨z₁, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun z => P.transitionMatrix z z₀) ⟨Classical.ofNonempty, Finset.mem_univ _⟩
  exact P.tendsto_pushProb_iterate (z₀ := z₀) (p₀ := P.transitionMatrix z₁ z₀) (N := N + 1)
    (hreach z₁) (fun s => hmin _ (Finset.mem_univ _)) (P.badStep_iterate_eq hN) μ₀ hμ

end Measure

end IncomeFluctuation

end LeanEconomics
