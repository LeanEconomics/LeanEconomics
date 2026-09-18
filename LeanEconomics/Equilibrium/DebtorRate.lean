/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationEuler
import LeanEconomics.Models.IncomeFluctuationConsumption
import LeanEconomics.Models.IncomeFluctuationRate

/-!
# Saving and the rate with borrowing: the debtor's loss term

`Equilibrium/ElasticityReduction` proves Light's Theorem 1 from the Euler inequalities at a zero
borrowing limit. With a negative limit — Huggett (1993) — the same four inequalities go
through, except at the one step that used `a ≥ 0`: at the same asset level a higher rate raises
cash on hand for a creditor and LOWERS it for a debtor. The chain then yields

  `policy₁(a, z) ≤ policy₂(a, z) + (r₂ - r₁) · max 0 (-a)`:

saving can fall with the rate for a debtor, but by no more than the extra interest on the
debt (`policy_le_policy_add_withRate_of_marginal_at`). For `a ≥ 0` the loss term vanishes and
Theorem 1 holds as before; for `a > 0` at an interior choice and `r₁ < r₂` it holds STRICTLY
(`policy_lt_policy_withRate_of_marginal_at`), which is what single crossing against a constant
demand — Huggett's zero net supply — needs.

What this means for Huggett: the pointwise route gives exact monotonicity on the creditor side
and near-monotonicity on the debtor side, with a loss of first order in the rate gap; the FOSD
coupling needs exact monotonicity, so closing Huggett requires either showing the loss is
absorbed (the debtor's consumption falls by the full interest cost) or a coupling that tolerates
it. Neither is done here.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **The Euler chain, at two states.** Economy one at `(a₁, z)`, economy two at `(a₂, z)`: if
saving is lower and consumption strictly higher in economy two, the four Euler inequalities and
the elasticity condition at economy one's saving contradict each other. The two states need not
coincide — comparing economy two at the rescaled asset level `t a₁`, which has the same cash
on hand, is what handles debtors. -/
theorem euler_chain_absurd' {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₂ h₂).policy s < assetCap)
    {a₁ a₂ : ℝ} (ha₁ : a₁ ∈ Icc assetFloor assetCap) (ha₂ : a₂ ∈ Icc assetFloor assetCap) (z : Z)
    (helas : ∀ z' : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z)))
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z))))
    (hAlt : (P.withRate r₂ h₂).policy (a₂, z) < (P.withRate r₁ h₁).policy (a₁, z))
    (hclt : (P.withRate r₁ h₁).consumptionFn z a₁ < (P.withRate r₂ h₂).consumptionFn z a₂) :
    False := by
  classical
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hA₁mem : (P.withRate r₁ h₁).policy (a₁, z) ∈ Icc assetFloor assetCap :=
    (P.withRate r₁ h₁).policy_mem_region _
  have hA₂mem : (P.withRate r₂ h₂).policy (a₂, z) ∈ Icc assetFloor assetCap :=
    (P.withRate r₂ h₂).policy_mem_region _
  have hc₁pos : 0 < (P.withRate r₁ h₁).consumptionFn z a₁ :=
    (P.withRate r₁ h₁).consumptionFn_pos hpc₁ ha₁ z
  have hc₂pos : 0 < (P.withRate r₂ h₂).consumptionFn z a₂ :=
    (P.withRate r₂ h₂).consumptionFn_pos hpc₂ ha₂ z
  have hdu : du ((P.withRate r₂ h₂).consumptionFn z a₂)
      < du ((P.withRate r₁ h₁).consumptionFn z a₁) :=
    hanti (mem_Ioi.mpr hc₁pos) (mem_Ioi.mpr hc₂pos) hclt
  have hc₁' : ∀ z' : Z,
      0 < (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z)) :=
    fun z' => (P.withRate r₁ h₁).consumptionFn_pos hpc₁ hA₁mem z'
  have hc₂' : ∀ z' : Z,
      0 < (P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z)) :=
    fun z' => (P.withRate r₂ h₂).consumptionFn_pos hpc₂ hA₂mem z'
  -- Euler at the higher rate: room under the cap
  have hbv₂ := (P.withRate r₂ h₂).toExtended.bellman_valueFunction
  have hroom₂ : (P.withRate r₂ h₂).policy (a₂, z) < (P.withRate r₂ h₂).maxSaving (a₂, z) := by
    rw [maxSaving_eq]
    refine lt_min (hslack₂ _ ha₂) ?_
    have := hc₂pos
    simp only [consumptionFn, consumption] at this
    linarith
  have hE₂ := (P.withRate r₂ h₂).euler_le (v := (P.withRate r₂ h₂).toExtended.valueFunction)
    (z := z) (a := a₂) (A := (P.withRate r₂ h₂).policy (a₂, z))
    (du := du ((P.withRate r₂ h₂).consumptionFn z a₂))
    (du' := fun z' => du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z))))
    ha₂ (by rw [hbv₂]; exact congrFun (P.withRate r₂ h₂).policyOf_valueFunction _) hroom₂
    (by rw [hbv₂]; exact hc₂pos) (by rw [hbv₂]; exact hderiv _ hc₂pos)
    (fun z' => hc₂' z') (fun z' => hderiv _ (hc₂' z'))
  -- Euler at the lower rate: room above the floor
  have hbv₁ := (P.withRate r₁ h₁).toExtended.bellman_valueFunction
  have hA₁pos : assetFloor < (P.withRate r₁ h₁).policy (a₁, z) := lt_of_le_of_lt hA₂mem.1 hAlt
  have hslackA₁ : ∀ z' : Z, (P.withRate r₁ h₁).policyOf (P.withRate r₁ h₁).toExtended.valueFunction
      ((P.withRate r₁ h₁).policy (a₁, z), z')
      < (P.withRate r₁ h₁).maxSaving ((P.withRate r₁ h₁).policy (a₁, z), z') := by
    intro z'
    rw [(P.withRate r₁ h₁).policyOf_valueFunction, maxSaving_eq]
    refine lt_min (hslack₁ _ hA₁mem) ?_
    have := hc₁' z'
    simp only [consumptionFn, consumption] at this
    linarith
  have hE₁ := (P.withRate r₁ h₁).euler_ge (v := (P.withRate r₁ h₁).toExtended.valueFunction)
    (z := z) (a := a₁) (A := (P.withRate r₁ h₁).policy (a₁, z))
    (du := du ((P.withRate r₁ h₁).consumptionFn z a₁))
    (du' := fun z' => du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z))))
    ha₁ (by rw [hbv₁]; exact congrFun (P.withRate r₁ h₁).policyOf_valueFunction _) hA₁pos hslackA₁
    (by rw [hbv₁]; exact hc₁pos) (by rw [hbv₁]; exact hderiv _ hc₁pos)
    (fun z' => hc₁' z') (fun z' => hderiv _ (hc₁' z'))
  simp only [IncomeFluctuation.withRate_discount, IncomeFluctuation.withRate_interest,
    IncomeFluctuation.withRate_transitionMatrix] at hE₁ hE₂
  -- consumption rises with assets
  have hdu₂ : ∀ z' : Z,
      du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z)))
        ≤ du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z))) := by
    intro z'
    have hmono := (P.withRate r₂ h₂).consumptionFn_mono (z := z') hA₂mem hA₁mem hAlt.le
    exact hanti.antitoneOn (mem_Ioi.mpr (hc₂' z'))
      (mem_Ioi.mpr ((P.withRate r₂ h₂).consumptionFn_pos hpc₂ hA₁mem z')) hmono
  have hsum : (1 + r₁) * ∑ z', P.transitionMatrix z z'
        * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z)))
      ≤ (1 + r₂) * ∑ z', P.transitionMatrix z z'
        * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun z' _ => ?_
    have hπ := P.transitionMatrix_nonneg z z'
    have h1 := helas z'
    have h2 := mul_le_mul_of_nonneg_left (hdu₂ z') hR₂.le
    calc (1 + r₁) * (P.transitionMatrix z z'
            * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z))))
        = P.transitionMatrix z z' * ((1 + r₁)
            * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z)))) := by
          ring
      _ ≤ P.transitionMatrix z z' * ((1 + r₂)
            * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z)))) :=
          mul_le_mul_of_nonneg_left (le_trans h1 h2) hπ
      _ = (1 + r₂) * (P.transitionMatrix z z'
            * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z)))) := by
          ring
  have := mul_le_mul_of_nonneg_left hsum hβ
  linarith

/-- **The Euler chain at a common state.** -/
theorem euler_chain_absurd {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₂ h₂).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z)
    (helas : ∀ z' : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z))))
    (hAlt : (P.withRate r₂ h₂).policy (a, z) < (P.withRate r₁ h₁).policy (a, z))
    (hclt : (P.withRate r₁ h₁).consumptionFn z a < (P.withRate r₂ h₂).consumptionFn z a) :
    False :=
  P.euler_chain_absurd' h₁ h₂ hderiv hanti hpc₁ hpc₂ hslack₁ hslack₂ ha ha z helas hAlt hclt

theorem consumptionFn_withRate_eq {r : ℝ} (hr : P.RateOK r) (z : Z) {a : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) :
    (P.withRate r hr).consumptionFn z a
      = P.income z + (1 + r) * a - (P.withRate r hr).policy (a, z) := by
  simp only [consumptionFn, consumption, resources, IncomeFluctuation.withRate_income,
    IncomeFluctuation.withRate_interest, max_eq_right ha.1]

/-- **Theorem 1 with borrowing: the debtor's loss term.** Saving at the higher rate is at least
saving at the lower rate, less the extra interest on any debt. -/
theorem policy_le_policy_add_withRate_of_marginal_at {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁)
    (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂) {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₂ h₂).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z)
    (helas : ∀ z' : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))) :
    (P.withRate r₁ h₁).policy (a, z)
      ≤ (P.withRate r₂ h₂).policy (a, z) + (r₂ - r₁) * max 0 (-a) := by
  by_contra hcon
  push Not at hcon
  have hloss : 0 ≤ (r₂ - r₁) * max 0 (-a) := mul_nonneg (by linarith) (le_max_left _ _)
  have hAlt : (P.withRate r₂ h₂).policy (a, z) < (P.withRate r₁ h₁).policy (a, z) := by
    linarith
  have hclt : (P.withRate r₁ h₁).consumptionFn z a < (P.withRate r₂ h₂).consumptionFn z a := by
    rw [P.consumptionFn_withRate_eq h₁ z ha, P.consumptionFn_withRate_eq h₂ z ha]
    have hkey : 0 ≤ (r₂ - r₁) * (a + max 0 (-a)) :=
      mul_nonneg (by linarith) (by rcases le_total 0 a with h | h <;> simp [h])
    nlinarith
  exact P.euler_chain_absurd h₁ h₂ hderiv hanti hpc₁ hpc₂ hslack₁ hslack₂ ha z helas hAlt hclt

/-- **Theorem 1 for creditors, with borrowing allowed elsewhere**: at `a ≥ 0` the loss term
vanishes. -/
theorem policy_le_policy_withRate_of_marginal_at' {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁)
    (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂) {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₂ h₂).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (ha0 : 0 ≤ a) (z : Z)
    (helas : ∀ z' : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy (a, z) := by
  have := P.policy_le_policy_add_withRate_of_marginal_at h₁ h₂ hr hderiv hanti hpc₁ hpc₂ hslack₁
    hslack₂ ha z helas
  rwa [max_eq_left (by linarith), mul_zero, add_zero] at this

/-- **Strict Theorem 1**: a creditor with positive assets and an interior choice at the lower
rate saves STRICTLY more at a strictly higher rate. Single crossing against a constant demand
(zero net supply) needs this strictness. -/
theorem policy_lt_policy_withRate_of_marginal_at {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁)
    (h₂ : P.RateOK r₂) (hr : r₁ < r₂) {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₂ h₂).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (ha0 : 0 < a) (z : Z)
    (hint₁ : assetFloor < (P.withRate r₁ h₁).policy (a, z))
    (helas : ∀ z' : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))) :
    (P.withRate r₁ h₁).policy (a, z) < (P.withRate r₂ h₂).policy (a, z) := by
  classical
  by_contra hcon
  push Not at hcon
  -- consumption is strictly higher at the higher rate
  have hclt : (P.withRate r₁ h₁).consumptionFn z a < (P.withRate r₂ h₂).consumptionFn z a := by
    rw [P.consumptionFn_withRate_eq h₁ z ha, P.consumptionFn_withRate_eq h₂ z ha]
    nlinarith
  -- the chain, with `A₂ ≤ A₁` (not necessarily strict) and `floor < A₁` supplied directly
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hA₁mem : (P.withRate r₁ h₁).policy (a, z) ∈ Icc assetFloor assetCap :=
    (P.withRate r₁ h₁).policy_mem_region _
  have hA₂mem : (P.withRate r₂ h₂).policy (a, z) ∈ Icc assetFloor assetCap :=
    (P.withRate r₂ h₂).policy_mem_region _
  have hc₁pos : 0 < (P.withRate r₁ h₁).consumptionFn z a :=
    (P.withRate r₁ h₁).consumptionFn_pos hpc₁ ha z
  have hc₂pos : 0 < (P.withRate r₂ h₂).consumptionFn z a :=
    (P.withRate r₂ h₂).consumptionFn_pos hpc₂ ha z
  have hdu : du ((P.withRate r₂ h₂).consumptionFn z a)
      < du ((P.withRate r₁ h₁).consumptionFn z a) :=
    hanti (mem_Ioi.mpr hc₁pos) (mem_Ioi.mpr hc₂pos) hclt
  have hc₁' : ∀ z' : Z,
      0 < (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)) :=
    fun z' => (P.withRate r₁ h₁).consumptionFn_pos hpc₁ hA₁mem z'
  have hc₂' : ∀ z' : Z,
      0 < (P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z)) :=
    fun z' => (P.withRate r₂ h₂).consumptionFn_pos hpc₂ hA₂mem z'
  have hbv₂ := (P.withRate r₂ h₂).toExtended.bellman_valueFunction
  have hroom₂ : (P.withRate r₂ h₂).policy (a, z) < (P.withRate r₂ h₂).maxSaving (a, z) := by
    rw [maxSaving_eq]
    refine lt_min (hslack₂ _ ha) ?_
    have := hc₂pos
    simp only [consumptionFn, consumption] at this
    linarith
  have hE₂ := (P.withRate r₂ h₂).euler_le (v := (P.withRate r₂ h₂).toExtended.valueFunction)
    (z := z) (a := a) (A := (P.withRate r₂ h₂).policy (a, z))
    (du := du ((P.withRate r₂ h₂).consumptionFn z a))
    (du' := fun z' => du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z))))
    ha (by rw [hbv₂]; exact congrFun (P.withRate r₂ h₂).policyOf_valueFunction _) hroom₂
    (by rw [hbv₂]; exact hc₂pos) (by rw [hbv₂]; exact hderiv _ hc₂pos)
    (fun z' => hc₂' z') (fun z' => hderiv _ (hc₂' z'))
  have hbv₁ := (P.withRate r₁ h₁).toExtended.bellman_valueFunction
  have hslackA₁ : ∀ z' : Z, (P.withRate r₁ h₁).policyOf (P.withRate r₁ h₁).toExtended.valueFunction
      ((P.withRate r₁ h₁).policy (a, z), z')
      < (P.withRate r₁ h₁).maxSaving ((P.withRate r₁ h₁).policy (a, z), z') := by
    intro z'
    rw [(P.withRate r₁ h₁).policyOf_valueFunction, maxSaving_eq]
    refine lt_min (hslack₁ _ hA₁mem) ?_
    have := hc₁' z'
    simp only [consumptionFn, consumption] at this
    linarith
  have hE₁ := (P.withRate r₁ h₁).euler_ge (v := (P.withRate r₁ h₁).toExtended.valueFunction)
    (z := z) (a := a) (A := (P.withRate r₁ h₁).policy (a, z))
    (du := du ((P.withRate r₁ h₁).consumptionFn z a))
    (du' := fun z' => du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z))))
    ha (by rw [hbv₁]; exact congrFun (P.withRate r₁ h₁).policyOf_valueFunction _) hint₁ hslackA₁
    (by rw [hbv₁]; exact hc₁pos) (by rw [hbv₁]; exact hderiv _ hc₁pos)
    (fun z' => hc₁' z') (fun z' => hderiv _ (hc₁' z'))
  simp only [IncomeFluctuation.withRate_discount, IncomeFluctuation.withRate_interest,
    IncomeFluctuation.withRate_transitionMatrix] at hE₁ hE₂
  have hdu₂ : ∀ z' : Z,
      du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
        ≤ du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z))) := by
    intro z'
    have hmono := (P.withRate r₂ h₂).consumptionFn_mono (z := z') hA₂mem hA₁mem hcon
    exact hanti.antitoneOn (mem_Ioi.mpr (hc₂' z'))
      (mem_Ioi.mpr ((P.withRate r₂ h₂).consumptionFn_pos hpc₂ hA₁mem z')) hmono
  have hsum : (1 + r₁) * ∑ z', P.transitionMatrix z z'
        * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
      ≤ (1 + r₂) * ∑ z', P.transitionMatrix z z'
        * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun z' _ => ?_
    have hπ := P.transitionMatrix_nonneg z z'
    have h1 := helas z'
    have h2 := mul_le_mul_of_nonneg_left (hdu₂ z') hR₂.le
    calc (1 + r₁) * (P.transitionMatrix z z'
            * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z))))
        = P.transitionMatrix z z' * ((1 + r₁)
            * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))) := by
          ring
      _ ≤ P.transitionMatrix z z' * ((1 + r₂)
            * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z)))) :=
          mul_le_mul_of_nonneg_left (le_trans h1 h2) hπ
      _ = (1 + r₂) * (P.transitionMatrix z z'
            * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z)))) := by
          ring
  have := mul_le_mul_of_nonneg_left hsum hβ
  linarith

/-- **Theorem 1 at equal cash on hand, for any sign of assets.** Economy two at the rescaled
asset level `t·a`, `t = R₁/R₂`, has the same cash on hand as economy one at `a`, so the
consumption comparison in the Euler chain is automatic; saving is then at least as high at the
higher rate, at every `a ∈ [floor, cap]` with `floor ≤ 0`. For a creditor `t a ≤ a` and this
recovers `policy₁(a) ≤ policy₂(a)`; for a debtor `t a > a` is a SMALLER debt with the same
interest bill, which is exactly where the loss term of
`policy_le_policy_add_withRate_of_marginal_at` comes from. -/
theorem policy_le_policy_scaled_withRate_of_marginal_at {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁)
    (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂) (hfl : assetFloor ≤ 0) {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₂ h₂).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z)
    (helas : ∀ z' : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy ((1 + r₁) / (1 + r₂) * a, z) := by
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have ht0 : 0 < (1 + r₁) / (1 + r₂) := div_pos hR₁ hR₂
  have ht1 : (1 + r₁) / (1 + r₂) ≤ 1 := by rw [div_le_one hR₂]; linarith
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hta : (1 + r₁) / (1 + r₂) * a ∈ Icc assetFloor assetCap := by
    rcases le_total 0 a with h0 | h0
    · exact ⟨le_trans hfl (mul_nonneg ht0.le h0), by nlinarith [ha.2]⟩
    · refine ⟨?_, le_trans (by nlinarith) hcap0⟩
      nlinarith [ha.1]
  by_contra hcon
  push Not at hcon
  have hclt : (P.withRate r₁ h₁).consumptionFn z a
      < (P.withRate r₂ h₂).consumptionFn z ((1 + r₁) / (1 + r₂) * a) := by
    rw [P.consumptionFn_withRate_eq h₁ z ha, P.consumptionFn_withRate_eq h₂ z hta]
    have hm : (1 + r₂) * ((1 + r₁) / (1 + r₂) * a) = (1 + r₁) * a := by field_simp
    rw [hm]
    linarith
  exact P.euler_chain_absurd' h₁ h₂ hderiv hanti hpc₁ hpc₂ hslack₁ hslack₂ ha hta z helas hcon hclt

end IncomeFluctuation

end LeanEconomics
