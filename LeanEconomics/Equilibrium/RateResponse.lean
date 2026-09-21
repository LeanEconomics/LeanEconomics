/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.SlackEuler
import LeanEconomics.Models.ConsumptionSandwich

/-!
# The rate response of consumption: the transfer lemma

The slack elasticity condition of `SlackEuler` is numerically true at every wealth level but
unproved. What would prove it is a one-sided **rate-response bound**,

  `c₂(a, z) - c₁(a, z) ≤ (r₂ - r₁)(α a + B)`   on the region,

with `α` below `Þ₂` and `B` of the order of income. This file proves the step such a bound is
built from: the two Euler inequalities transfer a bound on TOMORROW's consumption gap into a
bound on TODAY's.

## The transfer lemma

Fix a state `(a, z)` at which the lower-rate household saves (`a'₁ > 0`). Let `X ≥ 0` bound
tomorrow's gap in every income state, `c₂(a'₂, z') ≤ c₁(a'₁, z') + X`, and let `c_min` bound the
lower-rate household's consumption tomorrow from below, `c_min ≤ c₁(a'₁, z')`. Then

  `c₂(a, z) ≤ (R₁/R₂)^{1/γ} · c₁(a, z) · (1 + X / c_min)`   (`consumption_transfer`).

The proof is the slack chain with the consumption difference kept explicit: the Euler inequality
under the cap at the higher rate, `(c' + X)^{-γ} ≥ c'^{-γ}(1 + X/c_min)^{-γ}`, and the Euler
equality above the floor at the lower rate.

## What the lemma says about the programme

Two factors appear, and they are the whole difficulty.

* `(R₁/R₂)^{1/γ} ≤ 1 - Δr/(γR₂)`: the substitution effect, a relative fall in consumption of
  `Δr/(γR)` per unit rate gap. This is the margin the induction lives on.
* `c₁(a, z)/c_min`: today's consumption relative to the worst case tomorrow. At high wealth it is
  about `1/Þ₁`, and then the induction closes exactly when `α ≥ 1 - (1 - κ)/γ`, the true
  asymptotic slope, with room `(1 - κ)/γ - κ`. At moderate wealth the ratio can be as large as
  the drop in consumption from a high-income state today to the lowest tomorrow, of the order
  of `y_max/y_min` at persistent income, and the additive bound `X` is amplified by it. Whether the
  substitution margin covers that amplification on the middle of the wealth range is the open
  quantitative question; using the minimum over `z'` is crude, since the Euler equation weights
  tomorrow's states by marginal utility and the effective ratio is smaller.

So the rate-response bound is not proved here. What is proved is its inductive step, in the form
that isolates the two numbers a proof must control.
-/

open Set Filter Topology

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **The transfer lemma.** A bound `X` on tomorrow's consumption gap, and a floor `c_min` on the
lower-rate household's consumption tomorrow, give
`c₂(a,z) ≤ (R₁/R₂)^{1/γ} c₁(a,z) (1 + X/c_min)` at a state where the lower-rate household
saves. -/
theorem consumption_transfer {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    (hβ : 0 < (P.discount : ℝ))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₂ h₂).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (hint₁ : 0 < (P.withRate r₁ h₁).policy (a, z))
    {X : ℝ} (hX : 0 ≤ X)
    (hgap : ∀ z' : Z, (P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z))
      ≤ (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)) + X)
    {cmin : ℝ} (hcmin : 0 < cmin)
    (hfloor : ∀ z' : Z,
      cmin ≤ (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z))) :
    (P.withRate r₂ h₂).consumptionFn z a
      ≤ ((1 + r₁) / (1 + r₂)) ^ (1 / γ) * (P.withRate r₁ h₁).consumptionFn z a
        * (1 + X / cmin) := by
  classical
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  set A₁ : ℝ := (P.withRate r₁ h₁).policy (a, z) with hA₁
  set A₂ : ℝ := (P.withRate r₂ h₂).policy (a, z) with hA₂
  have hA₁mem : A₁ ∈ Icc (0 : ℝ) assetCap := (P.withRate r₁ h₁).policy_mem_region _
  have hA₂mem : A₂ ∈ Icc (0 : ℝ) assetCap := (P.withRate r₂ h₂).policy_mem_region _
  set c₁ : ℝ := (P.withRate r₁ h₁).consumptionFn z a with hc₁
  set c₂ : ℝ := (P.withRate r₂ h₂).consumptionFn z a with hc₂
  have hc₁0 : 0 < c₁ := (P.withRate r₁ h₁).consumptionFn_pos hpc₁ ha z
  have hc₂0 : 0 < c₂ := (P.withRate r₂ h₂).consumptionFn_pos hpc₂ ha z
  have hc₁' : ∀ z' : Z, 0 < (P.withRate r₁ h₁).consumptionFn z' A₁ :=
    fun z' => (P.withRate r₁ h₁).consumptionFn_pos hpc₁ hA₁mem z'
  have hc₂' : ∀ z' : Z, 0 < (P.withRate r₂ h₂).consumptionFn z' A₂ :=
    fun z' => (P.withRate r₂ h₂).consumptionFn_pos hpc₂ hA₂mem z'
  have hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (c ^ (-γ)) c := fun c hc => by
    rw [hu]; exact hasDerivAt_crraUtility γ hc
  -- Euler at the higher rate: room under the cap
  have hbv₂ := (P.withRate r₂ h₂).toExtended.bellman_valueFunction
  have hroom₂ : A₂ < (P.withRate r₂ h₂).maxSaving (a, z) := by
    rw [maxSaving_eq]
    refine lt_min (hslack₂ _ ha) ?_
    have := hc₂0
    change 0 < (P.withRate r₂ h₂).resources (a, z) - A₂ at this
    linarith
  have hE₂ := (P.withRate r₂ h₂).euler_le (v := (P.withRate r₂ h₂).toExtended.valueFunction)
    (z := z) (a := a) (A := A₂) (du := c₂ ^ (-γ))
    (du' := fun z' => ((P.withRate r₂ h₂).consumptionFn z' A₂) ^ (-γ))
    ha (by rw [hbv₂]; exact congrFun (P.withRate r₂ h₂).policyOf_valueFunction _) hroom₂
    (by rw [hbv₂]; exact hc₂0) (by rw [hbv₂]; exact hderiv _ hc₂0)
    (fun z' => hc₂' z') (fun z' => hderiv _ (hc₂' z'))
  -- Euler at the lower rate: room above the floor
  have hbv₁ := (P.withRate r₁ h₁).toExtended.bellman_valueFunction
  have hslackA₁ : ∀ z' : Z, (P.withRate r₁ h₁).policyOf (P.withRate r₁ h₁).toExtended.valueFunction
      (A₁, z') < (P.withRate r₁ h₁).maxSaving (A₁, z') := by
    intro z'
    rw [(P.withRate r₁ h₁).policyOf_valueFunction, maxSaving_eq]
    refine lt_min (hslack₁ _ hA₁mem) ?_
    have := hc₁' z'
    change 0 < (P.withRate r₁ h₁).resources (A₁, z') - (P.withRate r₁ h₁).policy (A₁, z') at this
    linarith
  have hE₁ := (P.withRate r₁ h₁).euler_ge (v := (P.withRate r₁ h₁).toExtended.valueFunction)
    (z := z) (a := a) (A := A₁) (du := c₁ ^ (-γ))
    (du' := fun z' => ((P.withRate r₁ h₁).consumptionFn z' A₁) ^ (-γ))
    ha (by rw [hbv₁]; exact congrFun (P.withRate r₁ h₁).policyOf_valueFunction _) hint₁ hslackA₁
    (by rw [hbv₁]; exact hc₁0) (by rw [hbv₁]; exact hderiv _ hc₁0)
    (fun z' => hc₁' z') (fun z' => hderiv _ (hc₁' z'))
  simp only [IncomeFluctuation.withRate_discount, IncomeFluctuation.withRate_interest,
    IncomeFluctuation.withRate_transitionMatrix] at hE₁ hE₂
  -- tomorrow: `c₂' ≤ c₁' + X ≤ c₁' (1 + X/cmin)`
  set θ : ℝ := 1 + X / cmin with hθ
  have hθ1 : 1 ≤ θ := by rw [hθ]; have := div_nonneg hX hcmin.le; linarith
  have hθ0 : 0 < θ := by linarith
  have hterm : ∀ z' : Z, (θ * (P.withRate r₁ h₁).consumptionFn z' A₁) ^ (-γ)
      ≤ ((P.withRate r₂ h₂).consumptionFn z' A₂) ^ (-γ) := by
    intro z'
    refine rpow_neg_antitone hγ0 (hc₂' z') ?_
    have h1 := hgap z'
    have h2 : X ≤ X / cmin * (P.withRate r₁ h₁).consumptionFn z' A₁ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hcmin]
      exact mul_le_mul_of_nonneg_left (hfloor z') hX
    rw [hθ]
    nlinarith [h1, h2]
  have hsum : ∑ z', P.transitionMatrix z z' * (θ * (P.withRate r₁ h₁).consumptionFn z' A₁) ^ (-γ)
      ≤ ∑ z', P.transitionMatrix z z' * ((P.withRate r₂ h₂).consumptionFn z' A₂) ^ (-γ) :=
    Finset.sum_le_sum fun z' _ =>
      mul_le_mul_of_nonneg_left (hterm z') (P.transitionMatrix_nonneg z z')
  -- pull `θ^{-γ}` out of the sum
  have hpull : ∑ z', P.transitionMatrix z z' * (θ * (P.withRate r₁ h₁).consumptionFn z' A₁) ^ (-γ)
      = θ ^ (-γ)
        * ∑ z', P.transitionMatrix z z' * ((P.withRate r₁ h₁).consumptionFn z' A₁) ^ (-γ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [Real.mul_rpow hθ0.le (hc₁' z').le]
    ring
  rw [hpull] at hsum
  -- chain: `(R₂/R₁) θ^{-γ} c₁^{-γ} ≤ c₂^{-γ}`
  have hθγ : 0 < θ ^ (-γ) := Real.rpow_pos_of_pos hθ0 _
  have hS₁ : 0 ≤ ∑ z', P.transitionMatrix z z' * ((P.withRate r₁ h₁).consumptionFn z' A₁) ^ (-γ) :=
    Finset.sum_nonneg fun z' _ =>
      mul_nonneg (P.transitionMatrix_nonneg z z') (Real.rpow_nonneg (hc₁' z').le _)
  have hchain : (1 + r₂) / (1 + r₁) * θ ^ (-γ) * c₁ ^ (-γ) ≤ c₂ ^ (-γ) := by
    have h1 : (1 + r₂) * θ ^ (-γ) * c₁ ^ (-γ)
        ≤ (1 + r₂) * θ ^ (-γ) * ((P.discount : ℝ) * ((1 + r₁)
          * ∑ z', P.transitionMatrix z z' * ((P.withRate r₁ h₁).consumptionFn z' A₁) ^ (-γ))) :=
      mul_le_mul_of_nonneg_left hE₁ (mul_nonneg hR₂.le hθγ.le)
    have h2 := mul_le_mul_of_nonneg_left hsum (mul_nonneg hβ.le hR₂.le)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hR₁]
    nlinarith [h1, h2, hE₂]
  -- read off `c₂ ≤ (R₁/R₂)^{1/γ} c₁ θ`
  have hratio : (1 + r₂) / (1 + r₁) * θ ^ (-γ) * c₁ ^ (-γ)
      = (((1 + r₁) / (1 + r₂)) ^ (1 / γ) * c₁ * θ) ^ (-γ) := by
    have hq : (0 : ℝ) < (1 + r₁) / (1 + r₂) := div_pos hR₁ hR₂
    rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hq.le _) hc₁0.le) hθ0.le,
      Real.mul_rpow (Real.rpow_nonneg hq.le _) hc₁0.le, ← Real.rpow_mul hq.le,
      show 1 / γ * (-γ) = -1 from by field_simp, Real.rpow_neg_one, inv_div]
    ring
  rw [hratio] at hchain
  exact le_of_rpow_neg_le (by positivity) hc₂0 hγ0 hchain

/-- **The gap form**: `c₂ - c₁ ≤ c₁ [(R₁/R₂)^{1/γ}(1 + X/c_min) - 1]`. -/
theorem consumption_gap_transfer {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    (hβ : 0 < (P.discount : ℝ))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₂ h₂).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (hint₁ : 0 < (P.withRate r₁ h₁).policy (a, z))
    {X : ℝ} (hX : 0 ≤ X)
    (hgap : ∀ z' : Z, (P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z))
      ≤ (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)) + X)
    {cmin : ℝ} (hcmin : 0 < cmin)
    (hfloor : ∀ z' : Z,
      cmin ≤ (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z))) :
    (P.withRate r₂ h₂).consumptionFn z a - (P.withRate r₁ h₁).consumptionFn z a
      ≤ (P.withRate r₁ h₁).consumptionFn z a
        * (((1 + r₁) / (1 + r₂)) ^ (1 / γ) * (1 + X / cmin) - 1) := by
  have := P.consumption_transfer hγ0 hu h₁ h₂ hβ hpc₁ hpc₂ hslack₁ hslack₂ ha z hint₁ hX hgap hcmin
    hfloor
  nlinarith [this]

end IncomeFluctuation

end LeanEconomics
