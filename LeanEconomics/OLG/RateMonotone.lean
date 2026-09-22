/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.Equilibrium

/-!
# Theorem 1 in the life cycle: saving rises with the interest rate

This is the one hypothesis the life-cycle chain of `Equilibrium` still assumes, and the case the
infinite horizon could not settle above logarithmic utility. In the life cycle the statement has
a form the stationary problem does not offer.

## The statement is its own terminal condition

Since `a' = R a + y(z) - c` at either rate, saving rising with the rate is the same as a bound on
the response of consumption:

  `g_k(a, z; r₂) ≥ g_k(a, z; r₁)`  ⟺  `c_k(a, z; r₂) - c_k(a, z; r₁) ≤ (r₂ - r₁) a`

(`stagePolicy_le_iff_consumption_le`). In the last period consumption is cash on hand, so the
right-hand statement holds *with equality* (`stagePolicy_mono_zero`): the terminal condition is
exactly the claim. Everything reduces to whether it propagates backward.

## The step

`stagePolicy_mono_step` is the induction step. Suppose the claim holds at stage `k` and fails at
stage `k+1` at some state. Then the higher-rate household saves strictly less, so the lower-rate
household saves strictly more than nothing and its Euler equation holds above the floor, while
the higher-rate household's holds under the cap. The claim at stage `k`, and monotonicity of
consumption in assets, bound the higher-rate household's consumption next period by

  `c_k(z', a'₁; r₁) + (r₂ - r₁) a'₁`,

and one inequality between the two Euler equations then contradicts the failure. That inequality
is `StageSlack`: with `b = g_{k+1}(a, z; r₁)` the lower-rate household's saving and
`C'(z') = c_k(z', b; r₁)` its consumption next period,

  `R₁ ∑ π(z,z') C'(z')^{-γ} ≤ R₂ ∑ π(z,z') (C'(z') + Δr·b)^{-γ} · (1 + Δr·a/c)^γ`.

It says the same thing as the slack elasticity condition of the stationary development, read at
one age: the ratio of assets to consumption may rise from one age to the next by at most about
`1/(γR)`. With the condition at every age, Theorem 1 holds at every age
(`stagePolicy_mono_of_stageSlack`), aggregate capital rises with the rate
(`olgCapital_le_of_stageSlack`), and the equilibrium rate is unique
(`olgEquilibriumRate_unique`).

## What is proved and what is assumed

The reduction is proved. The condition is not proved from primitives, and the numerical section
of the write-up reports exactly where it and its conclusion stand: Theorem 1 holds throughout a
sixty-period life for relative risk aversion up to about `3.4` at Aiyagari's calibration, so it
covers his `μ = 3` and fails at his `μ = 5`, where saving at zero wealth in the highest income
state falls as the rate rises. Two features of the finite horizon that the stationary case lacks
are used above and worth naming: the terminal stage is an equality rather than a hypothesis, and
a household at a corner needs no argument at all, because consumption cannot exceed cash on hand.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- Saving rises with the rate exactly when the consumption response is at most the extra
interest income. The two are the same statement, by the budget constraint. -/
theorem stagePolicy_le_iff_consumption_le {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).stagePolicy k (a, z) ≤ (P.withRate r₂ h₂).stagePolicy k (a, z)
      ↔ (P.withRate r₂ h₂).stageConsumption k z a
        ≤ (P.withRate r₁ h₁).stageConsumption k z a + (r₂ - r₁) * a := by
  rw [stageConsumption_eq, stageConsumption_eq, (P.withRate r₁ h₁).resources_eq_of_mem ha z,
    (P.withRate r₂ h₂).resources_eq_of_mem ha z]
  simp only [withRate_income, withRate_interest]
  constructor <;> intro h <;> nlinarith [h]

/-- **The terminal stage is an equality.** In the last period consumption is cash on hand, so
both households save nothing. -/
theorem stagePolicy_mono_zero {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).stagePolicy 0 (a, z) ≤ (P.withRate r₂ h₂).stagePolicy 0 (a, z) := by
  rw [(P.withRate r₁ h₁).stagePolicy_zero ha z, (P.withRate r₂ h₂).stagePolicy_zero ha z]

/-- **The age-indexed slack condition.** At the state `(a, z)` with `k+1` periods still to come,
written at the lower-rate household's own saving `b` and consumption. -/
def StageSlack {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (γ : ℝ) (k : ℕ) (a : ℝ)
    (z : Z) : Prop :=
  (1 + r₁) * ∑ z', P.transitionMatrix z z'
      * ((P.withRate r₁ h₁).stageConsumption k z'
        ((P.withRate r₁ h₁).stagePolicy (k + 1) (a, z))) ^ (-γ)
    ≤ (1 + r₂) * (∑ z', P.transitionMatrix z z'
      * ((P.withRate r₁ h₁).stageConsumption k z'
          ((P.withRate r₁ h₁).stagePolicy (k + 1) (a, z))
        + (r₂ - r₁) * (P.withRate r₁ h₁).stagePolicy (k + 1) (a, z)) ^ (-γ))
      * (1 + (r₂ - r₁) * a / (P.withRate r₁ h₁).stageConsumption (k + 1) z a) ^ γ

/-- **The induction step.** Given the claim at stage `k` and the slack condition at
`(a, z)`, saving rises with the rate at stage `k+1` there. -/
theorem stagePolicy_mono_step {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hdunb : P.Unbounded) {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁)
    (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hcap₁ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate r₁ h₁).stagePolicy j (b, w) < assetCap)
    (hcap₂ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate r₂ h₂).stagePolicy j (b, w) < assetCap)
    (k : ℕ) (ih : ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate r₁ h₁).stagePolicy k (b, w) ≤ (P.withRate r₂ h₂).stagePolicy k (b, w))
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hslack : P.StageSlack h₁ h₂ γ k a z) :
    (P.withRate r₁ h₁).stagePolicy (k + 1) (a, z)
      ≤ (P.withRate r₂ h₂).stagePolicy (k + 1) (a, z) := by
  classical
  unfold StageSlack at hslack
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  by_contra hcon
  rw [not_le] at hcon
  have hbmem : (P.withRate r₁ h₁).stagePolicy (k + 1) (a, z) ∈ Icc (0 : ℝ) assetCap :=
    (P.withRate r₁ h₁).stagePolicy_mem_region _ _
  have hdmem : (P.withRate r₂ h₂).stagePolicy (k + 1) (a, z) ∈ Icc (0 : ℝ) assetCap :=
    (P.withRate r₂ h₂).stagePolicy_mem_region _ _
  have hb0 : 0 < (P.withRate r₁ h₁).stagePolicy (k + 1) (a, z) := lt_of_le_of_lt hdmem.1 hcon
  have hc₁0 : 0 < (P.withRate r₁ h₁).stageConsumption (k + 1) z a :=
    (P.withRate r₁ h₁).stageConsumption_pos hdunb _ z ha
  have hc₂0 : 0 < (P.withRate r₂ h₂).stageConsumption (k + 1) z a :=
    (P.withRate r₂ h₂).stageConsumption_pos hdunb _ z ha
  -- the failure, in consumption terms
  have hfail : (P.withRate r₁ h₁).stageConsumption (k + 1) z a + (r₂ - r₁) * a
      < (P.withRate r₂ h₂).stageConsumption (k + 1) z a := by
    by_contra hnc
    rw [not_lt] at hnc
    exact absurd ((P.stagePolicy_le_iff_consumption_le h₁ h₂ (k + 1) z ha).mpr hnc)
      (not_le.mpr hcon)
  -- Euler above the floor at the lower rate
  have hslack₁ : ∀ z' : Z, (P.withRate r₁ h₁).stagePolicy k
      ((P.withRate r₁ h₁).stagePolicy (k + 1) (a, z), z')
      < (P.withRate r₁ h₁).maxSaving ((P.withRate r₁ h₁).stagePolicy (k + 1) (a, z), z') := by
    intro z'
    rw [maxSaving_eq]
    refine lt_min (hcap₁ k _ hbmem z') ?_
    have := (P.withRate r₁ h₁).stageConsumption_pos hdunb k z' hbmem
    change 0 < (P.withRate r₁ h₁).resources _ - (P.withRate r₁ h₁).stagePolicy k _ at this
    linarith
  have hE₁ := (P.withRate r₁ h₁).stage_euler_ge hu hdunb k z ha hb0 hslack₁
  -- Euler under the cap at the higher rate
  have hroom₂ : (P.withRate r₂ h₂).stagePolicy (k + 1) (a, z)
      < (P.withRate r₂ h₂).maxSaving (a, z) := by
    rw [maxSaving_eq]
    refine lt_min (hcap₂ (k + 1) a ha z) ?_
    have := hc₂0
    change 0 < (P.withRate r₂ h₂).resources (a, z)
      - (P.withRate r₂ h₂).stagePolicy (k + 1) (a, z) at this
    linarith
  have hE₂ := (P.withRate r₂ h₂).stage_euler_le hu hdunb k z ha hroom₂
  simp only [withRate_transitionMatrix, withRate_interest, withRate_discount] at hE₁ hE₂
  -- tomorrow's consumption at the higher rate, bounded by the claim at stage `k`
  have hDC : ∀ z' : Z, (P.withRate r₂ h₂).stageConsumption k z'
        ((P.withRate r₂ h₂).stagePolicy (k + 1) (a, z))
      ≤ (P.withRate r₁ h₁).stageConsumption k z'
          ((P.withRate r₁ h₁).stagePolicy (k + 1) (a, z))
        + (r₂ - r₁) * (P.withRate r₁ h₁).stagePolicy (k + 1) (a, z) := by
    intro z'
    have hstep := (P.stagePolicy_le_iff_consumption_le h₁ h₂ k z' hdmem).mp
      (ih _ hdmem z')
    have hmono : (P.withRate r₁ h₁).stageConsumption k z'
        ((P.withRate r₂ h₂).stagePolicy (k + 1) (a, z))
        ≤ (P.withRate r₁ h₁).stageConsumption k z'
          ((P.withRate r₁ h₁).stagePolicy (k + 1) (a, z)) :=
      (P.withRate r₁ h₁).stageConsumption_mono k hdmem hbmem hcon.le
    have hdb : (r₂ - r₁) * (P.withRate r₂ h₂).stagePolicy (k + 1) (a, z)
        ≤ (r₂ - r₁) * (P.withRate r₁ h₁).stagePolicy (k + 1) (a, z) :=
      mul_le_mul_of_nonneg_left hcon.le (by linarith)
    linarith
  have hsum₂ : ∑ z', P.transitionMatrix z z'
        * ((P.withRate r₁ h₁).stageConsumption k z'
            ((P.withRate r₁ h₁).stagePolicy (k + 1) (a, z))
          + (r₂ - r₁) * (P.withRate r₁ h₁).stagePolicy (k + 1) (a, z)) ^ (-γ)
      ≤ ∑ z', P.transitionMatrix z z'
        * ((P.withRate r₂ h₂).stageConsumption k z'
            ((P.withRate r₂ h₂).stagePolicy (k + 1) (a, z))) ^ (-γ) := by
    refine Finset.sum_le_sum fun z' _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (P.transitionMatrix_nonneg z z')
    exact rpow_neg_antitone hγ0
      ((P.withRate r₂ h₂).stageConsumption_pos hdunb k z' hdmem) (hDC z')
  have hra : (0 : ℝ) ≤ (r₂ - r₁) * a := mul_nonneg (by linarith) ha.1
  -- the scaling factor
  have hfac : (0 : ℝ) < 1 + (r₂ - r₁) * a / (P.withRate r₁ h₁).stageConsumption (k + 1) z a := by
    have := div_nonneg hra hc₁0.le
    linarith
  have hrew : ((P.withRate r₁ h₁).stageConsumption (k + 1) z a + (r₂ - r₁) * a) ^ (-γ)
      = ((P.withRate r₁ h₁).stageConsumption (k + 1) z a) ^ (-γ)
        * ((1 + (r₂ - r₁) * a
          / (P.withRate r₁ h₁).stageConsumption (k + 1) z a) ^ γ)⁻¹ := by
    rw [show (P.withRate r₁ h₁).stageConsumption (k + 1) z a + (r₂ - r₁) * a
        = (P.withRate r₁ h₁).stageConsumption (k + 1) z a
          * (1 + (r₂ - r₁) * a / (P.withRate r₁ h₁).stageConsumption (k + 1) z a) by field_simp,
      Real.mul_rpow hc₁0.le hfac.le, Real.rpow_neg hfac.le]
  -- name the four quantities and chain
  set c₁ : ℝ := (P.withRate r₁ h₁).stageConsumption (k + 1) z a with hc₁def
  set c₂ : ℝ := (P.withRate r₂ h₂).stageConsumption (k + 1) z a with hc₂def
  set S : ℝ := ∑ z', P.transitionMatrix z z'
    * ((P.withRate r₁ h₁).stageConsumption k z'
      ((P.withRate r₁ h₁).stagePolicy (k + 1) (a, z))) ^ (-γ) with hSdef
  set T : ℝ := ∑ z', P.transitionMatrix z z'
    * ((P.withRate r₁ h₁).stageConsumption k z'
        ((P.withRate r₁ h₁).stagePolicy (k + 1) (a, z))
      + (r₂ - r₁) * (P.withRate r₁ h₁).stagePolicy (k + 1) (a, z)) ^ (-γ) with hTdef
  set U : ℝ := ∑ z', P.transitionMatrix z z'
    * ((P.withRate r₂ h₂).stageConsumption k z'
      ((P.withRate r₂ h₂).stagePolicy (k + 1) (a, z))) ^ (-γ) with hUdef
  set F : ℝ := (1 + (r₂ - r₁) * a / c₁) ^ γ with hFdef
  have hFpos : 0 < F := Real.rpow_pos_of_pos hfac γ
  have h2 : c₁ ^ (-γ) ≤ (P.discount : ℝ) * ((1 + r₂) * T * F) :=
    hE₁.trans (mul_le_mul_of_nonneg_left hslack hβ.le)
  have h3 : c₁ ^ (-γ) * F⁻¹ ≤ (P.discount : ℝ) * ((1 + r₂) * T) := by
    rw [mul_inv_le_iff₀ hFpos]
    nlinarith [h2]
  have h4 : (P.discount : ℝ) * ((1 + r₂) * T) ≤ (P.discount : ℝ) * ((1 + r₂) * U) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum₂ hR₂.le) hβ.le
  have hchain : (c₁ + (r₂ - r₁) * a) ^ (-γ) ≤ c₂ ^ (-γ) := by
    rw [hrew]
    linarith [h3, h4, hE₂]
  have := le_of_rpow_neg_le (by linarith [hra] : (0 : ℝ) < c₁ + (r₂ - r₁) * a) hc₂0 hγ0 hchain
  linarith [hfail]

/-- **Theorem 1 in the life cycle**, given the slack condition at every age and state: saving
rises with the interest rate at every age. The terminal stage is unconditional. -/
theorem stagePolicy_mono_of_stageSlack {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hdunb : P.Unbounded) {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁)
    (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hcap₁ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate r₁ h₁).stagePolicy j (b, w) < assetCap)
    (hcap₂ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate r₂ h₂).stagePolicy j (b, w) < assetCap)
    (hsl : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, P.StageSlack h₁ h₂ γ j b w)
    (k : ℕ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r₁ h₁).stagePolicy k (a, z) ≤ (P.withRate r₂ h₂).stagePolicy k (a, z) := by
  induction k generalizing a z with
  | zero => exact P.stagePolicy_mono_zero h₁ h₂ z ha
  | succ k ih =>
    exact P.stagePolicy_mono_step hγ0 hu hβ hdunb h₁ h₂ hr hcap₁ hcap₂ k
      (fun b hb w => ih hb w) z ha (hsl k a ha z)

/-- **Aggregate capital rises with the rate**, given the slack condition at every age. With the
single crossing of `olgEquilibriumRate_unique` this is uniqueness of the life-cycle equilibrium
rate. -/
theorem olgCapital_le_of_stageSlack {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hdunb : P.Unbounded) {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁)
    (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hcap₁ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate r₁ h₁).stagePolicy j (b, w) < assetCap)
    (hcap₂ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate r₂ h₂).stagePolicy j (b, w) < assetCap)
    (hsl : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, P.StageSlack h₁ h₂ γ j b w)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) :
    (P.withRate r₁ h₁).olgCapital K ν ≤ (P.withRate r₂ h₂).olgCapital K ν :=
  (P.withRate r₁ h₁).olgCapital_le_of_stagePolicy_le (Q := P.withRate r₂ h₂) rfl
    (fun j s hs => by
      simpa using P.stagePolicy_mono_of_stageSlack hγ0 hu hβ hdunb h₁ h₂ hr hcap₁ hcap₂ hsl j
        hs s.2) K hν

end IncomeFluctuation

end LeanEconomics
