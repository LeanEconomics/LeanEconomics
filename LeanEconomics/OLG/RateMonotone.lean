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

/-! ### A second route: the value gap

`StageSlack` is an Euler condition, and at logarithmic utility it is false at rates at or above
the rate of time preference, which is where a life-cycle equilibrium sits. This section gives a
different sufficient condition, which at logarithmic utility holds everywhere.

The condition is that the extra value the higher rate confers rises with the household's assets.
By the envelope theorem the slope of that gap is `R₂u'(c₂) - R₁u'(c₁)`, so it says the marginal
value of assets rises with the rate. At logarithmic utility that reads `c(R₂)/R₂ ≤ c(R₁)/R₁`, and
it is easy to see why it holds: the propensity to consume out of total wealth is `1/∑ β^i`, which
does not depend on the rate at all when `γ = 1`, while human wealth falls as the rate rises, so
consumption rises by proportionally less than the rate does.

Unlike `StageSlack` this needs no induction over ages. The condition on the continuation gives the
conclusion for the household that faces it, directly, by Topkis: the two households differ only in
their cash on hand, which is ordered, and in their continuations, whose difference is increasing.
Only concavity of period utility is used.
-/

/-- **The value-gap condition on the stage-`k` continuation**, with slope at least `θ`. -/
def ValueGap {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (θ : ℝ) (k : ℕ) : Prop :=
  ∀ z : Z, ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ y ∈ Icc (0 : ℝ) assetCap, x ≤ y →
    θ * (y - x)
      ≤ ((P.withRate r₂ h₂).stageValue k (y, z) - (P.withRate r₁ h₁).stageValue k (y, z))
        - ((P.withRate r₂ h₂).stageValue k (x, z) - (P.withRate r₁ h₁).stageValue k (x, z))

/-- **Saving rises with the rate when the value gap rises with assets.** The proof is Topkis with
two continuations: the higher-rate household has weakly more cash on hand and a continuation whose
gap to the lower one is increasing, so its saving cannot be smaller. Only concavity of period
utility is used, and no induction over ages. -/
theorem stagePolicy_mono_of_valueGap {θ : ℝ} (hθ : 0 < θ) (hβ : 0 < (P.discount : ℝ))
    (hdunb : P.Unbounded) {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (k : ℕ) (hgap : P.ValueGap h₁ h₂ θ k) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).stagePolicy k (a, z) ≤ (P.withRate r₂ h₂).stagePolicy k (a, z) := by
  classical
  set P₁ := P.withRate r₁ h₁ with hP₁
  set P₂ := P.withRate r₂ h₂ with hP₂
  set x₁ := P₁.stagePolicy k (a, z) with hx₁
  set x₂ := P₂.stagePolicy k (a, z) with hx₂
  by_contra hcon
  push Not at hcon
  have hmem₁ : x₁ ∈ Icc (0 : ℝ) assetCap := P₁.stagePolicy_mem_region _ _
  have hmem₂ : x₂ ∈ Icc (0 : ℝ) assetCap := P₂.stagePolicy_mem_region _ _
  have hc₁ : 0 < P₁.resources (a, z) - x₁ := P₁.stageConsumption_pos hdunb k z ha
  have hc₂ : 0 < P₂.resources (a, z) - x₂ := P₂.stageConsumption_pos hdunb k z ha
  have hmle : P₁.resources (a, z) ≤ P₂.resources (a, z) := by
    rw [P₁.resources_eq_of_mem ha z, P₂.resources_eq_of_mem ha z]
    have : (1 + r₁) * a ≤ (1 + r₂) * a := mul_le_mul_of_nonneg_right (by linarith) ha.1
    simpa [hP₁, hP₂] using this
  -- both deviations are feasible in the other problem
  have hfeas₁ : x₂ ∈ P₁.toExtended.feasible (a, z) := by
    refine ⟨hmem₂.1, ?_⟩
    show x₂ ≤ max (0 : ℝ) (min assetCap (P₁.resources (a, z)))
    exact le_trans (le_min hmem₂.2 (by linarith)) (le_max_right _ _)
  have hfeas₂ : x₁ ∈ P₂.toExtended.feasible (a, z) := by
    refine ⟨hmem₁.1, ?_⟩
    show x₁ ≤ max (0 : ℝ) (min assetCap (P₂.resources (a, z)))
    exact le_trans (le_min hmem₁.2 (by linarith)) (le_max_right _ _)
  -- the two optimality comparisons
  have e₁ : P₁.lazyValue (P₁.stageValue k) z x₂ a ≤ P₁.lazyValue (P₁.stageValue k) z x₁ a := by
    have hle := P₁.lazyValue_le (P₁.stageValue k) z ha hfeas₁ (by
      show 0 < P₁.resources (a, z) - x₂; linarith)
    have heq : P₁.lazyValue (P₁.stageValue k) z x₁ a
        = P₁.toExtended.bellmanFn (P₁.stageValue k) (a, z) :=
      P₁.lazyValue_eq_dom (P₁.stageValue k) z ha (P₁.policyOf_mem _ (a, z))
        (P₁.mem_dom_of_pos hc₁) (P₁.policyOf_optimal _ (a, z))
    rw [heq]; exact hle
  have e₂ : P₂.lazyValue (P₂.stageValue k) z x₁ a ≤ P₂.lazyValue (P₂.stageValue k) z x₂ a := by
    have hle := P₂.lazyValue_le (P₂.stageValue k) z ha hfeas₂ (by
      show 0 < P₂.resources (a, z) - x₁; linarith)
    have heq : P₂.lazyValue (P₂.stageValue k) z x₂ a
        = P₂.toExtended.bellmanFn (P₂.stageValue k) (a, z) :=
      P₂.lazyValue_eq_dom (P₂.stageValue k) z ha (P₂.policyOf_mem _ (a, z))
        (P₂.mem_dom_of_pos hc₂) (P₂.policyOf_optimal _ (a, z))
    rw [heq]; exact hle
  simp only [lazyValue] at e₁ e₂
  -- the gap between the continuations, averaged over the shock
  have hgapsum : θ * (x₁ - x₂)
      ≤ ((∑ z' : Z, P.transitionMatrix z z' * P₂.stageValue k (x₁, z'))
          - ∑ z' : Z, P.transitionMatrix z z' * P₁.stageValue k (x₁, z'))
        - ((∑ z' : Z, P.transitionMatrix z z' * P₂.stageValue k (x₂, z'))
          - ∑ z' : Z, P.transitionMatrix z z' * P₁.stageValue k (x₂, z')) := by
    have hterm : ∀ z' : Z, P.transitionMatrix z z' * (θ * (x₁ - x₂))
        ≤ P.transitionMatrix z z'
            * ((P₂.stageValue k (x₁, z') - P₁.stageValue k (x₁, z'))
              - (P₂.stageValue k (x₂, z') - P₁.stageValue k (x₂, z'))) := fun z' =>
      mul_le_mul_of_nonneg_left (hgap z' x₂ hmem₂ x₁ hmem₁ hcon.le)
        (P.transitionMatrix_nonneg z z')
    have hsum := Finset.sum_le_sum fun z' (_ : z' ∈ Finset.univ) => hterm z'
    rw [← Finset.sum_mul, P.transitionMatrix_sum z, one_mul] at hsum
    have hexp : ∑ z' : Z, P.transitionMatrix z z'
          * ((P₂.stageValue k (x₁, z') - P₁.stageValue k (x₁, z'))
            - (P₂.stageValue k (x₂, z') - P₁.stageValue k (x₂, z')))
        = ((∑ z' : Z, P.transitionMatrix z z' * P₂.stageValue k (x₁, z'))
            - ∑ z' : Z, P.transitionMatrix z z' * P₁.stageValue k (x₁, z'))
          - ((∑ z' : Z, P.transitionMatrix z z' * P₂.stageValue k (x₂, z'))
            - ∑ z' : Z, P.transitionMatrix z z' * P₁.stageValue k (x₂, z')) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hexp] at hsum
    exact hsum
  -- concavity of period utility across the four consumption levels
  set A := P₁.resources (a, z) - x₁ with hA
  set D := P₂.resources (a, z) - x₂ with hD
  have hAD : (0 : ℝ) < D - A := by rw [hA, hD]; linarith
  set lam : ℝ := (D - (P₁.resources (a, z) - x₂)) / (D - A) with hlam
  set mu : ℝ := ((P₁.resources (a, z) - x₂) - A) / (D - A) with hmu
  have hlam0 : 0 ≤ lam := div_nonneg (by rw [hD]; linarith) hAD.le
  have hmu0 : 0 ≤ mu := div_nonneg (by rw [hA]; linarith) hAD.le
  have hne : D - A ≠ 0 := hAD.ne'
  have hsum1 : lam + mu = 1 := by
    rw [hlam, hmu, ← add_div, div_eq_one_iff_eq hne]; ring
  have hcomb1 : lam * A + mu * D = P₁.resources (a, z) - x₂ := by
    rw [hlam, hmu, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]; ring
  have hcomb2 : mu * A + lam * D = P₂.resources (a, z) - x₁ := by
    rw [hlam, hmu, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne, hA, hD]
    ring
  have hcon1 : ConcaveOn ℝ (Ioi (0 : ℝ)) P.u := by
    have h := P.strictConcaveOn_u_dom
    rw [hdunb] at h
    exact h.concaveOn
  have hA0 : (0 : ℝ) < A := hc₁
  have hD0 : (0 : ℝ) < D := hc₂
  have k1 := hcon1.2 (mem_Ioi.2 hA0) (mem_Ioi.2 hD0) hlam0 hmu0 hsum1
  have k2 := hcon1.2 (mem_Ioi.2 hA0) (mem_Ioi.2 hD0) hmu0 hlam0 (by linarith)
  simp only [smul_eq_mul, hcomb1, hcomb2] at k1 k2
  have hid : lam * P.u A + mu * P.u D + (mu * P.u A + lam * P.u D) = P.u A + P.u D := by
    linear_combination (P.u A + P.u D) * hsum1
  have hu₁ : P₁.u = P.u := rfl
  have hu₂ : P₂.u = P.u := rfl
  have hd₁ : (P₁.discount : ℝ) = (P.discount : ℝ) := rfl
  have hd₂ : (P₂.discount : ℝ) = (P.discount : ℝ) := rfl
  have hπ₁ : P₁.transitionMatrix = P.transitionMatrix := rfl
  have hπ₂ : P₂.transitionMatrix = P.transitionMatrix := rfl
  rw [hu₁, hd₁, hπ₁] at e₁
  rw [hu₂, hd₂, hπ₂] at e₂
  nlinarith [e₁, e₂, k1, k2, hid, mul_le_mul_of_nonneg_left hgapsum hβ.le,
    mul_pos hβ (mul_pos hθ (sub_pos.2 hcon))]

/-- **Theorem 1 at every age, from the value gap.** The gap is trivial at the terminal stage, where
the claim is an equality anyway, so only the later continuations need the condition. -/
theorem stagePolicy_mono_of_valueGap_all {θ : ℝ} (hθ : 0 < θ) (hβ : 0 < (P.discount : ℝ))
    (hdunb : P.Unbounded) {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hgap : ∀ k : ℕ, P.ValueGap h₁ h₂ θ (k + 1)) (k : ℕ) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).stagePolicy k (a, z) ≤ (P.withRate r₂ h₂).stagePolicy k (a, z) := by
  cases k with
  | zero => exact P.stagePolicy_mono_zero h₁ h₂ z ha
  | succ k => exact P.stagePolicy_mono_of_valueGap hθ hβ hdunb h₁ h₂ hr (k + 1) (hgap k) z ha

/-- **Aggregate capital rises with the rate, from the value gap.** -/
theorem olgCapital_le_of_valueGap {θ : ℝ} (hθ : 0 < θ) (hβ : 0 < (P.discount : ℝ))
    (hdunb : P.Unbounded) {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hgap : ∀ k : ℕ, P.ValueGap h₁ h₂ θ (k + 1)) (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) :
    (P.withRate r₁ h₁).olgCapital K ν ≤ (P.withRate r₂ h₂).olgCapital K ν :=
  (P.withRate r₁ h₁).olgCapital_le_of_stagePolicy_le (Q := P.withRate r₂ h₂) rfl
    (fun j s hs => P.stagePolicy_mono_of_valueGap_all hθ hβ hdunb h₁ h₂ hr hgap j s.2 hs) K hν

end IncomeFluctuation

end LeanEconomics
