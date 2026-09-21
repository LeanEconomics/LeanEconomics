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

/-! ### The obstruction: every step of the induction is expansive

Numerically, at Aiyagari's `γ = 3` (see the write-up), the one-sided affine bound is TRUE with a
tiny intercept, yet iterating the transfer step on it diverges. The reason is a theorem. Write
the transfer bound with the exact Euler weighting over tomorrow's income in place of the
minimum, as a function of a uniform bound `X` on tomorrow's gap:

  `Φ(X) = (R₁/R₂)^{1/γ} · c₁ · (∑ π c'^{-γ} / ∑ π (c' + X)^{-γ})^{1/γ}`   (`transferBound`).

Its derivative at `X = 0` is the multiplier of one step of the induction,

  `Φ'(0) = (R₁/R₂)^{1/γ} · c₁ · ∑ π c'^{-γ-1} / ∑ π c'^{-γ}`   (`hasDerivAt_transferBound`),

and at every state where the lower-rate household saves this multiplier is at least
`(β R₂)^{-1/γ} = 1/Þ₂` (`transfer_multiplier_ge`). The proof is two lines: the Euler inequality
above the floor, `c₁^{-γ} ≤ β R₁ ∑ π c'^{-γ}`, and Jensen for the power `(γ+1)/γ`,
`∑ π c'^{-γ-1} ≥ (∑ π c'^{-γ})^{(γ+1)/γ}` (`euler_amplification_ge`). So whenever the
higher-rate household is impatient the multiplier exceeds one (`one_lt_transfer_multiplier`):
a supremum induction on an affine bound loses ground at every interior state, and no slope and
no intercept, not even one depending on the income state, can be self-consistent. This is the
mechanism that made the Lipschitz-in-rate recursion neutral: impatience is a neutral or
expansive direction of the Euler fixed point. The rate-response programme is closed here; the
transfer lemma stands as a single step, and the bound it was meant to prove stands as a
numerical fact.
-/

section Obstruction

omit [TopologicalSpace Z] [DiscreteTopology Z] [Nonempty Z] in
/-- Weighted Jensen for the power `(γ+1)/γ`, written for `y = c^{-γ}` so that
`y^{(γ+1)/γ} = c^{-(γ+1)}`. -/
theorem sum_rpow_neg_succ_ge {γ : ℝ} (hγ0 : 0 < γ) (π : Z → ℝ) (hπ : ∀ z', 0 ≤ π z')
    (hπ1 : ∑ z', π z' = 1) (c : Z → ℝ) (hc : ∀ z', 0 < c z') :
    (∑ z', π z' * c z' ^ (-γ)) ^ ((γ + 1) / γ) ≤ ∑ z', π z' * c z' ^ (-(γ + 1)) := by
  have hp : (1 : ℝ) ≤ (γ + 1) / γ := by rw [le_div_iff₀ hγ0]; linarith
  have h := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ π (fun z' => c z' ^ (-γ))
    (fun z' _ => hπ z') hπ1 (fun z' _ => Real.rpow_nonneg (hc z').le _) hp
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun z' _ => ?_))
  rw [← Real.rpow_mul (hc z').le]
  congr 2
  field_simp

/-- The Euler inequality above the floor at rate `r₁`, at a state where the household saves. -/
theorem crra_euler_ge_withRate {γ : ℝ} (hu : P.u = crraUtility γ)
    {r₁ : ℝ} (h₁ : P.RateOK r₁) (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₁ h₁).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (hint₁ : 0 < (P.withRate r₁ h₁).policy (a, z)) :
    (P.withRate r₁ h₁).consumptionFn z a ^ (-γ)
      ≤ (P.discount : ℝ) * ((1 + r₁) * ∑ z', P.transitionMatrix z z'
        * (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)) ^ (-γ)) := by
  classical
  set A₁ : ℝ := (P.withRate r₁ h₁).policy (a, z) with hA₁
  have hA₁mem : A₁ ∈ Icc (0 : ℝ) assetCap := (P.withRate r₁ h₁).policy_mem_region _
  set c₁ : ℝ := (P.withRate r₁ h₁).consumptionFn z a with hc₁
  have hc₁0 : 0 < c₁ := (P.withRate r₁ h₁).consumptionFn_pos hpc₁ ha z
  have hc₁' : ∀ z' : Z, 0 < (P.withRate r₁ h₁).consumptionFn z' A₁ :=
    fun z' => (P.withRate r₁ h₁).consumptionFn_pos hpc₁ hA₁mem z'
  have hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (c ^ (-γ)) c := fun c hc => by
    rw [hu]; exact hasDerivAt_crraUtility γ hc
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
  simpa only [IncomeFluctuation.withRate_discount, IncomeFluctuation.withRate_interest,
    IncomeFluctuation.withRate_transitionMatrix] using hE₁

/-- **The Euler-weighted amplification is at least `1/Þ₁`**: at a state where the household
saves, `c₁ · ∑ π c'^{-γ-1} / ∑ π c'^{-γ} ≥ (β R₁)^{-1/γ}`. -/
theorem euler_amplification_ge {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    {r₁ : ℝ} (h₁ : P.RateOK r₁) (hβ : 0 < (P.discount : ℝ))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₁ h₁).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (hint₁ : 0 < (P.withRate r₁ h₁).policy (a, z)) :
    ((P.discount : ℝ) * (1 + r₁)) ^ (-(1 / γ))
      ≤ (P.withRate r₁ h₁).consumptionFn z a
        * ((∑ z', P.transitionMatrix z z'
            * (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)) ^ (-(γ + 1)))
          / (∑ z', P.transitionMatrix z z'
            * (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)) ^ (-γ))) := by
  classical
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hβR : (0 : ℝ) < (P.discount : ℝ) * (1 + r₁) := mul_pos hβ hR₁
  set A₁ : ℝ := (P.withRate r₁ h₁).policy (a, z) with hA₁
  have hA₁mem : A₁ ∈ Icc (0 : ℝ) assetCap := (P.withRate r₁ h₁).policy_mem_region _
  set c₁ : ℝ := (P.withRate r₁ h₁).consumptionFn z a with hc₁
  have hc₁0 : 0 < c₁ := (P.withRate r₁ h₁).consumptionFn_pos hpc₁ ha z
  have hc₁' : ∀ z' : Z, 0 < (P.withRate r₁ h₁).consumptionFn z' A₁ :=
    fun z' => (P.withRate r₁ h₁).consumptionFn_pos hpc₁ hA₁mem z'
  have hE₁ := P.crra_euler_ge_withRate hu h₁ hpc₁ hslack₁ ha z hint₁
  set S : ℝ := ∑ z', P.transitionMatrix z z'
    * (P.withRate r₁ h₁).consumptionFn z' A₁ ^ (-γ) with hS
  set T : ℝ := ∑ z', P.transitionMatrix z z'
    * (P.withRate r₁ h₁).consumptionFn z' A₁ ^ (-(γ + 1)) with hT
  have hcγ : 0 < c₁ ^ (-γ) := Real.rpow_pos_of_pos hc₁0 _
  have hSpos : 0 < S := by
    by_contra hcon
    push Not at hcon
    have : (P.discount : ℝ) * ((1 + r₁) * S) ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hR₁.le hcon
      exact mul_nonpos_of_nonneg_of_nonpos hβ.le this
    linarith
  have hJ : S ^ ((γ + 1) / γ) ≤ T :=
    sum_rpow_neg_succ_ge hγ0 (P.transitionMatrix z) (P.transitionMatrix_nonneg z)
      (P.transitionMatrix_sum z) _ hc₁'
  have hSpow : S ^ ((γ + 1) / γ) = S * S ^ (1 / γ) := by
    rw [show (γ + 1) / γ = 1 + 1 / γ by field_simp, Real.rpow_add hSpos, Real.rpow_one]
  have h1 : (c₁ ^ (-γ) / ((P.discount : ℝ) * (1 + r₁))) ^ (1 / γ) ≤ S ^ (1 / γ) := by
    refine Real.rpow_le_rpow (div_nonneg hcγ.le hβR.le) ?_ (by positivity)
    rw [div_le_iff₀ hβR]
    linarith [hE₁]
  have h2 : (c₁ ^ (-γ) / ((P.discount : ℝ) * (1 + r₁))) ^ (1 / γ)
      = c₁⁻¹ * ((P.discount : ℝ) * (1 + r₁)) ^ (-(1 / γ)) := by
    rw [Real.div_rpow hcγ.le hβR.le, ← Real.rpow_mul hc₁0.le,
      show -γ * (1 / γ) = -1 by field_simp, Real.rpow_neg_one, Real.rpow_neg hβR.le,
      div_eq_mul_inv]
  calc ((P.discount : ℝ) * (1 + r₁)) ^ (-(1 / γ))
      = c₁ * (c₁⁻¹ * ((P.discount : ℝ) * (1 + r₁)) ^ (-(1 / γ))) := by
        field_simp
    _ ≤ c₁ * S ^ (1 / γ) := mul_le_mul_of_nonneg_left (h2 ▸ h1) hc₁0.le
    _ ≤ c₁ * (T / S) := by
        refine mul_le_mul_of_nonneg_left ?_ hc₁0.le
        rw [le_div_iff₀ hSpos]
        linarith [hJ, hSpow, mul_comm S (S ^ (1 / γ))]

/-- **The multiplier of the transfer step is at least `1/Þ₂`**: with the substitution factor
`(R₁/R₂)^{1/γ}` included, the Euler-weighted step multiplier is at least `(β R₂)^{-1/γ}`. -/
theorem transfer_multiplier_ge {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hβ : 0 < (P.discount : ℝ))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₁ h₁).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (hint₁ : 0 < (P.withRate r₁ h₁).policy (a, z)) :
    ((P.discount : ℝ) * (1 + r₂)) ^ (-(1 / γ))
      ≤ ((1 + r₁) / (1 + r₂)) ^ (1 / γ) * (P.withRate r₁ h₁).consumptionFn z a
        * ((∑ z', P.transitionMatrix z z'
            * (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)) ^ (-(γ + 1)))
          / (∑ z', P.transitionMatrix z z'
            * (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)) ^ (-γ))) := by
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hβR₁ : (0 : ℝ) < (P.discount : ℝ) * (1 + r₁) := mul_pos hβ hR₁
  have hβR₂ : (0 : ℝ) < (P.discount : ℝ) * (1 + r₂) := mul_pos hβ hR₂
  have hq : (0 : ℝ) < (1 + r₁) / (1 + r₂) := div_pos hR₁ hR₂
  have h := P.euler_amplification_ge hγ0 hu h₁ hβ hpc₁ hslack₁ ha z hint₁
  have key : ((1 + r₁) / (1 + r₂)) ^ (1 / γ) * ((P.discount : ℝ) * (1 + r₁)) ^ (-(1 / γ))
      = ((P.discount : ℝ) * (1 + r₂)) ^ (-(1 / γ)) := by
    rw [Real.rpow_neg hβR₁.le, Real.rpow_neg hβR₂.le, ← Real.inv_rpow hβR₁.le,
      ← Real.inv_rpow hβR₂.le, ← Real.mul_rpow hq.le (inv_nonneg.2 hβR₁.le)]
    congr 1
    field_simp
  calc ((P.discount : ℝ) * (1 + r₂)) ^ (-(1 / γ))
      = ((1 + r₁) / (1 + r₂)) ^ (1 / γ) * ((P.discount : ℝ) * (1 + r₁)) ^ (-(1 / γ)) := key.symm
    _ ≤ ((1 + r₁) / (1 + r₂)) ^ (1 / γ) * ((P.withRate r₁ h₁).consumptionFn z a * (_ / _)) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hq.le _)
    _ = _ := by ring

/-- **Impatience makes the step expansive**: if `β R₂ < 1`, the multiplier exceeds one. -/
theorem one_lt_transfer_multiplier {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hβ : 0 < (P.discount : ℝ))
    (hβR₂ : (P.discount : ℝ) * (1 + r₂) < 1)
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₁ h₁).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (hint₁ : 0 < (P.withRate r₁ h₁).policy (a, z)) :
    1 < ((1 + r₁) / (1 + r₂)) ^ (1 / γ) * (P.withRate r₁ h₁).consumptionFn z a
        * ((∑ z', P.transitionMatrix z z'
            * (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)) ^ (-(γ + 1)))
          / (∑ z', P.transitionMatrix z z'
            * (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)) ^ (-γ))) := by
  refine lt_of_lt_of_le ?_ (P.transfer_multiplier_ge hγ0 hu h₁ h₂ hβ hpc₁ hslack₁ ha z hint₁)
  have hβR₂0 : (0 : ℝ) < (P.discount : ℝ) * (1 + r₂) := mul_pos hβ h₂.1
  rw [Real.rpow_neg hβR₂0.le, one_lt_inv₀ (Real.rpow_pos_of_pos hβR₂0 _)]
  exact Real.rpow_lt_one hβR₂0.le hβR₂ (by positivity)

/-- The transfer bound with the exact Euler weighting, as a function of a uniform bound `X` on
tomorrow's consumption gap. -/
noncomputable def transferBound (q c₁ γ : ℝ) (π c : Z → ℝ) (X : ℝ) : ℝ :=
  q * c₁ * ((∑ z', π z' * c z' ^ (-γ)) / (∑ z', π z' * (c z' + X) ^ (-γ))) ^ (1 / γ)

omit [TopologicalSpace Z] [DiscreteTopology Z] [Nonempty Z] in
/-- **The multiplier is the derivative of the transfer bound at a zero gap.** -/
theorem hasDerivAt_transferBound {γ : ℝ} (hγ0 : 0 < γ) (q c₁ : ℝ) (π c : Z → ℝ)
    (hc : ∀ z', 0 < c z') (hS : 0 < ∑ z', π z' * c z' ^ (-γ)) :
    HasDerivAt (transferBound q c₁ γ π c)
      (q * c₁ * ((∑ z', π z' * c z' ^ (-(γ + 1))) / (∑ z', π z' * c z' ^ (-γ)))) 0 := by
  set S : ℝ := ∑ z', π z' * c z' ^ (-γ) with hSdef
  set T : ℝ := ∑ z', π z' * c z' ^ (-(γ + 1)) with hTdef
  have hD : HasDerivAt (fun X : ℝ => ∑ z', π z' * (c z' + X) ^ (-γ)) (-γ * T) 0 := by
    have hterm : ∀ z', HasDerivAt (fun X : ℝ => π z' * (c z' + X) ^ (-γ))
        (π z' * (1 * (-γ) * (c z' + 0) ^ (-γ - 1))) 0 := by
      intro z'
      refine HasDerivAt.const_mul _ ?_
      refine ((hasDerivAt_id' (0 : ℝ)).const_add (c z')).rpow_const (Or.inl ?_)
      rw [add_zero]; exact (hc z').ne'
    have h := HasDerivAt.sum (u := Finset.univ) fun z' _ => hterm z'
    have hfun : (∑ i : Z, fun X : ℝ => π i * (c i + X) ^ (-γ))
        = fun X => ∑ z', π z' * (c z' + X) ^ (-γ) := by
      ext X; simp [Finset.sum_apply]
    rw [hfun] at h
    refine h.congr_deriv ?_
    rw [hTdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [add_zero, one_mul, show -γ - 1 = -(γ + 1) by ring]
    ring
  have hQ : HasDerivAt (fun X : ℝ => S / ∑ z', π z' * (c z' + X) ^ (-γ)) (γ * T / S) 0 := by
    refine ((hasDerivAt_const (0 : ℝ) S).div hD ?_).congr_deriv ?_
    · simp only [add_zero]
      rw [← hSdef]
      exact hS.ne'
    · simp only [add_zero]
      rw [← hSdef]
      field_simp
      ring
  have hP := hQ.rpow_const (p := 1 / γ) (Or.inl (by
    simp only [add_zero]
    rw [← hSdef, div_self hS.ne']
    exact one_ne_zero))
  change HasDerivAt (fun X : ℝ => q * c₁ * (S / ∑ z', π z' * (c z' + X) ^ (-γ)) ^ (1 / γ)) _ 0
  refine (hP.const_mul (q * c₁)).congr_deriv ?_
  simp only [add_zero]
  rw [← hSdef, div_self hS.ne', Real.one_rpow]
  field_simp

end Obstruction

end IncomeFluctuation

end LeanEconomics
