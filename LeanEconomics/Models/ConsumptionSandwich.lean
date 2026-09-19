/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.MinimalMPC

/-!
# The consumption sandwich: asymptotic linearity in the capped model

`MinimalMPC` proves the lower bound `κ·m ≤ c(m)` with `κ = 1 - Þ/R`, by an induction along
Bellman iterates. This file proves the matching UPPER bound at the fixed point,

  `c(a, z) ≤ κ · m(a, z) + κ · y_max / r`,   `m(a, z) = y(z) + R a`,   `r > 0`,

so that consumption is squeezed between two lines of slope `κ`. The constant `κ y_max / r` is
`κ` times the present value of the highest income: the consumption of a perfect-foresight
household whose income is `y_max` forever is exactly `κ(m + y_max/r)`, and no household with
income at most `y_max` consumes more. This is Ma and Toda's (2022) asymptotic linearity,
`c(m)/m → κ`, in the form the capped model can state: `|c/m - κ| ≤ κ y_max/(r m)`.

## The proof is one supremum, not an induction

An induction from the zero continuation fails here — the household with no future eats
everything, which violates the bound — and starting it elsewhere means computing a policy by
hand. Instead take `s`, the supremum over the compact region of `c - κ m`. At every state the
Euler inequality with room under the cap, `u'(c) ≥ βR E[u'(c')]`, and `c' ≤ κ m' + s` with
`m' ≤ y_max + R a'` give `c ≤ (κ(y_max + R a') + s)/Þ`; with `a' = m - c` and `Þ + κR = R` this
is `c - κ m ≤ (κ y_max + s)/R`. The supremum therefore satisfies `s ≤ (κ y_max + s)/R`, hence
`s ≤ κ y_max/(R - 1)`. No corner case: the Euler inequality in this direction holds at the
constraint too.

## Why this is here

The programme for relative risk aversion above one (`Equilibrium/SlackEuler`) needs the ratio of
consumption at two rates to relative precision of order the rate gap. Write
`c(a, z) = κ(r) m(a, z) + e(a, z, r)`; the sandwich says the correction `e` lies in
`[0, κ y_max/r]`. The question becomes whether `e` is Lipschitz in `r` with a constant of the
order of human wealth, and that is stated here as the target, not proved. The zero-income
homogeneous problem, where `e ≡ 0` and `c = κ m` exactly, is the case `y_max → 0` of the
sandwich, so no separate uncapped model is needed for it.
-/

open Set Finset Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **The correction term**: consumption minus its minimal-MPC share of cash on hand. -/
noncomputable def correction (γ : ℝ) (z : Z) (a : ℝ) : ℝ :=
  P.consumptionFn z a - P.minMPC γ * P.resources (a, z)

theorem resources_eq_of_mem {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.resources (a, z) = P.income z + (1 + P.interest) * a := by
  simp only [resources, max_eq_right ha.1]

/-- **The upper sandwich**: at a positive rate, `c ≤ κ m + κ y_max / r` at every state, from the
Euler inequality under the cap and one supremum. -/
theorem crra_consumptionFn_le_of_minMPC {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hint : 0 < P.interest)
    (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → P.policy s < assetCap)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.consumptionFn z a
      ≤ P.minMPC γ * P.resources (a, z) + P.minMPC γ * P.maxIncome / P.interest := by
  classical
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  set κ : ℝ := P.minMPC γ with hκdef
  set T : ℝ := ((P.discount : ℝ) * (1 + P.interest)) ^ (1 / γ) with hTdef
  have hT0 : 0 < T := patience_pos (P := P) hγ0 hβ
  have hkey : (1 - κ) * (1 + P.interest) = T := one_sub_minMPC_mul (P := P)
  have hTneg : T ^ (-γ) = ((P.discount : ℝ) * (1 + P.interest))⁻¹ := by
    rw [hTdef, ← Real.rpow_mul hβR0.le,
      show (1 / γ) * (-γ) = -1 from by field_simp, Real.rpow_neg_one]
  -- the correction over the compact region, and its supremum
  let f : (↥(Icc (0 : ℝ) assetCap) × Z) → ℝ := fun p =>
    P.consumptionFn p.2 p.1 - κ * P.resources ((p.1 : ℝ), p.2)
  have : Nonempty (↥(Icc (0 : ℝ) assetCap) × Z) :=
    ⟨(⟨0, ⟨le_rfl, hcap0⟩⟩, Classical.ofNonempty)⟩
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨P.maxIncome + (1 + P.interest) * assetCap, ?_⟩
    rintro _ ⟨⟨⟨b, hb⟩, w⟩, rfl⟩
    show P.consumptionFn w b - κ * P.resources (b, w) ≤ _
    have hpol : 0 ≤ P.policy (b, w) := (P.policy_mem_region (b, w)).1
    have hc : P.consumptionFn w b = P.resources (b, w) - P.policy (b, w) := rfl
    have hres := P.resources_eq_of_mem hb w
    have hinc := P.le_maxIncome w
    have hres0 : 0 ≤ P.resources (b, w) := (P.assetFloor_lt_resources (b, w)).le
    have : 0 ≤ κ * P.resources (b, w) := mul_nonneg hκ.le hres0
    nlinarith [mul_le_mul_of_nonneg_left hb.2 hR.le]
  set s : ℝ := ⨆ p, f p with hsdef
  have hle_s : ∀ w : Z, ∀ b ∈ Icc (0 : ℝ) assetCap,
      P.consumptionFn w b - κ * P.resources (b, w) ≤ s :=
    fun w b hb => le_ciSup hbdd (⟨b, hb⟩, w)
  -- the Euler step at every state
  have hstate : ∀ w : Z, ∀ b ∈ Icc (0 : ℝ) assetCap,
      P.consumptionFn w b ≤ κ * P.resources (b, w) + (κ * P.maxIncome + s) / (1 + P.interest) := by
    intro w b hb
    set A : ℝ := P.policy (b, w) with hAdef
    have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region (b, w)
    set c : ℝ := P.consumptionFn w b with hcdef
    have hcA : c = P.resources (b, w) - A := rfl
    have hc0 : 0 < c := P.consumptionFn_pos hpc hb w
    have hc' : ∀ z' : Z, 0 < P.consumptionFn z' A := fun z' => P.consumptionFn_pos hpc hAmem z'
    have hroom : A < P.maxSaving (b, w) := by
      rw [maxSaving_eq]
      refine lt_min (hslack _ hb) ?_
      have := hc0
      rw [hcA] at this
      linarith
    have hbv := P.toExtended.bellman_valueFunction
    have hE := P.euler_le (v := P.toExtended.valueFunction) (z := w) (a := b) (A := A)
      (du := c ^ (-γ)) (du' := fun z' => (P.consumptionFn z' A) ^ (-γ))
      hb (by rw [hbv]; exact congrFun P.policyOf_valueFunction _) hroom
      (by rw [hbv]; exact hc0) (by rw [hbv, hu]; exact hasDerivAt_crraUtility γ hc0)
      hc' (fun z' => by rw [hu]; exact hasDerivAt_crraUtility γ (hc' z'))
    -- tomorrow's consumption is at most `κ(y_max + R A) + s`
    set Y : ℝ := κ * (P.maxIncome + (1 + P.interest) * A) + s with hYdef
    have hcY : ∀ z' : Z, P.consumptionFn z' A ≤ Y := by
      intro z'
      have h1 := hle_s z' A hAmem
      rw [P.resources_eq_of_mem hAmem z'] at h1
      have hinc := P.le_maxIncome z'
      rw [hYdef]
      nlinarith [hκ.le]
    have hY0 : 0 < Y := lt_of_lt_of_le (hc' Classical.ofNonempty) (hcY _)
    have hsum : Y ^ (-γ) ≤ ∑ z' : Z, P.transitionMatrix w z' * (P.consumptionFn z' A) ^ (-γ) := by
      calc Y ^ (-γ) = ∑ z' : Z, P.transitionMatrix w z' * Y ^ (-γ) := by
            rw [← Finset.sum_mul, P.transitionMatrix_sum w, one_mul]
        _ ≤ ∑ z' : Z, P.transitionMatrix w z' * (P.consumptionFn z' A) ^ (-γ) :=
            Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left
              (rpow_neg_antitone hγ0 (hc' z') (hcY z')) (P.transitionMatrix_nonneg w z')
    have hchain : (P.discount : ℝ) * (1 + P.interest) * Y ^ (-γ) ≤ c ^ (-γ) := by
      have := le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hR.le) hβ.le) hE
      linarith [this]
    have hYT : (Y / T) ^ (-γ) ≤ c ^ (-γ) := by
      rw [Real.div_rpow hY0.le hT0.le, hTneg, div_inv_eq_mul]
      nlinarith [hchain]
    have hcle : c ≤ Y / T := le_of_rpow_neg_le (div_pos hY0 hT0) hc0 hγ0 hYT
    have hTc : c * T ≤ Y := (le_div_iff₀ hT0).1 hcle
    -- `T c ≤ κ y_max + κ R (m - c) + s` and `T + κ R = R`
    rw [show κ * P.resources (b, w) + (κ * P.maxIncome + s) / (1 + P.interest)
        = (κ * P.resources (b, w) * (1 + P.interest) + (κ * P.maxIncome + s)) / (1 + P.interest)
        by field_simp, le_div_iff₀ hR]
    rw [hYdef, hcA] at hTc
    nlinarith [hTc, hkey]
  -- the supremum bounds itself
  have hs : s ≤ (κ * P.maxIncome + s) / (1 + P.interest) := by
    refine ciSup_le fun p => ?_
    have := hstate p.2 p.1 p.1.2
    show P.consumptionFn p.2 p.1 - κ * P.resources ((p.1 : ℝ), p.2) ≤ _
    linarith
  have hs' : s ≤ κ * P.maxIncome / P.interest := by
    rw [le_div_iff₀ hR] at hs
    rw [le_div_iff₀ hint]
    nlinarith [hs]
  have := hle_s z a ha
  linarith [hs']

/-- **The sandwich**: `κ m ≤ c ≤ κ m + κ y_max / r`. The lower bound needs the iterate
hypotheses of `crra_minMPC_mul_le_consumptionFn`; the upper bound needs only the fixed point. -/
theorem crra_consumption_sandwich {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hint : 0 < P.interest)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcap : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → P.policy s < assetCap)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    0 ≤ P.correction γ z a ∧ P.correction γ z a ≤ P.minMPC γ * P.maxIncome / P.interest := by
  unfold correction
  constructor
  · linarith [P.crra_minMPC_mul_le_consumptionFn hγ0 hu rfl hκ hβ hβR hpos hcap z ha]
  · linarith [P.crra_consumptionFn_le_of_minMPC hγ0 hu hκ hβ hβR hint hpc hslack z ha]

/-- **Asymptotic linearity** (Ma–Toda 2022) in the capped model: the consumption share of cash on
hand is within `κ y_max/(r m)` of `κ`, which vanishes as cash on hand grows. -/
theorem crra_abs_consumptionFn_div_sub_minMPC_le {γ : ℝ} (hγ0 : 0 < γ)
    (hu : P.u = crraUtility γ) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hint : 0 < P.interest)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcap : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → P.policy s < assetCap)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    |P.consumptionFn z a / P.resources (a, z) - P.minMPC γ|
      ≤ P.minMPC γ * P.maxIncome / (P.interest * P.resources (a, z)) := by
  have hm : 0 < P.resources (a, z) := P.assetFloor_lt_resources (a, z)
  have hm' : P.resources (a, z) ≠ 0 := hm.ne'
  obtain ⟨h0, h1⟩ := P.crra_consumption_sandwich hγ0 hu hκ hβ hβR hint hpos hcap hpc hslack z ha
  unfold correction at h0 h1
  have hK : 0 ≤ P.minMPC γ * P.maxIncome / P.interest :=
    div_nonneg (mul_nonneg hκ.le (le_trans P.minIncome_pos.le (P.minIncome_le_maxIncome)))
      hint.le
  rw [show P.minMPC γ * P.maxIncome / (P.interest * P.resources (a, z))
      = (P.minMPC γ * P.maxIncome / P.interest) / P.resources (a, z) by rw [div_div],
    abs_sub_le_iff]
  constructor
  · rw [show P.consumptionFn z a / P.resources (a, z) - P.minMPC γ
        = (P.consumptionFn z a - P.minMPC γ * P.resources (a, z)) / P.resources (a, z) by
        field_simp]
    exact div_le_div_of_nonneg_right h1 hm.le
  · rw [show P.minMPC γ - P.consumptionFn z a / P.resources (a, z)
        = -((P.consumptionFn z a - P.minMPC γ * P.resources (a, z)) / P.resources (a, z)) by
        field_simp; ring]
    exact le_trans (neg_nonpos.2 (div_nonneg h0 hm.le)) (div_nonneg hK hm.le)

end IncomeFluctuation

end LeanEconomics
