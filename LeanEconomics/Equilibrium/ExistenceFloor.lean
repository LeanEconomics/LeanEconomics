/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.EulerVariance
import LeanEconomics.Models.ConsumptionSandwich
import LeanEconomics.Models.EulerCorner
import LeanEconomics.Analysis.PowerMean

/-!
# The existence floor from primitives

`EulerVariance` reduced the supply floor at `μ = 1` to a variance floor: if every household saving
at most `A₀` faces conditional variance of next period's marginal utility at least `v₀`, then
`K(μ) ≥ A₀ (1 - 2(1 - βR)‖u'(c)‖²/v₀)`. The variance floor is a gap in marginal utility between
two income states at tomorrow's assets, which needs an UPPER bound on consumption in a low-income
state and a LOWER bound on consumption in a high-income state, both at moderate wealth. This file
supplies both from primitives.

## The state-dependent sandwich

The upper sandwich `c ≤ κ m + κ y_max / r` of `ConsumptionSandwich` bounds tomorrow's income by
its maximum. Keeping the income state gives the sharper
`c(a, z) ≤ κ (m + H_z)` (`crra_consumptionFn_le_of_humanWealth`), where `H` is any nonnegative
super-solution of the human-wealth equation `∑ π(z,z') (y_{z'} + H_{z'}) ≤ R H_z`, so that
`H_z = E[∑_{t ≥ 1} R^{-t} y_t | z]` is the expected present value of future income. The proof is
the one-supremum argument with a constant shift and Jensen for the negative power
(`convexOn_rpow_of_neg`). For the worst income state `κ H_{z_min}` is well below `κ y_max / r`.

## The zero-wealth floor

The lower bound is a floor on consumption at zero wealth in a high-income state. From concavity
(Carroll–Kimball) and the sandwich, the consumption function has slope at least
`κ R - κ y_max / (r (cap - b))` on `[0, b]` (`secant_ge_of_concaveOn_Icc`,
`crra_consumptionFn_sub_ge`). At zero wealth the household either sits at the corner, consuming its
income, or saves `A = y_z - c`, and then the Euler inequality above the floor plus the slope bound
on tomorrow's consumption give an implicit lower bound on `c(0, z)`
(`crra_consumptionFn_zero_ge`): for every `t ≤ y_z`,

  `min t (Þ⁻¹ (∑ π(z,z') (f_{z'} + σ (y_z - t))^{-γ})^{-1/γ}) ≤ c(0, z)`

whenever `f ≤ c(0, ·)` and `σ` is the slope. Iterating from `f = y_min` (which holds by
`minIncome_le_consumptionFn_floor`) produces a floor at zero wealth in every income state that is
a fixed point of an explicit finite-dimensional operator on the primitives.

## The assembly

`condVar_ge_of_gap` turns an upper bound `U` on `c(A, z₁)` and a lower bound `L > U` on `c(A, z₂)`
into a variance floor, and `aggregateCapital_ge_of_gap` into the capital floor. The CRRA
instantiation `crra_aggregateCapital_ge_of_primitives` takes `U = κ (R A₀ + y_{z₁} + H_{z₁})` and
`L = f_{z₂}`: the whole floor rests on ONE primitive inequality,
`κ (R A₀ + y_{z₁} + H_{z₁}) < f_{z₂}`, together with positive transition probabilities into `z₁`
and `z₂` from every state. Numerically (Aiyagari's numbers, `WriteUpResults/numerics`) it
holds for the extreme pair up to `A₀ ≈ 12` mean
incomes at `μ = 1`, well above capital demand, but the transition probabilities into the extreme
states are tiny, so the floor is non-vacuous only for `βR` within about `10^{-27}` of one: an
existence argument for rates close enough to `λ`, not a quantitative one.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

/-- `c ↦ c ^ (-γ)` is continuous on the positive half-line. -/
theorem continuousOn_rpow_neg (γ : ℝ) : ContinuousOn (fun c : ℝ => c ^ (-γ)) (Ioi (0 : ℝ)) :=
  fun c hc => (Real.continuousAt_rpow_const c (-γ) (Or.inl (ne_of_gt hc))).continuousWithinAt

/-! ### A slope floor for a concave function on a bounded interval -/

/-- **Secants of a concave function on `[0, cap]` are bounded below by the secant to the cap.**
If the rise from `b` to the cap is at least `m (cap - b) - C`, then the slope on `[a, b]` is at
least `m - C / (cap - b)`. On an unbounded domain the loss `C / (cap - b)` disappears; on a
bounded one it is the price of the cap. -/
theorem secant_ge_of_concaveOn_Icc {g : ℝ → ℝ} {cap m C : ℝ}
    (hg : ConcaveOn ℝ (Icc (0 : ℝ) cap) g) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < cap)
    (hend : m * (cap - b) - C ≤ g cap - g b) :
    (m - C / (cap - b)) * (b - a) ≤ g b - g a := by
  rcases hab.lt_or_eq with hlt | rfl
  · have hcb : 0 < cap - b := by linarith
    have hba : 0 < b - a := by linarith
    have hsl := hg.slope_anti_adjacent (x := a) (y := b) (z := cap)
      ⟨ha, by linarith⟩ ⟨by linarith, le_rfl⟩ hlt hb
    have h1 : m - C / (cap - b) ≤ (g cap - g b) / (cap - b) := by
      rw [sub_div' hcb.ne', div_le_div_iff_of_pos_right hcb]
      linarith
    have h2 : m - C / (cap - b) ≤ (g b - g a) / (b - a) := h1.trans hsl
    rw [le_div_iff₀ hba] at h2
    exact h2
  · simp

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]

section Sandwich

variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **The state-dependent sandwich**: for any nonnegative super-solution `H` of the human-wealth
equation `∑ π(z,z') (y_{z'} + H_{z'}) ≤ R H_z`, consumption satisfies `c(a, z) ≤ κ (m + H_z)`.
With `H_z` the expected present value of future income given `z` this is Ma–Toda's bound with the
income state kept. -/
theorem crra_consumptionFn_le_of_humanWealth {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ)) (hint : 0 < P.interest)
    (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → P.policy s < assetCap)
    {H : Z → ℝ} (hH0 : ∀ z, 0 ≤ H z)
    (hH : ∀ z, ∑ z', P.transitionMatrix z z' * (P.income z' + H z') ≤ (1 + P.interest) * H z)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.consumptionFn z a ≤ P.minMPC γ * (P.resources (a, z) + H z) := by
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
  -- the state-adjusted correction over the compact region, and its supremum
  let f : (↥(Icc (0 : ℝ) assetCap) × Z) → ℝ := fun p =>
    P.consumptionFn p.2 p.1 - κ * (P.resources ((p.1 : ℝ), p.2) + H p.2)
  have : Nonempty (↥(Icc (0 : ℝ) assetCap) × Z) :=
    ⟨(⟨0, ⟨le_rfl, hcap0⟩⟩, Classical.ofNonempty)⟩
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨P.maxIncome + (1 + P.interest) * assetCap, ?_⟩
    rintro _ ⟨⟨⟨b, hb⟩, w⟩, rfl⟩
    change P.consumptionFn w b - κ * (P.resources (b, w) + H w) ≤ _
    have hpol : 0 ≤ P.policy (b, w) := (P.policy_mem_region (b, w)).1
    have hc : P.consumptionFn w b = P.resources (b, w) - P.policy (b, w) := rfl
    have hres := P.resources_eq_of_mem hb w
    have hinc := P.le_maxIncome w
    have hres0 : 0 ≤ P.resources (b, w) := (P.assetFloor_lt_resources (b, w)).le
    have : 0 ≤ κ * (P.resources (b, w) + H w) := mul_nonneg hκ.le (add_nonneg hres0 (hH0 w))
    nlinarith [mul_le_mul_of_nonneg_left hb.2 hR.le]
  set s : ℝ := ⨆ p, f p with hsdef
  have hle_s : ∀ w : Z, ∀ b ∈ Icc (0 : ℝ) assetCap,
      P.consumptionFn w b - κ * (P.resources (b, w) + H w) ≤ s :=
    fun w b hb => le_ciSup hbdd (⟨b, hb⟩, w)
  -- the Euler step at every state
  have hstate : ∀ w : Z, ∀ b ∈ Icc (0 : ℝ) assetCap,
      P.consumptionFn w b ≤ κ * (P.resources (b, w) + H w) + s / (1 + P.interest) := by
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
    -- tomorrow's consumption is at most `κ (y_{z'} + R A + H_{z'}) + s`, state by state
    have hcY : ∀ z' : Z, P.consumptionFn z' A
        ≤ κ * (P.income z' + (1 + P.interest) * A + H z') + s := by
      intro z'
      have h1 := hle_s z' A hAmem
      rw [P.resources_eq_of_mem hAmem z'] at h1
      linarith
    set Y : ℝ := ∑ z', P.transitionMatrix w z'
      * (κ * (P.income z' + (1 + P.interest) * A + H z') + s) with hYdef
    set Ec : ℝ := ∑ z', P.transitionMatrix w z' * P.consumptionFn z' A with hEcdef
    have hEc0 : 0 < Ec := by
      have := (convex_Ioi (0 : ℝ)).sum_mem (t := Finset.univ) (w := P.transitionMatrix w)
        (z := fun z' => P.consumptionFn z' A) (fun z' _ => P.transitionMatrix_nonneg w z')
        (P.transitionMatrix_sum w) (fun z' _ => hc' z')
      simpa [smul_eq_mul, hEcdef] using this
    have hEcY : Ec ≤ Y :=
      Finset.sum_le_sum fun z' _ =>
        mul_le_mul_of_nonneg_left (hcY z') (P.transitionMatrix_nonneg w z')
    have hY0 : 0 < Y := hEc0.trans_le hEcY
    -- Jensen for the negative power: `Ec^{-γ} ≤ ∑ π c'^{-γ}`
    have hJ : Ec ^ (-γ) ≤ ∑ z', P.transitionMatrix w z' * (P.consumptionFn z' A) ^ (-γ) := by
      have := (convexOn_rpow_of_neg (by linarith : -γ < 0)).map_sum_le (t := Finset.univ)
        (w := P.transitionMatrix w) (p := fun z' => P.consumptionFn z' A)
        (fun z' _ => P.transitionMatrix_nonneg w z') (P.transitionMatrix_sum w)
        (fun z' _ => hc' z')
      simpa [smul_eq_mul, hEcdef] using this
    have hYE : Y ^ (-γ) ≤ Ec ^ (-γ) := rpow_neg_antitone hγ0 hEc0 hEcY
    have hchain : (P.discount : ℝ) * (1 + P.interest) * Y ^ (-γ) ≤ c ^ (-γ) := by
      have := le_trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hYE.trans hJ) hR.le) hβ.le) hE
      linarith [this]
    have hYT : (Y / T) ^ (-γ) ≤ c ^ (-γ) := by
      rw [Real.div_rpow hY0.le hT0.le, hTneg, div_inv_eq_mul]
      nlinarith [hchain]
    have hcle : c ≤ Y / T := le_of_rpow_neg_le (div_pos hY0 hT0) hc0 hγ0 hYT
    have hTc : c * T ≤ Y := (le_div_iff₀ hT0).1 hcle
    -- `Y = κ ∑ π (y' + H') + κ R A + s ≤ κ R H_w + κ R A + s`
    have hY_eq : Y = ∑ z', κ * (P.transitionMatrix w z' * (P.income z' + H z'))
        + ∑ z', P.transitionMatrix w z' * (κ * (1 + P.interest) * A + s) := by
      rw [hYdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z' _ => by ring
    rw [← Finset.mul_sum, ← Finset.sum_mul, P.transitionMatrix_sum w, one_mul] at hY_eq
    have hYle : Y ≤ κ * ((1 + P.interest) * H w) + (κ * (1 + P.interest) * A + s) := by
      rw [hY_eq]
      have := mul_le_mul_of_nonneg_left (hH w) hκ.le
      linarith
    -- `T c ≤ κ R H + κ R (m - c) + s` and `T + κ R = R`
    rw [show κ * (P.resources (b, w) + H w) + s / (1 + P.interest)
        = (κ * (P.resources (b, w) + H w) * (1 + P.interest) + s) / (1 + P.interest)
        by field_simp, le_div_iff₀ hR]
    rw [hcA] at hTc
    nlinarith [hTc, hkey, hYle]
  -- the supremum bounds itself
  have hs : s ≤ s / (1 + P.interest) := by
    refine ciSup_le fun p => ?_
    have := hstate p.2 p.1 p.1.2
    change P.consumptionFn p.2 p.1 - κ * (P.resources ((p.1 : ℝ), p.2) + H p.2) ≤ _
    linarith
  have hs' : s ≤ 0 := by
    rw [le_div_iff₀ hR] at hs
    have hsr : s * P.interest ≤ 0 := by linarith
    by_contra h
    push Not at h
    linarith [mul_pos h hint]
  have := hle_s z a ha
  linarith [hs']

end Sandwich

/-! ### The slope floor and the zero-wealth floor -/

section Floor

variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **The consumption function has slope at least `κ R - κ y_max / (r (cap - b))` on `[0, b]`**,
from concavity, the lower sandwich at the cap and the upper sandwich at `b`. -/
theorem crra_consumptionFn_sub_ge {γ : ℝ}
    (hconc : ∀ z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap) (P.consumptionFn z))
    (hlow : ∀ z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      P.minMPC γ * P.resources (a, z) ≤ P.consumptionFn z a)
    (hup : ∀ z, ∀ a ∈ Icc (0 : ℝ) assetCap, P.consumptionFn z a
      ≤ P.minMPC γ * P.resources (a, z) + P.minMPC γ * P.maxIncome / P.interest)
    (z : Z) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < assetCap) :
    (P.minMPC γ * (1 + P.interest)
        - P.minMPC γ * P.maxIncome / P.interest / (assetCap - b)) * (b - a)
      ≤ P.consumptionFn z b - P.consumptionFn z a := by
  refine secant_ge_of_concaveOn_Icc (hconc z) ha hab hb ?_
  have hcapmem : assetCap ∈ Icc (0 : ℝ) assetCap := ⟨P.assetCap_nonneg, le_rfl⟩
  have hbmem : b ∈ Icc (0 : ℝ) assetCap := ⟨ha.trans hab, hb.le⟩
  have h1 := hlow z assetCap hcapmem
  have h2 := hup z b hbmem
  rw [P.resources_eq_of_mem hcapmem z] at h1
  rw [P.resources_eq_of_mem hbmem z] at h2
  linarith

/-- **The floor at zero wealth.** With `f` a floor on `c(0, ·)` and `σ ≥ 0` a slope floor on
`[0, y_max]`, for every `t ≤ y_z`,
`min t (Þ⁻¹ (∑ π(z,z') (f_{z'} + σ (y_z - t))^{-γ})^{-1/γ}) ≤ c(0, z)`: either the household sits
at the corner and consumes `y_z ≥ t`, or it consumes at least `t`, or it saves more than
`y_z - t` and the Euler inequality above the floor bounds its consumption below by tomorrow's. -/
theorem crra_consumptionFn_zero_ge {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → P.policy s < assetCap)
    {f : Z → ℝ} (hf0 : ∀ z, 0 < f z) (hf : ∀ z, f z ≤ P.consumptionFn z 0)
    {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hslope : ∀ z, ∀ A ∈ Icc (0 : ℝ) P.maxIncome,
      P.consumptionFn z 0 + σ * A ≤ P.consumptionFn z A)
    (z : Z) {t : ℝ} (ht : t ≤ P.income z) :
    min t (((P.discount : ℝ) * (1 + P.interest)) ^ (-(1 / γ))
      * (∑ z', P.transitionMatrix z z' * (f z' + σ * (P.income z - t)) ^ (-γ)) ^ (-(1 / γ)))
      ≤ P.consumptionFn z 0 := by
  classical
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) assetCap := ⟨le_rfl, hcap0⟩
  set c : ℝ := P.consumptionFn z 0 with hcdef
  set A : ℝ := P.policy (0, z) with hAdef
  have hcA : c = P.resources (0, z) - A := rfl
  have hres0 : P.resources (0, z) = P.income z := P.resources_zero rfl z
  have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region (0, z)
  have hc0 : 0 < c := P.consumptionFn_pos hpc h0mem z
  -- at the corner, consumption is income
  rcases eq_or_lt_of_le hAmem.1 with hA0 | hA0
  · have : c = P.income z := by rw [hcA, hres0, ← hA0, sub_zero]
    rw [this]
    exact (min_le_left _ _).trans ht
  -- or consumption is at least `t`
  rcases le_or_gt t c with htc | htc
  · exact (min_le_left _ _).trans htc
  -- or it saves more than `y_z - t`, and the Euler inequality bounds it below
  refine (min_le_right _ _).trans ?_
  have hAt : P.income z - t ≤ A := by
    have h := htc
    rw [hcA, hres0] at h
    linarith
  have hAy : A ≤ P.maxIncome := by
    have h1 := P.le_maxIncome z
    have h2 := hc0
    rw [hcA, hres0] at h2
    linarith
  have hc' : ∀ z' : Z, 0 < P.consumptionFn z' A := fun z' => P.consumptionFn_pos hpc hAmem z'
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt P.u (x ^ (-γ)) x := fun x hx => by
    rw [hu]; exact hasDerivAt_crraUtility γ hx
  have hbv := P.toExtended.bellman_valueFunction
  have hslackA : ∀ z' : Z, P.policyOf P.toExtended.valueFunction (A, z')
      < P.maxSaving (A, z') := by
    intro z'
    rw [P.policyOf_valueFunction, maxSaving_eq]
    refine lt_min (hslack _ hAmem) ?_
    have := hc' z'
    change 0 < P.resources (A, z') - P.policy (A, z') at this
    linarith
  have hE := P.euler_ge (v := P.toExtended.valueFunction) (z := z) (a := 0) (A := A)
    (du := c ^ (-γ)) (du' := fun z' => (P.consumptionFn z' A) ^ (-γ))
    h0mem (by rw [hbv]; exact congrFun P.policyOf_valueFunction _) hA0 hslackA
    (by rw [hbv]; exact hc0) (by rw [hbv]; exact hderiv _ hc0)
    (fun z' => hc' z') (fun z' => hderiv _ (hc' z'))
  -- tomorrow's consumption is at least `f_{z'} + σ (y_z - t)`
  set b : Z → ℝ := fun z' => f z' + σ * (P.income z - t) with hbdef
  have hb0 : ∀ z', 0 < b z' := fun z' => by
    have := hf0 z'
    have : 0 ≤ σ * (P.income z - t) := mul_nonneg hσ0 (by linarith)
    simp only [hbdef]; linarith
  have hbc : ∀ z', b z' ≤ P.consumptionFn z' A := fun z' => by
    have h1 := hslope z' A ⟨hAmem.1, hAy⟩
    have h2 := hf z'
    have h3 : σ * (P.income z - t) ≤ σ * A := mul_le_mul_of_nonneg_left hAt hσ0
    simp only [hbdef]; linarith
  set S : ℝ := ∑ z', P.transitionMatrix z z' * b z' ^ (-γ) with hSdef
  have hsum : ∑ z', P.transitionMatrix z z' * (P.consumptionFn z' A) ^ (-γ) ≤ S :=
    Finset.sum_le_sum fun z' _ =>
      mul_le_mul_of_nonneg_left (rpow_neg_antitone hγ0 (hb0 z') (hbc z'))
        (P.transitionMatrix_nonneg z z')
  have hS0 : 0 < S := by
    have hcγ : 0 < c ^ (-γ) := Real.rpow_pos_of_pos hc0 _
    have h1 : c ^ (-γ) ≤ (P.discount : ℝ) * ((1 + P.interest) * S) :=
      hE.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hR.le) hβ.le)
    by_contra hcon
    push Not at hcon
    have : (P.discount : ℝ) * ((1 + P.interest) * S) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hβ.le (mul_nonpos_of_nonneg_of_nonpos hR.le hcon)
    linarith
  -- `c^{-γ} ≤ βR S`, so `c ≥ (βR S)^{-1/γ}`
  have hcle : c ^ (-γ) ≤ (P.discount : ℝ) * (1 + P.interest) * S := by
    have := hE.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hR.le) hβ.le)
    linarith [this]
  have hγ' : (0 : ℝ) < 1 / γ := by positivity
  have h := rpow_neg_antitone hγ' (Real.rpow_pos_of_pos hc0 _) hcle
  rw [← Real.rpow_mul hc0.le, show -γ * -(1 / γ) = 1 by field_simp, Real.rpow_one,
    Real.mul_rpow hβR0.le hS0.le] at h
  exact h

omit [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z] in
/-- One step of the zero-wealth floor operator: the bound of `crra_consumptionFn_zero_ge` with
its free parameter chosen by `τ`. -/
noncomputable def zeroFloorStep (π : Z → Z → ℝ) (y : Z → ℝ) (βR γ σ : ℝ) (τ f : Z → ℝ) :
    Z → ℝ :=
  fun z => min (τ z)
    (βR ^ (-(1 / γ)) * (∑ z', π z z' * (f z' + σ * (y z - τ z)) ^ (-γ)) ^ (-(1 / γ)))

omit [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z] in
/-- The iterated zero-wealth floor, started from the constant `y₀`. -/
noncomputable def zeroFloorIter (π : Z → Z → ℝ) (y : Z → ℝ) (βR γ σ y₀ : ℝ) (τ : ℕ → Z → ℝ) :
    ℕ → Z → ℝ
  | 0 => fun _ => y₀
  | n + 1 => zeroFloorStep π y βR γ σ (τ n) (zeroFloorIter π y βR γ σ y₀ τ n)

/-- **Every iterate of the zero-wealth floor operator is a floor**, starting from `y_min`. -/
theorem zeroFloorIter_le {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → P.policy s < assetCap)
    {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hslope : ∀ z, ∀ A ∈ Icc (0 : ℝ) P.maxIncome,
      P.consumptionFn z 0 + σ * A ≤ P.consumptionFn z A)
    (hbase : ∀ z, P.minIncome ≤ P.consumptionFn z 0)
    (τ : ℕ → Z → ℝ) (hτ0 : ∀ k z, 0 < τ k z) (hτ : ∀ k z, τ k z ≤ P.income z) (n : ℕ) :
    (∀ z, 0 < zeroFloorIter P.transitionMatrix P.income ((P.discount : ℝ) * (1 + P.interest))
        γ σ P.minIncome τ n z)
      ∧ ∀ z, zeroFloorIter P.transitionMatrix P.income ((P.discount : ℝ) * (1 + P.interest))
        γ σ P.minIncome τ n z ≤ P.consumptionFn z 0 := by
  induction n with
  | zero => exact ⟨fun _ => P.minIncome_pos, hbase⟩
  | succ n ih =>
    refine ⟨fun z => ?_, fun z => ?_⟩
    · have hb : ∀ z', 0 < zeroFloorIter P.transitionMatrix P.income
          ((P.discount : ℝ) * (1 + P.interest)) γ σ P.minIncome τ n z'
          + σ * (P.income z - τ n z) := fun z' => by
        have h1 := ih.1 z'
        have h2 : 0 ≤ σ * (P.income z - τ n z) := mul_nonneg hσ0 (by linarith [hτ n z])
        linarith
      have hS := sum_rpow_pos (p := -γ) (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hb
      simp only [zeroFloorIter, zeroFloorStep]
      exact lt_min (hτ0 n z) (mul_pos
        (Real.rpow_pos_of_pos (mul_pos hβ P.interest_gt_neg_one) _) (Real.rpow_pos_of_pos hS _))
    · simp only [zeroFloorIter, zeroFloorStep]
      exact P.crra_consumptionFn_zero_ge hγ0 hu hβ hpc hslack ih.1 ih.2 hσ0 hslope z (hτ n z)

/-! ### Bounds at any wealth: the one-step lemmas of a certified iteration

The zero-wealth floor is the case `a = 0` of a general fact: a monotone lower bound `L` on the
consumption function, fed through the Euler inequality above the floor, gives a new lower bound
at every state; a monotone upper bound `U`, fed through the Euler inequality under the cap, gives
a new upper bound. Together with concavity of the true consumption function (which makes linear
interpolation of grid lower bounds valid) and monotonicity in wealth (which makes step upper
bounds valid), these two lemmas are all a certified two-sided time iteration needs. Numerically
(`WriteUpResults/numerics/twosided.m`, log utility, Rouwenhorst chain) fifty to a hundred
iterations from the primitive sub- and super-solutions bring the bounds within `0.003` (below)
and `0.02` (above) of the true consumption function on `[0, 6]`. -/

/-- **A lower bound propagates**: if `L` is a positive lower bound on consumption, monotone in
wealth, then for every `t ≤ m(a, z)`,
`min t (Þ⁻¹ (∑ π(z,z') L(m - t, z')^{-γ})^{-1/γ}) ≤ c(a, z)`. -/
theorem crra_consumptionFn_ge_of_lower {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → P.policy s < assetCap)
    {L : ℝ → Z → ℝ} (hLpos : ∀ z, ∀ a, 0 ≤ a → 0 < L a z)
    (hLmono : ∀ z, ∀ a b, 0 ≤ a → a ≤ b → L a z ≤ L b z)
    (hL : ∀ z, ∀ a ∈ Icc (0 : ℝ) assetCap, L a z ≤ P.consumptionFn z a)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) {t : ℝ} (ht : t ≤ P.resources (a, z)) :
    min t (((P.discount : ℝ) * (1 + P.interest)) ^ (-(1 / γ))
      * (∑ z', P.transitionMatrix z z' * (L (P.resources (a, z) - t) z') ^ (-γ)) ^ (-(1 / γ)))
      ≤ P.consumptionFn z a := by
  classical
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  set c : ℝ := P.consumptionFn z a with hcdef
  set A : ℝ := P.policy (a, z) with hAdef
  set m : ℝ := P.resources (a, z) with hmdef
  have hcA : c = m - A := rfl
  have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region (a, z)
  have hc0 : 0 < c := P.consumptionFn_pos hpc ha z
  rcases eq_or_lt_of_le hAmem.1 with hA0 | hA0
  · have : c = m := by rw [hcA, ← hA0, sub_zero]
    rw [this]
    exact (min_le_left _ _).trans ht
  rcases le_or_gt t c with htc | htc
  · exact (min_le_left _ _).trans htc
  refine (min_le_right _ _).trans ?_
  have hmt0 : 0 ≤ m - t := by linarith
  have hAt : m - t ≤ A := by rw [hcA] at htc; linarith
  have hc' : ∀ z' : Z, 0 < P.consumptionFn z' A := fun z' => P.consumptionFn_pos hpc hAmem z'
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt P.u (x ^ (-γ)) x := fun x hx => by
    rw [hu]; exact hasDerivAt_crraUtility γ hx
  have hbv := P.toExtended.bellman_valueFunction
  have hslackA : ∀ z' : Z, P.policyOf P.toExtended.valueFunction (A, z')
      < P.maxSaving (A, z') := by
    intro z'
    rw [P.policyOf_valueFunction, maxSaving_eq]
    refine lt_min (hslack _ hAmem) ?_
    have := hc' z'
    change 0 < P.resources (A, z') - P.policy (A, z') at this
    linarith
  have hE := P.euler_ge (v := P.toExtended.valueFunction) (z := z) (a := a) (A := A)
    (du := c ^ (-γ)) (du' := fun z' => (P.consumptionFn z' A) ^ (-γ))
    ha (by rw [hbv]; exact congrFun P.policyOf_valueFunction _) hA0 hslackA
    (by rw [hbv]; exact hc0) (by rw [hbv]; exact hderiv _ hc0)
    (fun z' => hc' z') (fun z' => hderiv _ (hc' z'))
  have hb0 : ∀ z', 0 < L (m - t) z' := fun z' => hLpos z' _ hmt0
  have hbc : ∀ z', L (m - t) z' ≤ P.consumptionFn z' A := fun z' =>
    (hLmono z' _ _ hmt0 hAt).trans (hL z' A hAmem)
  set S : ℝ := ∑ z', P.transitionMatrix z z' * (L (m - t) z') ^ (-γ) with hSdef
  have hsum : ∑ z', P.transitionMatrix z z' * (P.consumptionFn z' A) ^ (-γ) ≤ S :=
    Finset.sum_le_sum fun z' _ =>
      mul_le_mul_of_nonneg_left (rpow_neg_antitone hγ0 (hb0 z') (hbc z'))
        (P.transitionMatrix_nonneg z z')
  have hcle : c ^ (-γ) ≤ (P.discount : ℝ) * (1 + P.interest) * S := by
    have := hE.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hR.le) hβ.le)
    linarith [this]
  have hS0 : 0 < S := by
    have hcγ : 0 < c ^ (-γ) := Real.rpow_pos_of_pos hc0 _
    by_contra hcon
    push Not at hcon
    have : (P.discount : ℝ) * (1 + P.interest) * S ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hβR0.le hcon
    linarith
  have hγ' : (0 : ℝ) < 1 / γ := by positivity
  have h := rpow_neg_antitone hγ' (Real.rpow_pos_of_pos hc0 _) hcle
  rw [← Real.rpow_mul hc0.le, show -γ * -(1 / γ) = 1 by field_simp, Real.rpow_one,
    Real.mul_rpow hβR0.le hS0.le] at h
  exact h

/-- **An upper bound propagates**: if `U` is a positive upper bound on consumption, monotone in
wealth, and `t` satisfies `Þ⁻¹ (∑ π(z,z') U(m - t, z')^{-γ})^{-1/γ} ≤ t`, then
`c(a, z) ≤ t`. -/
theorem crra_consumptionFn_le_of_upper {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → P.policy s < assetCap)
    {U : ℝ → Z → ℝ} (hUpos : ∀ z, ∀ a, 0 ≤ a → 0 < U a z)
    (hUmono : ∀ z, ∀ a b, 0 ≤ a → a ≤ b → U a z ≤ U b z)
    (hU : ∀ z, ∀ a ∈ Icc (0 : ℝ) assetCap, P.consumptionFn z a ≤ U a z)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) {t : ℝ}
    (hcert : ((P.discount : ℝ) * (1 + P.interest)) ^ (-(1 / γ))
      * (∑ z', P.transitionMatrix z z' * (U (P.resources (a, z) - t) z') ^ (-γ)) ^ (-(1 / γ))
      ≤ t) :
    P.consumptionFn z a ≤ t := by
  classical
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  set c : ℝ := P.consumptionFn z a with hcdef
  set A : ℝ := P.policy (a, z) with hAdef
  set m : ℝ := P.resources (a, z) with hmdef
  have hcA : c = m - A := rfl
  have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region (a, z)
  have hc0 : 0 < c := P.consumptionFn_pos hpc ha z
  by_contra hcon
  push Not at hcon
  have hAt : A ≤ m - t := by rw [hcA] at hcon; linarith
  have hmt0 : 0 ≤ m - t := hAmem.1.trans hAt
  have hc' : ∀ z' : Z, 0 < P.consumptionFn z' A := fun z' => P.consumptionFn_pos hpc hAmem z'
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt P.u (x ^ (-γ)) x := fun x hx => by
    rw [hu]; exact hasDerivAt_crraUtility γ hx
  have hroom : A < P.maxSaving (a, z) := by
    rw [maxSaving_eq]
    refine lt_min (hslack _ ha) ?_
    have := hc0
    rw [hcA] at this
    linarith
  have hbv := P.toExtended.bellman_valueFunction
  have hE := P.euler_le (v := P.toExtended.valueFunction) (z := z) (a := a) (A := A)
    (du := c ^ (-γ)) (du' := fun z' => (P.consumptionFn z' A) ^ (-γ))
    ha (by rw [hbv]; exact congrFun P.policyOf_valueFunction _) hroom
    (by rw [hbv]; exact hc0) (by rw [hbv]; exact hderiv _ hc0)
    (fun z' => hc' z') (fun z' => hderiv _ (hc' z'))
  have hbc : ∀ z', P.consumptionFn z' A ≤ U (m - t) z' := fun z' =>
    (hU z' A hAmem).trans (hUmono z' _ _ hAmem.1 hAt)
  set S : ℝ := ∑ z', P.transitionMatrix z z' * (U (m - t) z') ^ (-γ) with hSdef
  have hsum : S ≤ ∑ z', P.transitionMatrix z z' * (P.consumptionFn z' A) ^ (-γ) :=
    Finset.sum_le_sum fun z' _ =>
      mul_le_mul_of_nonneg_left (rpow_neg_antitone hγ0 (hc' z') (hbc z'))
        (P.transitionMatrix_nonneg z z')
  have hS0 : 0 < S :=
    sum_rpow_pos (p := -γ) (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z)
      fun z' => hUpos z' _ hmt0
  have hchain : (P.discount : ℝ) * (1 + P.interest) * S ≤ c ^ (-γ) := by
    have := le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hR.le) hβ.le) hE
    linarith [this]
  -- so `c ≤ (βR S)^{-1/γ} ≤ t`
  have hγ' : (0 : ℝ) < 1 / γ := by positivity
  have h := rpow_neg_antitone hγ' (mul_pos hβR0 hS0) hchain
  rw [← Real.rpow_mul hc0.le, show -γ * -(1 / γ) = 1 by field_simp, Real.rpow_one,
    Real.mul_rpow hβR0.le hS0.le] at h
  linarith [h.trans hcert]

end Floor

/-! ### From a consumption gap to the capital floor -/

section Assembly

variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- A consumption floor bounds the marginal-utility function in norm. -/
theorem norm_marginalState_le_of_floor {du : ℝ → ℝ} (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption) (hanti : AntitoneOn du (Ioi (0 : ℝ)))
    (hdupos : ∀ c : ℝ, 0 < c → 0 ≤ du c) {cmin : ℝ} (hcmin : 0 < cmin)
    (hfloor : ∀ z, ∀ a ∈ Icc (0 : ℝ) assetCap, cmin ≤ P.consumptionFn z a) :
    ‖P.marginalState du hdu hpc‖ ≤ du cmin := by
  refine (norm_le (hdupos cmin hcmin)).2 fun s => ?_
  have hc : 0 < P.consumptionFn s.2 (s.1 : ℝ) := P.consumptionFn_pos hpc s.1.2 s.2
  rw [marginalState_apply, Real.norm_eq_abs, abs_of_nonneg (hdupos _ hc)]
  exact hanti hcmin hc (hfloor s.2 _ s.1.2)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **A consumption gap is a variance floor.** If tomorrow's consumption in state `z₁` is at most
`U` and in state `z₂` at least `L ≥ U`, the conditional variance of marginal utility is at least
`min(π₁, π₂)/2 · (u'(U) - u'(L))²`. -/
theorem condVar_ge_of_gap {du : ℝ → ℝ} (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hpc : P.PositiveConsumption)
    (s : P.State) (z₁ z₂ : Z) {U L : ℝ} (hU0 : 0 < U) (hUL : U ≤ L)
    (hU : P.consumptionFn z₁ (P.policy (P.incl s)) ≤ U)
    (hL : L ≤ P.consumptionFn z₂ (P.policy (P.incl s))) :
    min (P.transitionMatrix s.2 z₁) (P.transitionMatrix s.2 z₂) / 2 * (du U - du L) ^ 2
      ≤ P.condVar du hdu hpc s := by
  refine le_trans ?_ (P.condVar_ge_pair du hdu hpc s z₁ z₂)
  have hmem : (P.policy (P.incl s)) ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region _
  have hc₁ : 0 < P.consumptionFn z₁ (P.policy (P.incl s)) := P.consumptionFn_pos hpc hmem z₁
  have hc₂ : 0 < P.consumptionFn z₂ (P.policy (P.incl s)) := P.consumptionFn_pos hpc hmem z₂
  have hM₁ : P.marginalState du hdu hpc (P.nextState s z₁)
      = du (P.consumptionFn z₁ (P.policy (P.incl s))) := rfl
  have hM₂ : P.marginalState du hdu hpc (P.nextState s z₂)
      = du (P.consumptionFn z₂ (P.policy (P.incl s))) := rfl
  rw [hM₁, hM₂]
  have h1 : du U ≤ du (P.consumptionFn z₁ (P.policy (P.incl s))) :=
    hanti hc₁ hU0 hU
  have h2 : du (P.consumptionFn z₂ (P.policy (P.incl s))) ≤ du L :=
    hanti (hU0.trans_le hUL) hc₂ hL
  have h3 : du L ≤ du U := hanti hU0 (hU0.trans_le hUL) hUL
  have hsq : (du U - du L) ^ 2
      ≤ (du (P.consumptionFn z₁ (P.policy (P.incl s)))
        - du (P.consumptionFn z₂ (P.policy (P.incl s)))) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hπ : 0 ≤ min (P.transitionMatrix s.2 z₁) (P.transitionMatrix s.2 z₂) / 2 :=
    div_nonneg (le_min (P.transitionMatrix_nonneg _ _) (P.transitionMatrix_nonneg _ _)) two_pos.le
  change min (P.prob s z₁) (P.prob s z₂) / 2 * _ ≤ min (P.prob s z₁) (P.prob s z₂) / 2 * _
  exact mul_le_mul_of_nonneg_left hsq hπ

/-- **The capital floor from a consumption gap at low saving.** -/
theorem aggregateCapital_ge_of_gap {du : ℝ → ℝ} (hdu : ContinuousOn du (Ioi (0 : ℝ)))
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c) (hdupos : ∀ c : ℝ, 0 < c → 0 ≤ du c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hstrict : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → P.policy s < assetCap)
    (hβR0 : 0 < (P.discount : ℝ) * (1 + P.interest))
    (hβR : (P.discount : ℝ) * (1 + P.interest) ≤ 1)
    {A₀ : ℝ} (hA₀ : 0 ≤ A₀) (z₁ z₂ : Z) {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hp : ∀ z, p₀ ≤ min (P.transitionMatrix z z₁) (P.transitionMatrix z z₂))
    {U L : ℝ} (hU0 : 0 < U) (hUL : U < L)
    (hU : ∀ s : P.State, P.policyCoord s ≤ A₀ → P.consumptionFn z₁ (P.policy (P.incl s)) ≤ U)
    (hL : ∀ s : P.State, P.policyCoord s ≤ A₀ → L ≤ P.consumptionFn z₂ (P.policy (P.incl s)))
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    A₀ - A₀ / (p₀ / 2 * (du U - du L) ^ 2) * (2 * (1 - (P.discount : ℝ) * (1 + P.interest))
      * ‖P.marginalState du hdu hpc‖ ^ 2) ≤ P.aggregateCapital μ := by
  have hgap : 0 < du U - du L := by
    have := hstrict hU0 (hU0.trans hUL) hUL
    linarith
  have hv₀ : 0 < p₀ / 2 * (du U - du L) ^ 2 := by positivity
  refine P.aggregateCapital_ge_of_condVar hdu hderiv hdupos hpc hslack hβR0 hβR hA₀ hv₀ ?_ hμ
  intro s hs
  have h := P.condVar_ge_of_gap hdu hanti hpc s z₁ z₂ hU0 hUL.le (hU s hs) (hL s hs)
  refine le_trans ?_ h
  have := hp s.2
  have hsq : 0 ≤ (du U - du L) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right this hsq]

/-- **The CRRA floor from primitives.** With `H` a nonnegative super-solution of the human-wealth
equation, `f` a floor on consumption at zero wealth, and the ONE inequality
`κ (R A₀ + y_{z₁} + H_{z₁}) < f_{z₂}`, every stationary distribution has
`K(μ) ≥ A₀ - A₀ · 2(1 - βR)‖u'(c)‖² / v₀` with `v₀ = p₀/2 · (u'(U) - u'(L))²`. -/
theorem crra_aggregateCapital_ge_of_primitives {γ : ℝ} (hγ0 : 0 < γ)
    (hu : P.u = crraUtility γ) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hint : 0 < P.interest) (hβR : (P.discount : ℝ) * (1 + P.interest) ≤ 1)
    (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → P.policy s < assetCap)
    {H : Z → ℝ} (hH0 : ∀ z, 0 ≤ H z)
    (hH : ∀ z, ∑ z', P.transitionMatrix z z' * (P.income z' + H z') ≤ (1 + P.interest) * H z)
    {f : Z → ℝ} (hf : ∀ z, f z ≤ P.consumptionFn z 0)
    {A₀ : ℝ} (hA₀ : 0 ≤ A₀) (z₁ z₂ : Z) {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hp : ∀ z, p₀ ≤ min (P.transitionMatrix z z₁) (P.transitionMatrix z z₂))
    (hgap : P.minMPC γ * ((1 + P.interest) * A₀ + P.income z₁ + H z₁) < f z₂)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    A₀ - A₀ / (p₀ / 2 * ((P.minMPC γ * ((1 + P.interest) * A₀ + P.income z₁ + H z₁)) ^ (-γ)
        - (f z₂) ^ (-γ)) ^ 2)
      * (2 * (1 - (P.discount : ℝ) * (1 + P.interest))
        * ‖P.marginalState (fun c => c ^ (-γ)) (continuousOn_rpow_neg γ) hpc‖ ^ 2)
      ≤ P.aggregateCapital μ := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hU0 : 0 < P.minMPC γ * ((1 + P.interest) * A₀ + P.income z₁ + H z₁) := by
    have hy : 0 < P.income z₁ := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z₁)
    have := hH0 z₁
    have : 0 ≤ (1 + P.interest) * A₀ := mul_nonneg hR.le hA₀
    exact mul_pos hκ (by linarith)
  refine P.aggregateCapital_ge_of_gap (du := fun c => c ^ (-γ)) (continuousOn_rpow_neg γ)
    (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility γ hc)
    (fun c hc => (Real.rpow_pos_of_pos hc _).le)
    (fun x hx y hy hxy => rpow_neg_antitone hγ0 hx hxy)
    (fun x hx y hy hxy => by
      have := Real.rpow_lt_rpow (x := x) (y := y) (z := γ) hx.le hxy hγ0
      change y ^ (-γ) < x ^ (-γ)
      rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.trans hxy).le]
      exact inv_strictAnti₀ (Real.rpow_pos_of_pos hx _) this)
    hpc hslack hβR0 hβR hA₀ z₁ z₂ hp₀ hp hU0 hgap ?_ ?_ hμ
  · intro s hs
    have hmem : P.policy (P.incl s) ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region _
    have h := P.crra_consumptionFn_le_of_humanWealth hγ0 hu hκ hβ hint hpc hslack hH0 hH z₁ hmem
    rw [P.resources_eq_of_mem hmem z₁] at h
    have hs' : P.policy (P.incl s) ≤ A₀ := by simpa using hs
    have : P.minMPC γ * (P.income z₁ + (1 + P.interest) * P.policy (P.incl s) + H z₁)
        ≤ P.minMPC γ * ((1 + P.interest) * A₀ + P.income z₁ + H z₁) := by
      refine mul_le_mul_of_nonneg_left ?_ hκ.le
      linarith [mul_le_mul_of_nonneg_left hs' hR.le]
    linarith
  · intro s _
    have hmem : P.policy (P.incl s) ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region _
    exact (hf z₂).trans (P.consumptionFn_mono ⟨le_rfl, P.assetCap_nonneg⟩ hmem hmem.1)

end Assembly

end IncomeFluctuation

end LeanEconomics
