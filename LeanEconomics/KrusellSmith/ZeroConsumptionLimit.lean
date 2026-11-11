/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities

/-!
# The rental rate `δ α`: where aggregate consumption is zero

Walsh and Young (2025), *Equilibrium Multiplicity in Aiyagari and Krusell–Smith*, find
numerically that when an Aiyagari economy has several stationary equilibria the lowest rental rate
is close to `δ α` (depreciation times the capital share), and explain it by a zero-consumption
limit: if households consume nothing, stationary capital supply is `w L / (δ − r)`, which meets
capital demand at `r = δ α` and has a critical point there. This file records what is exact in
that explanation. It is accounting, with Cobb–Douglas production `K^α L^{1−α}` and the rental rate
`r = α K^{α−1} L^{1−α}` (depreciation paid by the household).

* **`netOutput_eq`**, **`netOutput_nonneg_iff`**, **`netOutput_eq_zero_iff`**: net output
  `K^α L^{1−α} − δ K` is `K (r / α − δ)`. So aggregate consumption is nonnegative iff `r ≥ δ α`
  and zero iff `r = δ α`: **`δ α` is the lowest rental rate any stationary allocation can have**,
  reached only when nothing is consumed.
* **`stationary_capital_eq`**: with `r < δ`, a stationary capital stock is
  `(w L − C) / (δ − r)`: the zero-consumption supply less capitalised consumption.
* **`zeroSupply_sub_demand`**, **`zeroSupply_eq_demand_iff`**: the zero-consumption supply meets
  demand on `(0, δ)` exactly at `r = δ α`, and lies above demand for `r > δ α`.
* **`zeroSupply_min`**: on `(0, δ)` the zero-consumption supply is smallest at `r = δ α`
  (weighted AM–GM).

None of this gives an equilibrium at or near `δ α`: equilibrium requires households' consumption
at the rental rate `r` to equal net output there, and at `δ α` net output is zero while
consumption is positive. Multiplicity needs bounds on household consumption on both sides, which
this accounting does not supply.
-/

namespace LeanEconomics

namespace KrusellSmith

namespace ZeroConsumption

variable {α δ L : ℝ}

/-- Capital demand at the rental rate `r`. -/
noncomputable def demand (α L r : ℝ) : ℝ := (α / r) ^ (1 / (1 - α)) * L

/-- The wage at the rental rate `r`. -/
noncomputable def wage (α r : ℝ) : ℝ := (1 - α) * (α / r) ^ (α / (1 - α))

/-- Stationary capital supply when households consume nothing. -/
noncomputable def zeroSupply (α δ L r : ℝ) : ℝ := wage α r * L / (δ - r)

/-- **Net output** at capital `K` is `K (r / α − δ)`, `r` the rental rate. -/
theorem netOutput_eq (hα : α ≠ 0) {K : ℝ} (hK : 0 < K) :
    K ^ α * L ^ (1 - α) - δ * K = K * (α * K ^ (α - 1) * L ^ (1 - α) / α - δ) := by
  rw [Real.rpow_sub_one hK.ne']
  field_simp

/-- **Aggregate consumption is nonnegative iff the rental rate is at least `δ α`.** -/
theorem netOutput_nonneg_iff (hα : 0 < α) {K : ℝ} (hK : 0 < K) :
    0 ≤ K ^ α * L ^ (1 - α) - δ * K ↔ δ * α ≤ α * K ^ (α - 1) * L ^ (1 - α) := by
  rw [netOutput_eq hα.ne' hK, mul_nonneg_iff_of_pos_left hK, sub_nonneg, le_div_iff₀ hα]

/-- **Aggregate consumption is zero iff the rental rate is `δ α`.** -/
theorem netOutput_eq_zero_iff (hα : 0 < α) {K : ℝ} (hK : 0 < K) :
    K ^ α * L ^ (1 - α) - δ * K = 0 ↔ α * K ^ (α - 1) * L ^ (1 - α) = δ * α := by
  rw [netOutput_eq hα.ne' hK, mul_eq_zero, or_iff_right hK.ne', sub_eq_zero,
    div_eq_iff hα.ne']

/-- **A stationary capital stock** is the zero-consumption supply less capitalised consumption:
if `K = w L + (1 + r − δ) K − C` and `r < δ`, then `K = (w L − C) / (δ − r)`. -/
theorem stationary_capital_eq {K w r C : ℝ} (hr : r < δ)
    (h : K = w * L + (1 + r - δ) * K - C) : K = (w * L - C) / (δ - r) := by
  rw [eq_div_iff (sub_pos.2 hr).ne']
  linarith

/-- The gap between the zero-consumption supply and demand. -/
theorem zeroSupply_sub_demand (hα1 : α < 1) {r : ℝ} (hα : 0 < α) (hr : 0 < r) (hrδ : r < δ) :
    zeroSupply α δ L r - demand α L r
      = (α / r) ^ (α / (1 - α)) * L * (r - δ * α) / (r * (δ - r)) := by
  have h1 : (0 : ℝ) < 1 - α := sub_pos.2 hα1
  have hx : 0 < α / r := div_pos hα hr
  have hexp : (α / r) ^ (1 / (1 - α)) = (α / r) ^ (α / (1 - α)) * (α / r) := by
    rw [show 1 / (1 - α) = α / (1 - α) + 1 by field_simp; ring, Real.rpow_add_one hx.ne']
  have hd := (sub_pos.2 hrδ).ne'
  rw [zeroSupply, demand, wage, hexp]
  field_simp
  ring

/-- **The zero-consumption supply lies above demand iff the rental rate exceeds `δ α`.** -/
theorem demand_le_zeroSupply_iff (hα : 0 < α) (hα1 : α < 1) (hL : 0 < L) {r : ℝ} (hr : 0 < r)
    (hrδ : r < δ) : demand α L r ≤ zeroSupply α δ L r ↔ δ * α ≤ r := by
  have hpos : 0 < (α / r) ^ (α / (1 - α)) * L :=
    mul_pos (Real.rpow_pos_of_pos (div_pos hα hr) _) hL
  rw [← sub_nonneg, zeroSupply_sub_demand hα1 hα hr hrδ,
    le_div_iff₀ (mul_pos hr (sub_pos.2 hrδ)), zero_mul, mul_nonneg_iff_of_pos_left hpos,
    sub_nonneg]

/-- **The zero-consumption supply meets demand exactly at `r = δ α`.** -/
theorem zeroSupply_eq_demand_iff (hα : 0 < α) (hα1 : α < 1) (hL : 0 < L) {r : ℝ} (hr : 0 < r)
    (hrδ : r < δ) : zeroSupply α δ L r = demand α L r ↔ r = δ * α := by
  have hpos : (α / r) ^ (α / (1 - α)) * L ≠ 0 :=
    (mul_pos (Real.rpow_pos_of_pos (div_pos hα hr) _) hL).ne'
  rw [← sub_eq_zero, zeroSupply_sub_demand hα1 hα hr hrδ,
    div_eq_zero_iff, or_iff_left (mul_pos hr (sub_pos.2 hrδ)).ne', mul_eq_zero,
    or_iff_right hpos, sub_eq_zero]

/-- Weighted AM–GM: `r^α (δ − r)^{1−α}` is largest at `r = δ α`. -/
theorem rpow_mul_rpow_le (hα : 0 < α) (hα1 : α < 1) {r : ℝ} (hr : 0 < r) (hrδ : r < δ) :
    r ^ α * (δ - r) ^ (1 - α) ≤ δ * (α ^ α * (1 - α) ^ (1 - α)) := by
  have h1 : (0 : ℝ) < 1 - α := sub_pos.2 hα1
  have hd : 0 < δ - r := sub_pos.2 hrδ
  have hAG := Real.geom_mean_le_arith_mean2_weighted hα.le h1.le (div_pos hr hα).le
    (div_pos hd h1).le (by ring : α + (1 - α) = 1)
  rw [Real.div_rpow hr.le hα.le, Real.div_rpow hd.le h1.le, mul_div_cancel₀ _ hα.ne',
    mul_div_cancel₀ _ h1.ne', div_mul_div_comm,
    div_le_iff₀ (mul_pos (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos h1 _))] at hAG
  linarith

/-- **The zero-consumption supply is smallest at `r = δ α`** on `(0, δ)`. -/
theorem zeroSupply_min (hα : 0 < α) (hα1 : α < 1) (hL : 0 < L) (hδ : 0 < δ) {r : ℝ}
    (hr : 0 < r) (hrδ : r < δ) : zeroSupply α δ L (δ * α) ≤ zeroSupply α δ L r := by
  have h1 : (0 : ℝ) < 1 - α := sub_pos.2 hα1
  have hd : 0 < δ - r := sub_pos.2 hrδ
  have hr0 : 0 < δ * α := mul_pos hδ hα
  have hd0 : 0 < δ - δ * α := by nlinarith
  -- the supply is a decreasing function of `r^α (δ − r)^{1−α}`
  have hform : ∀ ρ : ℝ, 0 < ρ → ρ < δ →
      zeroSupply α δ L ρ
        = (1 - α) * α ^ (α / (1 - α)) * L * (ρ ^ α * (δ - ρ) ^ (1 - α)) ^ (-(1 / (1 - α))) := by
    intro ρ hρ hρδ
    have hdρ : 0 < δ - ρ := sub_pos.2 hρδ
    have e1 : (ρ ^ α * (δ - ρ) ^ (1 - α)) ^ (-(1 / (1 - α)))
        = (ρ ^ (α / (1 - α)))⁻¹ * (δ - ρ)⁻¹ := by
      rw [Real.mul_rpow (Real.rpow_nonneg hρ.le _) (Real.rpow_nonneg hdρ.le _),
        ← Real.rpow_mul hρ.le, ← Real.rpow_mul hdρ.le,
        show α * -(1 / (1 - α)) = -(α / (1 - α)) by ring,
        show (1 - α) * -(1 / (1 - α)) = -1 by field_simp,
        Real.rpow_neg hρ.le, Real.rpow_neg_one]
    rw [e1, zeroSupply, wage, Real.div_rpow hα.le hρ.le]
    have := (Real.rpow_pos_of_pos hρ (α / (1 - α))).ne'
    field_simp
  rw [hform r hr hrδ, hform (δ * α) hr0 (by nlinarith)]
  have hmax : r ^ α * (δ - r) ^ (1 - α) ≤ (δ * α) ^ α * (δ - δ * α) ^ (1 - α) := by
    have hle := rpow_mul_rpow_le hα hα1 hr hrδ
    have heq : (δ * α) ^ α * (δ - δ * α) ^ (1 - α) = δ * (α ^ α * (1 - α) ^ (1 - α)) := by
      rw [show δ - δ * α = δ * (1 - α) by ring, Real.mul_rpow hδ.le hα.le,
        Real.mul_rpow hδ.le h1.le]
      have hδδ : δ ^ α * δ ^ (1 - α) = δ := by
        rw [← Real.rpow_add hδ, show α + (1 - α) = 1 by ring, Real.rpow_one]
      linear_combination (α ^ α * (1 - α) ^ (1 - α)) * hδδ
    rw [heq]
    exact hle
  have hpow : ((δ * α) ^ α * (δ - δ * α) ^ (1 - α)) ^ (-(1 / (1 - α)))
      ≤ (r ^ α * (δ - r) ^ (1 - α)) ^ (-(1 / (1 - α))) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hd _))
      hmax (by have := one_div_pos.2 h1; linarith)
  exact mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg h1.le (Real.rpow_nonneg hα.le _)) hL.le)

end ZeroConsumption

end KrusellSmith

end LeanEconomics
