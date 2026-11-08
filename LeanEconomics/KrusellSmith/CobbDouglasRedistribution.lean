/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CobbDouglas

/-!
# Capital redistributes cash under Cobb–Douglas

Route R1 of `EXISTENCE_EXTENSIONS_PLAN.md` (item 6): is there an order on capital paths under which
saving rises with capital, as the greatest-equilibrium route to a minimal-state recursive
equilibrium needs? These identities say no.

With `R = 1 − δ + α A K^{α−1} L^{1−α}` and `w = (1 − α) A K^α L^{−α}`, cash on hand `R a + w e` of a
household with assets `a` and efficiency `e` moves with capital at the rate

  `R_K a + w_K e = α (1 − α) A K^{α−2} L^{−α} (K e − L a)` (`cash_deriv`):

a rise in capital raises the cash of households with `a / e < K / L` and lowers it for the others.
Over a cross-section with mean assets `K` and mean efficiency `L`, the change is zero
(`integral_redistribution_eq_zero`, Euler's theorem for constant returns): capital only
redistributes cash. So no order containing a one-node perturbation of capital makes every
household's saving monotone; and when saving is affine in cash with a common slope the
redistribution has no aggregate effect, leaving the future-price effects — lower returns and higher
wages — which both lower saving: the equilibrium map is order-reversing, not order-preserving.
-/

open MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

namespace CobbDouglasRedistribution

variable (A α δ : ℝ)

/-- The gross return of the Cobb–Douglas technology. -/
noncomputable def ret (K L : ℝ) : ℝ := 1 - δ + α * A * K ^ (α - 1) * L ^ (1 - α)

/-- The wage of the Cobb–Douglas technology. -/
noncomputable def wage (K L : ℝ) : ℝ := (1 - α) * A * K ^ α * L ^ (-α)

variable {K L : ℝ} (hK : 0 < K) (hL : 0 < L)
include hK

theorem hasDerivAt_ret :
    HasDerivAt (fun k => ret A α δ k L) (α * A * ((α - 1) * K ^ (α - 1 - 1)) * L ^ (1 - α)) K := by
  have h := (Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hK.ne')).const_mul (α * A)
  have h2 := (h.mul_const (L ^ (1 - α))).const_add (1 - δ)
  simpa [ret, mul_assoc] using h2

theorem hasDerivAt_wage :
    HasDerivAt (fun k => wage A α k L) ((1 - α) * A * (α * K ^ (α - 1)) * L ^ (-α)) K := by
  have h := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul ((1 - α) * A)
  simpa [wage, mul_assoc] using h.mul_const (L ^ (-α))

include hL in
/-- **Capital moves cash by the sign of `K e − L a`**: the derivative of cash on hand in capital is
`α (1 − α) A K^{α−2} L^{−α} (K e − L a)`. -/
theorem cash_deriv (a e : ℝ) :
    HasDerivAt (fun k => ret A α δ k L * a + wage A α k L * e)
      (α * (1 - α) * A * K ^ (α - 2) * L ^ (-α) * (K * e - L * a)) K := by
  have h := ((hasDerivAt_ret A α δ hK (L := L)).mul_const a).add
    ((hasDerivAt_wage A α hK (L := L)).mul_const e)
  convert h using 1
  have hK1 : K ^ (α - 1) = K * K ^ (α - 2) := by
    rw [show α - 1 = 1 + (α - 2) by ring, Real.rpow_add hK, Real.rpow_one]
  have hK2 : K ^ (α - 1 - 1) = K ^ (α - 2) := by ring_nf
  have hL1 : L ^ (1 - α) = L * L ^ (-α) := by
    rw [show 1 - α = 1 + -α by ring, Real.rpow_add hL, Real.rpow_one]
  rw [hK1, hK2, hL1]
  ring

omit hK in
/-- **Capital only redistributes cash**: over a cross-section with mean assets `K` and mean
efficiency `L`, the weights `K e − L a` of the cash change integrate to zero. -/
theorem integral_redistribution_eq_zero {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {a e : X → ℝ} (ha : Integrable a ν) (he : Integrable e ν)
    (hKa : ∫ x, a x ∂ν = K) (hLe : ∫ x, e x ∂ν = L) :
    ∫ x, (K * e x - L * a x) ∂ν = 0 := by
  rw [integral_sub (he.const_mul K) (ha.const_mul L), integral_const_mul, integral_const_mul, hKa,
    hLe]
  ring

end CobbDouglasRedistribution

end KrusellSmith

end LeanEconomics
