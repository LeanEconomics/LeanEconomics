/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Fixed points depend continuously on parameters

A family of contractions with a COMMON modulus has fixed points that move continuously with
the parameter. In economics this is what says households respond continuously to prices: the
value function is the fixed point of a Bellman operator that depends on the interest rate, and
comparative statics needs that dependence to be continuous before any market can be cleared.

The hypothesis is weak in a useful way. Continuity of `r ↦ T r v` is needed at ONE function
`v`, namely the fixed point at the parameter of interest -- not uniformly over `v`, and not
in any joint sense. The reason is the triangle inequality: the contraction absorbs all the
movement of the fixed point, leaving only the movement of the operator at a single point.

  dist (fix r) (fix r₀) ≤ K · dist (fix r) (fix r₀) + dist (T r (fix r₀)) (fix r₀)

so `(1 - K) · dist (fix r) (fix r₀) ≤ dist (T r (fix r₀)) (fix r₀)`, and the right side goes
to zero by hypothesis. This is the standard argument; the point of recording it here is that
Mathlib has the Banach fixed point theorem but not this parametric companion to it.
-/

open scoped NNReal
open Filter Topology

/-- **The fixed point of a contraction depends continuously on a parameter.** The family must
contract with a COMMON modulus `K < 1`; continuity of the operator is needed only at the
single function `fix r₀`. -/
theorem continuousAt_fixedPoint {R : Type*} [TopologicalSpace R] {V : Type*} [MetricSpace V]
    {K : ℝ≥0} {T : R → V → V} {fix : R → V} (hT : ∀ r, LipschitzWith K (T r)) (hK : K < 1)
    (hfix : ∀ r, T r (fix r) = fix r) {r₀ : R}
    (hcont : ContinuousAt (fun r => T r (fix r₀)) r₀) :
    ContinuousAt fix r₀ := by
  have hK1 : (K : ℝ) < 1 := by exact_mod_cast hK
  have hpos : 0 < 1 - (K : ℝ) := by linarith
  -- the contraction absorbs the movement of the fixed point
  have hbound : ∀ r, dist (fix r) (fix r₀) ≤ (1 - (K : ℝ))⁻¹ * dist (T r (fix r₀)) (fix r₀) := by
    intro r
    have htri : dist (fix r) (fix r₀)
        ≤ dist (T r (fix r)) (T r (fix r₀)) + dist (T r (fix r₀)) (fix r₀) := by
      calc dist (fix r) (fix r₀) = dist (T r (fix r)) (fix r₀) := by rw [hfix r]
        _ ≤ _ := dist_triangle _ _ _
    have hlip : dist (T r (fix r)) (T r (fix r₀)) ≤ (K : ℝ) * dist (fix r) (fix r₀) := by
      simpa [dist_edist] using (hT r).dist_le_mul (fix r) (fix r₀)
    rw [le_inv_mul_iff₀ hpos]
    nlinarith [htri, hlip, dist_nonneg (x := fix r) (y := fix r₀)]
  -- and the operator's own movement vanishes
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) hbound ?_
  have hd : ContinuousAt (fun r => dist (T r (fix r₀)) (fix r₀)) r₀ :=
    hcont.dist continuousAt_const
  have hd0 : dist (T r₀ (fix r₀)) (fix r₀) = 0 := by rw [hfix r₀, dist_self]
  have := (hd.tendsto).const_mul ((1 - (K : ℝ))⁻¹)
  rwa [hd0, mul_zero] at this

/-- The same statement for a family that is `ContractingWith` a common modulus. -/
theorem ContractingWith.continuousAt_fixedPoint {R : Type*} [TopologicalSpace R] {V : Type*}
    [MetricSpace V] {K : ℝ≥0} {T : R → V → V} {fix : R → V}
    (hT : ∀ r, ContractingWith K (T r)) (hfix : ∀ r, T r (fix r) = fix r) {r₀ : R}
    (hcont : ContinuousAt (fun r => T r (fix r₀)) r₀) :
    ContinuousAt fix r₀ :=
  _root_.continuousAt_fixedPoint (fun r => (hT r).2) (hT r₀).1 hfix hcont
