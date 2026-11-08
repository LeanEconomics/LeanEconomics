/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CRRAEuler

/-!
# Capital stays bounded away from zero

Milestone C3 of `CLAMP_PLAN.md`, after Cao (2020, Lemma 9, part 1). With CRRA marginal utility,
along every sequential equilibrium:

* **the aggregate inequality** (`aggregate_le`): integrating the household bound
  `consumption_le` over the distribution at node `h`, with the identities of `Aggregates.lean`,

      R_h K_h + w_h L_h − K_c ≤ (β π R_c)^{-1/γ} (R_c K_c + w_c L_c) + K_c (R_h + w_h ē / assetCap),

  where `K_c` is capital at the children of `h` and `R_c, w_c, L_c` are prices and labour at the
  child with the same aggregate shock;
* **the lower bound** (`capital_ge`): if capital at the root is at least `k`, and the prices
  satisfy the **condition** `hB` — whenever capital `K_h ≥ k` falls to `K_c < k`, the wage at
  `K_h` beats the return to saving at `K_c` —

      (β π R(z, K_c, L'))^{-1/γ} (R(z, K_c, L') k + w(z, K_c, L') L')
        < w(z, K_h, L) (L − k ē / assetCap) − k,

  then capital is at least `k` at every node. The aggregate inequality at a node where capital
  first drops below `k` contradicts the condition.

Everything is generic in the price functions; `CobbDouglas` instances of the condition are
milestone C4.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (U : M.SmoothUtility) (z₀ : Z) (μ₀ : Measure M.AState)
  [IsProbabilityMeasure μ₀] {γ : ℝ}

/-- **The aggregate inequality at a node.** -/
theorem aggregate_le (hγ : 0 < γ) (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ))
    {Kc : List Z → ℝ} (hK : M.IsSequentialEquilibrium z₀ μ₀ Kc) (hb : M.borrowLimit = 0)
    (hsl : M.Slack z₀ (M.pricePath z₀ (M.initMass μ₀) Kc)) {π : ℝ} (hπ : 0 < π)
    (hπle : ∀ z, π ≤ M.aggProb z z) (hRpos : ∀ z k L, 0 < M.grossReturn z k L) {ē : ℝ}
    (hē : ∀ e, M.efficiency e ≤ ē) (h : List Z) :
    M.returnAt z₀ (M.pricePath z₀ (M.initMass μ₀) Kc) h * Kc h
        + M.wageAt z₀ (M.pricePath z₀ (M.initMass μ₀) Kc) h * M.labour z₀ (M.initMass μ₀) h
        - Kc (shockAt z₀ h :: h)
      ≤ (M.discount * π
            * M.returnAt z₀ (M.pricePath z₀ (M.initMass μ₀) Kc) (shockAt z₀ h :: h)) ^ (-1 / γ)
          * (M.returnAt z₀ (M.pricePath z₀ (M.initMass μ₀) Kc) (shockAt z₀ h :: h)
              * Kc (shockAt z₀ h :: h)
            + M.wageAt z₀ (M.pricePath z₀ (M.initMass μ₀) Kc) (shockAt z₀ h :: h)
              * M.labour z₀ (M.initMass μ₀) (shockAt z₀ h :: h))
        + Kc (shockAt z₀ h :: h)
          * (M.returnAt z₀ (M.pricePath z₀ (M.initMass μ₀) Kc) h
            + M.wageAt z₀ (M.pricePath z₀ (M.initMass μ₀) Kc) h * ē / M.assetCap) := by
  set P := M.pricePath z₀ (M.initMass μ₀) Kc with hP
  set zs := shockAt z₀ h with hzs
  set μh := M.nodeDist z₀ μ₀ P h with hμh
  have : IsProbabilityMeasure μh := M.isProbabilityMeasure_nodeDist z₀ μ₀ P h
  set Rc := M.returnAt z₀ P (zs :: h) with hRc
  set ρ := (M.discount * π * Rc) ^ (-1 / γ) with hρ
  set B := M.returnAt z₀ P h * M.assetCap + M.wageAt z₀ P h * ē with hB
  have hcap := M.assetCap_pos
  -- pointwise bound
  have hpt : ∀ x, M.consumptionAt z₀ P h x
      ≤ ρ * (∑ e', M.nextProb z₀ h zs e' x * M.consumptionAt z₀ P (zs :: h) (M.nextA z₀ P h e' x))
        + M.savingAt z₀ P h x / M.assetCap * B := fun x =>
    consumption_le U z₀ P hγ hdu hsl (x.1, ⟨x.2.idio, h⟩) hπ (hπle _) (hRpos _ _ _) hē
  have hint1 : Integrable (fun x => M.consumptionAt z₀ P h x) μh :=
    (M.consumptionAt z₀ P h).integrable _
  have hintS : Integrable (fun x => ∑ e', M.nextProb z₀ h zs e' x
      * M.consumptionAt z₀ P (zs :: h) (M.nextA z₀ P h e' x)) μh :=
    integrable_finsetSum _ fun e' _ =>
      M.integrable_term z₀ P h zs μh (M.consumptionAt z₀ P (zs :: h)) e'
  have hintB : Integrable (fun x => M.savingAt z₀ P h x / M.assetCap * B) μh :=
    (((M.savingAt z₀ P h).integrable _).div_const _).mul_const _
  have hI := integral_mono hint1 ((hintS.const_mul ρ).add hintB) hpt
  simp only [Pi.add_apply] at hI
  rw [integral_add (hintS.const_mul ρ) hintB, integral_const_mul, integral_mul_const,
    integral_div] at hI
  -- the integrals
  have hchild : ∫ x, ∑ e', M.nextProb z₀ h zs e' x
      * M.consumptionAt z₀ P (zs :: h) (M.nextA z₀ P h e' x) ∂μh
      = ∫ x, M.consumptionAt z₀ P (zs :: h) x ∂(M.nodeDist z₀ μ₀ P (zs :: h)) :=
    (M.integral_pushNode z₀ P h zs μh (M.consumptionAt z₀ P (zs :: h))).symm
  have hsave : ∫ x, M.savingAt z₀ P h x ∂μh = Kc (zs :: h) := by
    rw [hK (zs :: h), M.meanCapital_cons z₀ P μ₀ zs h]
  rw [hchild, hsave, M.integral_consumptionAt_eq z₀ μ₀ hK h zs,
    M.integral_consumptionAt_eq z₀ μ₀ hK (zs :: h) zs, hb, mul_zero, mul_zero, sub_zero,
    sub_zero] at hI
  -- drop next period's saving at the child
  have hgc : 0 ≤ Kc (zs :: zs :: h) := by
    rw [hK (zs :: zs :: h)]
    exact (M.meanCapital_mem z₀ μ₀ P _).1
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (mul_nonneg (mul_nonneg M.discount_pos.le hπ.le)
    (hRpos _ _ _).le) _
  have hdrop := mul_le_mul_of_nonneg_left (show M.returnAt z₀ P (zs :: h) * Kc (zs :: h)
      + M.wageAt z₀ P (zs :: h) * M.labour z₀ (M.initMass μ₀) (zs :: h) - Kc (zs :: zs :: h)
      ≤ M.returnAt z₀ P (zs :: h) * Kc (zs :: h)
        + M.wageAt z₀ P (zs :: h) * M.labour z₀ (M.initMass μ₀) (zs :: h) by linarith) hρ0
  have hlast : Kc (zs :: h) / M.assetCap * B
      = Kc (zs :: h) * (M.returnAt z₀ P h + M.wageAt z₀ P h * ē / M.assetCap) := by
    rw [hB]
    field_simp
  linarith

/-- **Capital never falls below `k`** along a sequential equilibrium, if it starts at least `k`
and the prices satisfy the condition `hB`. -/
theorem capital_ge (hγ : 0 < γ) (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ))
    {Kc : List Z → ℝ} (hK : M.IsSequentialEquilibrium z₀ μ₀ Kc) (hb : M.borrowLimit = 0)
    (hsl : M.Slack z₀ (M.pricePath z₀ (M.initMass μ₀) Kc)) {π : ℝ} (hπ : 0 < π)
    (hπle : ∀ z, π ≤ M.aggProb z z) (hRpos : ∀ z k L, 0 < M.grossReturn z k L) {ē : ℝ}
    (hē : ∀ e, M.efficiency e ≤ ē) (hē0 : 0 ≤ ē) {Llo Lhi : ℝ}
    (hlab : ∀ h, M.labour z₀ (M.initMass μ₀) h ∈ Icc Llo Lhi) {k : ℝ}
    (hB : ∀ (z : Z) (Kh Kc' L L' : ℝ), k ≤ Kh → 0 ≤ Kc' → Kc' < k → L ∈ Icc Llo Lhi →
      L' ∈ Icc Llo Lhi →
      (M.discount * π * M.grossReturn z Kc' L') ^ (-1 / γ)
          * (M.grossReturn z Kc' L' * k + M.wage z Kc' L' * L')
        < M.wage z Kh L * (L - k * ē / M.assetCap) - k)
    (h0 : k ≤ Kc []) : ∀ h, k ≤ Kc h := by
  intro h
  induction h with
  | nil => exact h0
  | cons z' h ih =>
    set P := M.pricePath z₀ (M.initMass μ₀) Kc with hP
    set zs := shockAt z₀ h with hzs
    have hsame : Kc (z' :: h) = Kc (zs :: h) := by
      rw [hK (z' :: h), hK (zs :: h), M.meanCapital_cons z₀ P μ₀ z' h,
        M.meanCapital_cons z₀ P μ₀ zs h]
    rw [hsame]
    by_contra hlt
    rw [not_le] at hlt
    have hA := aggregate_le U z₀ μ₀ hγ hdu hK hb hsl hπ hπle hRpos hē h
    have hc0 : 0 ≤ Kc (zs :: h) := by
      rw [hK (zs :: h)]
      exact (M.meanCapital_mem z₀ μ₀ P _).1
    have hBh := hB zs (Kc h) (Kc (zs :: h)) (M.labour z₀ (M.initMass μ₀) h)
      (M.labour z₀ (M.initMass μ₀) (zs :: h)) ih hc0 hlt (hlab h) (hlab (zs :: h))
    -- prices along the path are the price functions at path capital and labour
    have eRh : M.returnAt z₀ P h = M.grossReturn zs (Kc h) (M.labour z₀ (M.initMass μ₀) h) := rfl
    have ewh : M.wageAt z₀ P h = M.wage zs (Kc h) (M.labour z₀ (M.initMass μ₀) h) := rfl
    have eRc : M.returnAt z₀ P (zs :: h)
        = M.grossReturn zs (Kc (zs :: h)) (M.labour z₀ (M.initMass μ₀) (zs :: h)) := rfl
    have ewc : M.wageAt z₀ P (zs :: h)
        = M.wage zs (Kc (zs :: h)) (M.labour z₀ (M.initMass μ₀) (zs :: h)) := rfl
    rw [eRh, ewh, eRc, ewc] at hA
    set Rh := M.grossReturn zs (Kc h) (M.labour z₀ (M.initMass μ₀) h)
    set wh := M.wage zs (Kc h) (M.labour z₀ (M.initMass μ₀) h)
    set Rc := M.grossReturn zs (Kc (zs :: h)) (M.labour z₀ (M.initMass μ₀) (zs :: h))
    set wc := M.wage zs (Kc (zs :: h)) (M.labour z₀ (M.initMass μ₀) (zs :: h))
    set Lh := M.labour z₀ (M.initMass μ₀) h
    set Lc := M.labour z₀ (M.initMass μ₀) (zs :: h)
    set Kh := Kc h
    set K1 := Kc (zs :: h)
    set ρ := (M.discount * π * Rc) ^ (-1 / γ)
    have hRh : 0 ≤ Rh := M.grossReturn_nonneg _ _ _
    have hwh : 0 ≤ wh := M.wage_nonneg _ _ _
    have hRc : 0 ≤ Rc := M.grossReturn_nonneg _ _ _
    have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (mul_nonneg (mul_nonneg M.discount_pos.le hπ.le) hRc) _
    have hcap := M.assetCap_pos
    -- the left side, less the cap term, is at least `w_h (L_h − k ē / cap) − k`
    have hL : wh * (Lh - k * ē / M.assetCap) - k
        ≤ Rh * Kh + wh * Lh - K1 - K1 * (Rh + wh * ē / M.assetCap) := by
      have h1 : 0 ≤ Rh * (Kh - K1) := mul_nonneg hRh (by linarith)
      have h2 : K1 * ē / M.assetCap ≤ k * ē / M.assetCap :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlt.le hē0) hcap.le
      have h3 : wh * (K1 * ē / M.assetCap) ≤ wh * (k * ē / M.assetCap) :=
        mul_le_mul_of_nonneg_left h2 hwh
      have e1 : Rh * Kh + wh * Lh - K1 - K1 * (Rh + wh * ē / M.assetCap)
          = Rh * (Kh - K1) + wh * Lh - wh * (K1 * ē / M.assetCap) - K1 := by ring
      have e2 : wh * (Lh - k * ē / M.assetCap) = wh * Lh - wh * (k * ē / M.assetCap) := by ring
      rw [e1, e2]
      linarith
    -- the right side is at most `ρ (R_c k + w_c L_c)`
    have hR : ρ * (Rc * K1 + wc * Lc) ≤ ρ * (Rc * k + wc * Lc) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hρ0
    linarith

end KSModel

end KrusellSmith

end LeanEconomics
