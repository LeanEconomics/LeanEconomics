/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.RepAgentExpMap

/-!
# The aggregate order on cross-sections: how far it goes

Route 1 of `CROSS_SECTION_PLAN.md`: order saving rules by the capital paths they generate, and ask
whether the expectations map (`ExpectationsMap.lean`) reverses that order for heterogeneous
households, as it does from point masses (`expMap_antitone_dirac`).

* **`expMap_child_le`** (depth one, any cross-section): at the first children of the root a higher
  expected capital path gives lower realised capital. At the root both expectations face the same
  cross-section and the same prices, so every household has the same cash and saves less
  (`crra_policy_le_of_capital`).
* **`CobbDouglas.cash_le_of_ratio`** (the dispersion bound, deeper nodes): let realised capital
  fall from `A` to `A'`. A household whose assets fall from `a` to `a'` with
  `a' ≤ (A' / A)^{1 − α} a` has no more cash at `A'` than it had at `A`
  (`grossReturn_mul_ratio_le`: the return rises by at most the factor `(A / A')^{1 − α}`; the wage
  falls). The representative agent (`a = A`, `a' = A'`) and proportionally scaled cross-sections
  satisfy it.

The bound is what the induction below the root needs and does not have: it asks every household
to cut its assets proportionally at least `(1 − α)` times as much (in logs) as the aggregate. A
household that does not respond — at the asset cap, or with saving insensitive to expectations —
gains cash from the higher return and may then save more; with the rest of the cross-section at
the zero-saving corner, aggregate saving rises as capital falls. So the expectations map need not
reverse the aggregate order for heterogeneous households: the route stops at depth one.
-/

open MeasureTheory Set

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace CobbDouglas

variable (T : CobbDouglas Z)

/-- **The return rises by at most the factor `(A / A')^{1 − α}`** when capital falls from `A` to
`A'` (clamped capital). -/
theorem grossReturn_mul_ratio_le (z : Z) {A A' : ℝ} (h : A' ≤ A) (L : ℝ) :
    T.grossReturn z A' L * (T.clampCap A' / T.clampCap A) ^ (1 - T.share)
      ≤ T.grossReturn z A L := by
  have hc' := T.clampCap_pos A'
  have hc := T.clampCap_pos A
  have hcc := T.clampCap_mono h
  have hα : 0 ≤ 1 - T.share := by linarith [T.share_lt_one]
  have hr1 : (T.clampCap A' / T.clampCap A) ^ (1 - T.share) ≤ 1 :=
    Real.rpow_le_one (div_nonneg hc'.le hc.le) ((div_le_one hc).2 hcc) hα
  have key : T.clampCap A' ^ (T.share - 1) * (T.clampCap A' / T.clampCap A) ^ (1 - T.share)
      = T.clampCap A ^ (T.share - 1) := by
    rw [Real.div_rpow hc'.le hc.le, ← mul_div_assoc, ← Real.rpow_add hc',
      show T.share - 1 + (1 - T.share) = 0 by ring, Real.rpow_zero, one_div,
      ← Real.rpow_neg hc.le, neg_sub]
  have hδ : 0 ≤ 1 - T.depreciation := sub_nonneg.2 T.depreciation_le_one
  have e : (1 - T.depreciation
        + T.share * T.tfp z * T.clampCap A' ^ (T.share - 1) * T.clampLab L ^ (1 - T.share))
        * (T.clampCap A' / T.clampCap A) ^ (1 - T.share)
      = (1 - T.depreciation) * (T.clampCap A' / T.clampCap A) ^ (1 - T.share)
        + T.share * T.tfp z * (T.clampCap A' ^ (T.share - 1)
          * (T.clampCap A' / T.clampCap A) ^ (1 - T.share)) * T.clampLab L ^ (1 - T.share) := by
    ring
  simp only [grossReturn]
  rw [e, key]
  have := mul_le_of_le_one_right hδ hr1
  linarith

/-- **The dispersion bound**: when capital falls from `A` to `A'`, a household whose assets fall
by at least the factor `(A' / A)^{1 − α}` has no more cash. -/
theorem cash_le_of_ratio (z : Z) {A A' : ℝ} (h : A' ≤ A) (L : ℝ) {a a' e : ℝ} (ha : 0 ≤ a)
    (he : 0 ≤ e) (hr : a' ≤ (T.clampCap A' / T.clampCap A) ^ (1 - T.share) * a) :
    T.grossReturn z A' L * a' + T.wage z A' L * e
      ≤ T.grossReturn z A L * a + T.wage z A L * e := by
  have h1 : T.grossReturn z A' L * a'
      ≤ T.grossReturn z A' L * ((T.clampCap A' / T.clampCap A) ^ (1 - T.share) * a) :=
    mul_le_mul_of_nonneg_left hr (T.grossReturn_nonneg z A' L)
  have h2 := mul_le_mul_of_nonneg_right (T.grossReturn_mul_ratio_le z h L) ha
  have h3 := mul_le_mul_of_nonneg_right (T.wage_mono z h L) he
  nlinarith

end CobbDouglas

/-! ### Depth one: any cross-section -/

variable (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)

open Classical in
/-- **At the first children of the root, a higher expected capital path gives lower realised
capital**, from every initial cross-section: CRRA with `0 < γ ≤ 1`, Cobb–Douglas, floor and cap
slack along the Bellman iterates. -/
theorem expMap_child_le (hγ1 : γ ≤ 1)
    (hsl : ∀ (z : Z) (P : List Z → ℝ × ℝ) (n : ℕ), (crraModel V T hγ).SlackOf z P
      ((((crraModel V T hγ).household z P).bellman)^[n] 0))
    (hcap : ∀ (z : Z) (P : List Z → ℝ × ℝ) (n : ℕ) (s : (crraModel V T hγ).State),
      (crraModel V T hγ).policyOf z P ((((crraModel V T hγ).household z P).bellman)^[n] 0) s
        < (crraModel V T hγ).assetCap)
    (z₀ : Z) (μ₀ : Measure (crraModel V T hγ).AState) [IsProbabilityMeasure μ₀]
    {K K' : List Z → ℝ} (hKK : ∀ h, K h ≤ K' h) (z' : Z) :
    ∫ x, (crraModel V T hγ).assets x ∂((crraModel V T hγ).expDist z₀ μ₀ K' [z'])
      ≤ ∫ x, (crraModel V T hγ).assets x ∂((crraModel V T hγ).expDist z₀ μ₀ K [z']) := by
  have hQ : ∀ J : List Z → ℝ, (crraModel V T hγ).expDist z₀ μ₀ J [z']
      = (crraModel V T hγ).pushNode z₀
        (Function.update ((crraModel V T hγ).pricePath z₀ ((crraModel V T hγ).initMass μ₀) J) []
          (∫ x, (crraModel V T hγ).assets x ∂μ₀,
            (crraModel V T hγ).labour z₀ ((crraModel V T hγ).initMass μ₀) [])) [] z' μ₀ :=
    fun J => rfl
  rw [hQ K, hQ K', (crraModel V T hγ).integral_pushNode, (crraModel V T hγ).integral_pushNode]
  refine integral_mono (((crraModel V T hγ).expectedNext z₀ _ [] z' _).integrable _)
    (((crraModel V T hγ).expectedNext z₀ _ [] z' _).integrable _) fun x => ?_
  refine Finset.sum_le_sum fun e' _ => mul_le_mul_of_nonneg_left ?_
    ((crraModel V T hγ).nextProb_nonneg z₀ [] z' e' x)
  refine Subtype.coe_le_coe.2 (monotone_projIcc (crraModel V T hγ).assetCap_pos.le ?_)
  refine crra_policy_le_of_capital V T hγ hγ1 z₀ (fun g hg => ?_) (fun g hg => ?_)
    (hsl _ _) (hsl _ _) (hcap _ _) rfl (le_of_eq ?_)
  · rw [Function.update_of_ne hg, Function.update_of_ne hg]
    exact hKK g
  · rw [Function.update_of_ne hg, Function.update_of_ne hg]
    rfl
  · simp only [KSModel.cash, KSModel.returnAt, KSModel.wageAt, Function.update_self]

end KrusellSmith

end LeanEconomics
