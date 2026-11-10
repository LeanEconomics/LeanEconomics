/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CobbDouglas
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Representative-agent cash rises with capital

Step (b) of milestone B2 (`EXISTENCE_EXTENSIONS_PLAN.md`), representative-agent case. When every
household holds the aggregate capital `A`, cash on hand at Cobb–Douglas prices of that capital,
`R(A) A + w(A) L`, rises with `A` — also through the clamps of the price box (`repCash_mono`).

Inside the box Euler's theorem makes it `(1 − δ) A + z A^α L^{1−α}`. In general, with
`k = clamp A`, `r = k^{α−1}`, `P = k^α`, the difference between two capital levels is
`(1 − δ)(A' − A) + z L^{1−α} [α r'(A' − A) + α (r' − r) A + (1 − α)(P' − P)]`, and the bracket is
nonnegative by the tangent line of `t ↦ t^α` (`rpow_le_tangent`) when `A ≤ k`, and trivially
when `A > k` (both capital levels are above the box, so prices coincide).
-/

namespace LeanEconomics

namespace KrusellSmith

/-- **The tangent line of `t ↦ t^α` lies above it**, for `0 ≤ α ≤ 1`. -/
theorem rpow_le_tangent {s t α : ℝ} (hs : 0 < s) (ht : 0 < t) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    s ^ α ≤ t ^ α + α * t ^ (α - 1) * (s - t) := by
  have hst := rpow_one_add_le_one_add_mul_self
    (show (-1 : ℝ) ≤ s / t - 1 by have := div_pos hs ht; linarith) h0 h1
  rw [show 1 + (s / t - 1) = s / t by ring, Real.div_rpow hs.le ht.le] at hst
  have htα : 0 < t ^ α := Real.rpow_pos_of_pos ht α
  rw [div_le_iff₀ htα] at hst
  rw [Real.rpow_sub_one ht.ne']
  calc s ^ α ≤ (1 + α * (s / t - 1)) * t ^ α := hst
    _ = t ^ α + α * (t ^ α / t) * (s - t) := by field_simp

/-- The algebra of `repCash_mono`. -/
theorem repCash_core {α δ m r r' P P' k k' A A' : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hδ : δ ≤ 1) (hm : 0 ≤ m) (hr' : 0 ≤ r') (hrr : r' ≤ r) (hP : P = r * k)
    (hP' : P' = r' * k') (hA : 0 ≤ A) (hAA : A ≤ A')
    (htan : P ≤ P' + α * r' * (k - k')) (hcase : A ≤ k ∨ (r = r' ∧ P = P')) :
    ((1 - δ) + α * m * r) * A + (1 - α) * m * P
      ≤ ((1 - δ) + α * m * r') * A' + (1 - α) * m * P' := by
  have hd := mul_nonneg (sub_nonneg.2 hδ) (sub_nonneg.2 hAA)
  rcases hcase with hAk | ⟨hr, hPP⟩
  · set inner := α * r' * (A' - A) + α * (r' - r) * A + (1 - α) * (P' - P) with hin
    have h1 : (r' - r) * k ≤ (r' - r) * A := mul_le_mul_of_nonpos_left hAk (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h1 hα0
    have h3 := mul_nonneg (mul_nonneg hα0 hr') (sub_nonneg.2 hAA)
    have hinner : 0 ≤ inner := by
      rw [hin, hP, hP'] at *
      rw [hP, hP'] at htan
      nlinarith
    have h4 := mul_nonneg hm hinner
    have e : ((1 - δ) + α * m * r') * A' + (1 - α) * m * P'
        - (((1 - δ) + α * m * r) * A + (1 - α) * m * P)
        = (1 - δ) * (A' - A) + m * inner := by
      rw [hin]
      ring
    linarith
  · subst hr hPP
    have := mul_nonneg (mul_nonneg (mul_nonneg hα0 hm) hr') (sub_nonneg.2 hAA)
    nlinarith

namespace CobbDouglas

variable {Z : Type*} (T : CobbDouglas Z)

theorem clampCap_le_clampCap {K K' : ℝ} (h : K ≤ K') : T.clampCap K ≤ T.clampCap K' :=
  max_le_max le_rfl (min_le_min le_rfl h)

/-- **Representative-agent cash rises with capital**: with labour inside its box, cash on hand
`R(A) A + w(A) L` at the Cobb–Douglas prices of capital `A` is nondecreasing in `A ≥ 0`. -/
theorem repCash_mono (z : Z) {L : ℝ} (hL : T.clampLab L = L) {A A' : ℝ} (hA : 0 ≤ A)
    (hAA : A ≤ A') :
    T.grossReturn z A L * A + T.wage z A L * L ≤ T.grossReturn z A' L * A' + T.wage z A' L * L := by
  set k := T.clampCap A with hkdef
  set k' := T.clampCap A' with hk'def
  have hk : 0 < k := T.clampCap_pos A
  have hk' : 0 < k' := T.clampCap_pos A'
  have hkk : k ≤ k' := T.clampCap_le_clampCap hAA
  have hLpos : 0 < L := hL ▸ T.clampLab_pos L
  have hα0 := T.share_pos
  have hα1 := T.share_lt_one
  set α := T.share
  set c := T.tfp z
  have hc : 0 < c := T.tfp_pos z
  set m := c * L ^ (1 - α) with hmdef
  have hm : 0 ≤ m := mul_nonneg hc.le (Real.rpow_nonneg hLpos.le _)
  -- `L^{-α} L = L^{1-α}`
  have hLL : L ^ (-α) * L = L ^ (1 - α) := by
    rw [show (1 : ℝ) - α = -α + 1 by ring, Real.rpow_add_one hLpos.ne']
  -- `k^{α-1} k = k^α`
  have hkα : ∀ x : ℝ, 0 < x → x ^ α = x ^ (α - 1) * x := fun x hx => by
    rw [Real.rpow_sub_one hx.ne']
    field_simp
  have hR : ∀ K : ℝ, T.grossReturn z K L
      = (1 - T.depreciation) + α * m * T.clampCap K ^ (α - 1) := fun K => by
    simp only [grossReturn, hL, hmdef]
    ring
  have hw : ∀ K : ℝ, T.wage z K L * L = (1 - α) * m * T.clampCap K ^ α := fun K => by
    simp only [wage, hL, hmdef, ← hLL]
    ring
  rw [hR A, hR A', hw A, hw A']
  refine repCash_core hα0.le hα1.le T.depreciation_le_one hm (Real.rpow_nonneg hk'.le _)
    (Real.rpow_le_rpow_of_nonpos hk hkk (by linarith)) (hkα k hk) (hkα k' hk') hA hAA
    (rpow_le_tangent hk hk' hα0.le hα1.le) ?_
  rcases le_or_gt A k with h | h
  · exact Or.inl h
  · right
    -- above the box: both clamp to `capHi`
    have hkhi : k = T.capHi := by
      have hmin : min T.capHi A = T.capHi := by
        by_contra hne
        have hmA : min T.capHi A = A := (min_choice T.capHi A).resolve_left hne
        have hk2 : k = max T.capLo A := by rw [hkdef, clampCap, hmA]
        have : A ≤ k := hk2 ▸ le_max_right _ _
        linarith
      rw [hkdef, clampCap, hmin, max_eq_right T.capLo_le]
    have hk'hi : k' = T.capHi := le_antisymm (T.clampCap_mem A').2 (hkhi ▸ hkk)
    have e1 : T.clampCap A = T.capHi := hkhi
    have e2 : T.clampCap A' = T.capHi := hk'hi
    rw [e1, e2]
    exact ⟨rfl, rfl⟩

end CobbDouglas

end KrusellSmith

end LeanEconomics
