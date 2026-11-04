/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The endogenous-gridpoint transfer, for an affine budget

The derivative-free step of Carroll and Kimball (1996) that turns concavity of the consumption
paired with END-OF-PERIOD ASSETS into concavity of the consumption function, stated for any
budget line `α + β a = g a + h a` (cash on hand affine in assets, saving `g`, consumption `h`).
It was first proved for the income-fluctuation problem
(`IncomeFluctuation.concaveOn_of_egm`, `IncomeFluctuation.concaveOn_of_egm_corner`), which are
now corollaries; the Krusell–Smith household uses it node by node, with cash on hand
`R_h a + w_h e`.

* `concaveOn_of_egm_affine`: if `C` is concave, `A + C A` strictly increasing, consumption is at
  most `C` of saving everywhere and equal to it wherever saving is above the borrowing limit
  `lo`, then consumption is concave in assets. At the limit the saving is the minimum, below any
  average of savings, which is all the transfer needs there.
-/

open Set

namespace LeanEconomics

/-- **The endogenous-gridpoint transfer, with the corner, for an affine budget.** -/
theorem concaveOn_of_egm_affine {lo hi α β : ℝ} {g C h : ℝ → ℝ}
    (hC : ConcaveOn ℝ (Icc lo hi) C)
    (hM : StrictMonoOn (fun A => A + C A) (Icc lo hi))
    (hg : ∀ a ∈ Icc lo hi, g a ∈ Icc lo hi)
    (hbud : ∀ a ∈ Icc lo hi, α + β * a = g a + h a)
    (hle : ∀ a ∈ Icc lo hi, h a ≤ C (g a))
    (heq : ∀ a ∈ Icc lo hi, lo < g a → h a = C (g a)) :
    ConcaveOn ℝ (Icc lo hi) h := by
  refine ⟨convex_Icc _ _, fun a ha b hb θ φ hθ hφ hθφ => ?_⟩
  simp only [smul_eq_mul]
  have hm : θ * a + φ * b ∈ Icc lo hi := by
    simpa only [smul_eq_mul] using convex_Icc lo hi ha hb hθ hφ hθφ
  have hA₁ := hg a ha
  have hA₂ := hg b hb
  have hAθ := hg _ hm
  have hAm : θ * g a + φ * g b ∈ Icc lo hi := by
    simpa only [smul_eq_mul] using convex_Icc lo hi hA₁ hA₂ hθ hφ hθφ
  have h1 := hbud a ha
  have h2 := hbud b hb
  have h3 := hbud _ hm
  have hcomb : α + β * (θ * a + φ * b)
      = (θ * g a + φ * g b) + (θ * h a + φ * h b) := by
    linear_combination θ * h1 + φ * h2 - α * hθφ
  have hAle : g (θ * a + φ * b) ≤ θ * g a + φ * g b := by
    rcases eq_or_lt_of_le hAθ.1 with hcorner | hinterior
    · rw [← hcorner]
      have hsum : θ * lo + φ * lo = lo := by
        rw [← add_mul, hθφ, one_mul]
      linarith [mul_nonneg hθ (sub_nonneg.mpr hA₁.1), mul_nonneg hφ (sub_nonneg.mpr hA₂.1)]
    · have hCc : θ * h a + φ * h b ≤ C (θ * g a + φ * g b) := by
        have hca := hle a ha
        have hcb := hle b hb
        have hmid := hC.2 hA₁ hA₂ hθ hφ hθφ
        simp only [smul_eq_mul] at hmid
        nlinarith [mul_le_mul_of_nonneg_left hca hθ, mul_le_mul_of_nonneg_left hcb hφ]
      have hstep : g (θ * a + φ * b) + C (g (θ * a + φ * b))
          ≤ (θ * g a + φ * g b) + C (θ * g a + φ * g b) := by
        rw [← heq _ hm hinterior, ← h3, hcomb]; linarith
      by_contra hcon
      exact absurd (hM hAm hAθ (not_le.mp hcon)) (not_lt.mpr hstep)
  have hval : h (θ * a + φ * b)
      = (θ * g a + φ * g b) + (θ * h a + φ * h b) - g (θ * a + φ * b) := by
    rw [← hcomb, h3]; ring
  rw [hval]
  linarith

/-- **The endogenous-gridpoint transfer, interior form**: consumption is `C` of saving
everywhere. -/
theorem concaveOn_of_egm_affine_interior {lo hi α β : ℝ} {g C h : ℝ → ℝ}
    (hC : ConcaveOn ℝ (Icc lo hi) C)
    (hM : StrictMonoOn (fun A => A + C A) (Icc lo hi))
    (hg : ∀ a ∈ Icc lo hi, g a ∈ Icc lo hi)
    (hbud : ∀ a ∈ Icc lo hi, α + β * a = g a + C (g a))
    (hh : ∀ a ∈ Icc lo hi, h a = C (g a)) :
    ConcaveOn ℝ (Icc lo hi) h :=
  concaveOn_of_egm_affine hC hM hg (fun a ha => by rw [hbud a ha, hh a ha])
    (fun a ha => (hh a ha).le) (fun a ha _ => hh a ha)

end LeanEconomics
