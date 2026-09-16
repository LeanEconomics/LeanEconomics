/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.PositiveCapital
import LeanEconomics.Distribution.UniquenessTop

/-!
# The reverse corner: when the asset cap binds

`policy_eq_zero_of_corner_at` says the borrowing constraint binds where resources are small.
This is the mirror: the ASSET CAP binds where resources are large, so the household saves the
maximum. It is what `UniquenessTop` needs, and it is the last piece of the patient-region
argument.

## The comparison

Saving the maximum beats saving `x < assetCap` when the continuation's gain covers the utility
lost. The utility loss is bounded above by concavity of `log`,

  `log (m - x) - log (m - cap) = log (1 + (cap - x)/(m - cap)) ≤ (cap - x)/(m - cap)`,

LINEAR in `cap - x`, which is what makes a single condition cover every `x`. The continuation's
gain is bounded below by `log_cont_sub_ge_gen`, but that is logarithmic, not linear — and the fix
is `log_scale_le`: on `[0, T]` the logarithm is at least its chord, `log (1 + t) ≥ (t/T) log (1+T)`,
which is concavity of `log` again, used in the other direction.

Dividing out `cap - x` leaves a condition on the state's resources alone, and `assetCap` enters it
through `T₀ = (1+r)·assetCap / income z₀`. Note where it bites: the condition is EASIER when the
cap is small relative to income, which is the opposite regime from the borrowing-constraint
corner, exactly as it should be.
-/

open Set Filter Topology

namespace LeanEconomics

/-- **The logarithm dominates its chord.** On `[0, T]`, `log (1 + t) ≥ (t/T) log (1 + T)` — the
linear lower bound the corner argument needs. -/
theorem log_scale_le {t T : ℝ} (hT : 0 < T) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    t / T * Real.log (1 + T) ≤ Real.log (1 + t) := by
  have hθ0 : (0 : ℝ) ≤ t / T := by positivity
  have hθ1 : t / T ≤ 1 := by rw [div_le_one hT]; exact htT
  have hcomb : t / T * (1 + T) + (1 - t / T) * 1 = 1 + t := by field_simp; ring
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) + T ∈ Ioi 0 by simp only [mem_Ioi]; linarith)
    (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (0 : ℝ) ≤ t / T from hθ0)
    (show (0 : ℝ) ≤ 1 - t / T by linarith)
    (show t / T + (1 - t / T) = 1 by ring)
  simp only [smul_eq_mul] at h
  rw [hcomb] at h
  simpa using h

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z assetCap)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The asset cap binds where resources are large.** The household saves the maximum. -/
theorem policy_eq_assetCap_of_corner (hpc : P.PositiveConsumption) (hu : P.u = Real.log)
    {s : ℝ × Z}
    (hs : s.1 ∈ Icc 0 assetCap) (hcap : 0 < assetCap) (hres : assetCap < P.resources s) (z₀ : Z)
    (hcond : 1 / (P.resources s - assetCap)
      ≤ P.discount * (P.transitionMatrix s.2 z₀ * (P.income z₀
          * Real.log (1 + (1 + P.interest) * assetCap / P.income z₀)
          / (assetCap * (P.income z₀ + (1 + P.interest) * assetCap))))) :
    P.policy s = assetCap := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hy₀ : 0 < P.income z₀ := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z₀)
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hmc : P.maxSaving s = assetCap := by
    rw [P.maxSaving_eq]; exact min_eq_left hres.le
  have hmem : assetCap ∈ P.toExtended.feasible s := by
    rw [P.feasible_eq, hmc]; exact ⟨hcap.le, le_rfl⟩
  have hcpos : 0 < P.consumption s assetCap := by
    simp only [consumption]; linarith
  set T₀ : ℝ := (1 + P.interest) * assetCap / P.income z₀ with hT₀def
  have hT₀ : 0 < T₀ := by rw [hT₀def]; positivity
  have hlogT₀ : 0 ≤ Real.log (1 + T₀) := Real.log_nonneg (by linarith)
  -- saving the maximum beats every alternative
  have hmain : ∀ x ∈ P.toExtended.feasible s, P.objR s x ≤ P.objR s assetCap := by
    intro x hx
    rw [P.feasible_eq, hmc] at hx
    rcases eq_or_lt_of_le hx.2 with rfl | hlt
    · exact le_rfl
    set Δ : ℝ := assetCap - x with hΔdef
    have hΔ : 0 < Δ := by rw [hΔdef]; linarith
    have hxmem : x ∈ Icc (0 : ℝ) assetCap := ⟨hx.1, hlt.le⟩
    have hcapmem : assetCap ∈ Icc (0 : ℝ) assetCap := ⟨hcap.le, le_rfl⟩
    -- the utility loss, bounded above by concavity of log
    have hml : 0 < P.resources s - assetCap := by linarith
    have hratio : P.consumption s x / P.consumption s assetCap
        = 1 + Δ / (P.resources s - assetCap) := by
      simp only [consumption, hΔdef]
      field_simp
      ring
    have hloss : P.u (P.consumption s x) - P.u (P.consumption s assetCap)
        ≤ Δ / (P.resources s - assetCap) := by
      rw [hu]
      have hcx : 0 < P.consumption s x := by simp only [consumption]; linarith
      rw [← Real.log_div hcx.ne' hcpos.ne', hratio]
      have := Real.log_le_sub_one_of_pos (x := 1 + Δ / (P.resources s - assetCap))
        (by positivity)
      linarith
    -- the continuation gain, bounded below by its chord
    have hgen := P.log_cont_sub_ge_gen hpc hu s.2 z₀ hxmem hcapmem hlt.le
    set t : ℝ := (1 + P.interest) * (assetCap - x) / (P.income z₀ + (1 + P.interest) * x)
      with htdef
    have hden : 0 < P.income z₀ + (1 + P.interest) * x := by nlinarith [hx.1]
    have hdencap : 0 < P.income z₀ + (1 + P.interest) * assetCap := by nlinarith [hcap]
    have ht0 : 0 ≤ t := by rw [htdef]; positivity
    have htT : t ≤ T₀ := by
      rw [htdef, hT₀def, div_le_div_iff₀ hden hy₀]
      nlinarith [mul_nonneg (mul_nonneg hR.le hx.1) hdencap.le, hx.1, hR, hy₀, hcap]
    have hchord := log_scale_le hT₀ ht0 htT
    have hTratio_eq : t / T₀
        = Δ * P.income z₀ / (assetCap * (P.income z₀ + (1 + P.interest) * x)) := by
      rw [htdef, hT₀def, hΔdef]
      field_simp
    have htratio : Δ * P.income z₀
        / (assetCap * (P.income z₀ + (1 + P.interest) * assetCap)) ≤ t / T₀ := by
      rw [hTratio_eq]
      gcongr
    have hstep1 : Δ * P.income z₀
        / (assetCap * (P.income z₀ + (1 + P.interest) * assetCap)) * Real.log (1 + T₀)
        ≤ Real.log (1 + t) :=
      le_trans (mul_le_mul_of_nonneg_right htratio hlogT₀) hchord
    have hstep2 : P.transitionMatrix s.2 z₀ * (Δ * P.income z₀
        / (assetCap * (P.income z₀ + (1 + P.interest) * assetCap)) * Real.log (1 + T₀))
        ≤ P.cont s.2 assetCap - P.cont s.2 x :=
      le_trans (mul_le_mul_of_nonneg_left hstep1 (P.transitionMatrix_nonneg s.2 z₀)) hgen
    -- the condition, scaled by the gap
    have hcondΔ : Δ / (P.resources s - assetCap)
        ≤ (P.discount : ℝ) * (P.transitionMatrix s.2 z₀ * (Δ * P.income z₀
            / (assetCap * (P.income z₀ + (1 + P.interest) * assetCap)) * Real.log (1 + T₀))) := by
      have h := mul_le_mul_of_nonneg_left hcond hΔ.le
      have e1 : Δ * (1 / (P.resources s - assetCap)) = Δ / (P.resources s - assetCap) := by ring
      have e2 : Δ * ((P.discount : ℝ) * (P.transitionMatrix s.2 z₀ * (P.income z₀
            * Real.log (1 + T₀) / (assetCap * (P.income z₀ + (1 + P.interest) * assetCap)))))
          = (P.discount : ℝ) * (P.transitionMatrix s.2 z₀ * (Δ * P.income z₀
            / (assetCap * (P.income z₀ + (1 + P.interest) * assetCap)) * Real.log (1 + T₀))) := by
        ring
      rw [e1, e2] at h
      exact h
    have hscaled := mul_le_mul_of_nonneg_left hstep2 hβ
    have hdist : (P.discount : ℝ) * (P.cont s.2 assetCap - P.cont s.2 x)
        = (P.discount : ℝ) * P.cont s.2 assetCap - (P.discount : ℝ) * P.cont s.2 x := by ring
    simp only [objR]
    linarith [hloss, hcondΔ, hscaled, hdist.le, hdist.ge]
  -- the maximum therefore attains the Bellman value
  have hbound : ∀ x ∈ P.toExtended.feasible s,
      P.toExtended.objectiveE P.toExtended.valueFunction s x
        ≤ ((P.objR s assetCap : ℝ) : EReal) := by
    intro x hx
    have hxle : x ≤ assetCap := by
      have := hx; rw [P.feasible_eq, hmc] at this; exact this.2
    have hcx : 0 < P.consumption s x := by simp only [consumption]; linarith
    rw [P.objectiveE_eq_coe hs hx (P.mem_dom_of_pos hcx), EReal.coe_le_coe_iff]
    exact hmain x hx
  have hble := P.toExtended.bellmanFn_le P.toExtended.valueFunction hbound
  have hge := P.toExtended.le_bellmanFn P.toExtended.valueFunction hmem
  rw [P.objectiveE_eq_coe hs hmem (P.mem_dom_of_pos hcpos), EReal.coe_le_coe_iff] at hge
  refine (P.eq_policy_of_optimal hs hmem ?_).symm
  rw [P.objectiveE_eq_coe hs hmem (P.mem_dom_of_pos hcpos), le_antisymm hge hble]

end IncomeFluctuation

end LeanEconomics
