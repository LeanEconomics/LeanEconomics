/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ExogenousPrices

/-!
# Interior saving from crude Euler bounds

Milestone OI4 of `ORDER_STRUCTURE_PLAN.md` (OS4(b)), for log utility above the consumption floor.

* `policy_pos_of`, `policy_lt_cap_of`: optimal saving is positive (below the cap) when some
  feasible deviation upward (downward) from the corner does strictly better;
* **`value_sub_ge`**: extra assets `δ` are worth at least `Rδ / (cash + Rδ)` (keep the saving of
  the poorer state, consume the extra return; log tangent line);
* **`value_sub_le`**: the last `δ` of assets below `b` is worth at most
  `Rδ / (cash(b) − ā − Rδ)` (the poorer state copies the saving at `b`, consuming the missing
  return).

Summed over next period's shocks these bound the gain of the continuation, and the witness
(`InteriorWitness.lean`) checks the two corner deviations with explicit numbers.
-/

open Set

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

theorem log_sub_le {c d : ℝ} (hd : 0 ≤ d) (hcd : d < c) :
    Real.log c - Real.log (c - d) ≤ d / (c - d) := by
  have hpos : 0 < c - d := by linarith
  have hc : 0 < c := by linarith
  rw [← Real.log_div hc.ne' hpos.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hc hpos)
  have e : c / (c - d) - 1 = d / (c - d) := by
    field_simp
    ring
  linarith

theorem le_log_sub {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) :
    d / (c + d) ≤ Real.log (c + d) - Real.log c := by
  have hcd : 0 < c + d := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hc hcd)
  rw [Real.log_div hc.ne' hcd.ne'] at h
  have e : c / (c + d) - 1 = -(d / (c + d)) := by
    field_simp
    ring
  linarith

variable {M : KSModel Z E} (z₀ : Z) (K : List Z → ℝ × ℝ)

/-- **Saving is positive** when saving `δ` beats saving nothing. -/
theorem policy_pos_of {s : M.State} {δ : ℝ} (hδ : δ ∈ (M.household z₀ K).feasible s)
    (hgain : M.utility (M.cash z₀ K s) + M.discount * M.cont z₀ K s 0
      < M.utility (M.cash z₀ K s - δ) + M.discount * M.cont z₀ K s δ) :
    0 < M.policy z₀ K s := by
  by_contra h
  have h0 : M.policy z₀ K s = 0 := le_antisymm (not_lt.1 h) (M.policy_mem z₀ K s).1
  have v := M.valueFunction_eq_cont z₀ K s
  change _ = M.utility (M.cash z₀ K s - M.policy z₀ K s) + _ at v
  rw [h0, sub_zero] at v
  have := M.le_valueFunction z₀ K hδ
  linarith

/-- **Saving is below the cap** when saving `ā − δ` beats saving `ā`. -/
theorem policy_lt_cap_of {s : M.State} {δ : ℝ}
    (hδ : M.assetCap - δ ∈ (M.household z₀ K).feasible s)
    (hgain : M.utility (M.cash z₀ K s - M.assetCap) + M.discount * M.cont z₀ K s M.assetCap
      < M.utility (M.cash z₀ K s - (M.assetCap - δ))
        + M.discount * M.cont z₀ K s (M.assetCap - δ)) :
    M.policy z₀ K s < M.assetCap := by
  by_contra h
  have h0 : M.policy z₀ K s = M.assetCap :=
    le_antisymm (M.mem_Icc_of_mem_feasible z₀ K (M.policy_mem z₀ K s)).2 (not_lt.1 h)
  have v := M.valueFunction_eq_cont z₀ K s
  change _ = M.utility (M.cash z₀ K s - M.policy z₀ K s) + _ at v
  rw [h0] at v
  have := M.le_valueFunction z₀ K hδ
  linarith

variable (hlog : ∀ c, M.consFloor ≤ c → M.utility c = Real.log c) (hfl : 0 < M.consFloor)
include hlog hfl

/-- **Extra assets are worth at least the log tangent of the extra return.** -/
theorem value_sub_ge {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (haδ : a + δ ≤ M.assetCap)
    (l : Label Z E) :
    M.returnAt z₀ K l.node * δ / (M.returnAt z₀ K l.node * a
        + M.wageAt z₀ K l.node * M.efficiency l.idio + M.returnAt z₀ K l.node * δ)
      ≤ (M.household z₀ K).valueFunction (M.stateAt (a + δ) l)
        - (M.household z₀ K).valueFunction (M.stateAt a l) := by
  set R := M.returnAt z₀ K l.node with hRdef
  set y := M.wageAt z₀ K l.node * M.efficiency l.idio with hydef
  have hR : 0 ≤ R := M.returnAt_nonneg z₀ K _
  have hRδ : 0 ≤ R * δ := mul_nonneg hR hδ
  have hamem : a ∈ Icc 0 M.assetCap := ⟨ha, by linarith⟩
  have hbmem : a + δ ∈ Icc 0 M.assetCap := ⟨by linarith, haδ⟩
  have hca : M.cash z₀ K (M.stateAt a l) = R * a + y := M.cash_stateAt z₀ K hamem l
  have hcb : M.cash z₀ K (M.stateAt (a + δ) l) = R * a + y + R * δ := by
    rw [M.cash_stateAt z₀ K hbmem l]
    ring
  set p := M.policy z₀ K (M.stateAt a l) with hpdef
  have hp := M.policy_mem z₀ K (M.stateAt a l)
  have hpx : p ≤ M.cash z₀ K (M.stateAt a l) - M.consFloor := hp.2.trans (min_le_right _ _)
  rw [hca] at hpx
  have hf : p ∈ (M.household z₀ K).feasible (M.stateAt (a + δ) l) :=
    ⟨hp.1, le_min (hp.2.trans (min_le_left _ _)) (by
      change p ≤ M.cash z₀ K (M.stateAt (a + δ) l) - M.consFloor
      rw [hcb]
      linarith)⟩
  have h1 := M.le_valueFunction z₀ K hf
  have v1 := M.valueFunction_eq_cont z₀ K (M.stateAt a l)
  have hcont : M.cont z₀ K (M.stateAt (a + δ) l) p = M.cont z₀ K (M.stateAt a l) p := rfl
  rw [hcont, hcb] at h1
  change _ = M.utility (M.cash z₀ K (M.stateAt a l) - p) + _ at v1
  rw [hca] at v1
  have hc : M.consFloor ≤ R * a + y - p := by linarith
  rw [hlog _ hc] at v1
  rw [show R * a + y + R * δ - p = (R * a + y - p) + R * δ by ring, hlog _ (by linarith)] at h1
  have hl := le_log_sub (hfl.trans_le hc) hRδ
  have hmono : R * δ / (R * a + y + R * δ) ≤ R * δ / ((R * a + y - p) + R * δ) :=
    div_le_div_of_nonneg_left hRδ (by linarith) (by linarith [hp.1])
  linarith

/-- **The last `δ` of assets is worth at most the log tangent of the missing return**, when the
poorer state can copy the richer one's saving. -/
theorem value_sub_le {b δ : ℝ} (hδ : 0 ≤ δ) (hbδ : δ ≤ b) (hb : b ≤ M.assetCap) (l : Label Z E)
    (hfeas : M.consFloor ≤ M.returnAt z₀ K l.node * b + M.wageAt z₀ K l.node * M.efficiency l.idio
      - M.assetCap - M.returnAt z₀ K l.node * δ) :
    (M.household z₀ K).valueFunction (M.stateAt b l)
        - (M.household z₀ K).valueFunction (M.stateAt (b - δ) l)
      ≤ M.returnAt z₀ K l.node * δ / (M.returnAt z₀ K l.node * b
        + M.wageAt z₀ K l.node * M.efficiency l.idio - M.assetCap - M.returnAt z₀ K l.node * δ) := by
  set R := M.returnAt z₀ K l.node with hRdef
  set y := M.wageAt z₀ K l.node * M.efficiency l.idio with hydef
  have hR : 0 ≤ R := M.returnAt_nonneg z₀ K _
  have hRδ : 0 ≤ R * δ := mul_nonneg hR hδ
  have hbmem : b ∈ Icc 0 M.assetCap := ⟨by linarith, hb⟩
  have hamem : b - δ ∈ Icc 0 M.assetCap := ⟨by linarith, by linarith⟩
  have hcb : M.cash z₀ K (M.stateAt b l) = R * b + y := M.cash_stateAt z₀ K hbmem l
  have hca : M.cash z₀ K (M.stateAt (b - δ) l) = R * b + y - R * δ := by
    rw [M.cash_stateAt z₀ K hamem l]
    ring
  set p := M.policy z₀ K (M.stateAt b l) with hpdef
  have hp := M.policy_mem z₀ K (M.stateAt b l)
  have hpa : p ≤ M.assetCap := (M.mem_Icc_of_mem_feasible z₀ K hp).2
  have hf : p ∈ (M.household z₀ K).feasible (M.stateAt (b - δ) l) :=
    ⟨hp.1, le_min hpa (by
      change p ≤ M.cash z₀ K (M.stateAt (b - δ) l) - M.consFloor
      rw [hca]
      linarith)⟩
  have h1 := M.le_valueFunction z₀ K hf
  have v1 := M.valueFunction_eq_cont z₀ K (M.stateAt b l)
  have hcont : M.cont z₀ K (M.stateAt (b - δ) l) p = M.cont z₀ K (M.stateAt b l) p := rfl
  rw [hcont, hca] at h1
  change _ = M.utility (M.cash z₀ K (M.stateAt b l) - p) + _ at v1
  rw [hcb] at v1
  have hc : M.consFloor ≤ R * b + y - p - R * δ := by linarith
  rw [hlog _ (by linarith)] at v1
  rw [show R * b + y - R * δ - p = (R * b + y - p) - R * δ by ring, hlog _ (by linarith)] at h1
  have hl := log_sub_le hRδ (show R * δ < R * b + y - p by linarith)
  have hmono : R * δ / ((R * b + y - p) - R * δ) ≤ R * δ / (R * b + y - M.assetCap - R * δ) :=
    div_le_div_of_nonneg_left hRδ (by linarith) (by linarith)
  linarith

end KSModel

end KrusellSmith

end LeanEconomics
