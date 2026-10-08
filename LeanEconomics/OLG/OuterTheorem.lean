/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.OuterBridge
import LeanEconomics.OLG.OuterCertified

/-!
# No stationary equilibrium outside the bracket, at `γ = 3`

For the seven-state life cycle of the certificate with cap `10⁶`, `β = 24/25` and `γ = 3`:
capital supply is strictly below the firm's demand at every rate in `(-8%, 2.3%]`, by the affine
ceiling; and strictly above it at every rate in `[8.7%, 20%]`, by the clamped floor. Both are
read off the checker's verdicts on a mesh of rate cells (`OuterCertified`) through the bridge
(`OuterBridge`); the mesh covers each range because its breakpoints are increasing and start and
end where the checker says.
-/

open Set

namespace LeanEconomics.EnclCert

open IncomeFluctuation

/-- A point of `[b 0, b n]` lies in some cell `[b i, b (i+1)]` of an increasing mesh. -/
theorem exists_cell {b : ℕ → ℝ} : ∀ n : ℕ, 0 < n → (∀ i < n, b i < b (i + 1)) →
    ∀ r : ℝ, b 0 ≤ r → r ≤ b n → ∃ i < n, b i ≤ r ∧ r ≤ b (i + 1)
  | 0, h, _, _, _, _ => absurd h (lt_irrefl 0)
  | n + 1, _, hmono, r, h0, hn => by
    rcases le_or_gt r (b n) with hle | hgt
    · rcases Nat.eq_zero_or_pos n with hz | hpos
      · subst hz; exact ⟨0, by omega, h0, hn⟩
      · obtain ⟨i, hi, h1, h2⟩ := exists_cell n hpos (fun i hi => hmono i (by omega)) r h0 hle
        exact ⟨i, by omega, h1, h2⟩
    · exact ⟨n, by omega, hgt.le, hn⟩

theorem lowCheck_unpack (h : lowCheck () = true) :
    bLow 0 = -80000 ∧ bLow nLow = 23000
      ∧ ∀ i < nLow, bLow i < bLow (i + 1) ∧ cellCeilOK (bLow i) (bLow (i + 1)) = true := by
  simp only [lowCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem highCheck_unpack (h : highCheck () = true) :
    bHigh 0 = 87000 ∧ bHigh nHigh = 200000
      ∧ ∀ i < nHigh, bHigh i < bHigh (i + 1) ∧ cellFloorOK (bHigh i) (bHigh (i + 1)) = true := by
  simp only [highCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The economy at rate `r` is in the cell `[m₁/RD, m₂/RD]` containing `r`. -/
theorem inCell_olg7At {m1 m2 : Int} (r : ℝ) (hr : 0 < 1 + r)
    (h1 : ((m1 : Int) : ℝ) / ((RD : Int) : ℝ) ≤ r) (h2 : r ≤ ((m2 : Int) : ℝ) / ((RD : Int) : ℝ)) :
    InCell (olg7At r hr) m1 m2 where
  income _ := rfl
  trans _ _ := rfl
  disc := rfl
  u := rfl
  unb := rfl
  minInc := rfl
  maxInc := rfl
  rlo := by
    have hRD := RD_pos
    rw [rI, Rn, olg7At_interest]; push_cast
    rw [add_div, div_self hRD.ne']; linarith
  rhi := by
    have hRD := RD_pos
    rw [rI, Rn, olg7At_interest]; push_cast
    rw [add_div, div_self hRD.ne']; linarith

theorem bLow_cast_lt {i : ℕ} (h : bLow i < bLow (i + 1)) :
    ((bLow i : Int) : ℝ) / ((RD : Int) : ℝ) < ((bLow (i + 1) : Int) : ℝ) / ((RD : Int) : ℝ) :=
  div_lt_div_of_pos_right (by exact_mod_cast h) RD_pos

theorem bHigh_cast_lt {i : ℕ} (h : bHigh i < bHigh (i + 1)) :
    ((bHigh i : Int) : ℝ) / ((RD : Int) : ℝ) < ((bHigh (i + 1) : Int) : ℝ) / ((RD : Int) : ℝ) :=
  div_lt_div_of_pos_right (by exact_mod_cast h) RD_pos

/-- **No stationary equilibrium below `2.3%`**: capital supply is strictly below demand at every
rate in `(-8%, 2.3%]`. -/
theorem olg7_supply_lt_demand_low (r : ℝ) (hlo : -2 / 25 < r) (hhi : r ≤ 23 / 1000)
    (hr : 0 < 1 + r) : (olg7At r hr).olgCapital 59 nuR < olgDemand r := by
  obtain ⟨hb0, hbn, hcells⟩ := lowCheck_unpack lowCheck_eq_true
  have hmono : ∀ i < nLow, ((bLow i : Int) : ℝ) / ((RD : Int) : ℝ)
      < ((bLow (i + 1) : Int) : ℝ) / ((RD : Int) : ℝ) := fun i hi => bLow_cast_lt (hcells i hi).1
  obtain ⟨i, hi, h1, h2⟩ := exists_cell (b := fun i => ((bLow i : Int) : ℝ) / ((RD : Int) : ℝ))
    nLow (by decide) hmono r (by rw [hb0, RD_cast]; norm_num; linarith)
    (by rw [hbn, RD_cast]; norm_num; linarith)
  exact olgCapital_lt_demand_of_cell (inCell_olg7At r hr h1 h2) hlo (hcells i hi).2

/-- **No stationary equilibrium between `8.7%` and `20%`**: capital supply is strictly above
demand at every rate in `[8.7%, 20%]`. -/
theorem olg7_demand_lt_supply_high (r : ℝ) (hlo : 87 / 1000 ≤ r) (hhi : r ≤ 1 / 5)
    (hr : 0 < 1 + r) : olgDemand r < (olg7At r hr).olgCapital 59 nuR := by
  obtain ⟨hb0, hbn, hcells⟩ := highCheck_unpack highCheck_eq_true
  have hmono : ∀ i < nHigh, ((bHigh i : Int) : ℝ) / ((RD : Int) : ℝ)
      < ((bHigh (i + 1) : Int) : ℝ) / ((RD : Int) : ℝ) := fun i hi => bHigh_cast_lt (hcells i hi).1
  obtain ⟨i, hi, h1, h2⟩ := exists_cell (b := fun i => ((bHigh i : Int) : ℝ) / ((RD : Int) : ℝ))
    nHigh (by decide) hmono r (by rw [hb0, RD_cast]; norm_num; linarith)
    (by rw [hbn, RD_cast]; norm_num; linarith)
  exact demand_lt_olgCapital_of_cell (inCell_olg7At r hr h1 h2) (hcells i hi).2

end LeanEconomics.EnclCert
