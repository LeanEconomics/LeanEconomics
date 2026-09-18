/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.Uniqueness

/-!
# Multiplicity, and what it costs

`equilibriumRate_unique` says a monotone capital supply meets a strictly decreasing capital
demand once. This file is the other side of that statement.

## What is proved

* `not_monotoneOn_of_equilibria_ne` — the exact contrapositive. Two distinct equilibrium rates
  force capital supply to be NON-MONOTONE on any interval containing them. So every multiplicity
  result in the literature is, formally, a counterexample to Light's Theorem 1; there is no other
  way for it to happen.
* `exists_two_equilibria_of_sign_changes` and `exists_three_equilibria_of_sign_changes` — the
  intermediate value theorem run two and three times. Excess demand that changes sign three times
  gives three equilibrium rates, strictly ordered. Walsh and Young (2025) report that when they
  find multiplicity they find EXACTLY three, which is the shape of the second of these.
* `wiggleSupply` — an explicit continuous, strictly positive supply schedule whose equilibria
  with the Cobb--Douglas demand `capitalDemand 2 1` are exactly `r = 1, 2, 3`. The equilibrium
  SYSTEM therefore permits three equilibria: nothing in the firm side, the fixed-point
  machinery, or the intermediate value argument rules it out.

## What is NOT proved, and should not be read into this

That `wiggleSupply` is the capital supply of any household. It is not; it is
`capitalDemand 2 1 r + (r-1)(r-2)(r-3)/1000`, chosen so that the crossings are visible. Deriving
a backward-bending supply schedule from preferences is the hard part of the multiplicity
literature — Açıkgöz (2018) at `γ = 6.5`, Walsh and Young (2025) at high risk aversion with a
disaster state — and it is not attempted here.

Two obstructions are worth recording, because they say what such a proof would need. The only
lower bound on capital supply in this development is the gain test, and `gain_term_mono` says it
gets EASIER at higher rates; the only upper bound is the minimal MPC, and `(βR)^(1/γ)/R` gets
LARGER at higher rates. Both bounds therefore move the wrong way for showing supply falls. A
backward bend needs the bounds to be sharp enough to cross, which needs the precautionary
mechanism quantified, not merely present.

So what this file establishes is the division of labour: multiplicity is possible in the system,
impossible under monotone supply, and monotone supply is exactly what `γ ≤ 1` buys.
-/

open Set

namespace LeanEconomics

/-! ### Multiplicity is exactly a failure of monotone supply -/

/-- **Two equilibria force a non-monotone supply schedule.** The contrapositive of
`eq_of_monotoneOn_of_strictAntiOn`, and the reason every multiplicity example in the literature
is a counterexample to Light's Theorem 1 rather than to anything else. -/
theorem not_monotoneOn_of_equilibria_ne {S D : ℝ → ℝ} {s : Set ℝ} (hD : StrictAntiOn D s)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ s) (h₂ : r₂ ∈ s) (hne : r₁ ≠ r₂)
    (he₁ : S r₁ = D r₁) (he₂ : S r₂ = D r₂) : ¬ MonotoneOn S s :=
  fun hS => hne (eq_of_monotoneOn_of_strictAntiOn hS hD h₁ h₂ he₁ he₂)

/-- The same for the Cobb--Douglas firm: two equilibrium rates and capital supply cannot be
monotone. -/
theorem not_monotoneOn_of_equilibria_ne_capitalDemand {S : ℝ → ℝ} {A δ rlo rhi : ℝ} (hA : A ≠ 0)
    (hδ : 0 < rlo + δ) {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (hne : r₁ ≠ r₂) (he₁ : S r₁ = capitalDemand A δ r₁) (he₂ : S r₂ = capitalDemand A δ r₂) :
    ¬ MonotoneOn S (Icc rlo rhi) :=
  not_monotoneOn_of_equilibria_ne (capitalDemand_strictAntiOn hA hδ) h₁ h₂ hne he₁ he₂

/-! ### Sign changes give equilibria

The intermediate value theorem, run once per sign change. Nothing here is specific to capital:
`S` and `D` are any two continuous functions. -/

/-- **Two equilibria from two sign changes.** Excess demand non-positive at `r₁`, strictly
positive at `r₂`, non-positive again at `r₃` puts an equilibrium strictly on each side of `r₂`. -/
theorem exists_two_equilibria_of_sign_changes {S D : ℝ → ℝ} {r₁ r₂ r₃ : ℝ}
    (h₁₂ : r₁ ≤ r₂) (h₂₃ : r₂ ≤ r₃)
    (hS : ContinuousOn S (Icc r₁ r₃)) (hD : ContinuousOn D (Icc r₁ r₃))
    (hlo : S r₁ ≤ D r₁) (hmid : D r₂ < S r₂) (hhi : S r₃ ≤ D r₃) :
    ∃ ra ∈ Icc r₁ r₂, ∃ rb ∈ Icc r₂ r₃, ra < rb ∧ S ra = D ra ∧ S rb = D rb := by
  set f : ℝ → ℝ := fun r => S r - D r with hf
  have hfc : ContinuousOn f (Icc r₁ r₃) := hS.sub hD
  have hsub₁ : Icc r₁ r₂ ⊆ Icc r₁ r₃ := Icc_subset_Icc le_rfl h₂₃
  have hsub₂ : Icc r₂ r₃ ⊆ Icc r₁ r₃ := Icc_subset_Icc h₁₂ le_rfl
  have hf₁ : f r₁ ≤ 0 := by simp only [hf]; linarith
  have hf₂ : 0 < f r₂ := by simp only [hf]; linarith
  have hf₃ : f r₃ ≤ 0 := by simp only [hf]; linarith
  obtain ⟨ra, hra, hfa⟩ :=
    intermediate_value_Icc h₁₂ (hfc.mono hsub₁) ⟨hf₁, hf₂.le⟩
  obtain ⟨rb, hrb, hfb⟩ :=
    intermediate_value_Icc' h₂₃ (hfc.mono hsub₂) ⟨hf₃, hf₂.le⟩
  have hane : ra ≠ r₂ := by intro h; rw [h] at hfa; linarith
  have hbne : rb ≠ r₂ := by intro h; rw [h] at hfb; linarith
  refine ⟨ra, hra, rb, hrb, lt_of_lt_of_le (lt_of_le_of_ne hra.2 hane)
    (le_of_lt (lt_of_le_of_ne hrb.1 (Ne.symm hbne))), ?_, ?_⟩
  · simp only [hf] at hfa; linarith
  · simp only [hf] at hfb; linarith

/-- **Three equilibria from three sign changes**, strictly ordered. This is the shape Walsh and
Young (2025) report whenever they find multiplicity at all. -/
theorem exists_three_equilibria_of_sign_changes {S D : ℝ → ℝ} {r₀ r₁ r₂ r₃ : ℝ}
    (h₀₁ : r₀ ≤ r₁) (h₁₂ : r₁ ≤ r₂) (h₂₃ : r₂ ≤ r₃)
    (hS : ContinuousOn S (Icc r₀ r₃)) (hD : ContinuousOn D (Icc r₀ r₃))
    (h₀ : S r₀ ≤ D r₀) (hone : D r₁ < S r₁) (htwo : S r₂ < D r₂) (hthree : D r₃ < S r₃) :
    ∃ ra ∈ Icc r₀ r₁, ∃ rb ∈ Icc r₁ r₂, ∃ rc ∈ Icc r₂ r₃,
      ra < rb ∧ rb < rc ∧ S ra = D ra ∧ S rb = D rb ∧ S rc = D rc := by
  set f : ℝ → ℝ := fun r => S r - D r with hf
  have hfc : ContinuousOn f (Icc r₀ r₃) := hS.sub hD
  have hle₀₂ : r₀ ≤ r₂ := le_trans h₀₁ h₁₂
  have hle₁₃ : r₁ ≤ r₃ := le_trans h₁₂ h₂₃
  have hs₁ : Icc r₀ r₁ ⊆ Icc r₀ r₃ := Icc_subset_Icc le_rfl hle₁₃
  have hs₂ : Icc r₁ r₂ ⊆ Icc r₀ r₃ := Icc_subset_Icc h₀₁ h₂₃
  have hs₃ : Icc r₂ r₃ ⊆ Icc r₀ r₃ := Icc_subset_Icc hle₀₂ le_rfl
  have hf₀ : f r₀ ≤ 0 := by simp only [hf]; linarith
  have hf₁ : 0 < f r₁ := by simp only [hf]; linarith
  have hf₂ : f r₂ < 0 := by simp only [hf]; linarith
  have hf₃ : 0 < f r₃ := by simp only [hf]; linarith
  obtain ⟨ra, hra, hfa⟩ := intermediate_value_Icc h₀₁ (hfc.mono hs₁) ⟨hf₀, hf₁.le⟩
  obtain ⟨rb, hrb, hfb⟩ := intermediate_value_Icc' h₁₂ (hfc.mono hs₂) ⟨hf₂.le, hf₁.le⟩
  obtain ⟨rc, hrc, hfc'⟩ := intermediate_value_Icc h₂₃ (hfc.mono hs₃) ⟨hf₂.le, hf₃.le⟩
  have hane : ra ≠ r₁ := by intro h; rw [h] at hfa; linarith
  have hbne₁ : rb ≠ r₁ := by intro h; rw [h] at hfb; linarith
  have hbne₂ : rb ≠ r₂ := by intro h; rw [h] at hfb; linarith
  have hcne : rc ≠ r₂ := by intro h; rw [h] at hfc'; linarith
  refine ⟨ra, hra, rb, hrb, rc, hrc,
    lt_of_le_of_lt (lt_of_le_of_ne hra.2 hane).le (lt_of_le_of_ne hrb.1 (Ne.symm hbne₁)),
    lt_of_lt_of_le (lt_of_le_of_ne hrb.2 hbne₂) (lt_of_le_of_ne hrc.1 (Ne.symm hcne)).le,
    ?_, ?_, ?_⟩
  · simp only [hf] at hfa; linarith
  · simp only [hf] at hfb; linarith
  · simp only [hf] at hfc'; linarith

/-! ### An explicit three-equilibrium system

`capitalDemand 2 1 r = 1/(r+1)²`, and adding a cubic that vanishes at `1, 2, 3` gives a supply
schedule meeting it exactly there. The cubic is divided by `1000` so that the perturbation never
outweighs demand and supply stays positive. -/

/-- A continuous, strictly positive capital supply schedule with three equilibria. -/
noncomputable def wiggleSupply (r : ℝ) : ℝ :=
  capitalDemand 2 1 r + (r - 1) * (r - 2) * (r - 3) / 1000

theorem wiggleSupply_continuousOn : ContinuousOn wiggleSupply (Icc (1 / 2 : ℝ) (7 / 2)) := by
  refine (continuousOn_capitalDemand (by norm_num)).add ?_
  exact (((continuousOn_id.sub continuousOn_const).mul
    (continuousOn_id.sub continuousOn_const)).mul
      (continuousOn_id.sub continuousOn_const)).div_const _

/-- Supply stays positive: the cubic is at most `9375/1000000` in size on the interval, while
demand is at least `4/81`. -/
theorem wiggleSupply_pos {r : ℝ} (hr : r ∈ Icc (1 / 2 : ℝ) (7 / 2)) : 0 < wiggleSupply r := by
  obtain ⟨hlo, hhi⟩ := hr
  have hr1 : (0 : ℝ) < r + 1 := by linarith
  have hsq : (r + 1) ^ 2 ≤ 81 / 4 := by nlinarith
  have hdem : (4 : ℝ) / 81 ≤ capitalDemand 2 1 r := by
    simp only [capitalDemand]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hsq]
  have hcub : -(10 : ℝ) / 1000 ≤ (r - 1) * (r - 2) * (r - 3) / 1000 := by
    rw [le_div_iff₀ (by norm_num), neg_div]
    nlinarith [hlo, hhi, sq_nonneg (r - 2), sq_nonneg (r - 1), sq_nonneg (r - 3)]
  simp only [wiggleSupply]
  linarith

/-- **Three equilibria.** `wiggleSupply` meets Cobb--Douglas capital demand at `1`, `2` and `3`.
-/
theorem wiggleSupply_equilibria :
    wiggleSupply 1 = capitalDemand 2 1 1 ∧ wiggleSupply 2 = capitalDemand 2 1 2
      ∧ wiggleSupply 3 = capitalDemand 2 1 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> · simp only [wiggleSupply]; ring

/-- **And therefore it is not monotone.** The three equilibria are forced to coexist with a
backward bend — which is the content of the uniqueness theorem read backwards. -/
theorem wiggleSupply_not_monotoneOn :
    ¬ MonotoneOn wiggleSupply (Icc (1 / 2 : ℝ) (7 / 2)) := by
  obtain ⟨h1, h2, -⟩ := wiggleSupply_equilibria
  exact not_monotoneOn_of_equilibria_ne_capitalDemand (A := 2) (δ := 1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2

/-- **The monotonicity hypothesis of `equilibriumRate_unique` cannot be dropped.** There is a
continuous, strictly positive capital supply schedule with two (indeed three) equilibrium rates
against the Cobb--Douglas firm. Everything the uniqueness theorem assumes apart from
monotonicity — continuity, positivity, a well-behaved firm — is present here.

So the theorem is tight, and Light's Theorem 1 is not a technical convenience: it is the entire
content of uniqueness. -/
theorem equilibriumRate_not_unique_without_monotone :
    ∃ S : ℝ → ℝ, ContinuousOn S (Icc (1 / 2 : ℝ) (7 / 2))
      ∧ (∀ r ∈ Icc (1 / 2 : ℝ) (7 / 2), 0 < S r)
      ∧ ¬ MonotoneOn S (Icc (1 / 2 : ℝ) (7 / 2))
      ∧ ∃ r₁ ∈ Icc (1 / 2 : ℝ) (7 / 2), ∃ r₂ ∈ Icc (1 / 2 : ℝ) (7 / 2),
          ∃ r₃ ∈ Icc (1 / 2 : ℝ) (7 / 2),
          r₁ < r₂ ∧ r₂ < r₃
          ∧ S r₁ = capitalDemand 2 1 r₁ ∧ S r₂ = capitalDemand 2 1 r₂
          ∧ S r₃ = capitalDemand 2 1 r₃ := by
  obtain ⟨h1, h2, h3⟩ := wiggleSupply_equilibria
  exact ⟨wiggleSupply, wiggleSupply_continuousOn, fun _ hr => wiggleSupply_pos hr,
    wiggleSupply_not_monotoneOn,
    1, by norm_num, 2, by norm_num, 3, by norm_num, by norm_num, by norm_num, h1, h2, h3⟩

end LeanEconomics
