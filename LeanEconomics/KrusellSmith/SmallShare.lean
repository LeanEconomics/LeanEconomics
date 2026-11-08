/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CRRAContraction
import LeanEconomics.KrusellSmith.LawContraction

/-!
# Small capital shares: the contraction conditions hold

Analytic closure of Track A (`CRRAContraction.lean`) and of LS4 (`LawContraction.lean`) for CRRA
utility and clamped Cobb–Douglas prices: **there is a capital share `α₀ > 0` below which both
contraction conditions hold**, `κ < 1` (uniqueness of sequential equilibrium, recursive
equilibrium on the minimal state) and `r < 1` (the law of motion contracts).

Hold the environment (`KSEnvironment`), the risk aversion `γ > 0` and every Cobb–Douglas
parameter except the share fixed, with depreciation `δ > 0`, and vary the share `α`
(`CobbDouglas.withShare`). Every constant in `κ` and `r` is an explicit expression in `α`
(`smallR`, …, `smallRate`; `crraContractionHyp_κ`, `crraContractionHyp_lawRate`) that is
continuous at `α = 0`, where the expressions still make sense (`x ^ 0 = 1`). At `α = 0`:

* the price sensitivity `ℓ` vanishes (it carries the factor `α`), so `κ = 0` and `G = 0`;
* the gross return bound is `1 − δ`, so `r = 1 − δ < 1`, and `β R̄ < 1`, `R̄ < 1` (the weight
  `λ = 1` is admissible).

By continuity the strict inequalities persist for small `α > 0` (`exists_smallShare`). In
particular (`smallShare_contraction`), for such shares the CRRA model has a unique sequential
equilibrium from every state, and a `ContractionHyp` with `κ < 1` and `lawRate < 1`, so every
result of `LawContraction.lean` applies: fading memory, burn-in, explicit matching bounds and
uniqueness of the sequence-state equilibrium.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

namespace CobbDouglas

variable {Z : Type*}

/-- The same Cobb–Douglas technology with capital share `α`. -/
def withShare (T : CobbDouglas Z) (α : ℝ) (h0 : 0 < α) (h1 : α < 1) : CobbDouglas Z :=
  { T with share := α, share_pos := h0, share_lt_one := h1 }

end CobbDouglas

variable {Z E : Type*} [Fintype Z] [Fintype E]

section Formulas

variable (V : KSEnvironment Z E) (T : CobbDouglas Z) (γ : ℝ)

/-- The gross return bound at share `α`. -/
noncomputable def smallR (α : ℝ) : ℝ :=
  1 - T.depreciation + α * T.tfpHi * T.capLo ^ (α - 1) * T.labHi ^ (1 - α)

/-- The wage bound at share `α`. -/
noncomputable def smallWB (α : ℝ) : ℝ :=
  (1 - α) * T.tfpHi * T.capHi ^ α * T.labLo ^ (-α)

/-- The income floor at share `α`. -/
noncomputable def smallIF (α : ℝ) : ℝ :=
  (1 - α) * T.tfpLo * T.capLo ^ α * T.labHi ^ (-α) * V.effLo

/-- The price sensitivity `ℓ` at share `α`. -/
noncomputable def smallLip (α : ℝ) : ℝ :=
  max (α * T.tfpHi * T.labHi ^ (1 - α) * ((1 - α) * T.capLo ^ (α - 1 - 1)))
    ((1 - α) * T.tfpHi * T.labLo ^ (-α) * (α * T.capLo ^ (α - 1)))

/-- The largest consumption at share `α`. -/
noncomputable def smallTop (α : ℝ) : ℝ :=
  max (smallIF V T α) (smallR T α * V.assetCap + smallWB T α * ∑ e, V.efficiency e)

/-- The value bound at share `α`. -/
noncomputable def smallVB (α : ℝ) : ℝ :=
  max |crraUtility γ (smallIF V T α) / (1 - V.discount)|
    |crraUtility γ (smallTop V T α) / (1 - V.discount)|

/-- The consumption floor at share `α`. -/
noncomputable def smallFl (α : ℝ) : ℝ :=
  min ((V.discount * (4 * smallVB V T γ α / smallIF V T α) + 1) ^ (-1 / γ)) (smallIF V T α / 4)

/-- `κ` at share `α`. -/
noncomputable def smallκ (α : ℝ) : ℝ :=
  1 * (smallLip T α * (V.assetCap + 0 + ∑ e, V.efficiency e)
      + (V.discount * smallLip T α * smallFl V T γ α ^ (-γ) / 1
          + γ * (smallFl V T γ α / 2) ^ (-γ - 1) * smallLip T α
            * (V.assetCap + 0 + ∑ e, V.efficiency e)) / (1 - V.discount * smallR T α / 1)
        / (γ * smallTop V T α ^ (-γ - 1)))
    / (1 - 1 * smallR T α)

/-- The policy gain `G` at share `α`. -/
noncomputable def smallGain (α : ℝ) : ℝ :=
  smallLip T α * (V.assetCap + 0 + ∑ e, V.efficiency e)
    + (V.discount * smallLip T α * smallFl V T γ α ^ (-γ) / 1
        + γ * (smallFl V T γ α / 2) ^ (-γ - 1) * smallLip T α
          * (V.assetCap + 0 + ∑ e, V.efficiency e)) / (1 - V.discount * smallR T α / 1)
      / (γ * smallTop V T α ^ (-γ - 1))

/-- The contraction rate `r` of the law of motion at share `α`. -/
noncomputable def smallRate (α : ℝ) : ℝ :=
  smallR T α + smallGain V T γ α / (1 - smallκ V T γ α)

end Formulas

/-! ### The constants of the CRRA model are the formulas -/

section Identify

variable [Nonempty Z] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)
  {α : ℝ} (h0 : 0 < α) (h1 : α < 1)

omit [Fintype Z] [Nonempty Z] in
theorem withShare_returnBound : (T.withShare α h0 h1).returnBound = smallR T α := rfl

variable (hdisc : V.discount * (T.withShare α h0 h1).returnBound < 1)
  (hret : 1 * (T.withShare α h0 h1).returnBound < 1)

theorem crraContractionHyp_κ :
    (crraContractionHyp V (T.withShare α h0 h1) hγ 1 one_pos le_rfl hdisc hret).κ
      = smallκ V T γ α := rfl

theorem crraContractionHyp_lawRate :
    (crraContractionHyp V (T.withShare α h0 h1) hγ 1 one_pos le_rfl hdisc hret).lawRate
      = smallRate V T γ α := rfl

end Identify

/-! ### Continuity at share zero -/

section Limit

variable (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)
  (hδ : 0 < T.depreciation)
include hγ hδ

omit hδ in
/-- **At share zero** the policy gain vanishes, `G = 0`, the return bound is `1 − δ`, and both are
continuous there. -/
theorem smallGain_limits :
    smallGain V T γ 0 = 0 ∧ smallR T 0 = 1 - T.depreciation ∧ ContinuousAt (smallR T) 0 ∧
      ContinuousAt (smallGain V T γ) 0 := by
  have hcap := T.capLo_pos
  have hcapHi : 0 < T.capHi := hcap.trans_le T.capLo_le
  have hlab := T.labLo_pos
  have hlabHi : 0 < T.labHi := hlab.trans_le T.labLo_le
  have htfp := T.tfpLo_pos
  have hβ := V.discount_pos
  have hβ1 := V.discount_lt_one
  have hδ0 := T.depreciation_nonneg
  have hδ1 := T.depreciation_le_one
  have heff := V.effLo_pos
  -- values at zero
  have hR0 : smallR T 0 = 1 - T.depreciation := by simp [smallR]
  have hLip0 : smallLip T 0 = 0 := by simp [smallLip]
  have hIF0 : smallIF V T 0 = T.tfpLo * V.effLo := by simp [smallIF]
  have hIFp : 0 < smallIF V T 0 := by rw [hIF0]; exact mul_pos htfp heff
  have hTopp : 0 < smallTop V T 0 := hIFp.trans_le (le_max_left _ _)
  have hVB0 : 0 ≤ smallVB V T γ 0 := (abs_nonneg _).trans (le_max_left _ _)
  have hbase : 0 < V.discount * (4 * smallVB V T γ 0 / smallIF V T 0) + 1 := by
    have := mul_nonneg hβ.le (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hVB0) hIFp.le)
    linarith
  have hFlp : 0 < smallFl V T γ 0 :=
    lt_min (Real.rpow_pos_of_pos hbase _) (by linarith)
  have hm0 : 0 < γ * smallTop V T 0 ^ (-γ - 1) := mul_pos hγ (Real.rpow_pos_of_pos hTopp _)
  have hq0 : V.discount * smallR T 0 / 1 < 1 := by
    rw [hR0, div_one]
    nlinarith
  have hG0 : smallGain V T γ 0 = 0 := by simp [smallGain, hLip0]
  -- continuity
  have cid : ContinuousAt (fun α : ℝ => α) 0 := continuousAt_id
  have crpow : ∀ {b : ℝ}, 0 < b → ∀ {g : ℝ → ℝ}, ContinuousAt g 0 →
      ContinuousAt (fun α => b ^ g α) 0 :=
    fun hb _ hg => continuousAt_const.rpow hg (Or.inl hb.ne')
  have cR : ContinuousAt (smallR T) 0 := by
    unfold smallR
    exact continuousAt_const.add (((cid.mul continuousAt_const).mul
      (crpow hcap (cid.sub continuousAt_const))).mul (crpow hlabHi (continuousAt_const.sub cid)))
  have cWB : ContinuousAt (smallWB T) 0 := by
    unfold smallWB
    exact (((continuousAt_const.sub cid).mul continuousAt_const).mul (crpow hcapHi cid)).mul
      (crpow hlab cid.neg)
  have cIF : ContinuousAt (smallIF V T) 0 := by
    unfold smallIF
    exact ((((continuousAt_const.sub cid).mul continuousAt_const).mul (crpow hcap cid)).mul
      (crpow hlabHi cid.neg)).mul continuousAt_const
  have cLip : ContinuousAt (smallLip T) 0 := by
    unfold smallLip
    exact ((((cid.mul continuousAt_const).mul (crpow hlabHi (continuousAt_const.sub cid))).mul
      ((continuousAt_const.sub cid).mul
        (crpow hcap ((cid.sub continuousAt_const).sub continuousAt_const))))).max
      ((((continuousAt_const.sub cid).mul continuousAt_const).mul (crpow hlab cid.neg)).mul
        (cid.mul (crpow hcap (cid.sub continuousAt_const))))
  have cTop : ContinuousAt (smallTop V T) 0 := by
    unfold smallTop
    exact cIF.max ((cR.mul continuousAt_const).add (cWB.mul continuousAt_const))
  have cu : ∀ {g : ℝ → ℝ}, ContinuousAt g 0 → 0 < g 0 →
      ContinuousAt (fun α => crraUtility γ (g α)) 0 := fun hg hp =>
    ContinuousAt.comp (g := crraUtility γ)
      ((continuousOn_crraUtility γ).continuousAt (Ioi_mem_nhds hp)) hg
  have cVB : ContinuousAt (smallVB V T γ) 0 := by
    unfold smallVB
    exact ((cu cIF hIFp).div_const _).abs.max ((cu cTop hTopp).div_const _).abs
  have cFl : ContinuousAt (smallFl V T γ) 0 := by
    unfold smallFl
    exact (((continuousAt_const.mul ((continuousAt_const.mul cVB).div cIF hIFp.ne')).add
      continuousAt_const).rpow_const (Or.inl hbase.ne')).min (cIF.div_const _)
  have cD : ContinuousAt (fun α => smallFl V T γ α ^ (-γ)) 0 :=
    cFl.rpow_const (Or.inl hFlp.ne')
  have cMdu : ContinuousAt (fun α => γ * (smallFl V T γ α / 2) ^ (-γ - 1)) 0 :=
    continuousAt_const.mul ((cFl.div_const _).rpow_const (Or.inl (by positivity)))
  have cm : ContinuousAt (fun α => γ * smallTop V T α ^ (-γ - 1)) 0 :=
    continuousAt_const.mul (cTop.rpow_const (Or.inl hTopp.ne'))
  have cq : ContinuousAt (fun α => 1 - V.discount * smallR T α / 1) 0 :=
    continuousAt_const.sub ((continuousAt_const.mul cR).div_const _)
  have cAm : ContinuousAt (fun α => (V.discount * smallLip T α * smallFl V T γ α ^ (-γ) / 1
        + γ * (smallFl V T γ α / 2) ^ (-γ - 1) * smallLip T α
          * (V.assetCap + 0 + ∑ e, V.efficiency e)) / (1 - V.discount * smallR T α / 1)
      / (γ * smallTop V T α ^ (-γ - 1))) 0 := by
    refine ContinuousAt.div ?_ cm hm0.ne'
    refine ContinuousAt.div ?_ cq (by linarith)
    exact (((continuousAt_const.mul cLip).mul cD).div_const _).add
      ((cMdu.mul cLip).mul continuousAt_const)
  have cGain : ContinuousAt (smallGain V T γ) 0 := by
    unfold smallGain
    exact (cLip.mul continuousAt_const).add cAm
  exact ⟨hG0, hR0, cR, cGain⟩

/-- **At share zero**: `κ = 0` and `r = 1 − δ`, and all the formulas are continuous there. -/
theorem smallShare_limits :
    smallκ V T γ 0 = 0 ∧ smallRate V T γ 0 = 1 - T.depreciation ∧
      smallR T 0 = 1 - T.depreciation ∧ ContinuousAt (smallR T) 0 ∧
      ContinuousAt (smallκ V T γ) 0 ∧ ContinuousAt (smallRate V T γ) 0 := by
  obtain ⟨hG0, hR0, cR, cGain⟩ := smallGain_limits V T hγ
  have hLip0 : smallLip T 0 = 0 := by simp [smallLip]
  have hκ0 : smallκ V T γ 0 = 0 := by simp [smallκ, hLip0]
  have hδne : 1 - 1 * smallR T 0 ≠ 0 := by
    have : 1 - 1 * smallR T 0 = T.depreciation := by rw [hR0]; ring
    rw [this]
    exact hδ.ne'
  have cκ : ContinuousAt (smallκ V T γ) 0 := by
    change ContinuousAt (fun α => 1 * smallGain V T γ α / (1 - 1 * smallR T α)) 0
    exact (continuousAt_const.mul cGain).div
      (continuousAt_const.sub (continuousAt_const.mul cR)) hδne
  have cRate : ContinuousAt (smallRate V T γ) 0 := by
    unfold smallRate
    exact cR.add (cGain.div (continuousAt_const.sub cκ) (by rw [hκ0]; norm_num))
  have hRate0 : smallRate V T γ 0 = 1 - T.depreciation := by
    simp only [smallRate, hR0, hG0, hκ0, zero_div, add_zero]
  exact ⟨hκ0, hRate0, hR0, cR, cκ, cRate⟩

end Limit

/-! ### Small shares -/

variable [Nonempty Z] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)
  (hδ : 0 < T.depreciation)
include hγ hδ

/-- **Below some capital share `α₀ > 0`, both contraction conditions hold**: with weight `λ = 1`,
`κ < 1` and the law-of-motion rate `r < 1`. -/
theorem exists_smallShare :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ (h1 : α < 1)
      (hdisc : V.discount * (T.withShare α h0 h1).returnBound < 1)
      (hret : 1 * (T.withShare α h0 h1).returnBound < 1),
      (crraContractionHyp V (T.withShare α h0 h1) hγ 1 one_pos le_rfl hdisc hret).κ < 1 ∧
        (crraContractionHyp V (T.withShare α h0 h1) hγ 1 one_pos le_rfl hdisc hret).lawRate
          < 1 := by
  obtain ⟨hκ0, hr0, hR0, cR, cκ, cr⟩ := smallShare_limits V T hγ hδ
  have hβ1 := V.discount_lt_one
  have hβ0 := V.discount_pos
  have e1 : ∀ᶠ α in 𝓝 (0 : ℝ), smallκ V T γ α < 1 :=
    cκ.eventually (gt_mem_nhds (by rw [hκ0]; norm_num))
  have e2 : ∀ᶠ α in 𝓝 (0 : ℝ), smallRate V T γ α < 1 :=
    cr.eventually (gt_mem_nhds (by rw [hr0]; linarith))
  have e3 : ∀ᶠ α in 𝓝 (0 : ℝ), smallR T α < 1 :=
    cR.eventually (gt_mem_nhds (by rw [hR0]; linarith))
  have e4 : ∀ᶠ α in 𝓝 (0 : ℝ), V.discount * smallR T α < 1 :=
    have c4 : ContinuousAt (fun α => V.discount * smallR T α) 0 := continuousAt_const.mul cR
    c4.eventually (gt_mem_nhds (show V.discount * smallR T 0 < 1 by
      rw [hR0]; nlinarith [T.depreciation_le_one, T.depreciation_nonneg]))
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.1 (((e1.and e2).and e3).and e4)
  refine ⟨min ε 1, lt_min hε one_pos, fun α h0 hα => ?_⟩
  have hαε : dist α 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos h0]
    exact hα.trans_le (min_le_left _ _)
  obtain ⟨⟨⟨h1κ, h1r⟩, h1R⟩, h1β⟩ := hall hαε
  have h1 : α < 1 := hα.trans_le (min_le_right _ _)
  have hdisc : V.discount * (T.withShare α h0 h1).returnBound < 1 := h1β
  have hret : 1 * (T.withShare α h0 h1).returnBound < 1 := by
    rw [one_mul]
    exact h1R
  refine ⟨h1, hdisc, hret, ?_, ?_⟩
  · rw [crraContractionHyp_κ]
    exact h1κ
  · rw [crraContractionHyp_lawRate]
    exact h1r

/-- **For small capital shares, the CRRA economy has a unique sequential equilibrium and a law
of motion that contracts**: a `ContractionHyp` with `κ < 1` and `lawRate < 1`, so every result of
`LawContraction.lean` (fading memory, burn-in, explicit matching bounds, uniqueness of the
sequence-state equilibrium) applies. -/
theorem smallShare_contraction :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      (crraModel V (T.withShare α h0 hα) hγ).UniqueSequentialEquilibrium ∧
        ∃ H : (crraModel V (T.withShare α h0 hα) hγ).ContractionHyp, H.κ < 1 ∧ H.lawRate < 1 := by
  obtain ⟨α₀, hα₀, h⟩ := exists_smallShare V T hγ hδ
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, hdisc, hret, hκ, hr⟩ := h α h0 hα
  exact ⟨h1, (crraContractionHyp V (T.withShare α h0 h1) hγ 1 one_pos le_rfl hdisc hret)
    |>.uniqueSequentialEquilibrium hκ, _, hκ, hr⟩

end KrusellSmith

end LeanEconomics
