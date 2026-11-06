/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.MinimalMPC
import LeanEconomics.KrusellSmith.SlopeContraction
import LeanEconomics.KrusellSmith.EmploymentMarginals
import LeanEconomics.KrusellSmith.ComplementarityWitness

/-!
# Small capital shares with the minimal-MPC slope: depreciation may be zero

`SmallShare.lean` needs depreciation `δ > 0`, because the saving slope there is the gross return
bound `R̄ → 1 − δ` as the capital share vanishes. With the minimal-MPC slope of `MinimalMPC.lean`
the limit slope is `(β (1 − δ))^{1/γ} < 1` whatever `δ`, so the small-share theorems hold under

  `0 ≤ δ < 1`   and   `(β (1 − δ))^{1/γ} < 1 − δ`

(the second is automatic at `δ = 0`, and whenever `γ ≤ 1`).

* `KSInada.min_radius_le_consumptionOf`, `slackOf_iterate_radius`: the consumption floor is
  slack along the Bellman iterates for any Inada radius (here CRRA's explicit `crraRadius`).
* `CobbDouglas.returnLo`: a positive lower bound on the clamped gross return.
* `crraSavingSlope`: for CRRA and clamped Cobb–Douglas, **saving is `θ`-Lipschitz in assets** with
  `θ = R̄ (β R̄)^{1/γ} / R̲` along every path, when `(β R̄)^{1/γ} < R̲`.
* `crraSlopeContraction`: the `SlopeContraction` of the CRRA model.
* **`minMPC_smallShare`**: there is a share `α₀ > 0` below which `κ_θ < 1` and `r_θ < 1`.
* **`minMPC_smallShare_existsUnique_seqStateEquilibrium`**: under the Krusell–Smith employment
  design, **exactly one sequence-state equilibrium** for small shares;
  **`zeroDepreciation_smallShare_existsUnique_seqStateEquilibrium`**: the same with `δ = 0`, no
  further condition.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

/-! ### The consumption floor along the iterates, for any Inada radius -/

namespace KSInada

variable (P : KSInada Z E) {c : ℝ} (hc : 0 < c) (hcy : c ≤ P.incomeFloor) (z₀ : Z)
  (K : List Z → ℝ × ℝ)

/-- **Consumption against any bounded continuation with concave slices is at least
`min r (incomeFloor / 4)`** for any radius `r` below which marginal utility beats
`β · slopeConst + 1`. -/
theorem min_radius_le_consumptionOf {r : ℝ}
    (hr : ∀ c₁ c₂, c₁ ∈ Ioi 0 → c₁ < c₂ → c₂ ≤ r →
      (P.discount * P.slopeConst + 1) * (c₂ - c₁) ≤ P.utility c₂ - P.utility c₁)
    (w : (P.toModel c hc hcy).State →ᵇ ℝ)
    (hw : ∀ s, |w s| ≤ P.valueBound) (hwc : (P.toModel c hc hcy).ConcaveSlices w)
    (s : (P.toModel c hc hcy).State) :
    min r (P.incomeFloor / 4) ≤ (P.toModel c hc hcy).consumptionOf z₀ K w s := by
  have hMu : (P.toModel c hc hcy).utility = P.utility := rfl
  have hMd : (P.toModel c hc hcy).discount = P.discount := rfl
  have hyf := P.incomeFloor_pos
  have hβ : 0 ≤ P.discount := P.discount_pos.le
  by_contra hlt
  rw [not_le] at hlt
  set fl := min r (P.incomeFloor / 4) with hfl
  set p := (P.toModel c hc hcy).policyOf z₀ K w s with hpdef
  set cash := (P.toModel c hc hcy).cash z₀ K s with hcash
  have hcons : (P.toModel c hc hcy).consumptionOf z₀ K w s = cash - p := rfl
  rw [hcons] at hlt
  have hfδ : fl ≤ r := min_le_left _ _
  have hf4 : fl ≤ P.incomeFloor / 4 := min_le_right _ _
  have hpm := (P.toModel c hc hcy).policyOf_mem z₀ K w s
  have hcons' : c ≤ cash - p := le_sub_comm.1 (hpm.2.trans (min_le_right _ _))
  have hcashy : P.incomeFloor ≤ cash := P.incomeFloor_le_cash hc hcy z₀ K s
  have hpA : p ≤ P.assetCap := hpm.2.trans (min_le_left _ _)
  set h := fl - (cash - p) with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  have hlow : P.incomeFloor / 2 ≤ p - h := by rw [hh]; linarith
  have hfeas : p - h ∈ ((P.toModel c hc hcy).household z₀ K).feasible s :=
    ⟨by linarith, (by linarith : p - h ≤ p).trans hpm.2⟩
  have hdev := (P.toModel c hc hcy).le_bellman_contOf z₀ K w hfeas
  have hopt := (P.toModel c hc hcy).bellman_eq_contOf z₀ K w s
  rw [hopt, hcons] at hdev
  have hcfl : cash - (p - h) = fl := by rw [hh]; ring
  rw [hcfl, hMu, hMd] at hdev
  have hslope := P.contOf_sub_le hc hcy z₀ w hw hwc s hlow (by linarith) hpA
  rw [show p - (p - h) = h by ring] at hslope
  have hscaled := mul_le_mul_of_nonneg_left hslope hβ
  have hmarg := hr _ _ (mem_Ioi.2 (hc.trans_le hcons')) (by linarith) hfδ
  have he : fl - (cash - p) = h := by rw [hh]
  rw [he] at hmarg
  nlinarith [P.slopeConst_nonneg]

/-- **The floor is slack along every Bellman iterate**, when it is below `min r (incomeFloor/4)`
for an Inada radius `r`. -/
theorem slackOf_iterate_radius {r : ℝ}
    (hr : ∀ c₁ c₂, c₁ ∈ Ioi 0 → c₁ < c₂ → c₂ ≤ r →
      (P.discount * P.slopeConst + 1) * (c₂ - c₁) ≤ P.utility c₂ - P.utility c₁)
    (hcf : c < min r (P.incomeFloor / 4)) (n : ℕ) :
    (P.toModel c hc hcy).SlackOf z₀ K
      ((((P.toModel c hc hcy).household z₀ K).bellman)^[n] 0) := fun s =>
  hcf.trans_le (P.min_radius_le_consumptionOf hc hcy z₀ K hr _ (P.abs_iterate_le hc hcy z₀ K n)
    ((P.toModel c hc hcy).concaveSlices_iterate z₀ K n) s)

end KSInada

/-! ### A lower bound on the clamped gross return -/

namespace CobbDouglas

variable {Z : Type*} (T : CobbDouglas Z)

/-- A positive lower bound on the clamped gross return. -/
noncomputable def returnLo : ℝ :=
  1 - T.depreciation + T.share * T.tfpLo * T.capHi ^ (T.share - 1) * T.labLo ^ (1 - T.share)

theorem returnLo_pos : 0 < T.returnLo := by
  have h1 : 0 ≤ 1 - T.depreciation := sub_nonneg.2 T.depreciation_le_one
  have hcapHi : 0 < T.capHi := T.capLo_pos.trans_le T.capLo_le
  have h2 : 0 < T.share * T.tfpLo * T.capHi ^ (T.share - 1) * T.labLo ^ (1 - T.share) :=
    mul_pos (mul_pos (mul_pos T.share_pos T.tfpLo_pos) (Real.rpow_pos_of_pos hcapHi _))
      (Real.rpow_pos_of_pos T.labLo_pos _)
  unfold returnLo
  linarith

theorem returnLo_le_grossReturn (z : Z) (K L : ℝ) : T.returnLo ≤ T.grossReturn z K L := by
  have hK : T.capHi ^ (T.share - 1) ≤ T.clampCap K ^ (T.share - 1) :=
    Real.rpow_le_rpow_of_nonpos (T.clampCap_pos K) (T.clampCap_mem K).2
      (by linarith [T.share_lt_one])
  have hL : T.labLo ^ (1 - T.share) ≤ T.clampLab L ^ (1 - T.share) :=
    Real.rpow_le_rpow T.labLo_pos.le (T.clampLab_mem L).1 (by linarith [T.share_lt_one])
  have hcapHi : 0 < T.capHi := T.capLo_pos.trans_le T.capLo_le
  have hs := T.share_pos
  have h0K := Real.rpow_nonneg hcapHi.le (T.share - 1)
  have h0L := Real.rpow_nonneg T.labLo_pos.le (1 - T.share)
  have : T.share * T.tfpLo * T.capHi ^ (T.share - 1) * T.labLo ^ (1 - T.share)
      ≤ T.share * T.tfp z * T.clampCap K ^ (T.share - 1) * T.clampLab L ^ (1 - T.share) :=
    mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (T.tfpLo_le z) hs.le) hK h0K
      (mul_nonneg hs.le (T.tfp_pos z).le)) hL h0L
      (mul_nonneg (mul_nonneg hs.le (T.tfp_pos z).le) (Real.rpow_nonneg (T.clampCap_pos K).le _))
  unfold returnLo grossReturn
  linarith

end CobbDouglas

/-! ### The minimal-MPC slope for CRRA and clamped Cobb–Douglas -/

variable (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)

/-- **For CRRA and clamped Cobb–Douglas, saving is `θ`-Lipschitz in assets** with the minimal-MPC
slope `θ = R̄ (β R̄)^{1/γ} / R̲`, along every path, when `(β R̄)^{1/γ} < R̲`. -/
theorem crraSavingSlope (hA : 1 < (crraModel V T hγ).mpcGain γ T.returnLo) :
    (crraModel V T hγ).SavingSlope ((crraModel V T hγ).minMPCSlope γ T.returnLo) := by
  intro z₀ K a b l
  have hRlo : ∀ h, T.returnLo ≤ (crraModel V T hγ).returnAt z₀ K h := fun h =>
    T.returnLo_le_grossReturn _ _ _
  refine (crraModel V T hγ).abs_policy_sub_le_minMPC (crraSmoothUtility V T hγ) z₀ K hγ
    (fun _ _ => rfl) (fun h => T.returnLo_pos.trans_le (hRlo h)) T.returnLo_pos hRlo hA ?_ a b l
  exact (crraEconomy V T hγ).slackOf_iterate_radius (crraFloorLevel_half_pos V T hγ)
    (crraFloorLevel_half_le V T hγ) z₀ K (crraRadius_spec V T hγ)
    (half_lt_self (crraFloorLevel_pos V T hγ))

/-- **The `SlopeContraction` of the CRRA model** with the minimal-MPC slope. -/
noncomputable def crraSlopeContraction [Nonempty Z] (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) (hdisc : V.discount * T.returnBound < lam)
    (hA : 1 < (crraModel V T hγ).mpcGain γ T.returnLo)
    (hlθ : lam * (crraModel V T hγ).minMPCSlope γ T.returnLo < 1) :
    (crraModel V T hγ).SlopeContraction where
  B := crraContractionBase V T hγ lam hlam0 hlam1 hdisc
  θ := (crraModel V T hγ).minMPCSlope γ T.returnLo
  θ_nonneg := div_nonneg
    ((T.returnLo_pos.trans_le (T.returnLo_le_grossReturn (Classical.arbitrary Z) 0 0)).le.trans
      (T.grossReturn_le _ _ _)) (one_pos.trans hA).le
  slope := crraSavingSlope V T hγ hA
  lam_slope_lt := hlθ

/-! ### Small shares -/

section Formulas

variable (V : KSEnvironment Z E) (T : CobbDouglas Z) (γ : ℝ)

/-- The return lower bound at share `α`. -/
noncomputable def smallRlo (α : ℝ) : ℝ :=
  1 - T.depreciation + α * T.tfpLo * T.capHi ^ (α - 1) * T.labLo ^ (1 - α)

/-- The minimal-MPC slope at share `α`. -/
noncomputable def smallθ (α : ℝ) : ℝ :=
  smallR T α / (smallRlo T α / (V.discount * smallR T α) ^ (1 / γ))

/-- `κ_θ` at share `α`. -/
noncomputable def smallκθ (α : ℝ) : ℝ :=
  1 * smallGain V T γ α / (1 - 1 * smallθ V T γ α)

/-- `r_θ` at share `α`. -/
noncomputable def smallRateθ (α : ℝ) : ℝ :=
  smallθ V T γ α + smallGain V T γ α / (1 - smallκθ V T γ α)

end Formulas

variable [Nonempty Z]

section Identify

variable {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
  (hdisc : V.discount * (T.withShare α h0 h1).returnBound < 1)
  (hA : 1 < (crraModel V (T.withShare α h0 h1) hγ).mpcGain γ (T.withShare α h0 h1).returnLo)
  (hlθ : 1 * (crraModel V (T.withShare α h0 h1) hγ).minMPCSlope γ (T.withShare α h0 h1).returnLo
    < 1)

theorem crraSlopeContraction_κ :
    (crraSlopeContraction V (T.withShare α h0 h1) hγ 1 one_pos le_rfl hdisc hA hlθ).κ
      = smallκθ V T γ α := rfl

theorem crraSlopeContraction_rate :
    (crraSlopeContraction V (T.withShare α h0 h1) hγ 1 one_pos le_rfl hdisc hA hlθ).rate
      = smallRateθ V T γ α := rfl

end Identify

omit [Nonempty Z] in
include hγ in
/-- **At share zero**: `κ_θ = 0`, `r_θ = θ = (β (1 − δ))^{1/γ}`, and the formulas are continuous. -/
theorem minMPC_limits (hδ1 : T.depreciation < 1) :
    smallκθ V T γ 0 = 0 ∧ smallRateθ V T γ 0 = (V.discount * (1 - T.depreciation)) ^ (1 / γ) ∧
      smallθ V T γ 0 = (V.discount * (1 - T.depreciation)) ^ (1 / γ) ∧
      smallR T 0 = 1 - T.depreciation ∧ smallRlo T 0 = 1 - T.depreciation ∧
      ContinuousAt (smallR T) 0 ∧ ContinuousAt (smallRlo T) 0 ∧
      ContinuousAt (smallθ V T γ) 0 ∧ ContinuousAt (smallκθ V T γ) 0 ∧
      ContinuousAt (smallRateθ V T γ) 0 := by
  obtain ⟨hG0, hR0, cR, cG⟩ := smallGain_limits V T hγ
  have hδ : 0 < 1 - T.depreciation := sub_pos.2 hδ1
  have hβ := V.discount_pos
  have hβ1 := V.discount_lt_one
  have hcapHi : 0 < T.capHi := T.capLo_pos.trans_le T.capLo_le
  have hRlo0 : smallRlo T 0 = 1 - T.depreciation := by simp [smallRlo]
  have hβR : 0 < V.discount * smallR T 0 := by rw [hR0]; exact mul_pos hβ hδ
  have hB : 0 < (V.discount * smallR T 0) ^ (1 / γ) := Real.rpow_pos_of_pos hβR _
  have hA0 : 0 < smallRlo T 0 / (V.discount * smallR T 0) ^ (1 / γ) := by
    rw [hRlo0]; exact div_pos hδ hB
  have hθ0 : smallθ V T γ 0 = (V.discount * (1 - T.depreciation)) ^ (1 / γ) := by
    simp only [smallθ, hR0, hRlo0]
    field_simp
  have hθ1 : smallθ V T γ 0 < 1 := by
    rw [hθ0]
    exact Real.rpow_lt_one (mul_pos hβ hδ).le
      (by nlinarith [T.depreciation_nonneg]) (by positivity)
  have hκ0 : smallκθ V T γ 0 = 0 := by simp [smallκθ, hG0]
  have hr0 : smallRateθ V T γ 0 = (V.discount * (1 - T.depreciation)) ^ (1 / γ) := by
    simp [smallRateθ, hG0, hκ0, hθ0]
  have cid : ContinuousAt (fun α : ℝ => α) 0 := continuousAt_id
  have crpow : ∀ {b : ℝ}, 0 < b → ∀ {g : ℝ → ℝ}, ContinuousAt g 0 →
      ContinuousAt (fun α => b ^ g α) 0 :=
    fun hb _ hg => continuousAt_const.rpow hg (Or.inl hb.ne')
  have cRlo : ContinuousAt (smallRlo T) 0 := by
    unfold smallRlo
    exact continuousAt_const.add (((cid.mul continuousAt_const).mul
      (crpow hcapHi (cid.sub continuousAt_const))).mul
        (crpow T.labLo_pos (continuousAt_const.sub cid)))
  have cθ : ContinuousAt (smallθ V T γ) 0 := by
    unfold smallθ
    exact cR.div (cRlo.div ((continuousAt_const.mul cR).rpow_const (Or.inl hβR.ne'))
      hB.ne') hA0.ne'
  have cκ : ContinuousAt (smallκθ V T γ) 0 := by
    unfold smallκθ
    exact (continuousAt_const.mul cG).div (continuousAt_const.sub (continuousAt_const.mul cθ))
      (by linarith)
  have cr : ContinuousAt (smallRateθ V T γ) 0 := by
    unfold smallRateθ
    exact cθ.add (cG.div (continuousAt_const.sub cκ) (by rw [hκ0]; norm_num))
  exact ⟨hκ0, hr0, hθ0, hR0, hRlo0, cR, cRlo, cθ, cκ, cr⟩

/-- **Below some capital share `α₀ > 0`, the minimal-MPC contraction conditions hold**:
`κ_θ < 1` and `r_θ < 1`, for `0 ≤ δ < 1` with `(β (1 − δ))^{1/γ} < 1 − δ`. -/
theorem minMPC_smallShare (hδ1 : T.depreciation < 1)
    (hgap : (V.discount * (1 - T.depreciation)) ^ (1 / γ) < 1 - T.depreciation) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃ S : (crraModel V (T.withShare α h0 hα) hγ).SlopeContraction, S.κ < 1 ∧ S.rate < 1 := by
  obtain ⟨hκ0, hr0, hθ0, hR0, hRlo0, cR, cRlo, cθ, cκ, cr⟩ := minMPC_limits V T hγ hδ1
  have hβ := V.discount_pos
  have hβ1 := V.discount_lt_one
  have hδ : 0 < 1 - T.depreciation := sub_pos.2 hδ1
  have hβRpos : 0 < V.discount * smallR T 0 := by rw [hR0]; exact mul_pos hβ hδ
  have hrate1 : (V.discount * (1 - T.depreciation)) ^ (1 / γ) < 1 :=
    Real.rpow_lt_one (mul_pos hβ hδ).le (by nlinarith [T.depreciation_nonneg]) (by positivity)
  have cA : ContinuousAt (fun α => smallRlo T α / (V.discount * smallR T α) ^ (1 / γ)) 0 :=
    cRlo.div ((continuousAt_const.mul cR).rpow_const (Or.inl hβRpos.ne'))
      (Real.rpow_pos_of_pos hβRpos _).ne'
  have hA0 : 1 < smallRlo T 0 / (V.discount * smallR T 0) ^ (1 / γ) := by
    rw [hRlo0, hR0, one_lt_div (Real.rpow_pos_of_pos (mul_pos hβ hδ) _)]
    exact hgap
  have e1 : ∀ᶠ α in 𝓝 (0 : ℝ), smallκθ V T γ α < 1 :=
    cκ.eventually (gt_mem_nhds (by rw [hκ0]; norm_num))
  have e2 : ∀ᶠ α in 𝓝 (0 : ℝ), smallRateθ V T γ α < 1 :=
    cr.eventually (gt_mem_nhds (by rw [hr0]; exact hrate1))
  have e3 : ∀ᶠ α in 𝓝 (0 : ℝ), smallθ V T γ α < 1 :=
    cθ.eventually (gt_mem_nhds (by rw [hθ0]; exact hrate1))
  have c4 : ContinuousAt (fun α => V.discount * smallR T α) 0 := continuousAt_const.mul cR
  have e4 : ∀ᶠ α in 𝓝 (0 : ℝ), V.discount * smallR T α < 1 :=
    c4.eventually (gt_mem_nhds (show V.discount * smallR T 0 < 1 by
      rw [hR0]; nlinarith [T.depreciation_nonneg]))
  have e5 : ∀ᶠ α in 𝓝 (0 : ℝ), 1 < smallRlo T α / (V.discount * smallR T α) ^ (1 / γ) :=
    cA.eventually (lt_mem_nhds hA0)
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.1 ((((e1.and e2).and e3).and e4).and e5)
  refine ⟨min ε 1, lt_min hε one_pos, fun α h0 hα => ?_⟩
  have hαε : dist α 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos h0]
    exact hα.trans_le (min_le_left _ _)
  obtain ⟨⟨⟨⟨h1κ, h1r⟩, h1θ⟩, h1β⟩, h1A⟩ := hall hαε
  have h1 : α < 1 := hα.trans_le (min_le_right _ _)
  have hdisc : V.discount * (T.withShare α h0 h1).returnBound < 1 := h1β
  have hA : 1 < (crraModel V (T.withShare α h0 h1) hγ).mpcGain γ
      (T.withShare α h0 h1).returnLo := h1A
  have hlθ : 1 * (crraModel V (T.withShare α h0 h1) hγ).minMPCSlope γ
      (T.withShare α h0 h1).returnLo < 1 := by
    rw [one_mul]
    exact h1θ
  refine ⟨h1, crraSlopeContraction V (T.withShare α h0 h1) hγ 1 one_pos le_rfl hdisc hA hlθ,
    ?_, ?_⟩
  · rw [crraSlopeContraction_κ]
    exact h1κ
  · rw [crraSlopeContraction_rate]
    exact h1r

variable [Nonempty E] (D : EmploymentDesign V.idioProb)

include D in
/-- **Exactly one sequence-state equilibrium for small capital shares**, with the minimal-MPC
slope: CRRA utility, clamped Cobb–Douglas prices, `0 ≤ δ < 1` with `(β (1 − δ))^{1/γ} < 1 − δ`,
and the Krusell–Smith employment design. -/
theorem minMPC_smallShare_existsUnique_seqStateEquilibrium (hδ1 : T.depreciation < 1)
    (hgap : (V.discount * (1 - T.depreciation)) ^ (1 / γ) < 1 - T.depreciation) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃! μ : History Z → ProbabilityMeasure (crraModel V (T.withShare α h0 hα) hγ).AState,
        (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ := by
  obtain ⟨α₀, hα₀, h⟩ := minMPC_smallShare V T hγ hδ1 hgap
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, S, hκ, hr⟩ := h α h0 hα
  refine ⟨h1, ?_⟩
  obtain ⟨μ, hμ⟩ := (crraModel V (T.withShare α h0 h1) hγ).exists_seqStateEquilibrium
  refine ⟨μ, hμ, fun μ' hμ' => ?_⟩
  have D' : EmploymentDesign (crraModel V (T.withShare α h0 h1) hγ).idioProb := D
  exact (S.eq_of_rate_lt_one hκ hμ hr hμ' fun ω => by
    rw [hμ.initMass_eq_design D' ω, hμ'.initMass_eq_design D' ω]).symm

include D in
/-- **Zero depreciation**: exactly one sequence-state equilibrium for small capital shares, with
no further condition. -/
theorem zeroDepreciation_smallShare_existsUnique_seqStateEquilibrium (hδ : T.depreciation = 0) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃! μ : History Z → ProbabilityMeasure (crraModel V (T.withShare α h0 hα) hγ).AState,
        (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ := by
  refine minMPC_smallShare_existsUnique_seqStateEquilibrium V T hγ D (by rw [hδ]; norm_num) ?_
  rw [hδ, sub_zero, mul_one]
  exact Real.rpow_lt_one V.discount_pos.le V.discount_lt_one (by positivity)

end KrusellSmith

end LeanEconomics
