/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.DebtorRate
import LeanEconomics.Equilibrium.InvariantRegion

/-!
# The slack Euler chain: the term the elasticity condition threw away

`ElasticityReduction` proves that saving rises with the rate at `(a, z)` from four Euler
inequalities and the elasticity condition `R₁ u'(c₁(b, z')) ≤ R₂ u'(c₂(b, z'))` at `b = a'₁(a, z)`.
The chain starts from the supposition `a'₂ < a'₁`, which gives `c₂(a) > c₁(a) + (r₂ - r₁) a`,
and then uses only `c₂(a) > c₁(a)`. The extra interest income `(r₂ - r₁) a` is thrown away.

Keeping it, the chain closes under the weaker **slack elasticity condition**

  `R₁ u'(c₁(b, z')) · u'(c₁(a, z) + (r₂ - r₁) a) ≤ R₂ u'(c₂(b, z')) · u'(c₁(a, z))`,

the old condition multiplied by the factor `u'(c₁(a) + Δr·a)/u'(c₁(a)) < 1`
(`euler_chain_absurd_slack'`, `policy_le_policy_withRate_of_slack_at`). For CRRA it reads

  `(c₂(b)/c₁(b))^γ ≤ (R₂/R₁) · (1 + Δr · a / c₁(a))^γ`

(`crra_slack_elasticity_iff`).

## Why this matters at `γ > 1`

The old condition FAILS at high wealth (`crra_elasticity_fails_of_asymptotic_mpc`): with Ma–Toda's
asymptotic slopes `L_i = κ(R_i) R_i = R_i - Þ_i`, `Þ_i = (βR_i)^{1/γ}`, the left side tends to
`(L₂/L₁)^γ > R₂/R₁` when `γ > 1`. The slack factor at high wealth tends to
`(1 + Δr/L₁)^γ = ((R₂ - Þ₁)/(R₁ - Þ₁))^γ`, and

  `((R₂ - Þ₂)/(R₁ - Þ₁))^γ ≤ (R₂/R₁) · ((R₂ - Þ₁)/(R₁ - Þ₁))^γ`

holds for EVERY `γ`, with room to spare, simply because `Þ₁ ≤ Þ₂`
(`crra_slack_elasticity_of_patience`, `crra_slack_elasticity_holds_of_asymptotic_mpc`). In
logarithmic terms per unit of rate gap the margin is exactly `1/(κ₁R₁)`, about `25` at
Aiyagari's numbers. So the slack condition is true where the old one was false; at low wealth
the two coincide and the human-wealth effect makes both hold. What remains, and is NOT done
here, is to prove the slack condition from primitives on the whole support: that needs the
ratio `c₂/c₁` to relative precision of order `Δr`, uniformly in wealth.

The reduction theorems `equilibriumRate_unique_of_slack`, `equilibriumRate_unique_of_slack_on`
and their CRRA forms are `ElasticityReduction` and `InvariantRegion` with the slack condition in
place of the elasticity condition.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

/-! ### CRRA: the slack condition, and its behaviour at high wealth -/

/-- For CRRA the slack elasticity condition
`R₁ c₁'^{-γ} (c + g)^{-γ} ≤ R₂ c₂'^{-γ} c^{-γ}` says `(c₂'/c₁')^γ ≤ (R₂/R₁)((c + g)/c)^γ`. -/
theorem crra_slack_elasticity_iff {γ R₁ R₂ c₁ c₂ c g : ℝ} (hR₁ : 0 < R₁)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc : 0 < c) (hg : 0 ≤ g) :
    R₁ * c₁ ^ (-γ) * (c + g) ^ (-γ) ≤ R₂ * c₂ ^ (-γ) * c ^ (-γ)
      ↔ (c₂ / c₁) ^ γ ≤ R₂ / R₁ * ((c + g) / c) ^ γ := by
  have hcg : 0 < c + g := by linarith
  have hA : 0 < c₁ ^ γ := Real.rpow_pos_of_pos hc₁ _
  have hB : 0 < c₂ ^ γ := Real.rpow_pos_of_pos hc₂ _
  have hC : 0 < c ^ γ := Real.rpow_pos_of_pos hc _
  have hD : 0 < (c + g) ^ γ := Real.rpow_pos_of_pos hcg _
  rw [Real.rpow_neg hc₁.le, Real.rpow_neg hc₂.le, Real.rpow_neg hc.le, Real.rpow_neg hcg.le,
    Real.div_rpow hc₂.le hc₁.le, Real.div_rpow hcg.le hc.le, div_mul_div_comm,
    div_le_div_iff₀ hA (mul_pos hR₁ hC)]
  rw [show R₁ * (c₁ ^ γ)⁻¹ * ((c + g) ^ γ)⁻¹ = R₁ / (c₁ ^ γ * (c + g) ^ γ) by
    rw [div_eq_mul_inv, mul_inv, mul_assoc]]
  rw [show R₂ * (c₂ ^ γ)⁻¹ * (c ^ γ)⁻¹ = R₂ / (c₂ ^ γ * c ^ γ) by
    rw [div_eq_mul_inv, mul_inv, mul_assoc]]
  rw [div_le_div_iff₀ (mul_pos hA hD) (mul_pos hB hC)]
  constructor <;> intro h <;> linarith

/-- **In the homogeneous limit the slack condition holds for every `γ`.** With
`L_i = R_i - Þ_i` the asymptotic slopes and `Þ₁ ≤ Þ₂`, the left side `((R₂ - Þ₂)/(R₁ - Þ₁))^γ`
is at most `((R₂ - Þ₁)/(R₁ - Þ₁))^γ`, which is the slack factor, and `R₂/R₁ ≥ 1` is spare. -/
theorem crra_slack_elasticity_of_patience {γ R₁ R₂ Þ₁ Þ₂ : ℝ} (hγ : 0 ≤ γ) (hR₁ : 0 < R₁)
    (hR : R₁ ≤ R₂) (hÞ : Þ₁ ≤ Þ₂) (h₁ : Þ₁ < R₁) (h₂ : Þ₂ < R₂) :
    ((R₂ - Þ₂) / (R₁ - Þ₁)) ^ γ ≤ R₂ / R₁ * ((R₂ - Þ₁) / (R₁ - Þ₁)) ^ γ := by
  have hden : 0 < R₁ - Þ₁ := by linarith
  have hX : 0 ≤ (R₂ - Þ₂) / (R₁ - Þ₁) := div_nonneg (by linarith) hden.le
  have hXY : (R₂ - Þ₂) / (R₁ - Þ₁) ≤ (R₂ - Þ₁) / (R₁ - Þ₁) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  have hpow := Real.rpow_le_rpow hX hXY hγ
  have hone : 1 ≤ R₂ / R₁ := by rw [le_div_iff₀ hR₁]; linarith
  calc ((R₂ - Þ₂) / (R₁ - Þ₁)) ^ γ ≤ ((R₂ - Þ₁) / (R₁ - Þ₁)) ^ γ := hpow
    _ ≤ R₂ / R₁ * ((R₂ - Þ₁) / (R₁ - Þ₁)) ^ γ :=
      le_mul_of_one_le_left (Real.rpow_nonneg (div_nonneg (by linarith) hden.le) _) hone

/-- The strict form, for a strictly higher rate. -/
theorem crra_slack_elasticity_of_patience_lt {γ R₁ R₂ Þ₁ Þ₂ : ℝ} (hγ : 0 < γ) (hR₁ : 0 < R₁)
    (hR : R₁ ≤ R₂) (hÞ : Þ₁ < Þ₂) (h₁ : Þ₁ < R₁) (h₂ : Þ₂ < R₂) :
    ((R₂ - Þ₂) / (R₁ - Þ₁)) ^ γ < R₂ / R₁ * ((R₂ - Þ₁) / (R₁ - Þ₁)) ^ γ := by
  have hden : 0 < R₁ - Þ₁ := by linarith
  have hX : 0 ≤ (R₂ - Þ₂) / (R₁ - Þ₁) := div_nonneg (by linarith) hden.le
  have hXY : (R₂ - Þ₂) / (R₁ - Þ₁) < (R₂ - Þ₁) / (R₁ - Þ₁) :=
    div_lt_div_of_pos_right (by linarith) hden
  have hpow := Real.rpow_lt_rpow hX hXY hγ
  have hone : 1 ≤ R₂ / R₁ := by rw [le_div_iff₀ hR₁]; linarith
  calc ((R₂ - Þ₂) / (R₁ - Þ₁)) ^ γ < ((R₂ - Þ₁) / (R₁ - Þ₁)) ^ γ := hpow
    _ ≤ R₂ / R₁ * ((R₂ - Þ₁) / (R₁ - Þ₁)) ^ γ :=
      le_mul_of_one_le_left (Real.rpow_nonneg (div_nonneg (by linarith) hden.le) _) hone

/-- **With the minimal-MPC slopes.** `L_i = κ(R_i) R_i = R_i - (β R_i)^{1/γ}` (by
`one_sub_minMPC_mul`), and the slack factor at high wealth is `(1 + Δr/L₁)^γ`:
`(L₂/L₁)^γ < (R₂/R₁) · ((L₁ + (r₂ - r₁))/L₁)^γ` whenever `r₁ < r₂`. -/
theorem crra_slack_elasticity_of_minMPC {γ β r₁ r₂ : ℝ} (hγ : 0 < γ) (hβ : 0 < β)
    (hR₁ : 0 < 1 + r₁) (hr : r₁ < r₂)
    (hκ₁ : (β * (1 + r₁)) ^ (1 / γ) < 1 + r₁) (hκ₂ : (β * (1 + r₂)) ^ (1 / γ) < 1 + r₂) :
    (((1 + r₂) - (β * (1 + r₂)) ^ (1 / γ)) / ((1 + r₁) - (β * (1 + r₁)) ^ (1 / γ))) ^ γ
      < (1 + r₂) / (1 + r₁)
        * ((((1 + r₁) - (β * (1 + r₁)) ^ (1 / γ)) + (r₂ - r₁))
          / ((1 + r₁) - (β * (1 + r₁)) ^ (1 / γ))) ^ γ := by
  have hÞ : (β * (1 + r₁)) ^ (1 / γ) < (β * (1 + r₂)) ^ (1 / γ) :=
    Real.rpow_lt_rpow (by positivity) (by nlinarith) (by positivity)
  have := crra_slack_elasticity_of_patience_lt hγ hR₁ (by linarith) hÞ hκ₁ hκ₂
  convert this using 4
  ring

/-- **The slack condition holds at high wealth whenever the asymptotic slopes satisfy the
homogeneous inequality**: along `a ↦ b a` (tomorrow's assets), if `c₂(b a)/c₁(b a) → L₂/L₁` and
`c₁(a)/a → L₁`, and `(L₂/L₁)^γ < (R₂/R₁)((L₁ + Δ)/L₁)^γ`, then eventually
`(c₂(b a)/c₁(b a))^γ ≤ (R₂/R₁)(1 + Δ a/c₁(a))^γ`. The mirror image of
`crra_elasticity_fails_of_asymptotic_mpc`. -/
theorem crra_slack_elasticity_holds_of_asymptotic_mpc {γ R₁ R₂ L₁ L₂ Δ : ℝ} {c₁ c₂ b : ℝ → ℝ}
    (hγ : 0 < γ) (hL₁ : 0 < L₁)
    (h₁ : Tendsto (fun a => c₁ a / a) atTop (𝓝 L₁))
    (hb : Tendsto (fun a => c₂ (b a) / c₁ (b a)) atTop (𝓝 (L₂ / L₁)))
    (hgap : (L₂ / L₁) ^ γ < R₂ / R₁ * ((L₁ + Δ) / L₁) ^ γ) :
    ∀ᶠ a in atTop, (c₂ (b a) / c₁ (b a)) ^ γ ≤ R₂ / R₁ * (1 + Δ * a / c₁ a) ^ γ := by
  have hinv : Tendsto (fun a => (c₁ a / a)⁻¹) atTop (𝓝 L₁⁻¹) := h₁.inv₀ hL₁.ne'
  have hfac : Tendsto (fun a => 1 + Δ * a / c₁ a) atTop (𝓝 ((L₁ + Δ) / L₁)) := by
    have h := (hinv.const_mul Δ).const_add 1
    rw [show 1 + Δ * L₁⁻¹ = (L₁ + Δ) / L₁ by field_simp] at h
    refine h.congr fun a => ?_
    rw [inv_div, mul_div_assoc]
  have hL := hb.rpow_const (Or.inr hγ.le)
  have hR := (hfac.rpow_const (Or.inr hγ.le)).const_mul (R₂ / R₁)
  exact (hL.eventually_lt hR hgap).mono fun a h => h.le

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]

/-! ### The chain with a threshold -/

section GeneralFloor

variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **The Euler chain with a threshold `θ`.** As `euler_chain_absurd'`, but the strict
consumption gap is recorded as `u'(c₂(a₂)) < θ`, and the elasticity condition at `b = a'₁(a₁, z)`
is weakened by the factor `θ / u'(c₁(a₁))`. -/
theorem euler_chain_absurd_slack' {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₂ h₂).policy s < assetCap)
    {a₁ a₂ : ℝ} (ha₁ : a₁ ∈ Icc assetFloor assetCap) (ha₂ : a₂ ∈ Icc assetFloor assetCap) (z : Z)
    {θ : ℝ}
    (helas : ∀ z' : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z))) * θ
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z)))
          * du ((P.withRate r₁ h₁).consumptionFn z a₁))
    (hAlt : (P.withRate r₂ h₂).policy (a₂, z) < (P.withRate r₁ h₁).policy (a₁, z))
    (hθ : du ((P.withRate r₂ h₂).consumptionFn z a₂) < θ) : False := by
  classical
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hA₁mem : (P.withRate r₁ h₁).policy (a₁, z) ∈ Icc assetFloor assetCap :=
    (P.withRate r₁ h₁).policy_mem_region _
  have hA₂mem : (P.withRate r₂ h₂).policy (a₂, z) ∈ Icc assetFloor assetCap :=
    (P.withRate r₂ h₂).policy_mem_region _
  have hc₁pos : 0 < (P.withRate r₁ h₁).consumptionFn z a₁ :=
    (P.withRate r₁ h₁).consumptionFn_pos hpc₁ ha₁ z
  have hc₂pos : 0 < (P.withRate r₂ h₂).consumptionFn z a₂ :=
    (P.withRate r₂ h₂).consumptionFn_pos hpc₂ ha₂ z
  have hd₁pos : 0 < du ((P.withRate r₁ h₁).consumptionFn z a₁) := hdupos _ hc₁pos
  have hθpos : 0 < θ := lt_trans (hdupos _ hc₂pos) hθ
  have hc₁' : ∀ z' : Z,
      0 < (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z)) :=
    fun z' => (P.withRate r₁ h₁).consumptionFn_pos hpc₁ hA₁mem z'
  have hc₂' : ∀ z' : Z,
      0 < (P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z)) :=
    fun z' => (P.withRate r₂ h₂).consumptionFn_pos hpc₂ hA₂mem z'
  -- Euler at the higher rate: room under the cap
  have hbv₂ := (P.withRate r₂ h₂).toExtended.bellman_valueFunction
  have hroom₂ : (P.withRate r₂ h₂).policy (a₂, z) < (P.withRate r₂ h₂).maxSaving (a₂, z) := by
    rw [maxSaving_eq]
    refine lt_min (hslack₂ _ ha₂) ?_
    have := hc₂pos
    simp only [consumptionFn, consumption] at this
    linarith
  have hE₂ := (P.withRate r₂ h₂).euler_le (v := (P.withRate r₂ h₂).toExtended.valueFunction)
    (z := z) (a := a₂) (A := (P.withRate r₂ h₂).policy (a₂, z))
    (du := du ((P.withRate r₂ h₂).consumptionFn z a₂))
    (du' := fun z' => du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z))))
    ha₂ (by rw [hbv₂]; exact congrFun (P.withRate r₂ h₂).policyOf_valueFunction _) hroom₂
    (by rw [hbv₂]; exact hc₂pos) (by rw [hbv₂]; exact hderiv _ hc₂pos)
    (fun z' => hc₂' z') (fun z' => hderiv _ (hc₂' z'))
  -- Euler at the lower rate: room above the floor
  have hbv₁ := (P.withRate r₁ h₁).toExtended.bellman_valueFunction
  have hA₁pos : assetFloor < (P.withRate r₁ h₁).policy (a₁, z) := lt_of_le_of_lt hA₂mem.1 hAlt
  have hslackA₁ : ∀ z' : Z, (P.withRate r₁ h₁).policyOf (P.withRate r₁ h₁).toExtended.valueFunction
      ((P.withRate r₁ h₁).policy (a₁, z), z')
      < (P.withRate r₁ h₁).maxSaving ((P.withRate r₁ h₁).policy (a₁, z), z') := by
    intro z'
    rw [(P.withRate r₁ h₁).policyOf_valueFunction, maxSaving_eq]
    refine lt_min (hslack₁ _ hA₁mem) ?_
    have := hc₁' z'
    simp only [consumptionFn, consumption] at this
    linarith
  have hE₁ := (P.withRate r₁ h₁).euler_ge (v := (P.withRate r₁ h₁).toExtended.valueFunction)
    (z := z) (a := a₁) (A := (P.withRate r₁ h₁).policy (a₁, z))
    (du := du ((P.withRate r₁ h₁).consumptionFn z a₁))
    (du' := fun z' => du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z))))
    ha₁ (by rw [hbv₁]; exact congrFun (P.withRate r₁ h₁).policyOf_valueFunction _) hA₁pos hslackA₁
    (by rw [hbv₁]; exact hc₁pos) (by rw [hbv₁]; exact hderiv _ hc₁pos)
    (fun z' => hc₁' z') (fun z' => hderiv _ (hc₁' z'))
  simp only [IncomeFluctuation.withRate_discount, IncomeFluctuation.withRate_interest,
    IncomeFluctuation.withRate_transitionMatrix] at hE₁ hE₂
  -- consumption rises with assets
  have hdu₂ : ∀ z' : Z,
      du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z)))
        ≤ du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z))) := by
    intro z'
    have hmono := (P.withRate r₂ h₂).consumptionFn_mono (z := z') hA₂mem hA₁mem hAlt.le
    exact hanti.antitoneOn (mem_Ioi.mpr (hc₂' z'))
      (mem_Ioi.mpr ((P.withRate r₂ h₂).consumptionFn_pos hpc₂ hA₁mem z')) hmono
  -- the summed slack condition, with tomorrow's consumption moved to economy two's own policy
  set S₁ := ∑ z', P.transitionMatrix z z'
    * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z))) with hS₁
  set S₂ := ∑ z', P.transitionMatrix z z'
    * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z))) with hS₂
  set d₁ := du ((P.withRate r₁ h₁).consumptionFn z a₁) with hd₁
  have hsum : (1 + r₁) * S₁ * θ ≤ (1 + r₂) * S₂ * d₁ := by
    rw [hS₁, hS₂, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun z' _ => ?_
    have hπ := P.transitionMatrix_nonneg z z'
    have h1 := helas z'
    have h2 : (1 + r₂)
          * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z))) * d₁
        ≤ (1 + r₂)
          * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z))) * d₁ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdu₂ z') hR₂.le) hd₁pos.le
    calc (1 + r₁) * (P.transitionMatrix z z'
            * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z)))) * θ
        = P.transitionMatrix z z' * ((1 + r₁)
            * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a₁, z)))
            * θ) := by
          ring
      _ ≤ P.transitionMatrix z z' * ((1 + r₂)
            * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z))) * d₁) :=
          mul_le_mul_of_nonneg_left (le_trans h1 h2) hπ
      _ = (1 + r₂) * (P.transitionMatrix z z'
            * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a₂, z))))
            * d₁ := by
          ring
  -- close the chain
  have hA := mul_le_mul_of_nonneg_left hE₁ hθpos.le
  have hB := mul_le_mul_of_nonneg_left hsum hβ
  have hC := mul_le_mul_of_nonneg_right hE₂ hd₁pos.le
  have hD := mul_lt_mul_of_pos_right hθ hd₁pos
  nlinarith [hA, hB, hC, hD]

/-- **Theorem 1 with borrowing, from the slack condition.** The elasticity condition at
`b = a'₁(a, z)` is weakened by the factor `u'(c₁(a) + Δr·max 0 a)/u'(c₁(a))`; the conclusion is
the debtor's loss term of `policy_le_policy_add_withRate_of_marginal_at`. -/
theorem policy_le_policy_add_withRate_of_slack_at {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁)
    (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂) {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₂ h₂).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z)
    (helas : ∀ z' : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
          * du ((P.withRate r₁ h₁).consumptionFn z a + (r₂ - r₁) * max 0 a)
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
          * du ((P.withRate r₁ h₁).consumptionFn z a)) :
    (P.withRate r₁ h₁).policy (a, z)
      ≤ (P.withRate r₂ h₂).policy (a, z) + (r₂ - r₁) * max 0 (-a) := by
  by_contra hcon
  push Not at hcon
  have hloss : 0 ≤ (r₂ - r₁) * max 0 (-a) := mul_nonneg (by linarith) (le_max_left _ _)
  have hg : 0 ≤ (r₂ - r₁) * max 0 a := mul_nonneg (by linarith) (le_max_left _ _)
  have hAlt : (P.withRate r₂ h₂).policy (a, z) < (P.withRate r₁ h₁).policy (a, z) := by
    linarith
  have hc₁pos : 0 < (P.withRate r₁ h₁).consumptionFn z a :=
    (P.withRate r₁ h₁).consumptionFn_pos hpc₁ ha z
  have hc₂pos : 0 < (P.withRate r₂ h₂).consumptionFn z a :=
    (P.withRate r₂ h₂).consumptionFn_pos hpc₂ ha z
  have hkey : a + max 0 (-a) = max 0 a := by
    rcases le_total 0 a with h | h
    · rw [max_eq_left (neg_nonpos.2 h), max_eq_right h]; ring
    · rw [max_eq_right (neg_nonneg.2 h), max_eq_left h]; ring
  have hclt : (P.withRate r₁ h₁).consumptionFn z a + (r₂ - r₁) * max 0 a
      < (P.withRate r₂ h₂).consumptionFn z a := by
    rw [P.consumptionFn_withRate_eq h₁ z ha, P.consumptionFn_withRate_eq h₂ z ha, ← hkey]
    nlinarith
  have hθ : du ((P.withRate r₂ h₂).consumptionFn z a)
      < du ((P.withRate r₁ h₁).consumptionFn z a + (r₂ - r₁) * max 0 a) :=
    hanti (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr hc₂pos) hclt
  exact P.euler_chain_absurd_slack' h₁ h₂ hderiv hanti hdupos hpc₁ hpc₂ hslack₁ hslack₂ ha ha z
    helas hAlt hθ

end GeneralFloor

/-! ### Zero borrowing limit -/

section ZeroFloor

variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **Saving rises with the rate under the slack elasticity condition** at `b = a'₁(a, z)`:
`R₁ u'(c₁(b,z')) u'(c₁(a,z) + Δr·a) ≤ R₂ u'(c₂(b,z')) u'(c₁(a,z))`. -/
theorem policy_le_policy_withRate_of_slack_at {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁)
    (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂) {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₂ h₂).policy s < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (helas : ∀ z' : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
          * du ((P.withRate r₁ h₁).consumptionFn z a + (r₂ - r₁) * a)
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
          * du ((P.withRate r₁ h₁).consumptionFn z a)) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy (a, z) := by
  have hmax : max 0 a = a := max_eq_right ha.1
  have hmax' : max 0 (-a) = 0 := max_eq_left (neg_nonpos.2 ha.1)
  have := P.policy_le_policy_add_withRate_of_slack_at h₁ h₂ hr hderiv hanti hdupos hpc₁ hpc₂
    hslack₁ hslack₂ ha z (by simpa only [hmax] using helas)
  rwa [hmax', mul_zero, add_zero] at this

/-- **The equilibrium rate is unique on `[rlo, rhi]` under the slack elasticity condition**, for
any period utility, given the Doeblin data. -/
theorem equilibriumRate_unique_of_slack {rlo rhi α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ : 0 < rlo + δ) (hrlo : 0 < 1 + rlo) (hlohi : rlo ≤ rhi)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpc : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).PositiveConsumption)
    (hslack : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ s : ℝ × Z,
      s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r hrr).policy s < assetCap)
    (helas : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ hrr : P.RateOK r, ∀ hrr' : P.RateOK r', ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z z' : Z,
        (1 + r) * du ((P.withRate r hrr).consumptionFn z' ((P.withRate r hrr).policy (a, z)))
            * du ((P.withRate r hrr).consumptionFn z a + (r' - r) * a)
          ≤ (1 + r') * du ((P.withRate r' hrr').consumptionFn z' ((P.withRate r hrr).policy (a, z)))
            * du ((P.withRate r hrr).consumptionFn z a))
    [MeasurableSpace Z] [BorelSpace Z]
    (huniq : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      ∃! μ : ProbabilityMeasure P.State, (P.withRate r hrr).IsStationary μ)
    (htend : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ₀ μ : ProbabilityMeasure P.State,
      (P.withRate r hrr).IsStationary μ →
        Tendsto (fun m => (P.withRate r hrr).pushProb^[m] μ₀) atTop (𝓝 μ))
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (hμ₁ : (P.withRate r₁ hrr₁).IsStationary μ₁) (hμ₂ : (P.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : P.aggregateCapital μ₁ = normalisedDemand α δ r₁)
    (he₂ : P.aggregateCapital μ₂ = normalisedDemand α δ r₂) : r₁ = r₂ := by
  classical
  have hE : ∀ r : ℝ, ∃! μ : ProbabilityMeasure P.State,
      (P.withRate (clampRate rlo rhi r)
        (rateOK_of_floor_zero (one_add_clampRate_pos hrlo hlohi r))).IsStationary μ :=
    fun r => huniq _ (clampRate_mem hlohi r) _
  set ν : ℝ → ProbabilityMeasure P.State := fun r => (hE r).choose with hνdef
  have hν : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).IsStationary (ν r) := by
    intro r hr hrr
    have hc : clampRate rlo rhi r = r := clampRate_eq hr
    rw [← P.withRate_congr hc _ hrr]
    exact (hE r).choose_spec.1
  have hid : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate r hrr).IsStationary μ → μ = ν r := by
    intro r hr hrr μ hμ
    have hc : clampRate rlo rhi r = r := clampRate_eq hr
    refine (hE r).choose_spec.2 μ ?_
    rw [P.withRate_congr hc _ hrr]
    exact hμ
  have hpol : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap →
        (P.rateFamily hrlo hlohi r).policy s ≤ (P.rateFamily hrlo hlohi r').policy s := by
    intro r hr r' hr' hle s hs
    have hrok : P.RateOK r := rateOK_of_floor_zero (by linarith [hr.1])
    have hr'ok : P.RateOK r' := rateOK_of_floor_zero (by linarith [hr'.1])
    rw [P.rateFamily_eq _ _ hr hrok, P.rateFamily_eq _ _ hr' hr'ok]
    obtain ⟨a, z⟩ := s
    exact P.policy_le_policy_withRate_of_slack_at hrok hr'ok hle hderiv hanti hdupos (hpc r hr hrok)
      (hpc r' hr' hr'ok) (hslack r hr hrok) (hslack r' hr' hr'ok) hs z
      (helas r hr r' hr' hle hrok hr'ok a hs z)
  have hmono : MonotoneOn (fun r => P.aggregateCapital (ν r)) (Icc rlo rhi) := by
    refine P.monotoneOn_capitalSupply_of_policy_mono (P.rateFamily hrlo hlohi)
      (fun _ _ _ _ => rfl) hpol
      ⟨Measure.dirac (Classical.ofNonempty : P.State), inferInstance⟩ ν ?_
    intro r hr
    have hrr : P.RateOK r := rateOK_of_floor_zero (by linarith [hr.1])
    rw [P.rateFamily_eq _ _ hr hrr]
    exact htend r hr hrr _ _ (hν r hr hrr)
  rw [hid r₁ h₁ hrr₁ μ₁ hμ₁] at he₁
  rw [hid r₂ h₂ hrr₂ μ₂ hμ₂] at he₂
  exact eq_of_monotoneOn_of_strictAntiOn hmono (normalisedDemand_strictAntiOn hα0 hα1 hδ)
    h₁ h₂ he₁ he₂

/-- **The same on an invariant interval `[0, ā]`**: the slack condition is needed only at
`a ≤ ā`, and the coupling started at zero assets never leaves the interval. -/
theorem equilibriumRate_unique_of_slack_on {rlo rhi ā α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ : 0 < rlo + δ) (hrlo : 0 < 1 + rlo) (hlohi : rlo ≤ rhi) (hā : 0 ≤ ā)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpc : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).PositiveConsumption)
    (hslack : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ s : ℝ × Z,
      s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r hrr).policy s < assetCap)
    (hinv : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ s : ℝ × Z,
      s.1 ∈ Icc (0 : ℝ) assetCap → s.1 ≤ ā → (P.withRate r hrr).policy s ≤ ā)
    (helas : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ hrr : P.RateOK r, ∀ hrr' : P.RateOK r', ∀ a ∈ Icc (0 : ℝ) assetCap, a ≤ ā → ∀ z z' : Z,
        (1 + r) * du ((P.withRate r hrr).consumptionFn z' ((P.withRate r hrr).policy (a, z)))
            * du ((P.withRate r hrr).consumptionFn z a + (r' - r) * a)
          ≤ (1 + r') * du ((P.withRate r' hrr').consumptionFn z' ((P.withRate r hrr).policy (a, z)))
            * du ((P.withRate r hrr).consumptionFn z a))
    [MeasurableSpace Z] [BorelSpace Z]
    (huniq : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      ∃! μ : ProbabilityMeasure P.State, (P.withRate r hrr).IsStationary μ)
    (htend : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ₀ μ : ProbabilityMeasure P.State,
      (P.withRate r hrr).IsStationary μ →
        Tendsto (fun m => (P.withRate r hrr).pushProb^[m] μ₀) atTop (𝓝 μ))
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (hμ₁ : (P.withRate r₁ hrr₁).IsStationary μ₁) (hμ₂ : (P.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : P.aggregateCapital μ₁ = normalisedDemand α δ r₁)
    (he₂ : P.aggregateCapital μ₂ = normalisedDemand α δ r₂) : r₁ = r₂ := by
  classical
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hE : ∀ r : ℝ, ∃! μ : ProbabilityMeasure P.State,
      (P.withRate (clampRate rlo rhi r)
        (rateOK_of_floor_zero (one_add_clampRate_pos hrlo hlohi r))).IsStationary μ :=
    fun r => huniq _ (clampRate_mem hlohi r) _
  set ν : ℝ → ProbabilityMeasure P.State := fun r => (hE r).choose with hνdef
  have hν : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).IsStationary (ν r) := by
    intro r hr hrr
    have hc : clampRate rlo rhi r = r := clampRate_eq hr
    rw [← P.withRate_congr hc _ hrr]
    exact (hE r).choose_spec.1
  have hid : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate r hrr).IsStationary μ → μ = ν r := by
    intro r hr hrr μ hμ
    have hc : clampRate rlo rhi r = r := clampRate_eq hr
    refine (hE r).choose_spec.2 μ ?_
    rw [P.withRate_congr hc _ hrr]
    exact hμ
  have hpol : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → s.1 ≤ ā →
        (P.rateFamily hrlo hlohi r).policy s ≤ (P.rateFamily hrlo hlohi r').policy s := by
    intro r hr r' hr' hle s hs hsā
    have hrok : P.RateOK r := rateOK_of_floor_zero (by linarith [hr.1])
    have hr'ok : P.RateOK r' := rateOK_of_floor_zero (by linarith [hr'.1])
    rw [P.rateFamily_eq _ _ hr hrok, P.rateFamily_eq _ _ hr' hr'ok]
    obtain ⟨a, z⟩ := s
    exact P.policy_le_policy_withRate_of_slack_at hrok hr'ok hle hderiv hanti hdupos (hpc r hr hrok)
      (hpc r' hr' hr'ok) (hslack r hr hrok) (hslack r' hr' hr'ok) hs z
      (helas r hr r' hr' hle hrok hr'ok a hs hsā z)
  have hinv' : ∀ r ∈ Icc rlo rhi, ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → s.1 ≤ ā →
      (P.rateFamily hrlo hlohi r).policy s ≤ ā := by
    intro r hr s hs hsā
    have hrok : P.RateOK r := rateOK_of_floor_zero (by linarith [hr.1])
    rw [P.rateFamily_eq _ _ hr hrok]
    exact hinv r hr hrok s hs hsā
  set s₀ : P.State := (⟨0, ⟨le_rfl, hcap0⟩⟩, Classical.ofNonempty) with hs₀
  have h₀ : ((⟨Measure.dirac s₀, inferInstance⟩ : ProbabilityMeasure P.State) : Measure P.State)
      (AboveSet ā) = 0 := by
    have hA := measurableSet_aboveSet (assetFloor := (0 : ℝ)) (assetCap := assetCap) (Z := Z) ā
    change Measure.dirac s₀ (AboveSet ā) = 0
    rw [Measure.dirac_apply' _ hA]
    refine Set.indicator_of_notMem ?_ _
    simp only [AboveSet, mem_ofPred_eq, hs₀, not_lt]
    exact hā
  have hmono : MonotoneOn (fun r => P.aggregateCapital (ν r)) (Icc rlo rhi) := by
    refine P.monotoneOn_capitalSupply_of_policy_mono_on (P.rateFamily hrlo hlohi)
      (fun _ _ _ _ => rfl) hpol hinv' ⟨Measure.dirac s₀, inferInstance⟩ h₀ ν ?_
    intro r hr
    have hrr : P.RateOK r := rateOK_of_floor_zero (by linarith [hr.1])
    rw [P.rateFamily_eq _ _ hr hrr]
    exact htend r hr hrr _ _ (hν r hr hrr)
  rw [hid r₁ h₁ hrr₁ μ₁ hμ₁] at he₁
  rw [hid r₂ h₂ hrr₂ μ₂ hμ₂] at he₂
  exact eq_of_monotoneOn_of_strictAntiOn hmono (normalisedDemand_strictAntiOn hα0 hα1 hδ)
    h₁ h₂ he₁ he₂

/-- **CRRA, any `γ > 0`: uniqueness under the slack elasticity condition on an invariant
interval.** The condition at `a ≤ ā`, with `b = a'(a, z)` tomorrow's assets at the lower rate:
`R c(b,z')^{-γ} (c(a,z) + Δr·a)^{-γ} ≤ R' c'(b,z')^{-γ} c(a,z)^{-γ}`. The Doeblin data are the
minimal-MPC chain's, as in `crra_equilibriumRate_unique_of_marginal_on`. -/
theorem crra_equilibriumRate_unique_of_slack_on {γ rlo rhi ā α δ : ℝ} (hγ0 : 0 < γ)
    (hα0 : 0 < α) (hα1 : α < 1) (hδ : 0 < rlo + δ) (hu : P.u = crraUtility γ)
    (hunb : P.Unbounded) (hβ : 0 < (P.discount : ℝ)) (hrlo : 0 < 1 + rlo) (hlohi : rlo ≤ rhi)
    (hā : 0 ≤ ā) (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hκ : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, 0 < (P.withRate r hrr).minMPC γ)
    (hthr : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      (1 - (P.withRate r hrr).minMPC γ) * (P.maxIncome + (1 + r) * assetCap) < assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hreach : ∀ z, 0 < P.transitionMatrix z z₀) {a₀ : ℝ} (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hcorn : ∀ r ∈ Icc rlo rhi, (P.discount : ℝ) * (1 + r) * P.minIncome ^ (-γ)
      < (P.income z₀ + (1 + r) * a₀) ^ (-γ))
    (hinv : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ s : ℝ × Z,
      s.1 ∈ Icc (0 : ℝ) assetCap → s.1 ≤ ā → (P.withRate r hrr).policy s ≤ ā)
    (helas : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ hrr : P.RateOK r, ∀ hrr' : P.RateOK r', ∀ a ∈ Icc (0 : ℝ) assetCap, a ≤ ā → ∀ z z' : Z,
        (1 + r) * ((P.withRate r hrr).consumptionFn z' ((P.withRate r hrr).policy (a, z))) ^ (-γ)
            * ((P.withRate r hrr).consumptionFn z a + (r' - r) * a) ^ (-γ)
          ≤ (1 + r') * ((P.withRate r' hrr').consumptionFn z'
              ((P.withRate r hrr).policy (a, z))) ^ (-γ)
            * ((P.withRate r hrr).consumptionFn z a) ^ (-γ))
    [MeasurableSpace Z] [BorelSpace Z]
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (hμ₁ : (P.withRate r₁ hrr₁).IsStationary μ₁) (hμ₂ : (P.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : P.aggregateCapital μ₁ = normalisedDemand α δ r₁)
    (he₂ : P.aggregateCapital μ₂ = normalisedDemand α δ r₂) : r₁ = r₂ := by
  classical
  have hβR' : ∀ r ∈ Icc rlo rhi, (P.discount : ℝ) * (1 + r) < 1 := fun r hr => by
    nlinarith [hr.2, hβ]
  have hpcAll : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      (P.withRate r hrr).PositiveConsumptionAll :=
    fun r _ hrr => (P.withRate r hrr).positiveConsumptionAll_of_unbounded hunb
  have hposIt : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ n : ℕ, ∀ z : Z,
      ∀ a ∈ Icc (0 : ℝ) assetCap, 0 < (P.withRate r hrr).consumptionFnOf
        (((P.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a :=
    fun r hr hrr n z a ha =>
      hpcAll r hr hrr _ ((P.withRate r hrr).concaveSlices_iterate_zero n) z a ha
  have hthr' : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (1 - (P.withRate r hrr).minMPC γ)
      * ((P.withRate r hrr).maxIncome + (1 + (P.withRate r hrr).interest) * assetCap)
      < assetCap := fun r hr hrr => hthr r hr hrr
  have hβRw : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      ((P.withRate r hrr).discount : ℝ) * (1 + (P.withRate r hrr).interest) < 1 :=
    fun r hr _ => hβR' r hr
  refine P.equilibriumRate_unique_of_slack_on hα0 hα1 hδ hrlo hlohi hā
    (du := fun c => c ^ (-γ)) (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility γ hc)
    (fun x hx y _ hxy => Real.rpow_lt_rpow_of_neg hx hxy (by linarith))
    (fun c hc => Real.rpow_pos_of_pos hc _)
    (fun r _ hrr => (P.withRate r hrr).positiveConsumption_of_unbounded hunb)
    (fun r hr hrr s hs => ?_) hinv helas ?_ ?_ h₁ h₂ hrr₁ hrr₂ hμ₁ hμ₂ he₁ he₂
  · obtain ⟨a, z⟩ := s
    exact (P.withRate r hrr).crra_policy_lt_cap_of_minMPC hγ0 hu rfl (hκ r hr hrr) hβ
      (hβRw r hr hrr) (hposIt r hr hrr) (hthr' r hr hrr) hs z
  · intro r hr hrr
    exact (P.withRate r hrr).crra_existsUnique_isStationary_of_euler_corner_monotone hγ0 hu rfl
      (hκ r hr hrr) hβ (hβRw r hr hrr) (P.monotoneTransitions_withRate hmono hrr)
      (hpcAll r hr hrr) (hthr' r hr hrr) hz₀ hreach ha₀ hle (hcorn r hr)
  · intro r hr hrr μ₀ μ hμ
    exact (P.withRate r hrr).crra_tendsto_pushProb_of_euler_corner_monotone hγ0 hu rfl
      (hκ r hr hrr) hβ (hβRw r hr hrr) (P.monotoneTransitions_withRate hmono hrr)
      (hpcAll r hr hrr) (hthr' r hr hrr) hz₀ hreach ha₀ hle (hcorn r hr) μ₀ hμ

end ZeroFloor

end IncomeFluctuation

end LeanEconomics
