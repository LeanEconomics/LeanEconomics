/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.AiyagariExistence
import LeanEconomics.Equilibrium.ExistenceFloor

/-!
# Aiyagari (1994) at `μ = 1`: existence from primitives

`aiyagari1994_log_exists_equilibrium_of_floor` proved existence of an equilibrium on
`[r_lo, r_hi] ⊂ (-δ, λ)` given one fact about the household: a floor `m ≥ D(r_hi)` on capital
supply at `r_hi`. `ExistenceFloor` proved that floor from a single inequality on the primitives.
This file puts the two together.

## The statement

Beyond the hypotheses of the earlier theorem, the data are

* a nonnegative super-solution `H` of the human-wealth equation at `r_hi`,
  `∑ π(z,z') (y_{z'} + H_{z'}) ≤ (1 + r_hi) H_z`;
* a slope `σ ≥ 0` below `κ R - κ y_max / (r (ā - y_max))`, `κ = 1 - β` at `μ = 1`;
* a schedule `τ` of thresholds and a number `n` of iterations of the zero-wealth floor operator,
  giving the floor `f = zeroFloorIter ⋯ n`;
* a pair of income states `z₁, z₂` reached from every state with probability at least `p₀`;

and the two inequalities that carry the result: the consumption gap
`(1 - β)((1 + r_hi) A₀ + y_{z₁} + H_{z₁}) < f_{z₂}` and the demand comparison
`D(r_hi) ≤ A₀ - A₀ · 2(1 - βR)/y_min² / v₀` with `v₀ = p₀/2 (U⁻¹ - L⁻¹)²`. Every hypothesis
is an inequality between explicit expressions in `β`, `r_hi`, the income vector, the transition
matrix and the cap. Nothing about the household's policy or value function remains.

## What it is worth

At Aiyagari's numbers the consumption-gap inequality holds for the extreme pair up to
`A₀ ≈ 12` mean incomes, above capital demand, but `p₀` is of the order of `10^{-24}`, so the
demand comparison needs `βR` within about `10^{-27}` of one and a cap to match. The theorem is an
existence statement for rates close enough to `λ`; it is not quantitative, and the write-up says
why (Section on the existence floor).
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **Aiyagari (1994) at `μ = 1`: an equilibrium exists on `[r_lo, r_hi]`, from primitives.** -/
theorem aiyagari1994_log_exists_equilibrium {rlo rhi : ℝ}
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded) (hβ : (P.discount : ℝ) = 24 / 25)
    (hrlo : -2 / 25 < rlo) (hlt : rlo < rhi) (hrhi0 : 0 < rhi) (hlam : rhi < 1 / 24)
    (hcap : 2 * (24 / 25) * P.maxIncome < (1 - 24 / 25 * (1 + rhi)) * assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hmin : P.income z₀ = P.minIncome) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    -- human wealth at `r_hi`
    {H : Z → ℝ} (hH0 : ∀ z, 0 ≤ H z)
    (hH : ∀ z, ∑ z', P.transitionMatrix z z' * (P.income z' + H z') ≤ (1 + rhi) * H z)
    -- the slope floor and the zero-wealth floor
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hycap : P.maxIncome < assetCap)
    (hσ : σ ≤ (1 - (P.discount : ℝ)) * (1 + rhi)
      - (1 - (P.discount : ℝ)) * P.maxIncome / rhi / (assetCap - P.maxIncome))
    (τ : ℕ → Z → ℝ) (hτ0 : ∀ k z, 0 < τ k z) (hτ : ∀ k z, τ k z ≤ P.income z) (n : ℕ)
    -- the pair of states and the gap
    {A₀ p₀ : ℝ} (hA₀ : 0 ≤ A₀) (z₁ z₂ : Z) (hp₀ : 0 < p₀)
    (hp : ∀ z, p₀ ≤ min (P.transitionMatrix z z₁) (P.transitionMatrix z z₂))
    (hgap : (1 - (P.discount : ℝ)) * ((1 + rhi) * A₀ + P.income z₁ + H z₁)
      < zeroFloorIter P.transitionMatrix P.income ((P.discount : ℝ) * (1 + rhi)) 1 σ
          P.minIncome τ n z₂)
    -- demand against the ceiling at `r_lo` and the floor at `r_hi`
    (hDlo : 24 / 25 * P.maxIncome / (1 - 24 / 25 * (1 + rlo))
      ≤ normalisedDemand (9 / 25) (2 / 25) rlo)
    (hDhi : normalisedDemand (9 / 25) (2 / 25) rhi
      ≤ A₀ - A₀ / (p₀ / 2 * (((1 - (P.discount : ℝ)) * ((1 + rhi) * A₀ + P.income z₁ + H z₁))⁻¹
          - (zeroFloorIter P.transitionMatrix P.income ((P.discount : ℝ) * (1 + rhi)) 1 σ
              P.minIncome τ n z₂)⁻¹) ^ 2)
        * (2 * (1 - (P.discount : ℝ) * (1 + rhi)) / P.minIncome ^ 2)) :
    ∃ r ∈ Icc rlo rhi, IsAiyagariEquilibrium
      (P.rateFamily (by linarith : (0 : ℝ) < 1 + rlo) hlt.le)
      (normalisedDemand (9 / 25) (2 / 25)) r := by
  refine P.aiyagari1994_log_exists_equilibrium_of_floor hu hunb hβ hrlo hlt hlam hcap hmono hz₀
    hmin hreach (m := normalisedDemand (9 / 25) (2 / 25) rhi) ?_ hDlo le_rfl
  intro hrhi μ hμ
  set Q := P.withRate rhi hrhi with hQ
  have hQu : Q.u = crraUtility 1 := hu
  have hQunb : Q.Unbounded := hunb
  have hQβ : (Q.discount : ℝ) = 24 / 25 := hβ
  have hβ0 : (0 : ℝ) < Q.discount := by rw [hQβ]; norm_num
  have hQr : Q.interest = rhi := rfl
  have hβR : (Q.discount : ℝ) * (1 + Q.interest) < 1 := by rw [hQβ, hQr]; linarith
  have hint : 0 < Q.interest := hrhi0
  have hκ1 : Q.minMPC 1 = 1 - (Q.discount : ℝ) := Q.minMPC_one
  have hκ : 0 < Q.minMPC 1 := by rw [hκ1, hQβ]; norm_num
  have h125 : (0 : ℝ) ≤ 1 - P.discount := by rw [hβ]; norm_num
  have hmaxpos : 0 < P.maxIncome := lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxIncome
  have hthr : (1 - Q.minMPC 1) * (Q.maxIncome + (1 + Q.interest) * assetCap) < assetCap := by
    rw [hκ1, hQβ]
    change (1 - (1 - 24 / 25)) * (P.maxIncome + (1 + rhi) * assetCap) < assetCap
    nlinarith [hcap, hmaxpos]
  have hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < Q.consumptionFnOf ((Q.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a :=
    fun _ _ a ha => Q.consumptionFnOf_pos hQunb _ ha
  have hpcAll : Q.PositiveConsumptionAll := Q.positiveConsumptionAll_of_unbounded hQunb
  have hpc : Q.PositiveConsumption := Q.positiveConsumption_of_unbounded hQunb
  have hslack : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → Q.policy s < assetCap :=
    fun s hs => Q.crra_policy_lt_cap_of_minMPC one_pos hQu rfl hκ hβ0 hβR hpos hthr hs s.2
  have hslack_iter : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      Q.policyOf ((Q.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap :=
    fun n => (Q.crra_minMPC_of_cap one_pos hQu rfl hκ hβ0 hβR hpos hthr n).2
  have hconc : ∀ z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap) (Q.consumptionFn z) :=
    fun z => Q.concaveOn_consumptionFn_of_crra hpcAll one_pos hβ0 hQu hslack_iter z
  have hlow : ∀ z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      Q.minMPC 1 * Q.resources (a, z) ≤ Q.consumptionFn z a :=
    fun z a ha => Q.crra_minMPC_mul_le_consumptionFn_of_cap one_pos hQu rfl hκ hβ0 hβR hpos hthr
      z ha
  have hup : ∀ z, ∀ a ∈ Icc (0 : ℝ) assetCap, Q.consumptionFn z a
      ≤ Q.minMPC 1 * Q.resources (a, z) + Q.minMPC 1 * Q.maxIncome / Q.interest :=
    fun z a ha => Q.crra_consumptionFn_le_of_minMPC one_pos hQu hκ hβ0 hβR hint hpc hslack z ha
  -- the slope floor on `[0, y_max]`
  have hslope : ∀ z, ∀ A ∈ Icc (0 : ℝ) Q.maxIncome,
      Q.consumptionFn z 0 + σ * A ≤ Q.consumptionFn z A := by
    intro z A hA
    have hAcap : A < assetCap := lt_of_le_of_lt hA.2 hycap
    have h := Q.crra_consumptionFn_sub_ge (γ := 1) hconc hlow hup z le_rfl hA.1 hAcap
    have hσA : σ ≤ Q.minMPC 1 * (1 + Q.interest)
        - Q.minMPC 1 * Q.maxIncome / Q.interest / (assetCap - A) := by
      rw [hκ1]
      change σ ≤ (1 - (P.discount : ℝ)) * (1 + rhi)
        - (1 - (P.discount : ℝ)) * P.maxIncome / rhi / (assetCap - A)
      have h1 : (1 - (P.discount : ℝ)) * P.maxIncome / rhi / (assetCap - A)
          ≤ (1 - (P.discount : ℝ)) * P.maxIncome / rhi / (assetCap - P.maxIncome) :=
        div_le_div_of_nonneg_left (div_nonneg (mul_nonneg h125 hmaxpos.le) hrhi0.le)
          (by linarith) (by have hA2 : A ≤ P.maxIncome := hA.2; linarith)
      linarith [hσ]
    have := mul_le_mul_of_nonneg_right hσA hA.1
    linarith
  -- consumption is at least the minimum income everywhere
  have hbase : ∀ z, Q.minIncome ≤ Q.consumptionFn z 0 := by
    intro z
    have h := Q.minIncome_le_consumptionFn_floor hβR (du := fun c => c ^ (-(1 : ℝ)))
      (fun c hc => by rw [hQu]; exact hasDerivAt_crraUtility 1 hc)
      (fun x hx y _ hxy => rpow_neg_antitone one_pos hx hxy)
      (fun c hc => Real.rpow_pos_of_pos hc _) (fun z x hx => Q.consumptionFn_pos hpc hx z)
      (fun z x hx => by
        rw [maxSaving_eq]
        refine lt_min (hslack _ hx) ?_
        have := Q.consumptionFn_pos hpc hx z
        change 0 < Q.resources (x, z) - Q.policy (x, z) at this
        linarith) z
    simpa using h
  have hfloorc : ∀ z, ∀ a ∈ Icc (0 : ℝ) assetCap, Q.minIncome ≤ Q.consumptionFn z a :=
    fun z a ha => (hbase z).trans (Q.consumptionFn_mono ⟨le_rfl, Q.assetCap_nonneg⟩ ha ha.1)
  -- the iterated floor at zero wealth
  have hiter := Q.zeroFloorIter_le one_pos hQu hβ0 hpc hslack hσ0 hslope hbase τ hτ0 hτ n
  -- the capital floor
  have hMle : ‖Q.marginalState (fun c => c ^ (-(1 : ℝ))) (continuousOn_rpow_neg 1) hpc‖
      ≤ Q.minIncome ^ (-(1 : ℝ)) :=
    Q.norm_marginalState_le_of_floor (continuousOn_rpow_neg 1) hpc
      (fun x hx y _ hxy => rpow_neg_antitone one_pos hx hxy)
      (fun c hc => (Real.rpow_pos_of_pos hc _).le) Q.minIncome_pos hfloorc
  have hM2 : ‖Q.marginalState (fun c => c ^ (-(1 : ℝ))) (continuousOn_rpow_neg 1) hpc‖ ^ 2
      ≤ 1 / P.minIncome ^ 2 := by
    rw [Real.rpow_neg_one] at hMle
    calc _ ≤ (Q.minIncome⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hMle 2
      _ = 1 / P.minIncome ^ 2 := by rw [inv_pow, one_div]; rfl
  have hgap' : Q.minMPC 1 * ((1 + Q.interest) * A₀ + Q.income z₁ + H z₁)
      < zeroFloorIter Q.transitionMatrix Q.income ((Q.discount : ℝ) * (1 + Q.interest)) 1 σ
          Q.minIncome τ n z₂ := by
    rw [hκ1]; exact hgap
  have hK := Q.crra_aggregateCapital_ge_of_primitives one_pos hQu hκ hβ0 hint hβR.le hpc hslack
    hH0 hH hiter.2 hA₀ z₁ z₂ hp₀ hp hgap' hμ
  rw [hκ1] at hK
  -- read the floor in the primitives of `P`
  simp only [hQ, withRate_income, withRate_transitionMatrix, withRate_discount,
    withRate_interest, withRate_minIncome] at hK hM2
  rw [Real.rpow_neg_one, Real.rpow_neg_one] at hK
  set L : ℝ := zeroFloorIter P.transitionMatrix P.income ((P.discount : ℝ) * (1 + rhi)) 1 σ
    P.minIncome τ n z₂ with hL
  set U : ℝ := (1 - (P.discount : ℝ)) * ((1 + rhi) * A₀ + P.income z₁ + H z₁) with hU
  set X : ℝ := A₀ / (p₀ / 2 * (U⁻¹ - L⁻¹) ^ 2) with hX
  set c : ℝ := 2 * (1 - (P.discount : ℝ) * (1 + rhi)) with hc
  set Mn : ℝ := ‖(P.withRate rhi hrhi).marginalState (fun c => c ^ (-(1 : ℝ)))
    (continuousOn_rpow_neg 1) hpc‖ with hMn
  have hX0 : 0 ≤ X := div_nonneg hA₀ (by positivity)
  have hc0 : 0 ≤ c := by
    have : (P.discount : ℝ) * (1 + rhi) < 1 := hβR
    rw [hc]; linarith
  have hfin : X * (c * Mn ^ 2) ≤ X * (c / P.minIncome ^ 2) := by
    have h1 : X * (c * Mn ^ 2) = X * c * Mn ^ 2 := by ring
    have h2 : X * (c / P.minIncome ^ 2) = X * c * (1 / P.minIncome ^ 2) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hM2 (mul_nonneg hX0 hc0)
  change _ ≤ (P.withRate rhi hrhi).aggregateCapital μ
  linarith [hK, hDhi, hfin]

end IncomeFluctuation

end LeanEconomics
