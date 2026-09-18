/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.AiyagariUniqueness

/-!
# Saving rises with the rate whenever consumption's elasticity to the rate is small

Light's Theorem 1 — the saving policy is increasing in the interest rate, state by state — is
the only step of the uniqueness chain that uses relative risk aversion at most one. This file
isolates what that step actually needs, for any period utility:

  `R₁ · u'(c₁(b, z)) ≤ R₂ · u'(c₂(b, z))`   for every state `(b, z)` and rates `r₁ < r₂`,

that is, `u'(c)` falls with the rate by at most the factor the gross rate rises: for CRRA,
`c₂/c₁ ≤ (R₂/R₁)^{1/γ}`, an elasticity of consumption to the gross rate of at most `1/γ`.

The argument is four lines of Euler inequalities, with no value functions, no envelope theorem
and no induction. Suppose saving were LOWER at the higher rate at some `(a, z)`: `a'₂ < a'₁`.
Then the higher-rate household has room under the cap, so `βR₂ E u'(c₂(a'₂, ·)) ≤ u'(c₂(a, z))`;
the lower-rate household has room above the floor, so `u'(c₁(a, z)) ≤ βR₁ E u'(c₁(a'₁, ·))`;
it consumes strictly less today, so `u'(c₂(a, z)) < u'(c₁(a, z))`; and consumption rises with
assets, so `u'(c₂(a'₁, ·)) ≤ u'(c₂(a'₂, ·))`. Chaining these,
`R₂ E u'(c₂(a'₁, ·)) < R₁ E u'(c₁(a'₁, ·))`, which the elasticity condition at `b = a'₁` forbids
(`policy_le_policy_withRate_of_marginal`).

For `γ ≤ 1` the condition is what the rescaling argument of `policy_mono_withRate_hara`
delivers. For `γ > 1` it is a genuine restriction: it says the income effect of the rate on
consumption — through the marginal propensity to consume, which rises with the rate when
`γ > 1` — does not outweigh the human-wealth effect. It holds for households whose wealth is
small relative to their human wealth and fails for the very rich, so uniqueness at `γ > 1`
rests on the condition holding on the stationary support. That is not proved here from
primitives; it is stated as the hypothesis it is, and with it the rest of the chain —
capital supply monotone (`monotoneOn_capitalSupply_of_policy_mono`), single crossing against
Cobb--Douglas demand (`eq_of_monotoneOn_of_strictAntiOn`), the Doeblin uniqueness and convergence
of the stationary distribution — goes through unchanged
(`equilibriumRate_unique_of_marginal`, `crra_equilibriumRate_unique_of_marginal`).
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### Theorem 1 from the elasticity condition -/

/-- **Saving rises with the rate wherever `R·u'(c)` does.** Two rates `r₁ ≤ r₂` of the same
economy; positive consumption, cap slack at both rates, and the elasticity condition
`R₁ u'(c₁(b,z)) ≤ R₂ u'(c₂(b,z))` at every state. Then `policy₁ ≤ policy₂`. -/
theorem policy_le_policy_withRate_of_marginal {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    (hr : r₁ ≤ r₂) {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₂ h₂).policy s < assetCap)
    (helas : ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z b)
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z b))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy (a, z) := by
  classical
  by_contra hcon
  push Not at hcon
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  -- the two savings and the two consumptions today
  have hA₁mem : (P.withRate r₁ h₁).policy (a, z) ∈ Icc (0 : ℝ) assetCap :=
    (P.withRate r₁ h₁).feasible_subset_region ((P.withRate r₁ h₁).policy_mem _)
  have hA₂mem : (P.withRate r₂ h₂).policy (a, z) ∈ Icc (0 : ℝ) assetCap :=
    (P.withRate r₂ h₂).feasible_subset_region ((P.withRate r₂ h₂).policy_mem _)
  have hres₁ : (P.withRate r₁ h₁).resources (a, z) = P.income z + (1 + r₁) * a := by
    simp only [resources, IncomeFluctuation.withRate_income, IncomeFluctuation.withRate_interest,
      max_eq_right ha.1]
  have hres₂ : (P.withRate r₂ h₂).resources (a, z) = P.income z + (1 + r₂) * a := by
    simp only [resources, IncomeFluctuation.withRate_income, IncomeFluctuation.withRate_interest,
      max_eq_right ha.1]
  have hc₁ : (P.withRate r₁ h₁).consumptionFn z a
      = P.income z + (1 + r₁) * a - (P.withRate r₁ h₁).policy (a, z) := by
    simp only [consumptionFn, consumption, hres₁]
  have hc₂ : (P.withRate r₂ h₂).consumptionFn z a
      = P.income z + (1 + r₂) * a - (P.withRate r₂ h₂).policy (a, z) := by
    simp only [consumptionFn, consumption, hres₂]
  have hc₁pos : 0 < (P.withRate r₁ h₁).consumptionFn z a :=
    (P.withRate r₁ h₁).consumptionFn_pos hpc₁ ha z
  have hc₂pos : 0 < (P.withRate r₂ h₂).consumptionFn z a :=
    (P.withRate r₂ h₂).consumptionFn_pos hpc₂ ha z
  have hclt : (P.withRate r₁ h₁).consumptionFn z a < (P.withRate r₂ h₂).consumptionFn z a := by
    rw [hc₁, hc₂]
    have := mul_nonneg (sub_nonneg.mpr hr) ha.1
    nlinarith
  have hdu : du ((P.withRate r₂ h₂).consumptionFn z a)
      < du ((P.withRate r₁ h₁).consumptionFn z a) :=
    hanti (mem_Ioi.mpr hc₁pos) (mem_Ioi.mpr hc₂pos) hclt
  -- next period's consumptions are positive
  have hc₁' : ∀ z' : Z,
      0 < (P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)) :=
    fun z' => (P.withRate r₁ h₁).consumptionFn_pos hpc₁ hA₁mem z'
  have hc₂' : ∀ z' : Z,
      0 < (P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z)) :=
    fun z' => (P.withRate r₂ h₂).consumptionFn_pos hpc₂ hA₂mem z'
  -- the Euler inequality at the higher rate: room under the cap
  have hbv₂ := (P.withRate r₂ h₂).toExtended.bellman_valueFunction
  have hroom₂ : (P.withRate r₂ h₂).policy (a, z) < (P.withRate r₂ h₂).maxSaving (a, z) := by
    rw [maxSaving_eq]
    refine lt_min (hslack₂ _ ha) ?_
    have := hc₂pos
    simp only [consumptionFn, consumption] at this
    linarith
  have hE₂ := (P.withRate r₂ h₂).euler_le (v := (P.withRate r₂ h₂).toExtended.valueFunction)
    (z := z) (a := a) (A := (P.withRate r₂ h₂).policy (a, z))
    (du := du ((P.withRate r₂ h₂).consumptionFn z a))
    (du' := fun z' => du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z))))
    ha (by rw [hbv₂]; exact congrFun (P.withRate r₂ h₂).policyOf_valueFunction _) hroom₂
    (by rw [hbv₂]; exact hc₂pos) (by rw [hbv₂]; exact hderiv _ hc₂pos)
    (fun z' => hc₂' z') (fun z' => hderiv _ (hc₂' z'))
  -- the Euler inequality at the lower rate: room above the floor
  have hbv₁ := (P.withRate r₁ h₁).toExtended.bellman_valueFunction
  have hA₁pos : (0 : ℝ) < (P.withRate r₁ h₁).policy (a, z) := lt_of_le_of_lt hA₂mem.1 hcon
  have hslackA₁ : ∀ z' : Z, (P.withRate r₁ h₁).policyOf (P.withRate r₁ h₁).toExtended.valueFunction
      ((P.withRate r₁ h₁).policy (a, z), z')
      < (P.withRate r₁ h₁).maxSaving ((P.withRate r₁ h₁).policy (a, z), z') := by
    intro z'
    rw [(P.withRate r₁ h₁).policyOf_valueFunction, maxSaving_eq]
    refine lt_min (hslack₁ _ hA₁mem) ?_
    have := hc₁' z'
    simp only [consumptionFn, consumption] at this
    linarith
  have hE₁ := (P.withRate r₁ h₁).euler_ge (v := (P.withRate r₁ h₁).toExtended.valueFunction)
    (z := z) (a := a) (A := (P.withRate r₁ h₁).policy (a, z))
    (du := du ((P.withRate r₁ h₁).consumptionFn z a))
    (du' := fun z' => du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z))))
    ha (by rw [hbv₁]; exact congrFun (P.withRate r₁ h₁).policyOf_valueFunction _) hA₁pos hslackA₁
    (by rw [hbv₁]; exact hc₁pos) (by rw [hbv₁]; exact hderiv _ hc₁pos)
    (fun z' => hc₁' z') (fun z' => hderiv _ (hc₁' z'))
  simp only [IncomeFluctuation.withRate_discount, IncomeFluctuation.withRate_interest,
    IncomeFluctuation.withRate_transitionMatrix] at hE₁ hE₂
  -- consumption rises with assets, so the higher-rate household's tomorrow is cheaper at `a'₁`
  have hdu₂ : ∀ z' : Z,
      du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
        ≤ du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z))) := by
    intro z'
    have hmono := (P.withRate r₂ h₂).consumptionFn_mono (z := z') hA₂mem hA₁mem hcon.le
    exact hanti.antitoneOn (mem_Ioi.mpr (hc₂' z'))
      (mem_Ioi.mpr ((P.withRate r₂ h₂).consumptionFn_pos hpc₂ hA₁mem z')) hmono
  -- the elasticity condition at `b = a'₁`, summed against the transition row
  have hsum : (1 + r₁) * ∑ z', P.transitionMatrix z z'
        * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
      ≤ (1 + r₂) * ∑ z', P.transitionMatrix z z'
        * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun z' _ => ?_
    have hπ := P.transitionMatrix_nonneg z z'
    have h1 := helas _ hA₁mem z'
    have h2 := mul_le_mul_of_nonneg_left (hdu₂ z') hR₂.le
    calc (1 + r₁) * (P.transitionMatrix z z'
            * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z))))
        = P.transitionMatrix z z' * ((1 + r₁)
            * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))) := by
          ring
      _ ≤ P.transitionMatrix z z' * ((1 + r₂)
            * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z)))) :=
          mul_le_mul_of_nonneg_left (le_trans h1 h2) hπ
      _ = (1 + r₂) * (P.transitionMatrix z z'
            * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₂ h₂).policy (a, z)))) := by
          ring
  have := mul_le_mul_of_nonneg_left hsum hβ
  linarith

/-! ### The chain from Theorem 1 to uniqueness, for any utility -/

/-- **The equilibrium rate is unique on `[rlo, rhi]` under the elasticity condition**, for any
period utility, given the Doeblin data (a unique stationary distribution at each rate, reached
from any start). -/
theorem equilibriumRate_unique_of_marginal {rlo rhi α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ : 0 < rlo + δ) (hrlo : 0 < 1 + rlo) (hlohi : rlo ≤ rhi)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).PositiveConsumption)
    (hslack : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ s : ℝ × Z,
      s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r hrr).policy s < assetCap)
    (helas : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ hrr : P.RateOK r, ∀ hrr' : P.RateOK r', ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
        (1 + r) * du ((P.withRate r hrr).consumptionFn z b)
          ≤ (1 + r') * du ((P.withRate r' hrr').consumptionFn z b))
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
  -- the selection of stationary distributions, through the clamped rate
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
  -- Theorem 1 along the rate family
  have hpol : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap →
        (P.rateFamily hrlo hlohi r).policy s ≤ (P.rateFamily hrlo hlohi r').policy s := by
    intro r hr r' hr' hle s hs
    have hrok : P.RateOK r := rateOK_of_floor_zero (by linarith [hr.1])
    have hr'ok : P.RateOK r' := rateOK_of_floor_zero (by linarith [hr'.1])
    rw [P.rateFamily_eq _ _ hr hrok, P.rateFamily_eq _ _ hr' hr'ok]
    obtain ⟨a, z⟩ := s
    exact P.policy_le_policy_withRate_of_marginal hrok hr'ok hle hderiv hanti (hpc r hr hrok)
      (hpc r' hr' hr'ok) (hslack r hr hrok) (hslack r' hr' hr'ok)
      (helas r hr r' hr' hle hrok hr'ok) hs z
  -- Theorem 2: capital supply is monotone along the selection
  have hmono : MonotoneOn (fun r => P.aggregateCapital (ν r)) (Icc rlo rhi) := by
    refine P.monotoneOn_capitalSupply_of_policy_mono (P.rateFamily hrlo hlohi)
      (fun _ _ _ _ => rfl) hpol
      ⟨Measure.dirac (Classical.ofNonempty : P.State), inferInstance⟩ ν ?_
    intro r hr
    have hrr : P.RateOK r := rateOK_of_floor_zero (by linarith [hr.1])
    rw [P.rateFamily_eq _ _ hr hrr]
    exact htend r hr hrr _ _ (hν r hr hrr)
  -- Theorem 3: single crossing
  rw [hid r₁ h₁ hrr₁ μ₁ hμ₁] at he₁
  rw [hid r₂ h₂ hrr₂ μ₂ hμ₂] at he₂
  exact eq_of_monotoneOn_of_strictAntiOn hmono (normalisedDemand_strictAntiOn hα0 hα1 hδ)
    h₁ h₂ he₁ he₂

/-! ### CRRA, any risk aversion -/

/-- **CRRA with any `γ > 0`: the equilibrium rate is unique on `[rlo, rhi]` under the
elasticity condition** `R c₁^{-γ} ≤ R' c₂^{-γ}`, with the Doeblin data supplied by the
minimal-MPC chain at each rate: a positive minimal MPC, cap slack, the Euler corner. The
per-rate hypotheses are the same as the log theorem's, but with `κ = 1 - Þ/R` in place of
`1 - β` they are stated at each rate rather than collapsed to one inequality. -/
theorem crra_equilibriumRate_unique_of_marginal {γ rlo rhi α δ : ℝ} (hγ0 : 0 < γ)
    (hα0 : 0 < α) (hα1 : α < 1) (hδ : 0 < rlo + δ) (hu : P.u = crraUtility γ)
    (hunb : P.Unbounded) (hβ : 0 < (P.discount : ℝ)) (hrlo : 0 < 1 + rlo) (hlohi : rlo ≤ rhi)
    (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hκ : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, 0 < (P.withRate r hrr).minMPC γ)
    (hthr : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      (1 - (P.withRate r hrr).minMPC γ) * (P.maxIncome + (1 + r) * assetCap) < assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hreach : ∀ z, 0 < P.transitionMatrix z z₀) {a₀ : ℝ} (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hcorn : ∀ r ∈ Icc rlo rhi, (P.discount : ℝ) * (1 + r) * P.minIncome ^ (-γ)
      < (P.income z₀ + (1 + r) * a₀) ^ (-γ))
    (helas : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ hrr : P.RateOK r, ∀ hrr' : P.RateOK r', ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
        (1 + r) * ((P.withRate r hrr).consumptionFn z b) ^ (-γ)
          ≤ (1 + r') * ((P.withRate r' hrr').consumptionFn z b) ^ (-γ))
    [MeasurableSpace Z] [BorelSpace Z]
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (hμ₁ : (P.withRate r₁ hrr₁).IsStationary μ₁) (hμ₂ : (P.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : P.aggregateCapital μ₁ = normalisedDemand α δ r₁)
    (he₂ : P.aggregateCapital μ₂ = normalisedDemand α δ r₂) : r₁ = r₂ := by
  classical
  -- per-rate facts
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
  refine P.equilibriumRate_unique_of_marginal hα0 hα1 hδ hrlo hlohi
    (du := fun c => c ^ (-γ)) (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility γ hc)
    (fun x hx y _ hxy => Real.rpow_lt_rpow_of_neg hx hxy (by linarith))
    (fun r _ hrr => (P.withRate r hrr).positiveConsumption_of_unbounded hunb)
    (fun r hr hrr s hs => ?_) helas ?_ ?_ h₁ h₂ hrr₁ hrr₂ hμ₁ hμ₂ he₁ he₂
  · -- cap slack from the minimal MPC
    obtain ⟨a, z⟩ := s
    exact (P.withRate r hrr).crra_policy_lt_cap_of_minMPC hγ0 hu rfl (hκ r hr hrr) hβ
      (hβRw r hr hrr) (hposIt r hr hrr) (hthr' r hr hrr) hs z
  · -- a unique stationary distribution at each rate
    intro r hr hrr
    exact (P.withRate r hrr).crra_existsUnique_isStationary_of_euler_corner_monotone hγ0 hu rfl
      (hκ r hr hrr) hβ (hβRw r hr hrr) (P.monotoneTransitions_withRate hmono hrr)
      (hpcAll r hr hrr) (hthr' r hr hrr) hz₀ hreach ha₀ hle (hcorn r hr)
  · -- reached from any start
    intro r hr hrr μ₀ μ hμ
    exact (P.withRate r hrr).crra_tendsto_pushProb_of_euler_corner_monotone hγ0 hu rfl
      (hκ r hr hrr) hβ (hβRw r hr hrr) (P.monotoneTransitions_withRate hmono hrr)
      (hpcAll r hr hrr) (hthr' r hr hrr) hz₀ hreach ha₀ hle (hcorn r hr) μ₀ hμ

end IncomeFluctuation

end LeanEconomics
