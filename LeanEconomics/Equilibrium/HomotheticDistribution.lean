/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.Homothetic
import LeanEconomics.Equilibrium.PositiveCapital
import LeanEconomics.Equilibrium.AiyagariUniqueness

/-!
# Homotheticity at the level of the distribution

`Equilibrium/Homothetic` proves that scaling every income and the cap by `λ` scales the POLICY
by `λ` (`policy_scale`). Aiyagari's equilibrium condition needs the same for AGGREGATE capital:
his `Ea(r)` is computed at the wage `w(r)`, and Light's Theorem 3 works with the unit-wage economy,
so the bridge is Açıkgöz Proposition 7, `Ea_w = w · Ea₁`, at the level of the stationary
distribution.

## The map

`scaleState` sends `(a, z)` to `(λ a, z)`, a continuous map between the state spaces. Because the
policy scales, it commutes with one period of the distribution's motion: `push` of the pushforward
is the pushforward of `push` (`pushProb_scaleProb`). So the pushforward of a stationary distribution
is stationary, and its aggregate capital is `λ` times the original.

## The firm

For Cobb--Douglas with capital share `α`, `k(r) = (α/(r+δ))^(1/(1-α))` and `w(r) = (1-α) k(r)^α`,
and `k(r)/w(r) = α/((1-α)(r+δ))` — `normalisedDemand`, with no root
(`cobbDouglasCapital_div_wage`).
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

/-! ### The Cobb--Douglas firm with a general capital share -/

/-- Capital demand per unit of labour at rate `r`: the `k` solving `α k^(α-1) = r + δ`. -/
noncomputable def cobbDouglasCapital (α δ r : ℝ) : ℝ := (α / (r + δ)) ^ (1 / (1 - α))

/-- The wage at rate `r`: the marginal product of labour at `k(r)`. -/
noncomputable def cobbDouglasWage (α δ r : ℝ) : ℝ := (1 - α) * cobbDouglasCapital α δ r ^ α

theorem cobbDouglasCapital_pos {α δ r : ℝ} (hα0 : 0 < α) (hδ : 0 < r + δ) :
    0 < cobbDouglasCapital α δ r :=
  Real.rpow_pos_of_pos (div_pos hα0 hδ) _

theorem cobbDouglasWage_pos {α δ r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδ : 0 < r + δ) :
    0 < cobbDouglasWage α δ r :=
  mul_pos (by linarith) (Real.rpow_pos_of_pos (cobbDouglasCapital_pos hα0 hδ) _)

/-- **`k(r)/w(r)` needs no root**: it is `α/((1-α)(r+δ))`. -/
theorem cobbDouglasCapital_div_wage {α δ r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδ : 0 < r + δ) :
    cobbDouglasCapital α δ r / cobbDouglasWage α δ r = normalisedDemand α δ r := by
  set q : ℝ := α / (r + δ) with hq
  have hq0 : 0 < q := div_pos hα0 hδ
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hk : cobbDouglasCapital α δ r = q ^ (1 / (1 - α)) := rfl
  have hkα : cobbDouglasCapital α δ r ^ α = q ^ (1 / (1 - α) * α) := by
    rw [hk, ← Real.rpow_mul hq0.le]
  have hkdiv : cobbDouglasCapital α δ r / cobbDouglasCapital α δ r ^ α = q := by
    rw [hkα, hk, ← Real.rpow_sub hq0]
    have : 1 / (1 - α) - 1 / (1 - α) * α = 1 := by field_simp
    rw [this, Real.rpow_one]
  simp only [cobbDouglasWage, normalisedDemand]
  rw [div_mul_eq_div_div_swap, hkdiv, hq]
  field_simp

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetFloor assetCap lam : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### The state map -/

/-- `(a, z) ↦ (λ a, z)`, from the region of `P` to the region of `P.scale`. -/
noncomputable def scaleState (hlam : 0 < lam) (s : P.State) : (P.scale hlam).State :=
  (⟨lam * (s.1 : ℝ), ⟨mul_le_mul_of_nonneg_left s.1.2.1 hlam.le,
    mul_le_mul_of_nonneg_left s.1.2.2 hlam.le⟩⟩, s.2)

@[simp] theorem scaleState_fst (hlam : 0 < lam) (s : P.State) :
    ((P.scaleState hlam s).1 : ℝ) = lam * (s.1 : ℝ) := rfl

@[simp] theorem scaleState_snd (hlam : 0 < lam) (s : P.State) :
    (P.scaleState hlam s).2 = s.2 := rfl

theorem continuous_scaleState (hlam : 0 < lam) : Continuous (P.scaleState hlam) :=
  ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk
    continuous_snd

theorem measurable_scaleState (hlam : 0 < lam) : Measurable (P.scaleState hlam) :=
  (P.continuous_scaleState hlam).measurable

/-- The state map as a continuous map, for composing with test functions. -/
noncomputable def scaleStateC (hlam : 0 < lam) : C(P.State, (P.scale hlam).State) :=
  ⟨P.scaleState hlam, P.continuous_scaleState hlam⟩

/-! ### The motion commutes with the map

This is where the policy scaling enters: next period's assets in the scaled economy, starting
from the scaled state, are `λ` times next period's assets in the original. -/

theorem scaleState_nextState (hlam : 0 < lam)
    (hdom : ∀ c : ℝ, lam * c ∈ P.dom ↔ c ∈ P.dom) {k m : ℝ}
    (hu : ∀ c ∈ P.dom, P.u (lam * c) = k * P.u c + m) (hk : 0 < k)
    (s : P.State) (z' : Z) :
    (P.scale hlam).nextState (P.scaleState hlam s) z' = P.scaleState hlam (P.nextState s z') := by
  refine Prod.ext ?_ rfl
  refine Subtype.ext ?_
  show (P.scale hlam).policy (lam * (s.1 : ℝ), s.2) = lam * P.policy ((s.1 : ℝ), s.2)
  exact P.policy_scale hlam hdom hu hk s.1.2 s.2

theorem markovOp_scaleState (hlam : 0 < lam)
    (hdom : ∀ c : ℝ, lam * c ∈ P.dom ↔ c ∈ P.dom) {k m : ℝ}
    (hu : ∀ c ∈ P.dom, P.u (lam * c) = k * P.u c + m) (hk : 0 < k)
    (h : (P.scale hlam).State →ᵇ ℝ) (s : P.State) :
    (P.scale hlam).markovOp h (P.scaleState hlam s)
      = P.markovOp (h.compContinuous (P.scaleStateC hlam)) s := by
  simp only [markovOp_apply, compContinuous_apply]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [P.scaleState_nextState hlam hdom hu hk s z']
  rfl

/-! ### The pushforward of a distribution -/

/-- The pushforward of a probability measure on `P`'s states along `scaleState`. -/
noncomputable def scaleProb (hlam : 0 < lam) (μ : ProbabilityMeasure P.State) :
    ProbabilityMeasure (P.scale hlam).State :=
  ⟨(μ : Measure P.State).map (P.scaleState hlam), ⟨by
    have : IsProbabilityMeasure (μ : Measure P.State) := μ.2
    rw [Measure.map_apply (P.measurable_scaleState hlam) MeasurableSet.univ, preimage_univ,
      measure_univ]⟩⟩

theorem coe_scaleProb (hlam : 0 < lam) (μ : ProbabilityMeasure P.State) :
    ((P.scaleProb hlam μ : ProbabilityMeasure (P.scale hlam).State) : Measure (P.scale hlam).State)
      = (μ : Measure P.State).map (P.scaleState hlam) := rfl

theorem integral_scaleProb (hlam : 0 < lam) (μ : ProbabilityMeasure P.State)
    (h : (P.scale hlam).State →ᵇ ℝ) :
    ∫ s, h s ∂(P.scaleProb hlam μ : Measure (P.scale hlam).State)
      = ∫ s, h (P.scaleState hlam s) ∂(μ : Measure P.State) := by
  rw [coe_scaleProb, integral_map (P.measurable_scaleState hlam).aemeasurable
    h.continuous.measurable.aestronglyMeasurable]

/-- **One period of motion commutes with scaling.** -/
theorem pushProb_scaleProb (hlam : 0 < lam)
    (hdom : ∀ c : ℝ, lam * c ∈ P.dom ↔ c ∈ P.dom) {k m : ℝ}
    (hu : ∀ c ∈ P.dom, P.u (lam * c) = k * P.u c + m) (hk : 0 < k)
    (μ : ProbabilityMeasure P.State) :
    (P.scale hlam).pushProb (P.scaleProb hlam μ) = P.scaleProb hlam (P.pushProb μ) := by
  have key : ∀ f : (P.scale hlam).State →ᵇ ℝ,
      ∫ s, f s ∂(((P.scale hlam).pushProb (P.scaleProb hlam μ)
          : ProbabilityMeasure (P.scale hlam).State) : Measure (P.scale hlam).State)
        = ∫ s, f s ∂((P.scaleProb hlam (P.pushProb μ)
          : ProbabilityMeasure (P.scale hlam).State) : Measure (P.scale hlam).State) := by
    intro f
    haveI hprob : IsProbabilityMeasure (P.scaleProb hlam μ : Measure (P.scale hlam).State) :=
      (P.scaleProb hlam μ).2
    haveI hprob' : IsProbabilityMeasure (μ : Measure P.State) := μ.2
    calc ∫ s, f s ∂(((P.scale hlam).pushProb (P.scaleProb hlam μ)
            : ProbabilityMeasure (P.scale hlam).State) : Measure (P.scale hlam).State)
        = ∫ s, (P.scale hlam).markovOp f s
            ∂(P.scaleProb hlam μ : Measure (P.scale hlam).State) := by
          rw [coe_pushProb, (P.scale hlam).integral_push]
      _ = ∫ s, (P.scale hlam).markovOp f (P.scaleState hlam s) ∂(μ : Measure P.State) :=
          P.integral_scaleProb hlam μ _
      _ = ∫ s, P.markovOp (f.compContinuous (P.scaleStateC hlam)) s ∂(μ : Measure P.State) :=
          integral_congr_ae (Filter.Eventually.of_forall fun s =>
            P.markovOp_scaleState hlam hdom hu hk f s)
      _ = ∫ s, (f.compContinuous (P.scaleStateC hlam)) s ∂(P.push (μ : Measure P.State)) :=
          (P.integral_push _ _).symm
      _ = ∫ s, f (P.scaleState hlam s) ∂(P.push (μ : Measure P.State)) := rfl
      _ = ∫ s, f s ∂((P.scaleProb hlam (P.pushProb μ)
            : ProbabilityMeasure (P.scale hlam).State) : Measure (P.scale hlam).State) := by
          rw [P.integral_scaleProb hlam (P.pushProb μ), coe_pushProb]
  have hfin : ((P.scale hlam).pushProb (P.scaleProb hlam μ)).toFiniteMeasure
      = (P.scaleProb hlam (P.pushProb μ)).toFiniteMeasure :=
    FiniteMeasure.ext_of_forall_integral_eq key
  exact ProbabilityMeasure.toMeasure_injective
    (congrArg (fun x : FiniteMeasure (P.scale hlam).State => (x : Measure (P.scale hlam).State))
      hfin)

/-- **The pushforward of a stationary distribution is stationary.** -/
theorem isStationary_scaleProb (hlam : 0 < lam)
    (hdom : ∀ c : ℝ, lam * c ∈ P.dom ↔ c ∈ P.dom) {k m : ℝ}
    (hu : ∀ c ∈ P.dom, P.u (lam * c) = k * P.u c + m) (hk : 0 < k)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    (P.scale hlam).IsStationary (P.scaleProb hlam μ) := by
  change (P.scale hlam).pushProb (P.scaleProb hlam μ) = P.scaleProb hlam μ
  rw [P.pushProb_scaleProb hlam hdom hu hk μ]
  change P.scaleProb hlam (P.pushProb μ) = P.scaleProb hlam μ
  rw [show P.pushProb μ = μ from hμ]

/-- **Aggregate capital scales by `λ`**: Açıkgöz Proposition 7 at the level of the distribution. -/
theorem aggregateCapital_scaleProb (hlam : 0 < lam) (μ : ProbabilityMeasure P.State) :
    (P.scale hlam).aggregateCapital (P.scaleProb hlam μ) = lam * P.aggregateCapital μ := by
  simp only [aggregateCapital]
  rw [P.integral_scaleProb hlam μ (P.scale hlam).assetCoord]
  have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
  rw [← integral_const_mul]
  rfl

/-! ### Log utility -/

/-- The scaling law for log: `log (λ c) = 1 · log c + log λ`, on the domain `Ioi 0`. -/
theorem log_scale_law (hlam : 0 < lam) (hunb : P.Unbounded) (hu : P.u = crraUtility 1) :
    ∀ c ∈ P.dom, P.u (lam * c) = 1 * P.u c + Real.log lam := by
  intro c hc
  rw [hunb] at hc
  rw [hu, crraUtility_one]
  exact log_scale hlam c hc

theorem isStationary_scaleProb_log (hlam : 0 < lam) (hunb : P.Unbounded)
    (hu : P.u = crraUtility 1) {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    (P.scale hlam).IsStationary (P.scaleProb hlam μ) :=
  P.isStationary_scaleProb hlam (P.dom_scale_invariant_of_unbounded hlam hunb)
    (P.log_scale_law hlam hunb hu) one_pos hμ

/-! ### Scaling preserves the hypotheses of the Doeblin chain -/

/-- Monotone transitions are a property of the income ORDER, which scaling preserves. -/
theorem monotoneTransitions_scale (hlam : 0 < lam) (hmono : P.MonotoneTransitions) :
    (P.scale hlam).MonotoneTransitions := by
  intro z₁ z₂ hz f hf
  have hz' : P.income z₁ ≤ P.income z₂ :=
    le_of_mul_le_mul_left (by simpa [scale] using hz) hlam
  exact hmono z₁ z₂ hz' f fun w₁ w₂ hw =>
    hf w₁ w₂ (by simp only [scale]; exact mul_le_mul_of_nonneg_left hw hlam.le)

/-! ### Aiyagari's own equilibrium condition

Aiyagari writes the steady state as `K(r) = Ea(r)`, with `Ea` computed in the economy whose
income is `w(r) · l`. That economy is `(P.withRate r).scale (w r)` for the unit-wage economy `P`,
and its unique stationary distribution is the pushforward of `P`'s. So `Ea_w = w · Ea₁`, and his
condition is `Ea₁(r) = k(r)/w(r)` — the normalised one, whose
uniqueness is `log_equilibriumRate_unique`.
The theorem below is that argument, with the scaled economy's Doeblin hypotheses checked by
scaling the unit-wage ones. -/

section Bridge

variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **Uniqueness of the equilibrium rate in Aiyagari's own form.** Two rates in `[0, rhi]`, each
with a stationary distribution of the wage-`w(r)` economy whose aggregate capital is the firm's
`k(r)`, coincide. -/
theorem log_equilibriumRate_unique_wage {rhi ε a₀ α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ : 0 < δ) (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ)) (hrhi : 0 ≤ rhi) (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hε : 0 < ε)
    (hcap : (P.discount : ℝ) * P.maxIncome
      + ((P.discount : ℝ) * (1 + rhi) + ε) * assetCap < assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hreach : ∀ z, 0 < P.transitionMatrix z z₀) (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hcorn : (P.discount : ℝ) * (1 + rhi) * (P.income z₀ + (1 + rhi) * a₀) < P.minIncome)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc (0 : ℝ) rhi) (h₂ : r₂ ∈ Icc (0 : ℝ) rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    (hw₁ : 0 < cobbDouglasWage α δ r₁) (hw₂ : 0 < cobbDouglasWage α δ r₂)
    {μ₁ : ProbabilityMeasure ((P.withRate r₁ hrr₁).scale hw₁).State}
    {μ₂ : ProbabilityMeasure ((P.withRate r₂ hrr₂).scale hw₂).State}
    (hμ₁ : ((P.withRate r₁ hrr₁).scale hw₁).IsStationary μ₁)
    (hμ₂ : ((P.withRate r₂ hrr₂).scale hw₂).IsStationary μ₂)
    (he₁ : ((P.withRate r₁ hrr₁).scale hw₁).aggregateCapital μ₁ = cobbDouglasCapital α δ r₁)
    (he₂ : ((P.withRate r₂ hrr₂).scale hw₂).aggregateCapital μ₂ = cobbDouglasCapital α δ r₂) :
    r₁ = r₂ := by
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hcap' : (P.discount : ℝ) * (P.maxIncome + (1 + rhi) * assetCap) < assetCap := by
    have := mul_nonneg hε.le hcap0
    nlinarith
  have hmin : 0 < P.minIncome := P.minIncome_pos
  have hy₀ : 0 < P.income z₀ := lt_of_lt_of_le hmin (P.minIncome_le z₀)
  -- the scaled economy at rate `r` has a unique stationary distribution, by the same chain
  have key : ∀ {r : ℝ} (hr : r ∈ Icc (0 : ℝ) rhi) (hrr : P.RateOK r) {w : ℝ} (hw : 0 < w),
      ∃! μ : ProbabilityMeasure ((P.withRate r hrr).scale hw).State,
        ((P.withRate r hrr).scale hw).IsStationary μ := by
    intro r hr hrr w hw
    set Q := (P.withRate r hrr).scale hw with hQ
    have hR : (0 : ℝ) < 1 + r := by linarith [hr.1]
    have hβR' : (P.discount : ℝ) * (1 + r) < 1 := by nlinarith [hr.2, hβ]
    have hQκ : 1 - Q.minMPC 1 = (P.discount : ℝ) := by
      rw [IncomeFluctuation.minMPC_one]
      change 1 - (1 - (P.discount : ℝ)) = (P.discount : ℝ)
      ring
    refine Q.crra_existsUnique_isStationary_of_euler_corner_monotone (γ := 1) one_pos
      (show Q.u = crraUtility 1 from hu) (mul_zero w) (show (0 : ℝ) ≤ r from hr.1) hβ hβR'
      ((P.withRate r hrr).monotoneTransitions_scale hw hmono)
      (Q.positiveConsumptionAll_of_unbounded hunb) ?_ (z₀ := z₀) ?_ hreach (a₀ := w * a₀)
      (mul_pos hw ha₀) (mul_le_mul_of_nonneg_left hle hw.le) ?_
    · -- the cap condition, scaled by `w`
      rw [hQκ]
      change (P.discount : ℝ) * (w * P.maxIncome + (1 + r) * (w * assetCap)) < w * assetCap
      have hbase : (P.discount : ℝ) * (P.maxIncome + (1 + r) * assetCap) < assetCap := by
        have := mul_le_mul_of_nonneg_left (show (1 + r) * assetCap ≤ (1 + rhi) * assetCap from
          mul_le_mul_of_nonneg_right (by linarith [hr.2]) hcap0) hβ.le
        linarith
      have := mul_lt_mul_of_pos_left hbase hw
      nlinarith
    · intro z
      change w * P.income z₀ ≤ w * P.income z
      exact mul_le_mul_of_nonneg_left (hz₀ z) hw.le
    · -- the corner test, scaled by `w`
      change (P.discount : ℝ) * (1 + r) * (w * P.minIncome) ^ (-(1 : ℝ))
        < (w * P.income z₀ + (1 + r) * (w * a₀)) ^ (-(1 : ℝ))
      have hq : 0 < w * P.income z₀ + (1 + r) * (w * a₀) := by positivity
      have hbase : (P.discount : ℝ) * (1 + r) * (P.income z₀ + (1 + r) * a₀) < P.minIncome := by
        have h1 : (P.discount : ℝ) * (1 + r) ≤ (P.discount : ℝ) * (1 + rhi) :=
          mul_le_mul_of_nonneg_left (by linarith [hr.2]) hβ.le
        have h2 : P.income z₀ + (1 + r) * a₀ ≤ P.income z₀ + (1 + rhi) * a₀ := by
          nlinarith [hr.2]
        have h0 : 0 < P.income z₀ + (1 + r) * a₀ := by positivity
        calc (P.discount : ℝ) * (1 + r) * (P.income z₀ + (1 + r) * a₀)
            ≤ (P.discount : ℝ) * (1 + rhi) * (P.income z₀ + (1 + rhi) * a₀) :=
              mul_le_mul h1 h2 h0.le (by positivity)
          _ < P.minIncome := hcorn
      rw [Real.rpow_neg_one, Real.rpow_neg_one, mul_inv_lt_iff₀ (by positivity),
        inv_mul_eq_div, lt_div_iff₀ hq]
      have := mul_lt_mul_of_pos_left hbase hw
      nlinarith
  -- the unit-wage stationary distributions, and their pushforwards
  obtain ⟨ν₁, hν₁, -⟩ := P.log_existsUnique_isStationary hu hunb hβ hβR hcap' hmono hz₀ hreach ha₀
    hle hcorn h₁ hrr₁
  obtain ⟨ν₂, hν₂, -⟩ := P.log_existsUnique_isStationary hu hunb hβ hβR hcap' hmono hz₀ hreach ha₀
    hle hcorn h₂ hrr₂
  have hs₁ : ((P.withRate r₁ hrr₁).scale hw₁).IsStationary
      ((P.withRate r₁ hrr₁).scaleProb hw₁ ν₁) :=
    (P.withRate r₁ hrr₁).isStationary_scaleProb_log hw₁ hunb hu hν₁
  have hs₂ : ((P.withRate r₂ hrr₂).scale hw₂).IsStationary
      ((P.withRate r₂ hrr₂).scaleProb hw₂ ν₂) :=
    (P.withRate r₂ hrr₂).isStationary_scaleProb_log hw₂ hunb hu hν₂
  have hid₁ : μ₁ = (P.withRate r₁ hrr₁).scaleProb hw₁ ν₁ := by
    obtain ⟨m, -, huniq⟩ := key h₁ hrr₁ hw₁
    rw [huniq _ hμ₁, huniq _ hs₁]
  have hid₂ : μ₂ = (P.withRate r₂ hrr₂).scaleProb hw₂ ν₂ := by
    obtain ⟨m, -, huniq⟩ := key h₂ hrr₂ hw₂
    rw [huniq _ hμ₂, huniq _ hs₂]
  -- so aggregate capital at wage `w` is `w` times the unit-wage one, and the condition normalises
  rw [hid₁, (P.withRate r₁ hrr₁).aggregateCapital_scaleProb hw₁ ν₁] at he₁
  rw [hid₂, (P.withRate r₂ hrr₂).aggregateCapital_scaleProb hw₂ ν₂] at he₂
  have hn₁ : P.aggregateCapital ν₁ = normalisedDemand α δ r₁ := by
    rw [← cobbDouglasCapital_div_wage hα0 hα1 (by linarith [h₁.1]), eq_div_iff hw₁.ne',
      mul_comm]
    exact he₁
  have hn₂ : P.aggregateCapital ν₂ = normalisedDemand α δ r₂ := by
    rw [← cobbDouglasCapital_div_wage hα0 hα1 (by linarith [h₂.1]), eq_div_iff hw₂.ne',
      mul_comm]
    exact he₂
  exact P.log_equilibriumRate_unique hα0 hα1 hδ hu hunb hβ hrhi hβR hε hcap hmono hz₀ hreach ha₀
    hle hcorn h₁ h₂ hrr₁ hrr₂ hν₁ hν₂ hn₁ hn₂

/-- **Aiyagari (1994) at `μ = 1`, in his own form**: `K(r) = Ea(r)` at the wage `w(r)`, with the
constants constructed from one inequality on the cap. -/
theorem aiyagari1994_equilibriumRate_unique_wage {rhi : ℝ}
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded) (hβ : (P.discount : ℝ) = 24 / 25)
    (hrhi : 0 ≤ rhi) (hlam : rhi < 1 / 24)
    (hcap : 2 * (24 / 25) * P.maxIncome < (1 - 24 / 25 * (1 + rhi)) * assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hmin : P.income z₀ = P.minIncome) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc (0 : ℝ) rhi) (h₂ : r₂ ∈ Icc (0 : ℝ) rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    (hw₁ : 0 < cobbDouglasWage (9 / 25) (2 / 25) r₁) (hw₂ : 0 < cobbDouglasWage (9 / 25)
        (2 / 25) r₂)
    {μ₁ : ProbabilityMeasure ((P.withRate r₁ hrr₁).scale hw₁).State}
    {μ₂ : ProbabilityMeasure ((P.withRate r₂ hrr₂).scale hw₂).State}
    (hμ₁ : ((P.withRate r₁ hrr₁).scale hw₁).IsStationary μ₁)
    (hμ₂ : ((P.withRate r₂ hrr₂).scale hw₂).IsStationary μ₂)
    (he₁ : ((P.withRate r₁ hrr₁).scale hw₁).aggregateCapital μ₁
      = cobbDouglasCapital (9 / 25) (2 / 25) r₁)
    (he₂ : ((P.withRate r₂ hrr₂).scale hw₂).aggregateCapital μ₂
      = cobbDouglasCapital (9 / 25) (2 / 25) r₂) : r₁ = r₂ := by
  have hβ' : 0 < (P.discount : ℝ) := by rw [hβ]; norm_num
  have hβR : (P.discount : ℝ) * (1 + rhi) < 1 := by rw [hβ]; linarith
  have hroom : (0 : ℝ) < 1 - 24 / 25 * (1 + rhi) := by linarith
  have hmaxpos : 0 < P.maxIncome := lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxIncome
  have hcap0 : 0 < assetCap := by
    by_contra h
    have h' : assetCap ≤ 0 := not_lt.mp h
    have : (1 - 24 / 25 * (1 + rhi)) * assetCap ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hroom.le h'
    nlinarith [hcap, hmaxpos]
  have hminpos : 0 < P.minIncome := P.minIncome_pos
  set ε : ℝ := (1 - 24 / 25 * (1 + rhi)) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set A : ℝ := P.minIncome * (1 - 24 / 25 * (1 + rhi)) / (2 * (24 / 25) * (1 + rhi) ^ 2)
    with hAdef
  have hA : 0 < A := by rw [hAdef]; positivity
  set a₀ : ℝ := min assetCap A with ha₀def
  have ha₀ : 0 < a₀ := lt_min hcap0 hA
  have hle : a₀ ≤ assetCap := min_le_left _ _
  have ha₀A : a₀ ≤ A := min_le_right _ _
  have hcapε : (P.discount : ℝ) * P.maxIncome
      + ((P.discount : ℝ) * (1 + rhi) + ε) * assetCap < assetCap := by
    rw [hβ, hεdef]
    nlinarith [hcap]
  have hcorn : (P.discount : ℝ) * (1 + rhi) * (P.income z₀ + (1 + rhi) * a₀) < P.minIncome := by
    rw [hβ, hmin]
    have hR : (0 : ℝ) < 1 + rhi := by linarith
    have hkey : 24 / 25 * (1 + rhi) * ((1 + rhi) * A)
        = P.minIncome * (1 - 24 / 25 * (1 + rhi)) / 2 := by
      rw [hAdef]; field_simp; try ring
    have hmono' : 24 / 25 * (1 + rhi) * ((1 + rhi) * a₀) ≤ 24 / 25 * (1 + rhi) * ((1 + rhi) * A) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha₀A hR.le) (by positivity)
    have : 24 / 25 * (1 + rhi) * (P.minIncome + (1 + rhi) * a₀)
        = 24 / 25 * (1 + rhi) * P.minIncome + 24 / 25 * (1 + rhi) * ((1 + rhi) * a₀) := by ring
    rw [this]
    nlinarith [hkey, hmono', hroom, hminpos]
  exact P.log_equilibriumRate_unique_wage (by norm_num) (by norm_num) (by norm_num) hu hunb hβ'
    hrhi hβR hε hcapε hmono hz₀ hreach ha₀ hle hcorn h₁ h₂ hrr₁ hrr₂ hw₁ hw₂ hμ₁ hμ₂ he₁ he₂

end Bridge

end IncomeFluctuation

end LeanEconomics
