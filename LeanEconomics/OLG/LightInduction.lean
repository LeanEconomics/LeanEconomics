/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.RateMonotone
import LeanEconomics.Models.IncomeFluctuationRateStep

/-!
# Theorem 1 in the life cycle at relative risk aversion at most one: Light's induction

Light (2020) proves that saving rises with the interest rate by an induction on Bellman iterates
from zero: if the continuation's marginal value rises with the rate, so does the next iterate's,
given concavity of the consumption function and relative risk aversion at most one. The iterates
from zero are the stage values of the life cycle, so his induction IS the stage induction, and
the step is already proved for the stationary problem
(`incDiffSlices_bellman_withRate`, in `Models/IncomeFluctuationRateStep`). This file runs it on
`stageValue`.

The conclusion is `ValueGap` of `RateMonotone` with slope zero at every stage, and from it
Theorem 1 at every state and age by the one-economy chain of the stationary file:

  `g_k(a; r₁) = g_k^{(2)}(t a; v₁) ≤ g_k^{(2)}(t a; v₂) = g_k(t a; r₂) ≤ g_k(a; r₂)`,  `t = R₁/R₂`,

the equality the budget coincidence (`policyOf_withRate`), the first inequality single crossing
in the continuation (`policyOf_le_of_contOf_increasingDifferences`, which needs no margin: the
lower-rate maximiser is unique), the last monotonicity in wealth.

## What it gives

For CRRA with `γ ≤ 1`, any discount factor, any finite Markov earnings process and any horizon,
saving rises with the rate at every state and age (`stagePolicy_mono_light_crra`), so aggregate
capital rises with the rate (`olgCapital_le_light_crra`, `monotoneOn_olgCapital_light_crra`)
and the stationary equilibrium rate is unique (`olgEquilibriumRate_unique_light_crra`). The
hypotheses are the standing ones: utility unbounded below at zero consumption (which with CRRA
pins `γ = 1`, `crra_pinch`), and the saving cap slack at the higher rate along every stage. The
exact-arithmetic certificate of the write-up covered one calibration at `γ = 1`; this covers all
of them, with no computation.

Nothing here reaches `γ > 1`: the pivotal inequality of the step needs `c u'(c)` increasing.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)
variable {r₁ r₂ : ℝ}

/-- **Light's induction on the stage values.** The stage values at two rates have increasing
differences in wealth at every stage. The hybrid positivity and slack hypotheses of the
stationary step are discharged inside the induction: positivity from `Unbounded`, and cap slack
for economy two against economy ONE's continuation from single crossing (the induction
hypothesis) and cap slack against its own. -/
theorem stageValue_incDiffSlices (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hrra : MonotoneOn (fun y => y * du y) (Ioi (0 : ℝ)))
    (hdunn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ du y) (hdunb : P.Unbounded)
    (hcap₂ : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r₂ h₂).stagePolicy k (a, z) < assetCap)
    (hcons : ∀ k : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      ((P.withRate r₂ h₂).stageConsumption k z)) (k : ℕ) :
    IncDiffSlices (0 : ℝ) assetCap ((P.withRate r₁ h₁).stageValue k)
      ((P.withRate r₂ h₂).stageValue k) := by
  induction k with
  | zero => exact incDiffSlices_zero _ _
  | succ k ih =>
    have hd₂ : (P.withRate r₂ h₂).Unbounded := hdunb
    have hws := (P.withRate r₂ h₂).concaveSlices_stageValue k
    have hslackv : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
        (P.withRate r₂ h₂).policyOf ((P.withRate r₁ h₁).stageValue k) (a, z) < assetCap :=
      fun a ha z => lt_of_le_of_lt
        ((P.withRate r₂ h₂).policyOf_le_of_contOf_increasingDifferences hws
          ((P.withRate r₂ h₂).contOfIncreasingDifferences_of_slices ih) ha)
        (hcap₂ k a ha z)
    rw [(P.withRate r₁ h₁).stageValue_succ, (P.withRate r₂ h₂).stageValue_succ]
    exact P.incDiffSlices_bellman_withRate h₁ h₂ hr hderiv hanti hrra hdunn
      ((P.withRate r₁ h₁).concaveSlices_stageValue k) hws
      (fun a ha _ => (P.withRate r₂ h₂).consumptionFnOf_pos hd₂ _ ha)
      (fun a ha _ => (P.withRate r₂ h₂).consumptionFnOf_pos hd₂ _ ha)
      hslackv (fun a ha z => hcap₂ k a ha z) (hcons k) ih

/-- The induction read as the value-gap condition of `RateMonotone`, with slope zero. -/
theorem valueGap_zero_of_light (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hrra : MonotoneOn (fun y => y * du y) (Ioi (0 : ℝ)))
    (hdunn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ du y) (hdunb : P.Unbounded)
    (hcap₂ : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r₂ h₂).stagePolicy k (a, z) < assetCap)
    (hcons : ∀ k : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      ((P.withRate r₂ h₂).stageConsumption k z)) (k : ℕ) :
    P.ValueGap h₁ h₂ 0 k := by
  intro z x hx y hy hxy
  have h := P.stageValue_incDiffSlices h₁ h₂ hr hderiv hanti hrra hdunn hdunb hcap₂ hcons k
    z x y hx hy hxy
  linarith

/-- **Theorem 1 at every state and age, from Light's induction.** -/
theorem stagePolicy_mono_light (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hrra : MonotoneOn (fun y => y * du y) (Ioi (0 : ℝ)))
    (hdunn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ du y) (hdunb : P.Unbounded)
    (hcap₂ : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r₂ h₂).stagePolicy k (a, z) < assetCap)
    (hcons : ∀ k : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      ((P.withRate r₂ h₂).stageConsumption k z))
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).stagePolicy k (a, z) ≤ (P.withRate r₂ h₂).stagePolicy k (a, z) := by
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have ht0 : (0 : ℝ) < (1 + r₁) / (1 + r₂) := div_pos hR₁ hR₂
  have ht1 : (1 + r₁) / (1 + r₂) ≤ 1 := by rw [div_le_one hR₂]; linarith
  have htle : (1 + r₁) / (1 + r₂) * a ≤ a := mul_le_of_le_one_left ha.1 ht1
  have hta : (1 + r₁) / (1 + r₂) * a ∈ Icc (0 : ℝ) assetCap :=
    ⟨mul_nonneg ht0.le ha.1, le_trans htle ha.2⟩
  have hid := P.stageValue_incDiffSlices h₁ h₂ hr hderiv hanti hrra hdunn hdunb hcap₂ hcons k
  calc (P.withRate r₁ h₁).stagePolicy k (a, z)
      = (P.withRate r₂ h₂).policyOf ((P.withRate r₁ h₁).stageValue k)
          ((1 + r₁) / (1 + r₂) * a, z) :=
        P.policyOf_withRate h₁ h₂ hr ((P.withRate r₁ h₁).concaveSlices_stageValue k) z ha
    _ ≤ (P.withRate r₂ h₂).stagePolicy k ((1 + r₁) / (1 + r₂) * a, z) :=
        (P.withRate r₂ h₂).policyOf_le_of_contOf_increasingDifferences
          ((P.withRate r₂ h₂).concaveSlices_stageValue k)
          ((P.withRate r₂ h₂).contOfIncreasingDifferences_of_slices hid) hta
    _ ≤ (P.withRate r₂ h₂).stagePolicy k (a, z) :=
        (P.withRate r₂ h₂).stagePolicy_mono k hta ha htle

/-- **Theorem 1 for CRRA with relative risk aversion at most one**, every calibration. -/
theorem stagePolicy_mono_light_crra {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hu : P.u = crraUtility γ) (hβ : 0 < (P.discount : ℝ)) (hdunb : P.Unbounded)
    (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hcap₂ : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r₂ h₂).stagePolicy k (a, z) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).stagePolicy k (a, z) ≤ (P.withRate r₂ h₂).stagePolicy k (a, z) := by
  have hpow : ∀ c : ℝ, 0 < c → c * c ^ (-γ) = c ^ (1 - γ) := by
    intro c hc
    rw [show (1 : ℝ) - γ = 1 + -γ by ring, Real.rpow_add hc, Real.rpow_one]
  have hcons : ∀ k : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      ((P.withRate r₂ h₂).stageConsumption k z) := fun k z =>
    (P.withRate r₂ h₂).concaveOn_stageConsumption
      ((P.withRate r₂ h₂).positiveConsumptionAll_of_unbounded hdunb) hγ0 hβ hu hcap₂ k z
  refine P.stagePolicy_mono_light h₁ h₂ hr (du := fun c => c ^ (-γ)) ?_ ?_ ?_ ?_ hdunb hcap₂
    hcons k z ha
  · intro c hc
    rw [hu]
    exact hasDerivAt_crraUtility γ hc
  · intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)
  · intro x hx y hy hxy
    simp only []
    rw [hpow x hx, hpow y hy]
    exact Real.rpow_le_rpow hx.le hxy (by linarith)
  · intro y hy
    exact Real.rpow_nonneg hy.le _

/-- **Aggregate capital rises with the rate** (Theorem 2 in the life cycle), from Theorem 1. -/
theorem olgCapital_le_light_crra {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hu : P.u = crraUtility γ) (hβ : 0 < (P.discount : ℝ)) (hdunb : P.Unbounded)
    (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hcap₂ : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r₂ h₂).stagePolicy k (a, z) < assetCap)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) :
    (P.withRate r₁ h₁).olgCapital K ν ≤ (P.withRate r₂ h₂).olgCapital K ν :=
  (P.withRate r₁ h₁).olgCapital_le_of_stagePolicy_le (Q := P.withRate r₂ h₂) rfl
    (fun j s hs => by
      simpa using P.stagePolicy_mono_light_crra hγ0 hγ1 hu hβ hdunb h₁ h₂ hr hcap₂ j s.2 hs)
    K hν

/-- **Capital supply is monotone on a rate interval.** The economies along the interval are
given as a family `Q` agreeing with `P.withRate`, as in the stationary development. -/
theorem monotoneOn_olgCapital_light_crra {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hu : P.u = crraUtility γ) (hβ : 0 < (P.discount : ℝ)) (hdunb : P.Unbounded)
    {s : Set ℝ} (Q : ℝ → IncomeFluctuation Z 0 assetCap)
    (hQ : ∀ r ∈ s, ∃ h : P.RateOK r, Q r = P.withRate r h)
    (hcap : ∀ r ∈ s, ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (Q r).stagePolicy k (a, z) < assetCap)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) :
    MonotoneOn (fun r => (Q r).olgCapital K ν) s := by
  intro r hr r' hr' hle
  obtain ⟨h, hQr⟩ := hQ r hr
  obtain ⟨h', hQr'⟩ := hQ r' hr'
  have hcap' := hcap r' hr'
  rw [hQr'] at hcap'
  simp only [hQr, hQr']
  exact P.olgCapital_le_light_crra hγ0 hγ1 hu hβ hdunb h h' hle hcap' K hν

/-- **The stationary equilibrium rate is unique**, for CRRA with `γ ≤ 1`: two rates in `s` at
which capital supply meets a strictly falling demand are the same rate. -/
theorem olgEquilibriumRate_unique_light_crra {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hu : P.u = crraUtility γ) (hβ : 0 < (P.discount : ℝ)) (hdunb : P.Unbounded)
    {s : Set ℝ} (Q : ℝ → IncomeFluctuation Z 0 assetCap)
    (hQ : ∀ r ∈ s, ∃ h : P.RateOK r, Q r = P.withRate r h)
    (hcap : ∀ r ∈ s, ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (Q r).stagePolicy k (a, z) < assetCap)
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) {D : ℝ → ℝ} (hD : StrictAntiOn D s)
    {ra rb : ℝ} (hra : ra ∈ s) (hrb : rb ∈ s)
    (ha : (Q ra).olgCapital K ν = D ra) (hb : (Q rb).olgCapital K ν = D rb) : ra = rb :=
  olgEquilibriumRate_unique (P.monotoneOn_olgCapital_light_crra hγ0 hγ1 hu hβ hdunb Q hQ hcap K hν)
    hD hra hrb ha hb

end IncomeFluctuation

end LeanEconomics
