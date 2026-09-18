/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.CESRateMonotone
import LeanEconomics.Models.ImpatientDecline
import LeanEconomics.Equilibrium.CapitalSupplyMonotone
import LeanEconomics.Models.IncomeFluctuationHARA

/-!
# Uniqueness of the equilibrium rate, for a CLASS of economies

`CESUniqueness` proves the Aiyagari equilibrium rate unique for `nearLog`, one calibration. The
argument never used anything specific to it, and this file says so: it collects the hypotheses
into `Calibrated` and runs the whole chain from them.

## What the class asks for

Five things, and each is either a preference restriction or a statement that the asset cap is an
artefact.

* CRRA with `0 < γ < 1` and a bounded domain. `γ < 1` puts the economy in the bounded family,
  where consumption is positive because the margin pays for it; `γ ≤ 1` is Light's condition.
* Impatience `β(1 + r) < 1` on the rate interval. By `crra_exists_exhaust_of_impatient` this is
  the decline condition, so nothing numerical is needed for it.
* An oscillation bound `G` uniform in the rate, and the cap slack it buys: no continuation with
  oscillation at most `G` makes the household save all the way to the ceiling. This is the one
  genuinely numerical hypothesis, and it is the cap being an artefact.
* The corner condition: at the lowest income state the household saves nothing below `a₀`. The
  Doeblin argument needs the constraint to be REACHED, not approached, and that cannot come from
  impatience.
* Income iid, the lowest income state reachable from everywhere.

## What comes out

Capital supply is a genuine function of the rate (`stationary`), it is monotone
(`monotoneOn_capitalSupply`), and the equilibrium rate is unique (`equilibriumRate_unique`).
`nearLog` is an instance — `nearLog_calibrated` — so `CESUniqueness`'s results are this theorem
read at one point.
-/

open scoped NNReal
open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ}

/-- **A calibrated economy**: everything the uniqueness chain needs, in primitives. -/
structure Calibrated (P : IncomeFluctuation Z 0 assetCap) (γ η G a₀ : ℝ) (z₀ : Z)
    (rlo rhi : ℝ) : Prop where
  /-- Shifted CRRA, the `b ≠ 0` branch of HARA. `η = 0` is CRRA itself. -/
  gamma_pos : 0 < γ
  /-- Light's condition. Strictness is not needed: with a strictly positive subsistence level
  `γ = 1` — log Stone–Geary — is admissible, since `η + c` stays away from zero. -/
  gamma_le_one : γ ≤ 1
  eta_nonneg : 0 ≤ η
  utility : P.u = haraUtility γ η
  discount_pos : 0 < (P.discount : ℝ)
  /-- Consumption is positive at every optimum against every continuation the iteration can
  produce — concave slices, oscillation at most `G`. With CRRA this holds for EVERY continuation,
  by the Inada condition; with a subsistence level marginal utility at zero is finite and the
  oscillation bound is what makes the comparison go through
  (`consumptionFnOf_pos_of_marginal`). -/
  positive : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ v : (ℝ × Z) →ᵇ ℝ,
    ConcaveSlices (0 : ℝ) assetCap v → (P.withRate r hrr).OscOn v G →
    ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap, 0 < (P.withRate r hrr).consumptionFnOf v z a
  /-- The rate interval sits above zero, so every rate in it is admissible. -/
  rlo_nonneg : 0 ≤ rlo
  rate_le : rlo ≤ rhi
  /-- Income is iid, and `z₀` is its lowest state, reachable from everywhere. -/
  iid : P.IidIncome
  income_min : ∀ z, P.income z₀ ≤ P.income z
  reach : ∀ z, 0 < P.transitionMatrix z z₀
  /-- Impatience on the whole interval. -/
  impatient : ∀ r ∈ Icc rlo rhi, (P.discount : ℝ) * (1 + r) < 1
  /-- An oscillation bound uniform in the rate. -/
  osc_nonneg : 0 ≤ G
  osc_le : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).oscSpread ≤ G
  /-- The cap is slack against every continuation that oscillation bound allows. -/
  slack : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ v : (ℝ × Z) →ᵇ ℝ,
    ConcaveSlices (0 : ℝ) assetCap v → (P.withRate r hrr).OscOn v G →
    ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r hrr).policyOf v (a, z) < assetCap
  /-- The corner condition, below `a₀`. -/
  a₀_pos : 0 < a₀
  a₀_le : a₀ ≤ assetCap
  corner : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ a ∈ Icc (0 : ℝ) a₀,
    (P.withRate r hrr).policy (a, z₀) = 0

/-! ### Building the slack field from primitives

The `slack` field says the saving cap never binds against any continuation the iteration can
produce. `hara_policyOf_lt_assetCap` turns that into ONE inequality among the primitives, by
pricing a proportional deviation: cut saving to a fraction `θ` of itself, and the extra
consumption is worth more than the `βG` the continuation can possibly be giving up.

The only rate-dependence is through `1 + r` multiplying the cap, so the inequality is hardest at
the TOP of the interval and checking it at `rhi` suffices. `θ ∈ (0,1)` is a device of the proof,
not of the economy: any `θ` for which the inequality holds will do, and a witness picks the one
that makes its arithmetic easiest.

What is NOT eliminated is positivity of consumption, which the deviation argument needs in order
to price the margin. That is the class's own `positive` field, so a witness proves it once and
feeds it to both.

As with `corner_of_primitives`, this is the `η > 0` statement; pure CRRA keeps its own route
through `crra_policyOf_lt_assetCap`, where positivity is unconditional (Inada) and the exponent
is generally irrational, so the inequality is not rational arithmetic anyway. -/

theorem slack_of_primitives {P : IncomeFluctuation Z 0 assetCap} {γ η G θ : ℝ} {rlo rhi : ℝ}
    (hγ0 : 0 < γ) (hη : 0 ≤ η) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : P.u = haraUtility γ η)
    (hG : 0 ≤ G) (hrlo : 0 ≤ rlo)
    (hpos : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ v : (ℝ × Z) →ᵇ ℝ,
      ConcaveSlices (0 : ℝ) assetCap v → (P.withRate r hrr).OscOn v G →
      ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap, 0 < (P.withRate r hrr).consumptionFnOf v z a)
    (hcond : ((P.discount : ℝ) * G / θ)
        * (η + P.maxIncome + (1 + rhi - θ) * assetCap) ^ γ < assetCap) :
    ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ v : (ℝ × Z) →ᵇ ℝ,
      ConcaveSlices (0 : ℝ) assetCap v → (P.withRate r hrr).OscOn v G →
      ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r hrr).policyOf v (a, z) < assetCap := by
  intro r hr hrr v hv hosc a ha z
  have hcap : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hmax : (0 : ℝ) < P.maxIncome :=
    lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxIncome
  refine (P.withRate r hrr).hara_policyOf_lt_assetCap hγ0 hη hθ0 hθ1
    (show (P.withRate r hrr).u = haraUtility γ η from hu) hv hG hosc
    (fun z' a' ha' => hpos r hr hrr v hv hosc z' a' ha') ?_ ha z
  -- the inequality is hardest at `rhi`, since `r` enters only through `(1 + r - θ) * assetCap`
  have hbase : (0 : ℝ) ≤ η + P.maxIncome + (1 + r - θ) * assetCap := by
    have : (0 : ℝ) ≤ (1 + r - θ) * assetCap :=
      mul_nonneg (by linarith [hr.1]) hcap
    linarith
  have hmono : (η + P.maxIncome + (1 + r - θ) * assetCap) ^ γ
      ≤ (η + P.maxIncome + (1 + rhi - θ) * assetCap) ^ γ := by
    refine Real.rpow_le_rpow hbase ?_ hγ0.le
    have : (1 + r - θ) * assetCap ≤ (1 + rhi - θ) * assetCap :=
      mul_le_mul_of_nonneg_right (by linarith [hr.2]) hcap
    linarith
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hcoef : (0 : ℝ) ≤ (P.discount : ℝ) * G / θ := by positivity
  simp only [IncomeFluctuation.withRate_maxIncome, IncomeFluctuation.withRate_interest,
    IncomeFluctuation.withRate_discount, sub_zero, mul_zero]
  linarith [mul_le_mul_of_nonneg_left hmono hcoef, hcond]


/-! ### Building the corner field from primitives

The `corner` field is the one hypothesis of the class that a witness used to assemble by hand:
a Lipschitz bound for the value function, a marginal bound over the reachable consumption range,
and the comparison between them. For shifted CRRA both bounds have closed forms
(`hara_policy_eq_zero_of_primitives`), so the field reduces to ONE inequality among the
primitives, rate by rate. CRRA already had this (`crra_policy_eq_zero_uniform`); this is the
`η > 0` counterpart. -/

theorem corner_of_primitives {P : IncomeFluctuation Z 0 assetCap} {γ η a₀ : ℝ} {z₀ : Z}
    {rlo rhi : ℝ} (hγ0 : 0 < γ) (hη : 0 < η) (hu : P.u = haraUtility γ η)
    (ha₀ : 0 ≤ a₀) (ha₀cap : a₀ ≤ assetCap)
    (himp : ∀ r ∈ Icc rlo rhi, (P.discount : ℝ) * (1 + r) < 1)
    (hcond : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      (P.discount : ℝ) * (P.withRate r hrr).haraLipschitz γ η
        < (η + P.income z₀ + (1 + r) * a₀) ^ (-γ)) :
    ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ a ∈ Icc (0 : ℝ) a₀,
      (P.withRate r hrr).policy (a, z₀) = 0 := by
  intro r hr hrr a ha
  refine (P.withRate r hrr).hara_policy_eq_zero_of_primitives hγ0 hη
    (show (P.withRate r hrr).u = haraUtility γ η from hu) rfl ?_ z₀ ha₀ ha₀cap ?_ ha
  · rw [show ((P.withRate r hrr).discount : ℝ) = (P.discount : ℝ) from rfl,
      show (P.withRate r hrr).interest = r from rfl]
    exact himp r hr
  · rw [show ((P.withRate r hrr).discount : ℝ) = (P.discount : ℝ) from rfl,
      show (P.withRate r hrr).income z₀ = P.income z₀ from rfl,
      show (P.withRate r hrr).interest = r from rfl]
    exact hcond r hr hrr

namespace Calibrated

variable {P : IncomeFluctuation Z 0 assetCap} {γ η G a₀ : ℝ} {z₀ : Z} {rlo rhi : ℝ}
variable (h : Calibrated P γ η G a₀ z₀ rlo rhi)

include h

theorem rateOK {r : ℝ} (hr : r ∈ Icc rlo rhi) : P.RateOK r :=
  IncomeFluctuation.rateOK_of_floor_zero (by linarith [h.rlo_nonneg, hr.1])

/-- Concave slices of the iterates, in every economy of the family. -/
theorem concaveSlices_iterate {r : ℝ} (hrr : P.RateOK r) (n : ℕ) :
    ConcaveSlices (0 : ℝ) assetCap
      (((P.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
  induction n with
  | zero => exact concaveSlices_zero
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (P.withRate r hrr).concaveSlices_bellman ih

/-- Every iterate of every economy in the family oscillates by at most `G`, so the cap is slack
against all of them — including, at one rate, the iterates generated at another. -/
theorem oscOn_iterate_le {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) {r' : ℝ}
    (hrr' : P.RateOK r') (n : ℕ) :
    (P.withRate r' hrr').OscOn
      (((P.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) G :=
  IncomeFluctuation.OscOn.mono (P.withRate r' hrr')
    ((P.withRate r hrr).oscOn_iterate n) (h.osc_le r hr hrr)

/-- Positivity at the iterates of any rate in the interval, read in any economy of the family. -/
theorem positive_iterate {r r' : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r)
    (hr' : r' ∈ Icc rlo rhi) (hrr' : P.RateOK r') (n : ℕ) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    0 < (P.withRate r' hrr').consumptionFnOf
      (((P.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a :=
  h.positive r' hr' hrr' _ (h.concaveSlices_iterate hrr n) (h.oscOn_iterate_le hr hrr hrr' n)
    z a ha

/-- Positivity at the fixed point. -/
theorem positive_valueFunction {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) (z : Z)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) : 0 < (P.withRate r hrr).consumptionFn z a :=
  h.positive r hr hrr _ (P.withRate r hrr).concaveSlices_valueFunction
    (IncomeFluctuation.OscOn.mono (P.withRate r hrr)
      (P.withRate r hrr).oscOn_valueFunction (h.osc_le r hr hrr)) z a ha

theorem policyOf_iterate_lt_cap {r r' : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r)
    (hr' : r' ∈ Icc rlo rhi) (hrr' : P.RateOK r') (n : ℕ) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r' hrr').policyOf
      (((P.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap :=
  h.slack r' hr' hrr' _ (h.concaveSlices_iterate hrr n) (h.oscOn_iterate_le hr hrr hrr' n) a ha z

/-- **Carroll and Kimball** along the iteration, in every economy of the family. -/
theorem concaveOn_consumptionFnOf_iterates {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r)
    (n : ℕ) (z : Z) : ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      ((P.withRate r hrr).consumptionFnOf
        (((P.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z) :=
  (P.withRate r hrr).concaveOn_consumptionFnOf_iterates_of_hara h.gamma_pos h.eta_nonneg
    h.discount_pos h.utility
    (fun m z' a ha => h.positive_iterate hr hrr hr hrr m ha z')
    (fun m a ha z' => (P.withRate r hrr).policyOf_lt_maxSaving_of_pos
      (h.positive_iterate hr hrr hr hrr m ha z')
      (h.policyOf_iterate_lt_cap hr hrr hr hrr m ha z'))
    n z

/-- The cap is slack at the fixed point too: the value function is the uniform limit of the
iterates, so it oscillates no more than they do. -/
theorem policy_lt_cap {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) : (P.withRate r hrr).policy (a, z) < assetCap :=
  h.slack r hr hrr _ (P.withRate r hrr).concaveSlices_valueFunction
    (IncomeFluctuation.OscOn.mono (P.withRate r hrr)
      (P.withRate r hrr).oscOn_valueFunction (h.osc_le r hr hrr)) a ha z

theorem policy_lt_maxSaving {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r hrr).policy (a, z) < (P.withRate r hrr).maxSaving (a, z) :=
  (P.withRate r hrr).policyOf_lt_maxSaving_of_pos (h.positive_valueFunction hr hrr z ha)
    (h.policy_lt_cap hr hrr ha z)

/-- **Light (2018) Theorem 1** for the whole family. -/
theorem policy_mono {r r' : ℝ} (hr : r ∈ Icc rlo rhi) (hr' : r' ∈ Icc rlo rhi) (hle : r ≤ r')
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r (h.rateOK hr)).policy (a, z) ≤ (P.withRate r' (h.rateOK hr')).policy (a, z) :=
  P.policy_mono_withRate_hara h.gamma_pos h.gamma_le_one h.eta_nonneg h.utility
    (h.rateOK hr) (h.rateOK hr') hle
    (fun n b hb z' => h.positive_iterate hr (h.rateOK hr) hr' (h.rateOK hr') n hb z')
    (fun n b hb z' => h.positive_iterate hr' (h.rateOK hr') hr' (h.rateOK hr') n hb z')
    (fun n b hb z' => h.policyOf_iterate_lt_cap hr (h.rateOK hr) hr' (h.rateOK hr') n hb z')
    (fun n b hb z' => h.policyOf_iterate_lt_cap hr' (h.rateOK hr') hr' (h.rateOK hr') n hb z')
    (fun n z' => h.concaveOn_consumptionFnOf_iterates hr' (h.rateOK hr') n z') ha z

/-- **The exhaustion data**, from impatience and the corner condition. -/
theorem exhausts {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) :
    ∃ N : ℕ, ((P.withRate r hrr).gBad z₀)^[N] (P.withRate r hrr).topState
      = (P.withRate r hrr).botState := by
  refine (P.withRate r hrr).hara_exists_exhaust_of_impatient h.gamma_pos h.eta_nonneg
    h.utility ?_ h.iid
    (fun z b hb => h.positive_valueFunction hr hrr z hb)
    (fun z b hb => h.policy_lt_maxSaving hr hrr z hb) h.income_min h.a₀_pos h.a₀_le
    (fun b hb => h.corner r hr hrr b hb)
  · have := h.impatient r hr
    rw [show ((P.withRate r hrr).discount : ℝ) = (P.discount : ℝ) from rfl,
      show (P.withRate r hrr).interest = r from rfl]
    exact this


/-- **Carroll and Kimball at the fixed point**, at every rate in the interval. -/
theorem concaveOn_consumptionFn {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) (z : Z) :
    ConcaveOn ℝ (Icc (0 : ℝ) assetCap) ((P.withRate r hrr).consumptionFn z) :=
  (P.withRate r hrr).concaveOn_consumptionFn_of_iterates
    (fun n z' => h.concaveOn_consumptionFnOf_iterates hr hrr n z') z

/-! ### The distribution, and the equilibrium rate -/

variable [MeasurableSpace Z] [BorelSpace Z]

/-- **A unique stationary distribution at every rate in the interval.** -/
theorem existsUnique_stationary {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) :
    ∃! μ : ProbabilityMeasure P.State, (P.withRate r hrr).IsStationary μ :=
  (P.withRate r hrr).existsUnique_isStationary (z₀ := z₀) (fun z => h.reach z)
    (Classical.choose_spec (h.exhausts hr hrr))

/-- **Convergence to it**, from any starting distribution: Doeblin with the atom at the
borrowing constraint. -/
theorem tendsto_pushProb {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r)
    (μ₀ : ProbabilityMeasure P.State) {μ : ProbabilityMeasure P.State}
    (hμ : (P.withRate r hrr).IsStationary μ) :
    Tendsto (fun m => (P.withRate r hrr).pushProb^[m] μ₀) atTop (𝓝 μ) := by
  classical
  obtain ⟨z₁, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun z => P.transitionMatrix z z₀) ⟨Classical.ofNonempty, Finset.mem_univ _⟩
  exact (P.withRate r hrr).tendsto_pushProb_iterate (z₀ := z₀)
    (p₀ := P.transitionMatrix z₁ z₀) (N := Classical.choose (h.exhausts hr hrr) + 1)
    (h.reach z₁) (fun s => hmin _ (Finset.mem_univ _))
    ((P.withRate r hrr).badStep_iterate_eq (Classical.choose_spec (h.exhausts hr hrr))) μ₀ hμ

/-- The economy as a function of the rate, clamped outside the interval. -/
noncomputable def family : ℝ → IncomeFluctuation Z 0 assetCap :=
  P.rateFamily (by linarith [h.rlo_nonneg] : (0 : ℝ) < 1 + rlo) h.rate_le

theorem family_eq {r : ℝ} (hr : r ∈ Icc rlo rhi) : h.family r = P.withRate r (h.rateOK hr) :=
  P.rateFamily_eq _ _ hr _

/-- Capital supply: the stationary distribution at each rate. -/
noncomputable def stationary (r : ℝ) : ProbabilityMeasure P.State :=
  Classical.choose ((h.family r).exists_isStationary
    ⟨Measure.dirac (Classical.ofNonempty : P.State), inferInstance⟩)

theorem stationary_isStationary (r : ℝ) : (h.family r).IsStationary (h.stationary r) :=
  Classical.choose_spec ((h.family r).exists_isStationary
    ⟨Measure.dirac (Classical.ofNonempty : P.State), inferInstance⟩)

theorem tendsto_stationary (μ₀ : ProbabilityMeasure P.State) :
    ∀ r ∈ Icc rlo rhi, Tendsto (fun m => (h.family r).pushProb^[m] μ₀) atTop
      (𝓝 (h.stationary r)) := by
  intro r hr
  have hst := h.stationary_isStationary r
  rw [h.family_eq hr] at hst ⊢
  exact h.tendsto_pushProb hr (h.rateOK hr) μ₀ hst

/-- **Capital supply is monotone in the rate** — Light's Theorems 1 and 2 for the class. -/
theorem monotoneOn_capitalSupply :
    MonotoneOn (fun r => P.aggregateCapital (h.stationary r)) (Icc rlo rhi) := by
  refine P.monotoneOn_capitalSupply_of_policy_mono h.family (fun r r' z z' => ?_) ?_
    ⟨Measure.dirac (Classical.ofNonempty : P.State), inferInstance⟩ h.stationary
    (h.tendsto_stationary _)
  · simp only [family, rateFamily, IncomeFluctuation.withRate_transitionMatrix]
  · rintro r hr r' hr' hle ⟨a, z⟩ hs
    rw [h.family_eq hr, h.family_eq hr']
    exact h.policy_mono hr hr' hle hs z

/-- **Uniqueness of the equilibrium rate, for the class.** -/
theorem equilibriumRate_unique {A δ : ℝ} (hA : A ≠ 0) (hδ : 0 < rlo + δ)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (he₁ : P.aggregateCapital (h.stationary r₁) = capitalDemand A δ r₁)
    (he₂ : P.aggregateCapital (h.stationary r₂) = capitalDemand A δ r₂) : r₁ = r₂ :=
  LeanEconomics.equilibriumRate_unique hA hδ h.monotoneOn_capitalSupply h₁ h₂ he₁ he₂

/-- In any equilibrium the distribution is the canonical one, so the `IsAiyagariEquilibrium`
form of uniqueness follows. -/
theorem isAiyagariEquilibrium_unique {A δ : ℝ} (hA : A ≠ 0) (hδ : 0 < rlo + δ)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (he₁ : IsAiyagariEquilibrium h.family (capitalDemand A δ) r₁)
    (he₂ : IsAiyagariEquilibrium h.family (capitalDemand A δ) r₂) : r₁ = r₂ := by
  obtain ⟨μ₁, hst₁, hcap₁⟩ := he₁
  obtain ⟨μ₂, hst₂, hcap₂⟩ := he₂
  have hid : ∀ {r : ℝ}, r ∈ Icc rlo rhi → ∀ {μ : ProbabilityMeasure P.State},
      (h.family r).IsStationary μ → μ = h.stationary r := by
    intro r hr μ hμ
    obtain ⟨ν, -, huniq⟩ := h.existsUnique_stationary hr (h.rateOK hr)
    rw [h.family_eq hr] at hμ
    have hst := h.stationary_isStationary r
    rw [h.family_eq hr] at hst
    rw [huniq _ hμ, huniq _ hst]
  rw [hid h₁ hst₁] at hcap₁
  rw [hid h₂ hst₂] at hcap₂
  exact h.equilibriumRate_unique hA hδ h₁ h₂ hcap₁ hcap₂

end Calibrated

end IncomeFluctuation

/-! ### `nearLog` is an instance

Every field is a lemma that already existed; the class was extracted from this proof, so this is
the check that nothing specific to the calibration leaked into it. -/

theorem nearLog_calibrated :
    nearLog.Calibrated (15 / 16) 0 (27 / 5) (1 / 50) 0 0 (1 / 200) where
  gamma_pos := by norm_num
  gamma_le_one := by norm_num
  eta_nonneg := le_rfl
  utility := by rw [haraUtility_zero_shift]; rfl
  discount_pos := by rw [nearLog_discount]; norm_num
  positive := fun r _ hrr v hv _ z a ha =>
    nearLog_withRate_positiveConsumptionAll hrr v hv z a ha
  rlo_nonneg := le_rfl
  rate_le := by norm_num
  iid := fun _ _ _ => rfl
  income_min := fun z => by fin_cases z <;> norm_num
  reach := fun z => by rw [nearLog_transitionMatrix]; norm_num
  impatient := fun r hr => by rw [nearLog_discount]; linarith [hr.2]
  osc_nonneg := by norm_num
  osc_le := fun r hr hrr => by
    rw [IncomeFluctuation.oscSpread_eq_oscGap]
    exact nearLog_oscGap_le_uniform hr hrr
  slack := fun r hr hrr v hv hosc a ha z => nearLog_policyOf_lt_cap hr hrr hv hosc ha z
  a₀_pos := by norm_num
  a₀_le := by norm_num
  corner := fun r hr hrr a ha => nearLog_corner_uniform hr hrr ha

/-- **The nearLog uniqueness theorem, as an instance of the class.** `CESUniqueness` proves the
same thing directly; this says the direct proof used nothing specific to the calibration. -/
theorem nearLog_equilibriumRate_unique_of_class {A δ : ℝ} (hA : A ≠ 0) (hδ : 0 < δ)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc (0 : ℝ) (1 / 200)) (h₂ : r₂ ∈ Icc (0 : ℝ) (1 / 200))
    (he₁ : nearLog.aggregateCapital (nearLog_calibrated.stationary r₁) = capitalDemand A δ r₁)
    (he₂ : nearLog.aggregateCapital (nearLog_calibrated.stationary r₂) = capitalDemand A δ r₂) :
    r₁ = r₂ :=
  nearLog_calibrated.equilibriumRate_unique hA (by linarith) h₁ h₂ he₁ he₂

end LeanEconomics
