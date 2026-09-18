/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.Impatience
import LeanEconomics.Models.ImpatientDecline
import LeanEconomics.Equilibrium.SignChange
import LeanEconomics.Distribution.UniquenessTop

/-!
# Capital supply at or above the time-preference rate

Aiyagari's Figure IIb: capital supply tends to infinity as the rate approaches the
time-preference rate `λ` from below, so no equilibrium can lie at or above it. In a capped economy
"infinity" is the cap, and what can be proved is that at `β(1+r) > 1` every stationary
distribution holds capital comparable to the cap.

## Two results, and an honest gap

**Deterministic income.** Nobody runs assets down (`le_policy_of_patient`), so `policy - a ≥ 0`
pointwise; stationarity makes its integral zero, so `policy = a` almost everywhere; and a
household with room under the cap strictly accumulates (`lt_policy_of_patient`), so almost every
household is AT the cap. Capital supply IS the cap (`aggregateCapital_eq_assetCap_of_patient`).

**Income risk, given an atom at the cap.** If from the borrowing limit the richest income state
reaches the cap in `N` steps, then `N + 1` consecutive draws of that state — probability at least
`p₀^(N+1)` from anywhere — put the household at the cap, and the minorisation bound
`iterate_lower` turns that into `assetCap · p₀^(N+1) ≤ K` at every stationary distribution
(`assetCap_mul_le_aggregateCapital_of_atom`).

What is NOT proved is that patience delivers the atom with income risk. Patience gives strict
accumulation at the richest-consumption state wherever there is room, but strict accumulation
can approach the cap without reaching it — `a ↦ (a + cap)/2` does — and the finite-step atom is
exactly what the Doeblin argument needs. Closing that gap needs a QUANTITATIVE accumulation
bound under patience, the mirror image of the minimal MPC, and that is not here.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### Iterating the operator against a stationary distribution -/

theorem integral_markovOp_iterate_eq (h : P.State →ᵇ ℝ) (n : ℕ) :
    ∀ μ : ProbabilityMeasure P.State,
      ∫ s, (P.markovOp^[n] h) s ∂(μ : Measure P.State)
        = ∫ s, h s ∂((P.pushProb^[n] μ : ProbabilityMeasure P.State) : Measure P.State) := by
  induction n with
  | zero => intro μ; simp
  | succ k ih =>
    intro μ
    have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
    calc ∫ s, (P.markovOp^[k + 1] h) s ∂(μ : Measure P.State)
        = ∫ s, P.markovOp (P.markovOp^[k] h) s ∂(μ : Measure P.State) := by
          rw [Function.iterate_succ_apply']
      _ = ∫ s, (P.markovOp^[k] h) s ∂(P.push (μ : Measure P.State)) := (P.integral_push _ _).symm
      _ = ∫ s, (P.markovOp^[k] h) s
            ∂((P.pushProb μ : ProbabilityMeasure P.State) : Measure P.State) := rfl
      _ = ∫ s, h s ∂((P.pushProb^[k] (P.pushProb μ) : ProbabilityMeasure P.State)
            : Measure P.State) := ih (P.pushProb μ)
      _ = ∫ s, h s ∂((P.pushProb^[k + 1] μ : ProbabilityMeasure P.State) : Measure P.State) := by
          rw [Function.iterate_succ_apply]

/-- Against a stationary distribution, iterating the operator changes nothing. -/
theorem integral_markovOp_iterate_of_stationary (h : P.State →ᵇ ℝ) (n : ℕ)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    ∫ s, (P.markovOp^[n] h) s ∂(μ : Measure P.State) = ∫ s, h s ∂(μ : Measure P.State) := by
  rw [P.integral_markovOp_iterate_eq h n μ, Function.iterate_fixed hμ]

/-! ### Income risk, given an atom at the cap -/

/-- **Capital is at least `assetCap · p₀^(N+1)`** whenever `N` consecutive draws of the state `z₁`
carry the borrowing limit to the cap. -/
theorem assetCap_mul_le_aggregateCapital_of_atom {z₁ : Z} {N : ℕ}
    (hgro : (P.gBad z₁)^[N] P.botState = P.topState)
    {p₀ : ℝ} (hp0 : 0 ≤ p₀) (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    assetCap * p₀ ^ (N + 1) ≤ P.aggregateCapital μ := by
  have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
  have hp' : ∀ s : P.State, p₀ ≤ P.prob s z₁ := fun s => hp s.2
  have hinf : (0 : ℝ) ≤ P.infF P.assetCoord := by
    refine le_ciInf fun s => ?_
    exact s.1.2.1
  have hpow1 : p₀ ^ (N + 1) ≤ 1 := by
    have hz : Z := Classical.ofNonempty
    have h1 : p₀ ≤ 1 := by
      have hsum := P.transitionMatrix_sum hz
      have hsingle := Finset.single_le_sum (fun z' _ => P.transitionMatrix_nonneg hz z')
        (Finset.mem_univ z₁)
      linarith [hp hz]
    exact pow_le_one₀ hp0 h1
  -- pointwise: the iterated operator on assets is at least `p₀^(N+1) · cap`
  have hpt : ∀ s : P.State, assetCap * p₀ ^ (N + 1) ≤ (P.markovOp^[N + 1] P.assetCoord) s := by
    intro s
    have hlow := P.iterate_lower hp0 hp' P.assetCoord (N + 1) s
    rw [P.badStep_iterate_eq_top hgro s] at hlow
    have htop : P.assetCoord (P.topState, z₁) = assetCap := rfl
    rw [htop] at hlow
    have : 0 ≤ (1 - p₀ ^ (N + 1)) * P.infF P.assetCoord :=
      mul_nonneg (by linarith) hinf
    linarith
  calc assetCap * p₀ ^ (N + 1)
      = ∫ _s, assetCap * p₀ ^ (N + 1) ∂(μ : Measure P.State) := by simp
    _ ≤ ∫ s, (P.markovOp^[N + 1] P.assetCoord) s ∂(μ : Measure P.State) :=
        integral_mono (integrable_const _) ((P.markovOp^[N + 1] P.assetCoord).integrable _) hpt
    _ = P.aggregateCapital μ := P.integral_markovOp_iterate_of_stationary _ _ hμ

/-! ### Deterministic income -/

section Deterministic

variable [Subsingleton Z]

/-- **Under patience, capital supply is the cap**, with deterministic income. -/
theorem aggregateCapital_eq_assetCap_of_patient
    (hβR : 1 < (P.discount : ℝ) * (1 + P.interest))
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpc : P.PositiveConsumption)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    P.aggregateCapital μ = assetCap := by
  have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
  have hpos : ∀ (z : Z), ∀ x ∈ Icc (0 : ℝ) assetCap, 0 < P.consumptionFn z x :=
    fun z x hx => P.consumptionFn_pos hpc hx z
  -- `policy - a ≥ 0` everywhere, and its integral vanishes
  have hge : ∀ s : P.State, 0 ≤ P.policyCoord s - P.assetCoord s := fun s => by
    have hle : (s.1 : ℝ) ≤ P.policy ((s.1 : ℝ), s.2) :=
      P.le_policy_of_patient hpc hβR.le (a := (s.1 : ℝ)) s.1.2 s.2
    have hpc' : P.policyCoord s = P.policy ((s.1 : ℝ), s.2) := rfl
    have hac : P.assetCoord s = (s.1 : ℝ) := rfl
    rw [hpc', hac]
    linarith
  have hzero : ∫ s, (P.policyCoord s - P.assetCoord s) ∂(μ : Measure P.State) = 0 := by
    rw [integral_sub (P.policyCoord.integrable _) (P.assetCoord.integrable _),
      ← P.aggregateCapital_eq_integral_policy hμ]
    simp [aggregateCapital]
  have hae : (fun s => P.policyCoord s - P.assetCoord s) =ᵐ[(μ : Measure P.State)] 0 :=
    (integral_eq_zero_iff_of_nonneg hge
      ((P.policyCoord.integrable _).sub (P.assetCoord.integrable _))).mp hzero
  -- so almost every household sits at the cap
  have hatcap : (fun s => P.assetCoord s) =ᵐ[(μ : Measure P.State)] fun _ => assetCap := by
    filter_upwards [hae] with s hs
    have hs' : P.policy ((s.1 : ℝ), s.2) - (s.1 : ℝ) = 0 := hs
    have hfix : P.policy ((s.1 : ℝ), s.2) = (s.1 : ℝ) := by linarith
    by_contra hne
    have hne' : (s.1 : ℝ) ≠ assetCap := hne
    have hlt : (s.1 : ℝ) < assetCap := lt_of_le_of_ne s.1.2.2 hne'
    have hroom : P.policy ((s.1 : ℝ), s.2) < P.maxSaving ((s.1 : ℝ), s.2) := by
      rw [P.maxSaving_eq]
      refine lt_min (by rw [hfix]; exact hlt) ?_
      have := hpos s.2 _ s.1.2
      simp only [consumptionFn, consumption] at this
      linarith
    have := P.lt_policy_of_patient hβR hderiv hanti hdupos hpos s.1.2 (z := s.2) hroom
      (fun z' => by rw [Subsingleton.elim z' s.2])
    linarith
  calc P.aggregateCapital μ = ∫ s, P.assetCoord s ∂(μ : Measure P.State) := rfl
    _ = ∫ _s, assetCap ∂(μ : Measure P.State) := integral_congr_ae hatcap
    _ = assetCap := by simp

/-- **No equilibrium above the time-preference rate**, deterministic income, log utility:
capital supply is the cap, so any demand below the cap is unmet. -/
theorem log_no_equilibrium_of_patient (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβR : 1 < (P.discount : ℝ) * (1 + P.interest))
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) {D : ℝ} (hD : D < assetCap) :
    P.aggregateCapital μ ≠ D := by
  rw [P.aggregateCapital_eq_assetCap_of_patient hβR (du := fun c => c ^ (-(1 : ℝ)))
    (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility 1 hc)
    (fun _ hx _ _ hxy => Real.rpow_le_rpow_of_nonpos hx hxy (by norm_num))
    (fun c hc => Real.rpow_pos_of_pos hc _) (P.positiveConsumption_of_unbounded hunb) hμ]
  exact ne_of_gt hD

end Deterministic

end IncomeFluctuation

end LeanEconomics
