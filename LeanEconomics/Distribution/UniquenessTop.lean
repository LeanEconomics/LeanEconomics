/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Distribution.Uniqueness

/-!
# Uniqueness from an atom at the CAP

`Distribution.Uniqueness` gets a unique stationary distribution from an atom at the borrowing
constraint: repeated bad income draws drive every household to zero assets, which is a Doeblin
minorisation. That argument needs the constraint to bind, hence impatience, and it is why the
equilibrium interval in `EquilibriumWitness` stops well below the rate at which households would
start accumulating.

The mirror image works just as well. If repeated GOOD income draws drive every household to the
asset cap, that is an atom at the top, and the same minorisation applies. Nothing in
`stationary_unique` cares which state the mass collapses to — it is stated for an arbitrary `s₀`
and an arbitrary income state — so only the funnelling argument has to be mirrored, and
monotonicity of the policy does that as cleanly upwards as downwards.

## What this buys, and what it still needs

It opens the patient region to the same machinery: where the household accumulates rather than
decumulates, the atom moves from the borrowing constraint to the cap, and uniqueness survives.
That is the region `Equilibrium.SignChange` could not reach.

What is NOT here is the reverse corner condition — a sufficient condition in primitives for
`policy (a, z₁) = assetCap`, the analogue of `policy_eq_zero_of_corner_at`. The shape of the
argument is clear: saving the maximum is optimal when the continuation's gain beats the utility
lost, which needs an upper bound on the slope of `u` above `resources - assetCap` (for log,
`1 / (resources - assetCap)`) and a LINEAR lower bound on the continuation's gain, which
`log (1 + t) ≥ t log 2` on `t ∈ [0,1]` supplies from `log_cont_sub_ge_gen` once consumption is
bounded below. It is a real piece of work and it is not done, so the results below take the
cap-binding and accumulation conditions as hypotheses.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **Monotonicity reduces accumulation to the best case.** If the poorest household reaches the
cap in `N` good draws, everyone does. -/
theorem gBad_iterate_eq_top {z₁ : Z} {N : ℕ} (hgro : (P.gBad z₁)^[N] P.botState = P.topState)
    (x : ↥(Icc assetFloor assetCap)) : (P.gBad z₁)^[N] x = P.topState :=
  le_antisymm (P.le_topState _) (hgro ▸ (P.gBad_mono z₁).iterate N (P.botState_le x))

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The Doeblin condition from the top.** -/
theorem badStep_iterate_eq_top {z₁ : Z} {N : ℕ}
    (hgro : (P.gBad z₁)^[N] P.botState = P.topState) (s : P.State) :
    (P.badStep z₁)^[N + 1] s = (P.topState, z₁) := by
  rw [P.badStep_iterate_succ z₁ N s, P.gBad_iterate_eq_top hgro]

/-- **Uniqueness of the stationary distribution, from an atom at the cap.** -/
theorem stationary_unique_of_accumulates {z₁ : Z} {N : ℕ}
    (hreach : ∀ z, 0 < P.transitionMatrix z z₁)
    (hgro : (P.gBad z₁)^[N] P.botState = P.topState)
    {μ ν : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) (hν : P.IsStationary ν) :
    μ = ν := by
  classical
  obtain ⟨z₂, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun z => P.transitionMatrix z z₁) ⟨Classical.ofNonempty, Finset.mem_univ _⟩
  exact P.stationary_unique (p₀ := P.transitionMatrix z₂ z₁) (hreach z₂)
    (fun s => hmin _ (Finset.mem_univ _)) (P.badStep_iterate_eq_top hgro) hμ hν

/-- **Existence and uniqueness together, from an atom at the cap.** -/
theorem existsUnique_isStationary_of_accumulates {z₁ : Z} {N : ℕ}
    (hreach : ∀ z, 0 < P.transitionMatrix z z₁)
    (hgro : (P.gBad z₁)^[N] P.botState = P.topState) :
    ∃! μ : ProbabilityMeasure P.State, P.IsStationary μ := by
  obtain ⟨μ, hμ⟩ := P.exists_isStationary
    ⟨Measure.dirac (Classical.ofNonempty : P.State), inferInstance⟩
  exact ⟨μ, hμ, fun ν hν => P.stationary_unique_of_accumulates hreach hgro hν hμ⟩

/-! ### Reaching the cap

The mirror of `exists_exhaust_of_decline`: below a threshold assets strictly grow, above it the
cap binds, and compactness turns the strict growth into a uniform increment. -/

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem exists_growth_to_cap {z₁ : Z} {a₁ : ℝ} (ha₁0 : assetFloor ≤ a₁) (ha₁ : a₁ ≤ assetCap)
    (hcap : ∀ a ∈ Icc a₁ assetCap, P.policy (a, z₁) = assetCap)
    (hgro : ∀ a ∈ Icc assetFloor a₁, a < P.policy (a, z₁)) :
    ∃ N : ℕ, (P.gBad z₁)^[N] P.botState = P.topState := by
  classical
  have hne : (Icc assetFloor a₁).Nonempty := ⟨assetFloor, ⟨le_rfl, ha₁0⟩⟩
  have hcont : ContinuousOn (fun a : ℝ => P.policy (a, z₁) - a) (Icc assetFloor a₁) := by
    refine ContinuousOn.sub (P.continuousOn_policy.comp
      (continuous_id.prodMk continuous_const).continuousOn fun a ha => ?_) continuousOn_id
    exact ⟨ha.1, le_trans ha.2 ha₁⟩
  obtain ⟨am, hamem, hamin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  set Δ : ℝ := P.policy (am, z₁) - am with hΔdef
  have hΔpos : 0 < Δ := by rw [hΔdef]; linarith [hgro am hamem]
  have hstep : ∀ a ∈ Icc assetFloor a₁, a + Δ ≤ P.policy (a, z₁) := fun a ha => by
    have h := hamin ha
    rw [Set.mem_ofPred_eq] at h
    rw [hΔdef]; linarith
  have key : ∀ k : ℕ,
      a₁ ≤ (((P.gBad z₁)^[k] P.botState : ↥(Icc assetFloor assetCap)) : ℝ) ∨
      assetFloor + (k : ℝ) * Δ
        ≤ (((P.gBad z₁)^[k] P.botState : ↥(Icc assetFloor assetCap)) : ℝ) := by
    intro k
    induction k with
    | zero => right; simp [botState]
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        have hval : (((P.gBad z₁) ((P.gBad z₁)^[k] P.botState) :
            ↥(Icc assetFloor assetCap)) : ℝ)
            = P.policy ((((P.gBad z₁)^[k] P.botState : ↥(Icc assetFloor assetCap)) : ℝ), z₁) := rfl
        rcases ih with h | h
        · left
          rw [hval, hcap _ ⟨h, ((P.gBad z₁)^[k] P.botState).2.2⟩]
          exact ha₁
        · rcases le_total a₁ (((P.gBad z₁)^[k] P.botState : ↥(Icc assetFloor assetCap)) : ℝ)
            with hhigh | hlow
          · left
            rw [hval, hcap _ ⟨hhigh, ((P.gBad z₁)^[k] P.botState).2.2⟩]
            exact ha₁
          · right
            rw [hval]
            have hmem : (((P.gBad z₁)^[k] P.botState : ↥(Icc assetFloor assetCap)) : ℝ)
                ∈ Icc assetFloor a₁ := ⟨((P.gBad z₁)^[k] P.botState).2.1, hlow⟩
            have hinc := hstep _ hmem
            push_cast
            linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((a₁ - assetFloor) / Δ)
  refine ⟨N + 1, ?_⟩
  have hNge : a₁ ≤ (((P.gBad z₁)^[N] P.botState : ↥(Icc assetFloor assetCap)) : ℝ) := by
    rcases key N with h | h
    · exact h
    · rw [div_lt_iff₀ hΔpos] at hN
      linarith
  rw [Function.iterate_succ_apply']
  refine Subtype.ext ?_
  change P.policy ((((P.gBad z₁)^[N] P.botState : ↥(Icc assetFloor assetCap)) : ℝ), z₁) = assetCap
  exact hcap _ ⟨hNge, ((P.gBad z₁)^[N] P.botState).2.2⟩

end IncomeFluctuation

end LeanEconomics
