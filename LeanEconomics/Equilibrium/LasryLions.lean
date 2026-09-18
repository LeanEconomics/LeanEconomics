/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Lasry–Lions uniqueness, in its measure-theoretic core

The uniqueness argument of Lasry and Lions for mean field games is, stripped of the partial
differential equations, two optimality inequalities added together. This file records that core
in two settings where nothing needs to be differentiable.

## The static ("one-shot") game

A cost `F x m` for a player at state `x` when the population is distributed as `m`. A
**mean-field Nash** distribution is one under which the population does no worse, on average,
than any other distribution facing the same cost — Borges Prado (2021, eq. (3.4)), the limit of
symmetric Nash equilibria of the `N`-player game. Two such distributions `m₁, m₂` satisfy

`∫ (F(·,m₁) - F(·,m₂)) d(m₁ - m₂) ≤ 0`

(`llPairing_nonpos_of_nash`): use `m₂` as a deviation from `m₁` and vice versa, and add. The
**Lasry–Lions monotonicity** condition is the reverse inequality, so under it the pairing is
zero, and under STRICT monotonicity — the pairing vanishes only when the costs agree
(Cannarsa–Capuani 2018, Def. 4.2) — the two equilibria present the same cost to every player.
What is pinned down is the cost, not the distribution: this is Cannarsa–Capuani's Theorem 4.1
and their Remark 4.1 in one line each.

`llPairing_aggregate` is the scalar-interaction case: `F x m = g x + φ(A m) · a x` with `A m` the
mean of `a` under `m`, the price-through-an-aggregate structure of Calvia–Federico–Ferrari–Gozzi
(2026) and Graber–Matter (2024). The pairing is `(φ A₁ - φ A₂)(A₁ - A₂)`, so a monotone `φ` is
Lasry–Lions monotone and a strictly monotone `φ` makes the AGGREGATE unique
(`aggregate_eq_of_nash`).

## The finite-horizon, finite-state game

Players choose paths `γ : Fin (T+1) → X` in a finite state space (the finite-state mean field
games of Gomes–Mohr–Souza and Hajek–Livesay 2019, in discrete time). An equilibrium is a
distribution `η` over paths whose marginals `m t` generate the costs, and which is carried by
paths that are optimal from their own starting point against those costs — the *relaxed*
equilibrium of Cannarsa–Capuani, measures on arcs. Two equilibria WITH THE SAME INITIAL
DISTRIBUTION have, for every date, a zero Lasry–Lions pairing when each date's cost is monotone
(`llPairing_eq_zero_of_pathEquilibrium`), and the same value function when the costs are
strictly monotone (`value_eq_of_pathEquilibrium`).

## What this says about Bewley models

The argument cancels the term `∫ (u₁ - u₂) d(m₁(0) - m₂(0))` because the two equilibria start
from the same distribution. A stationary discounted equilibrium has no such common start: two
candidate rates carry two different stationary distributions. That is why the Lasry–Lions route
does not reach the Aiyagari uniqueness problem, and why the coupling through a market-clearing
price, which Graber and Matter show is typically NOT Lasry–Lions monotone, is handled there by
monotonicity of excess supply instead (`Equilibrium.Uniqueness`, `Analysis.StronglyMonotone`).
-/

open MeasureTheory

namespace LeanEconomics

namespace MeanFieldGame

/-! ### The static game -/

section Static

variable {X : Type*} [MeasurableSpace X]

/-- **A mean-field Nash distribution**: no distribution of the population does better against
the cost `F(·, m)` than `m` itself. Equivalently, `m` is carried by the minimisers of `F(·, m)`. -/
def IsMeanFieldNash (F : X → ProbabilityMeasure X → ℝ) (m : ProbabilityMeasure X) : Prop :=
  ∀ m' : ProbabilityMeasure X, ∫ x, F x m ∂(m : Measure X) ≤ ∫ x, F x m ∂(m' : Measure X)

/-- **The Lasry–Lions pairing** `∫ (F(·,m₁) - F(·,m₂)) d(m₁ - m₂)`. -/
noncomputable def llPairing (F : X → ProbabilityMeasure X → ℝ) (m₁ m₂ : ProbabilityMeasure X) :
    ℝ :=
  ∫ x, (F x m₁ - F x m₂) ∂(m₁ : Measure X) - ∫ x, (F x m₁ - F x m₂) ∂(m₂ : Measure X)

/-- **Lasry–Lions monotonicity**: the pairing is nonnegative. -/
def LasryLionsMonotone (F : X → ProbabilityMeasure X → ℝ) : Prop :=
  ∀ m₁ m₂, 0 ≤ llPairing F m₁ m₂

/-- **Strict Lasry–Lions monotonicity** (Cannarsa–Capuani Def. 4.2): monotone, and the pairing
vanishes only when the two costs agree at every state. -/
def StrictLasryLionsMonotone (F : X → ProbabilityMeasure X → ℝ) : Prop :=
  LasryLionsMonotone F ∧ ∀ m₁ m₂, llPairing F m₁ m₂ = 0 → ∀ x, F x m₁ = F x m₂

/-- **Two optimality inequalities added**: for two mean-field Nash distributions the pairing is
nonpositive. -/
theorem llPairing_nonpos_of_nash {F : X → ProbabilityMeasure X → ℝ} {m₁ m₂ : ProbabilityMeasure X}
    (h₁ : IsMeanFieldNash F m₁) (h₂ : IsMeanFieldNash F m₂)
    (hint : ∀ m m' : ProbabilityMeasure X, Integrable (fun x => F x m) (m' : Measure X)) :
    llPairing F m₁ m₂ ≤ 0 := by
  have a := h₁ m₂
  have b := h₂ m₁
  unfold llPairing
  rw [integral_sub (hint m₁ m₁) (hint m₂ m₁), integral_sub (hint m₁ m₂) (hint m₂ m₂)]
  linarith

/-- Under Lasry–Lions monotonicity the pairing of two equilibria is zero. -/
theorem llPairing_eq_zero_of_nash {F : X → ProbabilityMeasure X → ℝ} (hF : LasryLionsMonotone F)
    {m₁ m₂ : ProbabilityMeasure X} (h₁ : IsMeanFieldNash F m₁) (h₂ : IsMeanFieldNash F m₂)
    (hint : ∀ m m' : ProbabilityMeasure X, Integrable (fun x => F x m) (m' : Measure X)) :
    llPairing F m₁ m₂ = 0 :=
  le_antisymm (llPairing_nonpos_of_nash h₁ h₂ hint) (hF m₁ m₂)

/-- **Uniqueness of the cost** (Cannarsa–Capuani Thm. 4.1, static form): under strict
monotonicity two equilibria present the same cost to every player. -/
theorem cost_eq_of_nash {F : X → ProbabilityMeasure X → ℝ} (hF : StrictLasryLionsMonotone F)
    {m₁ m₂ : ProbabilityMeasure X} (h₁ : IsMeanFieldNash F m₁) (h₂ : IsMeanFieldNash F m₂)
    (hint : ∀ m m' : ProbabilityMeasure X, Integrable (fun x => F x m) (m' : Measure X)) :
    ∀ x, F x m₁ = F x m₂ :=
  hF.2 m₁ m₂ (llPairing_eq_zero_of_nash hF.1 h₁ h₂ hint)

end Static

/-! ### Scalar interaction through an aggregate -/

section Aggregate

variable {X : Type*} [MeasurableSpace X] [Finite X] [MeasurableSingletonClass X]

/-- The aggregate `∫ a dm`. -/
noncomputable def aggregate (a : X → ℝ) (m : ProbabilityMeasure X) : ℝ :=
  ∫ x, a x ∂(m : Measure X)

/-- The cost `g x + φ(A m) · a x`: a private part, plus a price `φ` of the aggregate paid on the
player's own quantity `a x`. -/
noncomputable def aggregateCost (g a : X → ℝ) (φ : ℝ → ℝ) (x : X) (m : ProbabilityMeasure X) :
    ℝ :=
  g x + φ (aggregate a m) * a x

omit [Finite X] [MeasurableSingletonClass X] in
/-- **The pairing of an aggregate cost is `(φ A₁ - φ A₂)(A₁ - A₂)`.** -/
theorem llPairing_aggregate (g a : X → ℝ) (φ : ℝ → ℝ) (m₁ m₂ : ProbabilityMeasure X) :
    llPairing (aggregateCost g a φ) m₁ m₂
      = (φ (aggregate a m₁) - φ (aggregate a m₂)) * (aggregate a m₁ - aggregate a m₂) := by
  have h : ∀ x, aggregateCost g a φ x m₁ - aggregateCost g a φ x m₂
      = (φ (aggregate a m₁) - φ (aggregate a m₂)) * a x := by
    intro x; unfold aggregateCost; ring
  unfold llPairing
  simp only [h, integral_const_mul]
  unfold aggregate
  ring

omit [Finite X] [MeasurableSingletonClass X] in
/-- A monotone price of the aggregate is Lasry–Lions monotone. -/
theorem lasryLionsMonotone_aggregate (g a : X → ℝ) {φ : ℝ → ℝ} (hφ : Monotone φ) :
    LasryLionsMonotone (aggregateCost g a φ) := by
  intro m₁ m₂
  rw [llPairing_aggregate]
  rcases le_total (aggregate a m₁) (aggregate a m₂) with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hφ h)) (sub_nonpos.2 h)
  · exact mul_nonneg (sub_nonneg.2 (hφ h)) (sub_nonneg.2 h)

/-- **A strictly monotone price makes the equilibrium aggregate unique.** The distributions may
differ; the aggregate they produce cannot. -/
theorem aggregate_eq_of_nash (g a : X → ℝ) {φ : ℝ → ℝ} (hφ : StrictMono φ)
    {m₁ m₂ : ProbabilityMeasure X} (h₁ : IsMeanFieldNash (aggregateCost g a φ) m₁)
    (h₂ : IsMeanFieldNash (aggregateCost g a φ) m₂) : aggregate a m₁ = aggregate a m₂ := by
  have h0 := llPairing_eq_zero_of_nash (lasryLionsMonotone_aggregate g a hφ.monotone) h₁ h₂
    (fun _ _ => Integrable.of_finite)
  rw [llPairing_aggregate] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact hφ.injective (sub_eq_zero.1 h)
  · exact sub_eq_zero.1 h

end Aggregate

/-! ### The finite-horizon, finite-state game -/

section Paths

variable {X : Type*} [MeasurableSpace X] [Finite X] [MeasurableSingletonClass X] {T : ℕ}

/-- A path of length `T + 1`. -/
abbrev Path (X : Type*) (T : ℕ) := Fin (T + 1) → X

/-- The date-`t` marginal of a distribution over paths. -/
noncomputable def marginal (η : ProbabilityMeasure (Path X T)) (t : Fin (T + 1)) :
    ProbabilityMeasure X :=
  η.map (measurable_pi_apply t).aemeasurable

/-- The cost of a path against the marginals `m`: the date-by-date costs added up. -/
def pathCost (F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ)
    (m : Fin (T + 1) → ProbabilityMeasure X) (γ : Path X T) : ℝ :=
  ∑ t, F t (γ t) (m t)

/-- The value from `x`: the least path cost over paths starting at `x`. -/
noncomputable def value (F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ)
    (m : Fin (T + 1) → ProbabilityMeasure X) (x : X) : ℝ :=
  ⨅ γ : {γ : Path X T // γ 0 = x}, pathCost F m γ.1

omit [MeasurableSingletonClass X] in
theorem value_le (F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ)
    (m : Fin (T + 1) → ProbabilityMeasure X) (γ : Path X T) :
    value F m (γ 0) ≤ pathCost F m γ :=
  ciInf_le (Set.finite_range _).bddBelow (⟨γ, rfl⟩ : {γ' : Path X T // γ' 0 = γ 0})

/-- **A relaxed equilibrium** (Cannarsa–Capuani): a distribution over paths carried by paths that
are optimal, from their own start, against the costs its own marginals generate. -/
def IsPathEquilibrium (F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ)
    (η : ProbabilityMeasure (Path X T)) : Prop :=
  ∀ᵐ γ ∂(η : Measure (Path X T)), pathCost F (marginal η) γ = value F (marginal η) (γ 0)

/-- The expected path cost is the sum over dates of the expected date cost under the marginal. -/
theorem integral_pathCost (F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ)
    (m : Fin (T + 1) → ProbabilityMeasure X) (η : ProbabilityMeasure (Path X T)) :
    ∫ γ, pathCost F m γ ∂(η : Measure (Path X T))
      = ∑ t, ∫ x, F t x (m t) ∂(marginal η t : Measure X) := by
  unfold pathCost
  rw [integral_finsetSum _ (fun t _ => Integrable.of_finite)]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold marginal
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_pi_apply t).aemeasurable (measurable_of_finite _).aestronglyMeasurable]

/-- The expected value at the start is the expected value of the starting point. -/
theorem integral_value (F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ)
    (m : Fin (T + 1) → ProbabilityMeasure X) (η : ProbabilityMeasure (Path X T)) :
    ∫ x, value F m x ∂(marginal η 0 : Measure X)
      = ∫ γ, value F m (γ 0) ∂(η : Measure (Path X T)) := by
  unfold marginal
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_pi_apply 0).aemeasurable (measurable_of_finite _).aestronglyMeasurable]

/-- Against ANY marginals, the expected value at the start is at most the expected path cost. -/
theorem integral_value_le (F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ)
    (m : Fin (T + 1) → ProbabilityMeasure X) (η : ProbabilityMeasure (Path X T)) :
    ∫ x, value F m x ∂(marginal η 0 : Measure X)
      ≤ ∑ t, ∫ x, F t x (m t) ∂(marginal η t : Measure X) := by
  rw [integral_value, ← integral_pathCost]
  exact integral_mono Integrable.of_finite Integrable.of_finite fun γ => value_le F m γ

/-- At an equilibrium, against its OWN marginals, the two are equal. -/
theorem integral_value_eq {F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ}
    {η : ProbabilityMeasure (Path X T)} (h : IsPathEquilibrium F η) :
    ∫ x, value F (marginal η) x ∂(marginal η 0 : Measure X)
      = ∑ t, ∫ x, F t x (marginal η t) ∂(marginal η t : Measure X) := by
  rw [integral_value, ← integral_pathCost]
  exact (integral_congr_ae h).symm

/-- **Lasry–Lions for the finite-horizon finite-state game** (Cannarsa–Capuani Thm. 4.1 in
discrete time): two relaxed equilibria from the same initial distribution, with each date's cost
Lasry–Lions monotone, have zero pairing at every date. -/
theorem llPairing_eq_zero_of_pathEquilibrium {F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ}
    (hF : ∀ t, LasryLionsMonotone (F t)) {η₁ η₂ : ProbabilityMeasure (Path X T)}
    (h₁ : IsPathEquilibrium F η₁) (h₂ : IsPathEquilibrium F η₂)
    (h0 : marginal η₁ 0 = marginal η₂ 0) (t : Fin (T + 1)) :
    llPairing (F t) (marginal η₁ t) (marginal η₂ t) = 0 := by
  -- the sum of the pairings over dates is at most zero
  have hsum : ∑ s, llPairing (F s) (marginal η₁ s) (marginal η₂ s) ≤ 0 := by
    have e₁ := integral_value_eq h₁
    have e₂ := integral_value_eq h₂
    have i₁ := integral_value_le F (marginal η₂) η₁
    have i₂ := integral_value_le F (marginal η₁) η₂
    rw [h0] at e₁ i₁
    have hpair : ∀ s, llPairing (F s) (marginal η₁ s) (marginal η₂ s)
        = (∫ x, F s x (marginal η₁ s) ∂(marginal η₁ s : Measure X)
            - ∫ x, F s x (marginal η₂ s) ∂(marginal η₁ s : Measure X))
          - (∫ x, F s x (marginal η₁ s) ∂(marginal η₂ s : Measure X)
            - ∫ x, F s x (marginal η₂ s) ∂(marginal η₂ s : Measure X)) := by
      intro s
      unfold llPairing
      rw [integral_sub Integrable.of_finite Integrable.of_finite,
        integral_sub Integrable.of_finite Integrable.of_finite]
    simp only [hpair, Finset.sum_sub_distrib]
    linarith
  -- each pairing is nonnegative, so each is zero
  have hnn : ∀ s ∈ Finset.univ, 0 ≤ llPairing (F s) (marginal η₁ s) (marginal η₂ s) :=
    fun s _ => hF s _ _
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
    (le_antisymm hsum (Finset.sum_nonneg hnn))
  exact hzero t (Finset.mem_univ t)

/-- **Uniqueness of the value function** under strict monotonicity: the two equilibria present
the same date costs, hence the same value from every state. The distributions over paths need
not coincide. -/
theorem value_eq_of_pathEquilibrium {F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ}
    (hF : ∀ t, StrictLasryLionsMonotone (F t)) {η₁ η₂ : ProbabilityMeasure (Path X T)}
    (h₁ : IsPathEquilibrium F η₁) (h₂ : IsPathEquilibrium F η₂)
    (h0 : marginal η₁ 0 = marginal η₂ 0) :
    value F (marginal η₁) = value F (marginal η₂) := by
  have hcost : ∀ t x, F t x (marginal η₁ t) = F t x (marginal η₂ t) := fun t x =>
    (hF t).2 _ _ (llPairing_eq_zero_of_pathEquilibrium (fun t => (hF t).1) h₁ h₂ h0 t) x
  funext x
  unfold value pathCost
  simp only [hcost]

end Paths

end MeanFieldGame

end LeanEconomics
