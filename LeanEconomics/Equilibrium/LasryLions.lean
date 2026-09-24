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

## The summed pairing, and what it is for

Adding the two optimality inequalities signs only the TOTAL of the date pairings
(`summedPairing_nonpos_of_pathEquilibrium`), and that step uses no monotonicity, no
integrability and no continuity. Date-by-date monotonicity is then one way — not the only way —
to conclude. `SummedLasryLionsMonotone` asks only for the total, and
`aggregate_eq_of_pathEquilibrium` shows that a cost whose summed pairing is strictly positive
whenever an aggregate differs makes that aggregate the same at every equilibrium.

The weakening is not cosmetic. In the overlapping-generations production economy the date-`t`
pairing is NEGATIVE over the first few ages, for every risk aversion, while the summed pairing is
positive throughout the bracket in which the equilibrium is known to lie. The date-by-date
hypothesis is false there and the summed one is not.

## What this says about Bewley models

The argument cancels the term `∫ (u₁ - u₂) d(m₁(0) - m₂(0))` because the two equilibria start
from the same distribution. A stationary discounted equilibrium has no such common start: two
candidate rates carry two different stationary distributions. That is why the Lasry–Lions route
does not reach the Aiyagari uniqueness problem, and why the coupling through a market-clearing
price, which Graber and Matter show is typically NOT Lasry–Lions monotone, is handled there by
monotonicity of excess supply instead (`Equilibrium.Uniqueness`, `Analysis.StronglyMonotone`).

Overlapping generations DO have a common start — every cohort is born with nothing — so that
obstruction is absent and the question becomes the monotonicity condition itself.
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

/-- The pairings of all the dates added up. -/
noncomputable def summedPairing (F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ)
    (m₁ m₂ : Fin (T + 1) → ProbabilityMeasure X) : ℝ :=
  ∑ t, llPairing (F t) (m₁ t) (m₂ t)

/-- **The engine of the Lasry–Lions argument**, with no monotonicity in it at all: two relaxed
equilibria from a common initial distribution have a nonpositive SUMMED pairing. Adding the two
optimality inequalities signs the TOTAL over dates; it says nothing about any single date. -/
theorem summedPairing_nonpos_of_pathEquilibrium
    {F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ}
    {η₁ η₂ : ProbabilityMeasure (Path X T)}
    (h₁ : IsPathEquilibrium F η₁) (h₂ : IsPathEquilibrium F η₂)
    (h0 : marginal η₁ 0 = marginal η₂ 0) :
    summedPairing F (marginal η₁) (marginal η₂) ≤ 0 := by
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
  unfold summedPairing
  simp only [hpair, Finset.sum_sub_distrib]
  linarith

/-- **Summed Lasry–Lions monotonicity**: the pairing of the WHOLE life is nonnegative, though no
single date need be. This is the weakest hypothesis the argument above can use. -/
def SummedLasryLionsMonotone (F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ) : Prop :=
  ∀ m₁ m₂ : Fin (T + 1) → ProbabilityMeasure X, 0 ≤ summedPairing F m₁ m₂

omit [Finite X] [MeasurableSingletonClass X] in
/-- Date-by-date monotonicity is the special case in which every summand is already nonnegative. -/
theorem summedLasryLionsMonotone_of_forall {F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ}
    (hF : ∀ t, LasryLionsMonotone (F t)) : SummedLasryLionsMonotone F :=
  fun _ _ => Finset.sum_nonneg fun t _ => hF t _ _

/-- Under the summed condition the total pairing is zero. -/
theorem summedPairing_eq_zero_of_pathEquilibrium
    {F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ} (hF : SummedLasryLionsMonotone F)
    {η₁ η₂ : ProbabilityMeasure (Path X T)}
    (h₁ : IsPathEquilibrium F η₁) (h₂ : IsPathEquilibrium F η₂)
    (h0 : marginal η₁ 0 = marginal η₂ 0) :
    summedPairing F (marginal η₁) (marginal η₂) = 0 :=
  le_antisymm (summedPairing_nonpos_of_pathEquilibrium h₁ h₂ h0) (hF _ _)

/-- **Uniqueness of an aggregate from the summed pairing alone.** If the cost SEPARATES a
statistic `A` — the summed pairing is strictly positive whenever `A` differs — then two relaxed
equilibria from a common initial distribution agree on `A`. No single date is assumed monotone,
and no integrability or continuity is used. -/
theorem aggregate_eq_of_pathEquilibrium {F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ}
    {A : (Fin (T + 1) → ProbabilityMeasure X) → ℝ}
    (hsep : ∀ m₁ m₂, A m₁ ≠ A m₂ → 0 < summedPairing F m₁ m₂)
    {η₁ η₂ : ProbabilityMeasure (Path X T)}
    (h₁ : IsPathEquilibrium F η₁) (h₂ : IsPathEquilibrium F η₂)
    (h0 : marginal η₁ 0 = marginal η₂ 0) :
    A (marginal η₁) = A (marginal η₂) := by
  by_contra h
  exact absurd (summedPairing_nonpos_of_pathEquilibrium h₁ h₂ h0) (not_le.2 (hsep _ _ h))

/-- **Lasry–Lions for the finite-horizon finite-state game** (Cannarsa–Capuani Thm. 4.1 in
discrete time): two relaxed equilibria from the same initial distribution, with each date's cost
Lasry–Lions monotone, have zero pairing at every date. -/
theorem llPairing_eq_zero_of_pathEquilibrium {F : Fin (T + 1) → X → ProbabilityMeasure X → ℝ}
    (hF : ∀ t, LasryLionsMonotone (F t)) {η₁ η₂ : ProbabilityMeasure (Path X T)}
    (h₁ : IsPathEquilibrium F η₁) (h₂ : IsPathEquilibrium F η₂)
    (h0 : marginal η₁ 0 = marginal η₂ 0) (t : Fin (T + 1)) :
    llPairing (F t) (marginal η₁ t) (marginal η₂ t) = 0 := by
  have hsum := summedPairing_nonpos_of_pathEquilibrium h₁ h₂ h0
  unfold summedPairing at hsum
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

/-! ### Costs that see the whole family of marginals -/

section Family

/-- A family of date marginals. -/
abbrev Marginals (X : Type*) [MeasurableSpace X] (T : ℕ) := Fin (T + 1) → ProbabilityMeasure X

/-- The cost of a path when each date's cost may depend on the WHOLE family of marginals, not
only on its own date's. A stationary overlapping-generations economy needs this: the aggregate
capital that prices every date is an average across ALL ages. -/
def famPathCost (F : Fin (T + 1) → X → Marginals X T → ℝ) (m : Marginals X T)
    (γ : Path X T) : ℝ :=
  ∑ t, F t (γ t) m

/-- The value from `x` against a family of marginals. -/
noncomputable def famValue (F : Fin (T + 1) → X → Marginals X T → ℝ) (m : Marginals X T)
    (x : X) : ℝ :=
  ⨅ γ : {γ : Path X T // γ 0 = x}, famPathCost F m γ.1

omit [MeasurableSingletonClass X] in
theorem famValue_le (F : Fin (T + 1) → X → Marginals X T → ℝ) (m : Marginals X T)
    (γ : Path X T) : famValue F m (γ 0) ≤ famPathCost F m γ :=
  ciInf_le (Set.finite_range _).bddBelow (⟨γ, rfl⟩ : {γ' : Path X T // γ' 0 = γ 0})

/-- A relaxed equilibrium for a family-dependent cost. -/
def IsFamPathEquilibrium (F : Fin (T + 1) → X → Marginals X T → ℝ)
    (η : ProbabilityMeasure (Path X T)) : Prop :=
  ∀ᵐ γ ∂(η : Measure (Path X T)), famPathCost F (marginal η) γ = famValue F (marginal η) (γ 0)

theorem integral_famPathCost (F : Fin (T + 1) → X → Marginals X T → ℝ) (m : Marginals X T)
    (η : ProbabilityMeasure (Path X T)) :
    ∫ γ, famPathCost F m γ ∂(η : Measure (Path X T))
      = ∑ t, ∫ x, F t x m ∂(marginal η t : Measure X) := by
  unfold famPathCost
  rw [integral_finsetSum _ (fun t _ => Integrable.of_finite)]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold marginal
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_pi_apply t).aemeasurable (measurable_of_finite _).aestronglyMeasurable]

theorem integral_famValue (F : Fin (T + 1) → X → Marginals X T → ℝ) (m : Marginals X T)
    (η : ProbabilityMeasure (Path X T)) :
    ∫ x, famValue F m x ∂(marginal η 0 : Measure X)
      = ∫ γ, famValue F m (γ 0) ∂(η : Measure (Path X T)) := by
  unfold marginal
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_pi_apply 0).aemeasurable (measurable_of_finite _).aestronglyMeasurable]

theorem integral_famValue_le (F : Fin (T + 1) → X → Marginals X T → ℝ) (m : Marginals X T)
    (η : ProbabilityMeasure (Path X T)) :
    ∫ x, famValue F m x ∂(marginal η 0 : Measure X)
      ≤ ∑ t, ∫ x, F t x m ∂(marginal η t : Measure X) := by
  rw [integral_famValue, ← integral_famPathCost]
  exact integral_mono Integrable.of_finite Integrable.of_finite fun γ => famValue_le F m γ

theorem integral_famValue_eq {F : Fin (T + 1) → X → Marginals X T → ℝ}
    {η : ProbabilityMeasure (Path X T)} (h : IsFamPathEquilibrium F η) :
    ∫ x, famValue F (marginal η) x ∂(marginal η 0 : Measure X)
      = ∑ t, ∫ x, F t x (marginal η) ∂(marginal η t : Measure X) := by
  rw [integral_famValue, ← integral_famPathCost]
  exact (integral_congr_ae h).symm

/-- The summed pairing for a family-dependent cost. -/
noncomputable def famSummedPairing (F : Fin (T + 1) → X → Marginals X T → ℝ)
    (m₁ m₂ : Marginals X T) : ℝ :=
  (∑ t, ∫ x, (F t x m₁ - F t x m₂) ∂(m₁ t : Measure X))
    - ∑ t, ∫ x, (F t x m₁ - F t x m₂) ∂(m₂ t : Measure X)

theorem famSummedPairing_eq (F : Fin (T + 1) → X → Marginals X T → ℝ) (m₁ m₂ : Marginals X T) :
    famSummedPairing F m₁ m₂
      = ((∑ t, ∫ x, F t x m₁ ∂(m₁ t : Measure X)) - ∑ t, ∫ x, F t x m₂ ∂(m₁ t : Measure X))
        - ((∑ t, ∫ x, F t x m₁ ∂(m₂ t : Measure X))
            - ∑ t, ∫ x, F t x m₂ ∂(m₂ t : Measure X)) := by
  have h : ∀ m : Marginals X T, (∑ t, ∫ x, (F t x m₁ - F t x m₂) ∂(m t : Measure X))
      = (∑ t, ∫ x, F t x m₁ ∂(m t : Measure X)) - ∑ t, ∫ x, F t x m₂ ∂(m t : Measure X) := by
    intro m
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ =>
      integral_sub Integrable.of_finite Integrable.of_finite
  unfold famSummedPairing
  rw [h m₁, h m₂]

/-- **The engine, for a cost that sees the whole family.** Two relaxed equilibria from a common
initial distribution have a nonpositive summed pairing. -/
theorem famSummedPairing_nonpos_of_pathEquilibrium
    {F : Fin (T + 1) → X → Marginals X T → ℝ} {η₁ η₂ : ProbabilityMeasure (Path X T)}
    (h₁ : IsFamPathEquilibrium F η₁) (h₂ : IsFamPathEquilibrium F η₂)
    (h0 : marginal η₁ 0 = marginal η₂ 0) :
    famSummedPairing F (marginal η₁) (marginal η₂) ≤ 0 := by
  have e₁ := integral_famValue_eq h₁
  have e₂ := integral_famValue_eq h₂
  have i₁ := integral_famValue_le F (marginal η₂) η₁
  have i₂ := integral_famValue_le F (marginal η₁) η₂
  rw [h0] at e₁ i₁
  rw [famSummedPairing_eq]
  linarith

/-- The cost borne by population `m'` when the prices are set by population `m`. -/
noncomputable def famCost (F : Fin (T + 1) → X → Marginals X T → ℝ) (m m' : Marginals X T) : ℝ :=
  ∑ t, ∫ x, F t x m ∂(m' t : Measure X)

theorem famSummedPairing_eq_cost (F : Fin (T + 1) → X → Marginals X T → ℝ)
    (m₁ m₂ : Marginals X T) :
    famSummedPairing F m₁ m₂
      = (famCost F m₁ m₁ - famCost F m₂ m₁) - (famCost F m₁ m₂ - famCost F m₂ m₂) :=
  famSummedPairing_eq F m₁ m₂

/-- **The pairing is minus the sum of the two cross-losses.** Pure algebra, no hypotheses. -/
theorem famSummedPairing_eq_neg_losses (F : Fin (T + 1) → X → Marginals X T → ℝ)
    (m₁ m₂ : Marginals X T) :
    famSummedPairing F m₁ m₂
      = -((famCost F m₁ m₂ - famCost F m₁ m₁) + (famCost F m₂ m₁ - famCost F m₂ m₂)) := by
  rw [famSummedPairing_eq_cost]; ring

/-- **Each cross-loss is nonnegative**: a population pays at least as much under someone else's
prices as the population those prices came from does. Revealed preference, twice. -/
theorem famCost_le_of_pathEquilibrium {F : Fin (T + 1) → X → Marginals X T → ℝ}
    {η₁ η₂ : ProbabilityMeasure (Path X T)} (h₁ : IsFamPathEquilibrium F η₁)
    (h0 : marginal η₁ 0 = marginal η₂ 0) :
    famCost F (marginal η₁) (marginal η₁) ≤ famCost F (marginal η₁) (marginal η₂) := by
  have e := integral_famValue_eq h₁
  have i := integral_famValue_le F (marginal η₁) η₂
  rw [← h0] at i
  unfold famCost
  linarith

/-- **Why the monotonicity hypothesis admits no local version.** At two relaxed equilibria from a
common start the summed pairing is minus a sum of two nonnegative revealed-preference losses. So a
hypothesis forcing it to be positive is not a perturbation statement about nearby populations: it
is exactly the assertion that no such pair exists, and any proof of it must be global. -/
theorem famSummedPairing_nonpos_of_losses {F : Fin (T + 1) → X → Marginals X T → ℝ}
    {η₁ η₂ : ProbabilityMeasure (Path X T)} (h₁ : IsFamPathEquilibrium F η₁)
    (h₂ : IsFamPathEquilibrium F η₂) (h0 : marginal η₁ 0 = marginal η₂ 0) :
    famSummedPairing F (marginal η₁) (marginal η₂) ≤ 0 := by
  rw [famSummedPairing_eq_neg_losses]
  have l₁ := famCost_le_of_pathEquilibrium h₁ h0
  have l₂ := famCost_le_of_pathEquilibrium h₂ h0.symm
  linarith

/-! #### Interaction through a real statistic -/

/-- The whole-life cost of the population `m`, priced by the statistic value `s`. -/
noncomputable def famLifetime (φ : Fin (T + 1) → X → ℝ → ℝ) (m : Marginals X T) (s : ℝ) : ℝ :=
  ∑ t, ∫ x, φ t x s ∂(m t : Measure X)

/-- **The reduction.** When the population enters only through a real statistic `θ`, the summed
pairing is exactly the MIXED DIFFERENCE of the whole-life cost in (population, statistic). A
condition on measures has become a submodularity condition on a function of two arguments. -/
theorem famSummedPairing_scalar (φ : Fin (T + 1) → X → ℝ → ℝ) (θ : Marginals X T → ℝ)
    (m₁ m₂ : Marginals X T) :
    famSummedPairing (fun t x m => φ t x (θ m)) m₁ m₂
      = (famLifetime φ m₁ (θ m₁) - famLifetime φ m₁ (θ m₂))
        - (famLifetime φ m₂ (θ m₁) - famLifetime φ m₂ (θ m₂)) := by
  rw [famSummedPairing_eq]
  rfl

/-- **Strictly increasing differences of the whole-life COST pin the statistic.** Equivalently,
for a payoff, strictly DECREASING differences: the plan that goes with the larger aggregate loses
its relative advantage as the aggregate rises. Two relaxed equilibria from a common initial
distribution then agree on `θ`. -/
theorem statistic_eq_of_increasingDifferences {φ : Fin (T + 1) → X → ℝ → ℝ}
    {θ : Marginals X T → ℝ}
    (hdd : ∀ m₁ m₂ : Marginals X T, θ m₁ ≠ θ m₂ →
      famLifetime φ m₂ (θ m₁) - famLifetime φ m₂ (θ m₂)
        < famLifetime φ m₁ (θ m₁) - famLifetime φ m₁ (θ m₂))
    {η₁ η₂ : ProbabilityMeasure (Path X T)}
    (h₁ : IsFamPathEquilibrium (fun t x m => φ t x (θ m)) η₁)
    (h₂ : IsFamPathEquilibrium (fun t x m => φ t x (θ m)) η₂)
    (h0 : marginal η₁ 0 = marginal η₂ 0) :
    θ (marginal η₁) = θ (marginal η₂) := by
  by_contra h
  have hle := famSummedPairing_nonpos_of_pathEquilibrium h₁ h₂ h0
  rw [famSummedPairing_scalar] at hle
  linarith [hdd (marginal η₁) (marginal η₂) h]

/-! #### What the hypothesis reduces to -/

/-- **The comonotonicity collapse.** Suppose a statistic `A` and a comparison functional `Φ` on a
family of candidates are COMONOTONE — whenever `A` is larger, `Φ` is at least as large — which is
the weakest form in which the hypothesis of `statistic_eq_of_increasingDifferences` can be imposed
on a family, and which does NOT ask `A` itself to be monotone. If `Φ` is strictly monotone along
the family, then `A` is monotone along it.

For the overlapping-generations economy this closes the route. The hypothesis was attractive
because it does not require capital supply to be monotone in the rate, which is the step that is
unavailable at high risk aversion. But `Φ` IS monotone along the family (measured, over the whole
bracket, at every risk aversion), so comonotonicity delivers monotone supply — and monotone supply
already gives uniqueness by single crossing, with no mean field game. The Lasry–Lions route, taken
to its end, is not logically weaker than the single-crossing route in this model. -/
theorem monotone_of_comonotone_of_strictMono {ι : Type*} [LinearOrder ι] {A Φ : ι → ℝ}
    (hc : ∀ i j, A j < A i → Φ j ≤ Φ i) (hΦ : StrictMono Φ) : Monotone A := by
  intro i j hij
  by_contra h
  have hlt : A j < A i := lt_of_not_ge h
  have h₁ : Φ j ≤ Φ i := hc i j hlt
  have h₂ : Φ i ≤ Φ j := hΦ.monotone hij
  have : i = j := hΦ.injective (le_antisymm h₂ h₁)
  exact absurd (this ▸ hlt) (lt_irrefl _)

end Family

end Paths

end MeanFieldGame

end LeanEconomics
