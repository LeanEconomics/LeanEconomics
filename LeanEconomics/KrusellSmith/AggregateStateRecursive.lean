/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.AggregateState

/-!
# Recursive equilibrium with aggregate shock and aggregate capital as the state

Milestone AK2 of `AGGREGATE_STATE_PLAN.md`.

`AggStateRecursiveEquilibrium`: the aggregate state is `(z, K)`, with `K` ranging over capital
sets `Kset z`; the household's state is `(z, K, a, e)`;

* capital evolves by `lawK z K z'` (staying in the capital sets), labour is `labourK z K`, and
  prices at `(z, K)` are those of `(z, K, labourK z K)`;
* value and saving are functions of `(z, K, a, e)`, satisfying the **Bellman equation** with
  continuation values at `(z', lawK z K z')` and optimal among feasible savings;
* **consistency of aggregation**: each `(z, K)` carries a nonempty set `dist z K` of
  distributions, all with mean assets `K` and labour `labourK z K`; from any of them, the saving
  policy and the idiosyncratic transitions lead to a distribution in `dist z' (lawK z K z')`
  (`lawOfMotion`); in particular **mean saving is `lawK z K z'`** (`integral_saving`).

`KSModel.toAggStateRecursive`: a sequence-state equilibrium satisfying `KSufficient` is such an
equilibrium, with `dist z K` the distributions the equilibrium visits at shock `z` with capital
`K`; it **represents** the sequence-state equilibrium: value, saving and the next capital at a
history are those at `(ω 0, capital ω)` (`seqValue_eq_valueK`, `seqPolicy_eq_savingK`,
`lawK_eq`). The capital sets are compact and `lawK`, `labourK` continuous on them
(`AggregateState.lean`).
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **A recursive equilibrium whose aggregate state is `(z, K)`.** -/
structure AggStateRecursiveEquilibrium where
  /-- The capital levels reached at each shock. -/
  Kset : Z → Set ℝ
  /-- The law of motion of capital. -/
  lawK : Z → ℝ → Z → ℝ
  /-- Labour at `(z, K)`. -/
  labourK : Z → ℝ → ℝ
  /-- The household's value. -/
  value : Z → ℝ → ↥(Icc (0 : ℝ) M.assetCap) → E → ℝ
  /-- The household's saving. -/
  saving : Z → ℝ → ↥(Icc (0 : ℝ) M.assetCap) → E → ↥(Icc (0 : ℝ) M.assetCap)
  /-- The distributions consistent with `(z, K)`. -/
  dist : Z → ℝ → Set (ProbabilityMeasure M.AState)
  lawK_mem : ∀ z k, k ∈ Kset z → ∀ z', lawK z k z' ∈ Kset z'
  dist_nonempty : ∀ z k, k ∈ Kset z → (dist z k).Nonempty
  capital_eq : ∀ z k ν, ν ∈ dist z k → ∫ x, M.assets x ∂(ν : Measure M.AState) = k
  labour_eq : ∀ z k ν, ν ∈ dist z k →
    labourK z k = ∑ e, M.initMass (ν : Measure M.AState) e * M.efficiency e
  feasible : ∀ z k, k ∈ Kset z → ∀ (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E),
    (saving z k a e : ℝ)
      ≤ M.grossReturn z k (labourK z k) * a + M.wage z k (labourK z k) * M.efficiency e
        - M.grossReturn z k (labourK z k) * M.borrowLimit
        - M.consFloor
  bellman : ∀ z k, k ∈ Kset z → ∀ (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E),
    value z k a e
      = M.utility (M.grossReturn z k (labourK z k) * a
          + M.wage z k (labourK z k) * M.efficiency e
        - M.grossReturn z k (labourK z k) * M.borrowLimit - saving z k a e)
        + M.discount * ∑ ze : Z × E, M.aggProb z ze.1 * M.idioProb z ze.1 e ze.2
            * value ze.1 (lawK z k ze.1) (saving z k a e) ze.2
  optimal : ∀ z k, k ∈ Kset z → ∀ (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E)
    (a' : ↥(Icc (0 : ℝ) M.assetCap)),
    (a' : ℝ) ≤ M.grossReturn z k (labourK z k) * a + M.wage z k (labourK z k) * M.efficiency e
        - M.grossReturn z k (labourK z k) * M.borrowLimit
      - M.consFloor →
    M.utility (M.grossReturn z k (labourK z k) * a
        + M.wage z k (labourK z k) * M.efficiency e
        - M.grossReturn z k (labourK z k) * M.borrowLimit - a')
      + M.discount * ∑ ze : Z × E, M.aggProb z ze.1 * M.idioProb z ze.1 e ze.2
          * value ze.1 (lawK z k ze.1) a' ze.2
      ≤ value z k a e
  lawOfMotion : ∀ z k ν, ν ∈ dist z k → ∀ z', ∃ ν' ∈ dist z' (lawK z k z'),
    ∀ f : M.AState →ᵇ ℝ, ∫ x, f x ∂(ν' : Measure M.AState)
      = ∫ x, ∑ e', M.idioProb z z' x.2.idio e' * f (saving z k x.1 x.2.idio, ⟨e'⟩)
          ∂(ν : Measure M.AState)

namespace AggStateRecursiveEquilibrium

variable {M}

/-- **Capital is predetermined**: mean saving at `(z, K)` is next period's capital
`lawK z K z'`, whatever the new shock. -/
theorem integral_saving (R : M.AggStateRecursiveEquilibrium) {z : Z} {k : ℝ}
    {ν : ProbabilityMeasure M.AState} (hν : ν ∈ R.dist z k) (z' : Z) :
    ∫ x, (R.saving z k x.1 x.2.idio : ℝ) ∂(ν : Measure M.AState) = R.lawK z k z' := by
  obtain ⟨ν', hν', hf⟩ := R.lawOfMotion z k ν hν z'
  have h := hf M.assets
  rw [R.capital_eq _ _ _ hν'] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change (R.saving z k x.1 x.2.idio : ℝ)
    = ∑ e', M.idioProb z z' x.2.idio e' * (R.saving z k x.1 x.2.idio : ℝ)
  rw [← Finset.sum_mul, M.idioProb_sum, one_mul]

end AggStateRecursiveEquilibrium

/-! ### The sequence-state equilibrium on `(z, K)` -/

variable {M} {μ : History Z → ProbabilityMeasure M.AState}

/-- The household's value at `(z, k)`: against the price tree `aggTree μ z k`. -/
noncomputable def valueK (μ : History Z → ProbabilityMeasure M.AState) (z : Z) (k : ℝ)
    (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) : ℝ :=
  (M.household z (aggTree μ z k)).valueFunction (a, ⟨e, []⟩)

/-- The household's saving at `(z, k)`. -/
noncomputable def savingK (μ : History Z → ProbabilityMeasure M.AState) (z : Z) (k : ℝ)
    (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) : ↥(Icc (0 : ℝ) M.assetCap) :=
  ⟨M.policy z (aggTree μ z k) (a, ⟨e, []⟩), M.policy_mem_Icc _ _ _⟩

theorem seqValue_eq_valueK (hS : KSufficient μ) (ω : History Z)
    (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    M.seqValue μ ω a e = valueK μ (ω 0) (capAt μ ω) a e := by
  rw [valueK, aggTree_eq hS ω]
  rfl

theorem seqPolicy_eq_savingK (hS : KSufficient μ) (ω : History Z)
    (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    M.seqPolicy μ ω a e = savingK μ (ω 0) (capAt μ ω) a e := by
  apply Subtype.ext
  change M.policy (ω 0) (M.seqPrices μ ω) (a, ⟨e, []⟩)
    = M.policy (ω 0) (aggTree μ (ω 0) (capAt μ ω)) (a, ⟨e, []⟩)
  rw [aggTree_eq hS ω]

theorem seqCash_eq_cashK (hS : KSufficient μ) (ω : History Z)
    (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    M.seqCash μ ω a e
      = M.grossReturn (ω 0) (capAt μ ω) (labourK μ (ω 0) (capAt μ ω)) * a
        + M.wage (ω 0) (capAt μ ω) (labourK μ (ω 0) (capAt μ ω)) * M.efficiency e
        - M.grossReturn (ω 0) (capAt μ ω) (labourK μ (ω 0) (capAt μ ω)) * M.borrowLimit := by
  rw [M.seqCash_eq, labourK_eq hS ω]
  rfl

theorem seqValue_cons_eq (hS : KSufficient μ) (ω : History Z) (z' : Z)
    (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    M.seqValue μ (History.cons z' ω) a e
      = valueK μ z' (lawK μ (ω 0) (capAt μ ω) z') a e := by
  rw [seqValue_eq_valueK hS, lawK_eq hS]
  rfl

/-- **A sequence-state equilibrium with `KSufficient` is a recursive equilibrium on `(z, K)`.** -/
noncomputable def toAggStateRecursive (hμ : M.IsSeqStateEquilibrium μ) (hS : KSufficient μ) :
    M.AggStateRecursiveEquilibrium where
  Kset := Kset μ
  lawK := lawK μ
  labourK := labourK μ
  value := valueK μ
  saving := savingK μ
  dist z k := {ν | ∃ ω : History Z, ω 0 = z ∧ capAt μ ω = k ∧ μ ω = ν}
  lawK_mem _ _ hk z' := lawK_mem hS hk z'
  dist_nonempty z k hk := by
    obtain ⟨ω, rfl, rfl⟩ := hk
    exact ⟨μ ω, ω, rfl, rfl, rfl⟩
  capital_eq z k ν hν := by
    obtain ⟨ω, -, rfl, rfl⟩ := hν
    rfl
  labour_eq z k ν hν := by
    obtain ⟨ω, rfl, rfl, rfl⟩ := hν
    exact labourK_eq hS ω
  feasible z k hk a e := by
    obtain ⟨ω, rfl, rfl⟩ := hk
    have h := M.seqPolicy_le μ ω a e
    rw [seqPolicy_eq_savingK hS, seqCash_eq_cashK hS] at h
    exact h
  bellman z k hk a e := by
    obtain ⟨ω, rfl, rfl⟩ := hk
    have h := M.seqValue_eq μ ω a e
    simp only [seqValue_cons_eq hS ω, seqPolicy_eq_savingK hS ω, seqCash_eq_cashK hS ω,
      seqValue_eq_valueK hS ω] at h
    exact h
  optimal z k hk a e a' ha' := by
    obtain ⟨ω, rfl, rfl⟩ := hk
    have ha'' : (a' : ℝ) ≤ M.seqCash μ ω a e - M.consFloor := by
      rw [seqCash_eq_cashK hS]
      exact ha'
    have h := M.objective_le_seqValue μ ω a e a' ha''
    simp only [seqValue_cons_eq hS ω, seqCash_eq_cashK hS ω, seqValue_eq_valueK hS ω] at h
    exact h
  lawOfMotion z k ν hν z' := by
    obtain ⟨ω, rfl, rfl, rfl⟩ := hν
    refine ⟨μ (History.cons z' ω), ⟨History.cons z' ω, rfl, (lawK_eq hS ω z').symm, rfl⟩,
      fun f => ?_⟩
    have h := hμ.integral_cons ω z' f
    simp only [seqPolicy_eq_savingK hS ω] at h
    exact h

end KSModel

end KrusellSmith

end LeanEconomics
