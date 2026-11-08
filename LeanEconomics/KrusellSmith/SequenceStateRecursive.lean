/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.SequenceStateEquilibrium

/-!
# Recursive equilibrium on infinite histories

Milestone TS4 of `SEQUENCE_STATE_PLAN.md`.

A sequence-state equilibrium (TS3) is a **time-homogeneous recursive equilibrium whose aggregate
state is the infinite history `ω` of aggregate shocks** (`HistoryRecursiveEquilibrium`): the
household's state is `(ω, a, e)`, and

* the aggregate law of motion is `ω ↦ cons z' ω` (the new shock is prepended);
* the distribution, capital and labour are functions of `ω`, with capital and labour the means
  of the distribution (`capital_eq`, `labour_eq`), and prices at `ω` are those of
  `(ω 0, capital ω, labour ω)`;
* the value and the saving policy are functions of `(ω, a, e)`, and satisfy the **Bellman
  equation** with continuation values at the histories `cons z' ω` (`bellman`), the saving
  being optimal among all feasible savings (`optimal`);
* the distribution evolves by the saving policy and the idiosyncratic transitions
  (`lawOfMotion`); in particular, **capital at `cons z' ω` is mean saving at `ω`**, whatever the
  new shock (`HistoryRecursiveEquilibrium.capital_cons`).

Nothing depends on calendar time, and nothing on an initial distribution.

The household side holds for every assignment, equilibrium or not: on the tree rooted at `ω`,
the value function and the policy at node `g` are the root ones at `prepend g ω`
(`valueFunction_node`, `policy_node`, by re-rooting, `Continuation.lean`), so the root value
`seqValue` satisfies a Bellman equation on histories (`seqValue_eq`, `objective_le_seqValue`).

`exists_historyRecursiveEquilibrium`: such an equilibrium exists in every `KSModel`;
`logEconomy_exists_historyRecursiveEquilibrium`: with log utility and Cobb–Douglas prices.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (μ : History Z → ProbabilityMeasure M.AState)

/-! ### The household on histories -/

/-- The value at the history `ω` with assets `a` and idiosyncratic state `e`: the root value of
the household problem against the prices seen at `ω`. -/
noncomputable def seqValue (ω : History Z) (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) : ℝ :=
  (M.household (ω 0) (M.seqPrices μ ω)).valueFunction (a, ⟨e, []⟩)

/-- The saving policy at the history `ω`. -/
noncomputable def seqPolicy (ω : History Z) (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    ↥(Icc (0 : ℝ) M.assetCap) :=
  ⟨M.policy (ω 0) (M.seqPrices μ ω) (a, ⟨e, []⟩), M.policy_mem_Icc _ _ _⟩

/-- Cash on hand at the history `ω`. -/
noncomputable def seqCash (ω : History Z) (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) : ℝ :=
  M.cash (ω 0) (M.seqPrices μ ω) (a, ⟨e, []⟩)

/-- **Prices at a history depend on it through today's shock and today's distribution.** -/
theorem seqCash_eq (ω : History Z) (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    M.seqCash μ ω a e
      = M.grossReturn (ω 0) (M.seqPrices μ ω []).1 (M.seqPrices μ ω []).2 * a
        + M.wage (ω 0) (M.seqPrices μ ω []).1 (M.seqPrices μ ω []).2 * M.efficiency e
        - M.grossReturn (ω 0) (M.seqPrices μ ω []).1 (M.seqPrices μ ω []).2 * M.borrowLimit := rfl

/-- The prices on the subtree below `g` are those seen at `prepend g ω`. -/
theorem seqPrices_prepend_eq_shiftPath (ω : History Z) (g : List Z) :
    M.seqPrices μ (History.prepend g ω) = shiftPath (M.seqPrices μ ω) g := by
  funext g'
  rw [M.seqPrices_prepend, shiftPath_apply]

/-- **The value at node `g` of the tree rooted at `ω` is the value at the history
`prepend g ω`.** -/
theorem valueFunction_node (ω : History Z) (g : List Z) (a : ↥(Icc (0 : ℝ) M.assetCap))
    (e : E) :
    (M.household (ω 0) (M.seqPrices μ ω)).valueFunction (a, ⟨e, g⟩)
      = M.seqValue μ (History.prepend g ω) a e := by
  have h := M.valueFunction_shift (ω 0) (M.seqPrices μ ω) g
  rw [seqValue, History.prepend_zero, M.seqPrices_prepend_eq_shiftPath, h]
  rfl

/-- **The policy at node `g` of the tree rooted at `ω` is the policy at the history
`prepend g ω`.** -/
theorem policy_node (ω : History Z) (g : List Z) (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    M.policy (ω 0) (M.seqPrices μ ω) (a, ⟨e, g⟩) = M.seqPolicy μ (History.prepend g ω) a e := by
  change _ = M.policy (History.prepend g ω 0) (M.seqPrices μ (History.prepend g ω)) (a, ⟨e, []⟩)
  rw [History.prepend_zero, M.seqPrices_prepend_eq_shiftPath, M.policy_shift]
  rfl

/-- The household objective at the root, written on histories. -/
theorem objective_root (ω : History Z) (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) {a' : ℝ}
    (ha' : a' ∈ (M.household (ω 0) (M.seqPrices μ ω)).feasible (a, ⟨e, []⟩)) :
    (M.household (ω 0) (M.seqPrices μ ω)).objective
        (M.household (ω 0) (M.seqPrices μ ω)).valueFunction (a, ⟨e, []⟩) a'
      = M.utility (M.seqCash μ ω a e - a')
        + M.discount * ∑ ze : Z × E, M.aggProb (ω 0) ze.1 * M.idioProb (ω 0) ze.1 e ze.2
            * M.seqValue μ (History.cons ze.1 ω) ⟨a', M.mem_Icc_of_mem_feasible _ _ ha'⟩ ze.2 := by
  rw [M.objective_eq _ _ _ ha']
  congr 2
  refine Finset.sum_congr rfl fun ze _ => ?_
  rw [M.clampAssets_of_mem (M.mem_Icc_of_mem_feasible _ _ ha'), M.valueFunction_node]
  rfl

/-- **The Bellman equation on histories**, attained at the policy. -/
theorem seqValue_eq (ω : History Z) (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    M.seqValue μ ω a e
      = M.utility (M.seqCash μ ω a e - M.seqPolicy μ ω a e)
        + M.discount * ∑ ze : Z × E, M.aggProb (ω 0) ze.1 * M.idioProb (ω 0) ze.1 e ze.2
            * M.seqValue μ (History.cons ze.1 ω) (M.seqPolicy μ ω a e) ze.2 := by
  have h := M.policy_optimal (ω 0) (M.seqPrices μ ω) (a, ⟨e, []⟩)
  rw [(M.household (ω 0) (M.seqPrices μ ω)).bellman_valueFunction,
    M.objective_root μ ω a e (M.policy_mem _ _ _)] at h
  exact h

/-- **Optimality on histories**: no feasible saving does better than the value. -/
theorem objective_le_seqValue (ω : History Z) (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E)
    (a' : ↥(Icc (0 : ℝ) M.assetCap)) (ha' : (a' : ℝ) ≤ M.seqCash μ ω a e - M.consFloor) :
    M.utility (M.seqCash μ ω a e - a')
        + M.discount * ∑ ze : Z × E, M.aggProb (ω 0) ze.1 * M.idioProb (ω 0) ze.1 e ze.2
            * M.seqValue μ (History.cons ze.1 ω) a' ze.2
      ≤ M.seqValue μ ω a e := by
  have hf : (a' : ℝ) ∈ (M.household (ω 0) (M.seqPrices μ ω)).feasible (a, ⟨e, []⟩) :=
    ⟨a'.2.1, le_min a'.2.2 ha'⟩
  have h := (M.household (ω 0) (M.seqPrices μ ω)).le_bellmanFn
    (M.household (ω 0) (M.seqPrices μ ω)).valueFunction hf
  rw [M.objective_root μ ω a e hf] at h
  change _ ≤ (M.household (ω 0) (M.seqPrices μ ω)).bellman
    (M.household (ω 0) (M.seqPrices μ ω)).valueFunction (a, ⟨e, []⟩) at h
  rw [(M.household (ω 0) (M.seqPrices μ ω)).bellman_valueFunction] at h
  exact h

theorem seqPolicy_le (ω : History Z) (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    (M.seqPolicy μ ω a e : ℝ) ≤ M.seqCash μ ω a e - M.consFloor :=
  (M.policy_mem (ω 0) (M.seqPrices μ ω) (a, ⟨e, []⟩)).2.trans (min_le_right _ _)

/-! ### The distribution on histories -/

variable {M μ}

/-- **The law of motion of the distribution** in a sequence-state equilibrium. -/
theorem IsSeqStateEquilibrium.integral_cons (hμ : M.IsSeqStateEquilibrium μ) (ω : History Z)
    (z' : Z) (f : M.AState →ᵇ ℝ) :
    ∫ x, f x ∂(μ (History.cons z' ω) : Measure M.AState)
      = ∫ x, ∑ e', M.idioProb (ω 0) z' x.2.idio e' * f (M.seqPolicy μ ω x.1 x.2.idio, ⟨e'⟩)
          ∂(μ ω : Measure M.AState) := by
  have h := congrArg (fun ν : History Z → ProbabilityMeasure M.AState =>
    (ν (History.cons z' ω) : Measure M.AState)) hμ
  rw [← h, M.coe_seqStep_cons, M.integral_pushNode]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine Finset.sum_congr rfl fun e' _ => ?_
  simp only [nextA, M.clampAssets_of_mem (M.policy_mem_Icc _ _ _)]
  rfl

/-! ### Recursive equilibrium with the infinite history as the aggregate state -/

variable (M)

/-- A **recursive equilibrium whose aggregate state is the infinite history of aggregate
shocks**. The household's state is `(ω, a, e)`; the aggregate law of motion is `ω ↦ cons z' ω`. -/
structure HistoryRecursiveEquilibrium where
  /-- The distribution of households at each history. -/
  dist : History Z → ProbabilityMeasure M.AState
  /-- Aggregate capital at each history. -/
  capital : History Z → ℝ
  /-- Aggregate labour at each history. -/
  labour : History Z → ℝ
  /-- The household's value. -/
  value : History Z → ↥(Icc (0 : ℝ) M.assetCap) → E → ℝ
  /-- The household's saving. -/
  saving : History Z → ↥(Icc (0 : ℝ) M.assetCap) → E → ↥(Icc (0 : ℝ) M.assetCap)
  capital_eq : ∀ ω, capital ω = ∫ x, M.assets x ∂(dist ω : Measure M.AState)
  labour_eq : ∀ ω, labour ω = ∫ x, M.efficiency x.2.idio ∂(dist ω : Measure M.AState)
  feasible : ∀ ω (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E), (saving ω a e : ℝ)
    ≤ M.grossReturn (ω 0) (capital ω) (labour ω) * a
      + M.wage (ω 0) (capital ω) (labour ω) * M.efficiency e
        - M.grossReturn (ω 0) (capital ω) (labour ω) * M.borrowLimit - M.consFloor
  bellman : ∀ ω (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E), value ω a e
    = M.utility (M.grossReturn (ω 0) (capital ω) (labour ω) * a
        + M.wage (ω 0) (capital ω) (labour ω) * M.efficiency e
        - M.grossReturn (ω 0) (capital ω) (labour ω) * M.borrowLimit - saving ω a e)
      + M.discount * ∑ ze : Z × E, M.aggProb (ω 0) ze.1 * M.idioProb (ω 0) ze.1 e ze.2
          * value (History.cons ze.1 ω) (saving ω a e) ze.2
  optimal : ∀ ω (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) (a' : ↥(Icc (0 : ℝ) M.assetCap)),
    (a' : ℝ) ≤ M.grossReturn (ω 0) (capital ω) (labour ω) * a
      + M.wage (ω 0) (capital ω) (labour ω) * M.efficiency e
        - M.grossReturn (ω 0) (capital ω) (labour ω) * M.borrowLimit - M.consFloor →
    M.utility (M.grossReturn (ω 0) (capital ω) (labour ω) * a
        + M.wage (ω 0) (capital ω) (labour ω) * M.efficiency e
        - M.grossReturn (ω 0) (capital ω) (labour ω) * M.borrowLimit - a')
      + M.discount * ∑ ze : Z × E, M.aggProb (ω 0) ze.1 * M.idioProb (ω 0) ze.1 e ze.2
          * value (History.cons ze.1 ω) a' ze.2
      ≤ value ω a e
  lawOfMotion : ∀ ω z' (f : M.AState →ᵇ ℝ),
    ∫ x, f x ∂(dist (History.cons z' ω) : Measure M.AState)
      = ∫ x, ∑ e', M.idioProb (ω 0) z' x.2.idio e' * f (saving ω x.1 x.2.idio, ⟨e'⟩)
          ∂(dist ω : Measure M.AState)

namespace HistoryRecursiveEquilibrium

variable {M}

/-- **Capital is predetermined**: capital at `cons z' ω` is mean saving at `ω`, whatever the new
shock `z'`. -/
theorem capital_cons (R : M.HistoryRecursiveEquilibrium) (ω : History Z) (z' : Z) :
    R.capital (History.cons z' ω)
      = ∫ x, (R.saving ω x.1 x.2.idio : ℝ) ∂(R.dist ω : Measure M.AState) := by
  rw [R.capital_eq, R.lawOfMotion]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change ∑ e', M.idioProb (ω 0) z' x.2.idio e' * (R.saving ω x.1 x.2.idio : ℝ) = _
  rw [← Finset.sum_mul, M.idioProb_sum, one_mul]

end HistoryRecursiveEquilibrium

variable {M} {μ : History Z → ProbabilityMeasure M.AState}

/-- **A sequence-state equilibrium is a recursive equilibrium on histories.** -/
noncomputable def IsSeqStateEquilibrium.toRecursive (hμ : M.IsSeqStateEquilibrium μ) :
    M.HistoryRecursiveEquilibrium where
  dist := μ
  capital ω := (M.seqPrices μ ω []).1
  labour ω := (M.seqPrices μ ω []).2
  value := M.seqValue μ
  saving := M.seqPolicy μ
  capital_eq _ := rfl
  labour_eq ω := hμ.labour_eq ω []
  feasible ω a e := M.seqPolicy_le μ ω a e
  bellman ω a e := M.seqValue_eq μ ω a e
  optimal ω a e a' ha' := M.objective_le_seqValue μ ω a e a' ha'
  lawOfMotion ω z' f := hμ.integral_cons ω z' f

variable (M) in
/-- **Existence of a recursive equilibrium with the infinite history as the aggregate state**,
in every Krusell–Smith economy. -/
theorem exists_historyRecursiveEquilibrium [Nonempty E] :
    Nonempty M.HistoryRecursiveEquilibrium :=
  let ⟨_, hμ⟩ := M.exists_seqStateEquilibrium
  ⟨hμ.toRecursive⟩

end KSModel

/-- **A recursive equilibrium on histories with log utility and Cobb–Douglas production.** -/
theorem logEconomy_exists_historyRecursiveEquilibrium [Nonempty E] (V : KSEnvironment Z E)
    (T : CobbDouglas Z) : Nonempty (logEconomy V T).floored.HistoryRecursiveEquilibrium :=
  (logEconomy V T).floored.exists_historyRecursiveEquilibrium

end KrusellSmith

end LeanEconomics
