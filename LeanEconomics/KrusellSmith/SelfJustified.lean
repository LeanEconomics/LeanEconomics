/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Expectations

/-!
# `J*` is self-justified

Milestone S5 (step 9) of `STATIONARITY_PLAN.md`. At every equilibrium state `ξ ∈ J*`, coming from
a sequential equilibrium `K`, the beliefs that tomorrow's state is the state at the child `[z']`
along `K` with probability `π(z, z')` (`justifiedBelief`) are supported on `J*` (`nodeState_mem`)
and consistent with `ξ` (`justifiedBelief_mem`). So **the expectations correspondence has
nonempty values** on `J*` (`expectations_nonempty`).

The conditions are the household's problem along `K` at the root: prices at the root depend on
`(z, μ)` alone (`cash_eq`), the next distribution is the distribution at `[z']`, and the objective
against the beliefs is the household's objective along `K` (`objective_eq_household`), so the
Bellman conditions are `policy_optimal` and `le_bellmanFn`.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory
open scoped ENNReal NNReal Classical

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **Beliefs justified by an equilibrium**: tomorrow's state is the state at the child `[z']`
along `K`, with probability `π(z, z')`. -/
noncomputable def justifiedBelief (z : Z) (μ : ProbabilityMeasure M.AState) {K : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium z (μ : Measure M.AState) K) :
    ProbabilityMeasure ↥M.equilibriumStates :=
  ⟨∑ z', ENNReal.ofReal (M.aggProb z z') •
      Measure.dirac (⟨M.nodeState z μ K [z'], M.nodeState_mem z μ hK [z']⟩ :
        ↥M.equilibriumStates), ⟨by
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun z' _ => M.aggProb_nonneg z z', M.aggProb_sum,
      ENNReal.ofReal_one]⟩⟩

theorem integral_justifiedBelief (z : Z) (μ : ProbabilityMeasure M.AState) {K : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium z (μ : Measure M.AState) K) {f : ↥M.equilibriumStates → ℝ}
    (hf : Continuous f) :
    ∫ ξ', f ξ' ∂(M.justifiedBelief z μ hK : Measure ↥M.equilibriumStates)
      = ∑ z', M.aggProb z z' * f ⟨M.nodeState z μ K [z'], M.nodeState_mem z μ hK [z']⟩ := by
  have hint : ∀ z' ∈ (Finset.univ : Finset Z), Integrable f (ENNReal.ofReal (M.aggProb z z') •
      Measure.dirac (⟨M.nodeState z μ K [z'], M.nodeState_mem z μ hK [z']⟩ :
        ↥M.equilibriumStates)) := fun z' _ =>
    ((BoundedContinuousFunction.mkOfCompact (ContinuousMap.mk f hf)).integrable _).smul_measure
      ENNReal.ofReal_ne_top
  change ∫ ξ', f ξ' ∂(∑ z', _) = _
  rw [integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (M.aggProb_nonneg z z'),
    smul_eq_mul]

/-! ### The household's problem at an equilibrium state -/

section AtState

variable {M} {ξ : M.KSState} {K : List Z → ℝ}
  (hK : M.IsSequentialEquilibrium ξ.shock (ξ.dist : Measure M.AState) K)

include hK

/-- **Cash at an equilibrium state** is cash at the root along the equilibrium. -/
theorem cash_eq_root (x : M.AState) :
    ξ.cash x = M.cash ξ.shock (M.pricePath ξ.shock (M.initMass (ξ.dist : Measure M.AState)) K)
      (M.placeAt [] x) := by
  have hK0 : K [] = ξ.capital := hK []
  simp only [KSState.cash, KSModel.cash, returnAt, wageAt, pricePath, placeAt, shockAt_nil, hK0]
  rfl

theorem maxSaving_eq_root (x : M.AState) :
    ξ.maxSaving x
      = M.maxSaving ξ.shock (M.pricePath ξ.shock (M.initMass (ξ.dist : Measure M.AState)) K)
          (M.placeAt [] x) := by
  rw [KSState.maxSaving, cash_eq_root hK]
  rfl

end AtState

/-- **Every equilibrium state justifies its continuation**: the beliefs justified by the
equilibrium are consistent with the state. -/
theorem justifiedBelief_mem (ξ : ↥M.equilibriumStates) {K : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium ξ.1.shock (ξ.1.dist : Measure M.AState) K)
    (hv : M.rootValue ξ.1.shock (ξ.1.dist : Measure M.AState) K = ξ.1.value)
    (ha : M.rootPolicy ξ.1.shock (ξ.1.dist : Measure M.AState) K = ξ.1.policy) :
    M.justifiedBelief ξ.1.shock ξ.1.dist hK ∈ M.expectations ξ := by
  set z := ξ.1.shock with hz
  set μ := ξ.1.dist with hμ
  set P := M.pricePath z (M.initMass (μ : Measure M.AState)) K with hP
  set D := M.household z P
  set V := D.valueFunction
  set γ := M.justifiedBelief z μ hK
  have hpol : ∀ x, ξ.1.policy x = M.policy z P (M.placeAt [] x) := fun x => by
    rw [← ha]
    rfl
  have hval : ∀ x, ξ.1.value x = V (M.placeAt [] x) := fun x => by
    rw [← hv]
    rfl
  -- the objective against the justified beliefs is the household's objective
  have hobj : ∀ x b, b ∈ D.feasible (M.placeAt [] x) →
      ξ.1.objective γ x b = D.objective V (M.placeAt [] x) b := by
    intro x b hb
    rw [M.objective_eq z P V hb, KSState.objective]
    have hcash := cash_eq_root hK x
    have hmax : b ≤ M.cash z P (M.placeAt [] x) - M.consFloor := hb.2.trans (min_le_right _ _)
    rw [hcash, max_eq_right (by linarith)]
    congr 2
    have hcv : Continuous fun ξ' : ↥M.equilibriumStates => ξ.1.contValue x b ξ'.1 :=
      (KSState.continuous_contValue_right ξ.1 x b).comp continuous_subtype_val
    rw [M.integral_justifiedBelief z μ hK hcv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [KSState.contValue, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    simp only [shockProb, ContinuousMap.coe_mk]
    change M.aggProb z z' * (M.idioProb z z' x.2.idio e'
        * V (M.clampAssets b, ⟨e', [z']⟩))
      = M.aggProb z z' * M.idioProb z z' x.2.idio e' * V (M.clampAssets b, ⟨e', z' :: []⟩)
    ring
  refine ⟨fun z' g => ?_, fun x => ?_, fun x => ?_, fun x b hb => ?_⟩
  · -- shocks and distributions
    rw [M.integral_justifiedBelief z μ hK (M.continuous_test z' g),
      Finset.sum_eq_single z']
    · have hd : (M.nodeState z μ K [z']).dist = ξ.1.nextDist z' := by
        apply Subtype.ext
        have hnp : ∀ e', ξ.1.nextPoint e' = M.nextA z P [] e' := fun e' => funext fun x => by
          simp only [KSState.nextPoint, nextA, hpol]
          rfl
        change M.pushNode z P [] z' (μ : Measure M.AState) = ξ.1.nextMeasure z'
        simp only [KSState.nextMeasure, hnp]
        rfl
      simp only [shockInd]
      change M.aggProb z z' * ((if z' = z' then (1 : ℝ) else 0) * g (M.nodeState z μ K [z']).dist)
        = _
      rw [ite_eq_left rfl, one_mul, hd]
    · intro z'' _ hne
      simp only [shockInd]
      change M.aggProb z z'' * ((if z'' = z' then (1 : ℝ) else 0) * _) = 0
      rw [ite_eq_right hne, zero_mul, mul_zero]
    · exact fun h => absurd (Finset.mem_univ z') h
  · -- feasibility
    rw [hpol, maxSaving_eq_root hK]
    exact M.policy_mem z P (M.placeAt [] x)
  · -- Bellman, attained
    rw [hval, hpol, hobj x _ (M.policy_mem z P (M.placeAt [] x))]
    have h := M.policy_optimal z P (M.placeAt [] x)
    rw [(M.household z P).bellman_valueFunction] at h
    exact h
  · -- Bellman, optimality
    have hfeas : min b (ξ.1.maxSaving x) ∈ D.feasible (M.placeAt [] x) := by
      refine ⟨le_min hb.1 ?_, ?_⟩
      · rw [maxSaving_eq_root hK]
        exact M.maxSaving_nonneg z P _
      · rw [← maxSaving_eq_root hK]
        exact min_le_right _ _
    rw [hobj x _ hfeas, hval]
    have h := D.le_bellmanFn V hfeas
    change _ ≤ D.bellman _ _ at h
    rw [D.bellman_valueFunction] at h
    exact h

/-- **The expectations correspondence has nonempty values** on `J*`. -/
theorem expectations_nonempty (ξ : ↥M.equilibriumStates) : (M.expectations ξ).Nonempty := by
  obtain ⟨K, hK, hv, ha⟩ := ξ.2
  exact ⟨_, M.justifiedBelief_mem ξ hK hv ha⟩

end KSModel

end KrusellSmith

end LeanEconomics
