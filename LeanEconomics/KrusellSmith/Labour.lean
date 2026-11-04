/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Equilibrium
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Labour on the tree is the labour of the distribution of households

Prices at a node use aggregate labour `labour z₀ h`, computed from the exogenous recursion
`stateMass` for the mass of households in each idiosyncratic state. This module shows that the
recursion is right: started from the masses of the initial distribution (`initMass μ₀`), it
gives at every node the masses of the distribution of households there, whatever the path of
capital and the policy (`real_nodeDist_idio`). Saving moves assets, not idiosyncratic states, so
the masses move by the idiosyncratic transitions alone.

Hence aggregate labour at every node is the mean efficiency of the households there
(`labour_eq_integral`), and the sequential equilibrium of `exists_sequentialEquilibrium` has
labour consistent with its distribution (`exists_sequentialEquilibrium_labour`).
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z)

/-- Households in idiosyncratic state `e`. -/
def idioSet (e : E) : Set M.AState := {x | x.2.idio = e}

theorem measurableSet_idioSet (e : E) : MeasurableSet (M.idioSet e) := by
  have h : MeasurableSet {i : Idio E | i.idio = e} := MeasurableSpace.measurableSet_top
  exact measurable_snd h

/-- The indicator of idiosyncratic state `e`, as a bounded continuous function. -/
noncomputable def idioInd (e : E) : M.AState →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup ((M.idioSet e).indicator 1)
    (continuous_prod_of_discrete_right.2 fun i => by
      by_cases hi : i.idio = e
      · exact (continuous_const : Continuous fun _ : ↥(Icc (0 : ℝ) M.assetCap) => (1 : ℝ)).congr
          fun a => by simp [idioSet, hi]
      · exact (continuous_const : Continuous fun _ : ↥(Icc (0 : ℝ) M.assetCap) => (0 : ℝ)).congr
          fun a => by simp [idioSet, hi])
    1 fun x => by
      by_cases hx : x ∈ M.idioSet e <;> simp [hx]

theorem idioInd_of_eq {e : E} {x : M.AState} (hx : x.2.idio = e) : M.idioInd e x = 1 := by
  change (M.idioSet e).indicator 1 x = _
  simp [idioSet, hx]

theorem idioInd_of_ne {e : E} {x : M.AState} (hx : ¬ x.2.idio = e) : M.idioInd e x = 0 := by
  change (M.idioSet e).indicator 1 x = _
  simp [idioSet, hx]

theorem integral_idioInd (μ : Measure M.AState) (e : E) :
    ∫ x, M.idioInd e x ∂μ = μ.real (M.idioSet e) :=
  integral_indicator_one (M.measurableSet_idioSet e)

/-- A function of the idiosyncratic state alone is a combination of the indicators. -/
theorem eq_sum_idioInd (c : E → ℝ) (x : M.AState) :
    c x.2.idio = ∑ e, c e * M.idioInd e x := by
  classical
  rw [Finset.sum_eq_single x.2.idio]
  · rw [M.idioInd_of_eq rfl, mul_one]
  · intro e _ he
    rw [M.idioInd_of_ne (Ne.symm he), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem integral_of_idio {μ : Measure M.AState} [IsProbabilityMeasure μ] (c : E → ℝ) :
    ∫ x, c x.2.idio ∂μ = ∑ e, c e * μ.real (M.idioSet e) := by
  simp_rw [M.eq_sum_idioInd c]
  rw [integral_finsetSum _ fun e _ => ((M.idioInd e).integrable μ).const_mul (c e)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_const_mul, M.integral_idioInd]

variable (μ₀ : Measure M.AState) [IsProbabilityMeasure μ₀]

/-- **The recursion `stateMass` gives the masses of the distribution of households** at every
node, for every path of capital. -/
theorem real_nodeDist_idio (K : List Z → ℝ × ℝ) :
    ∀ (h : List Z) (e : E),
      (M.nodeDist z₀ μ₀ K h).real (M.idioSet e) = M.stateMass z₀ (M.initMass μ₀) h e
  | [], _ => rfl
  | z' :: h, e' => by
    have := M.isProbabilityMeasure_nodeDist z₀ μ₀ K h
    have hnext : ∀ x, M.expectedNext z₀ K h z' (M.idioInd e') x = M.nextProb z₀ h z' e' x := by
      intro x
      classical
      change ∑ e'', M.nextProb z₀ h z' e'' x * M.idioInd e' (M.nextA z₀ K h e'' x) = _
      rw [Finset.sum_eq_single e']
      · rw [M.idioInd_of_eq (e := e') (x := M.nextA z₀ K h e' x) rfl, mul_one]
      · intro e'' _ he''
        rw [M.idioInd_of_ne (e := e') (x := M.nextA z₀ K h e'' x) he'', mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    rw [← M.integral_idioInd]
    change ∫ x, M.idioInd e' x ∂(M.pushNode z₀ K h z' (M.nodeDist z₀ μ₀ K h)) = _
    rw [M.integral_pushNode z₀ K h z' _ (M.idioInd e')]
    change ∫ x, M.expectedNext z₀ K h z' (M.idioInd e') x ∂(M.nodeDist z₀ μ₀ K h) = _
    simp only [hnext]
    change ∫ x, M.idioProb (shockAt z₀ h) z' x.2.idio e' ∂(M.nodeDist z₀ μ₀ K h) = _
    rw [M.integral_of_idio (fun e => M.idioProb (shockAt z₀ h) z' e e')]
    simp only [stateMass]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [real_nodeDist_idio K h e, mul_comm]

/-- **Aggregate labour at every node is the mean efficiency of the households there.** -/
theorem labour_eq_integral (K : List Z → ℝ × ℝ) (h : List Z) :
    M.labour z₀ (M.initMass μ₀) h
      = ∫ x, M.efficiency x.2.idio ∂(M.nodeDist z₀ μ₀ K h) := by
  have := M.isProbabilityMeasure_nodeDist z₀ μ₀ K h
  rw [M.integral_of_idio M.efficiency, labour]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [M.real_nodeDist_idio z₀ μ₀ K h e, mul_comm]

/-- **Existence of sequential equilibrium, with labour consistent with the distribution**: at
every node, capital is mean assets and labour is mean efficiency of the households there. -/
theorem exists_sequentialEquilibrium_labour :
    ∃ K ∈ M.capitalPaths (M.initCapital μ₀), M.IsSequentialEquilibrium z₀ μ₀ K ∧
      ∀ h, M.labour z₀ (M.initMass μ₀) h
        = ∫ x, M.efficiency x.2.idio
            ∂(M.nodeDist z₀ μ₀ (M.pricePath z₀ (M.initMass μ₀) K) h) := by
  obtain ⟨K, hK, heq⟩ := M.exists_sequentialEquilibrium z₀ μ₀
  exact ⟨K, hK, heq, fun h => M.labour_eq_integral z₀ μ₀ _ h⟩

end KSModel

end KrusellSmith

end LeanEconomics
