/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.CRRA
import LeanEconomics.DynamicProgramming.ExtendedStochastic
import LeanEconomics.Topology.IccCorrespondence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The income fluctuation problem with BOUNDED utility

`crra_pinch` showed that `IncomeFluctuation` admits CRRA only for `γ ≥ 1`, because it requires
utility to fall to `-∞` at zero consumption, and that Light's uniqueness condition needs `γ ≤ 1`.
The intersection is log alone. This structure removes the obstruction from the other side, so
that CES with `γ < 1` — where utility is bounded below — becomes expressible.

## Why a new structure rather than a weaker axiom

`tendsto_atBot_u` is not decoration. It is what makes `extendBot u` CONTINUOUS into `EReal`, and
continuity of the reward is what Berge's maximum theorem runs on. With `u (0⁺)` finite,
`extendBot u` jumps from a finite limit down to `⊥` at zero consumption: not upper semicontinuous,
so the maximum need not be attained. Concretely, the objective would approach its supremum as
saving rises to the maximum, and drop to `-∞` exactly there.

The fix is not to weaken the axiom but to change the reward. With `γ < 1` the utility extends
continuously to `[0, ∞)`, so the reward can be `u` itself, real-valued, with consumption clamped
into `[0, maxConsumption]`. That is `rewardFn` below, and `continuous_rewardFn` needs nothing but
continuity of `u` on `Ici 0`.

## What changes and what does not

Every field except the three conditions on `u` is identical, and those move from `Ioi 0` to
`Ici 0`: `u` is now required to behave AT zero rather than only near it. The reward is real, so
`reward_eq_coe` holds with no positivity side condition, which is a simplification rather than a
complication — the `-∞` case that every downstream proof had to dispatch simply is not there.

What is NOT done here is transporting the downstream theory. `Feller`, `Stationary`,
`Uniqueness`, `Aiyagari` and the rest are all stated for `IncomeFluctuation`, and Lean has no
structural subtyping, so they do not automatically apply. Either they are restated, or the two
structures are refactored over a common interface. This file builds the foundation and shows
CES with `γ < 1` sits on it; that choice is separate and larger.
-/

open scoped NNReal
open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

/-- The income fluctuation problem with period utility BOUNDED BELOW, so that CES with `γ < 1`
is admissible. Every field is as in `IncomeFluctuation` except that the three conditions on `u`
are imposed on `Ici 0` rather than `Ioi 0`, and utility is not required to diverge. -/
structure BoundedIncomeFluctuation (Z : Type*) [Fintype Z] [Nonempty Z] [TopologicalSpace Z]
    [DiscreteTopology Z] (assetCap : ℝ) where
  /-- Income in each state. -/
  income : Z → ℝ
  /-- The Markov transition matrix on income states. -/
  transitionMatrix : Z → Z → ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  /-- Period utility, required to behave on `[0, ∞)`. -/
  u : ℝ → ℝ
  /-- A lower bound on income. -/
  minIncome : ℝ
  /-- An upper bound on income. -/
  maxIncome : ℝ
  minIncome_pos : 0 < minIncome
  minIncome_le : ∀ z, minIncome ≤ income z
  le_maxIncome : ∀ z, income z ≤ maxIncome
  transitionMatrix_nonneg : ∀ z z', 0 ≤ transitionMatrix z z'
  transitionMatrix_sum : ∀ z, ∑ z', transitionMatrix z z' = 1
  interest_gt_neg_one : 0 < 1 + interest
  assetCap_nonneg : 0 ≤ assetCap
  discount_lt_one : discount < 1
  continuousOn_u : ContinuousOn u (Ici 0)
  monotoneOn_u : MonotoneOn u (Ici 0)
  strictConcaveOn_u : StrictConcaveOn ℝ (Ici 0) u

namespace BoundedIncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ}
variable (P : BoundedIncomeFluctuation Z assetCap)

/-- Cash on hand, with assets read as nonnegative. -/
noncomputable def resources (s : ℝ × Z) : ℝ := P.income s.2 + (1 + P.interest) * max 0 s.1

/-- The largest consumption the capped problem allows. -/
noncomputable def maxConsumption : ℝ := P.maxIncome + (1 + P.interest) * assetCap

/-- The largest asset holding that can be carried forward. -/
noncomputable def maxSaving (s : ℝ × Z) : ℝ := max 0 (min assetCap (P.resources s))

/-- Consumption on the budget line. -/
noncomputable def consumption (s : ℝ × Z) (a' : ℝ) : ℝ := P.resources s - a'

theorem minIncome_le_resources (s : ℝ × Z) : P.minIncome ≤ P.resources s := by
  have : 0 ≤ (1 + P.interest) * max 0 s.1 :=
    mul_nonneg P.interest_gt_neg_one.le (le_max_left _ _)
  have := P.minIncome_le s.2
  simp only [resources]; linarith

theorem resources_pos (s : ℝ × Z) : 0 < P.resources s :=
  lt_of_lt_of_le P.minIncome_pos (P.minIncome_le_resources s)

theorem minIncome_le_maxIncome : P.minIncome ≤ P.maxIncome :=
  (P.minIncome_le Classical.ofNonempty).trans (P.le_maxIncome _)

theorem minIncome_le_maxConsumption : P.minIncome ≤ P.maxConsumption := by
  have : 0 ≤ (1 + P.interest) * assetCap :=
    mul_nonneg P.interest_gt_neg_one.le P.assetCap_nonneg
  simp only [maxConsumption]; linarith [P.minIncome_le_maxIncome]

theorem maxConsumption_pos : 0 < P.maxConsumption :=
  lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxConsumption

theorem continuous_resources : Continuous P.resources :=
  (continuous_of_discreteTopology.comp continuous_snd).add
    (continuous_const.mul (continuous_const.max continuous_fst))

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max (continuous_const.min P.continuous_resources)

theorem maxSaving_le_resources (s : ℝ × Z) : P.maxSaving s ≤ P.resources s :=
  max_le (P.resources_pos s).le (min_le_right _ _)

theorem consumption_le_maxConsumption {s : ℝ × Z} {a' : ℝ} (hs : s.1 ∈ Icc 0 assetCap)
    (ha' : 0 ≤ a') : P.consumption s a' ≤ P.maxConsumption := by
  have hmax : max 0 s.1 = s.1 := max_eq_right hs.1
  have : (1 + P.interest) * s.1 ≤ (1 + P.interest) * assetCap :=
    mul_le_mul_of_nonneg_left hs.2 P.interest_gt_neg_one.le
  simp only [consumption, resources, maxConsumption, hmax]
  linarith [P.le_maxIncome s.2]

/-! ### The reward: real-valued, and continuous without any Inada condition -/

/-- Consumption clamped into `[0, maxConsumption]`, where `u` is required to behave. -/
noncomputable def clampedConsumption (p : (ℝ × Z) × ℝ) : ℝ :=
  min P.maxConsumption (max 0 (P.consumption p.1 p.2))

theorem clampedConsumption_nonneg (p : (ℝ × Z) × ℝ) : 0 ≤ P.clampedConsumption p :=
  le_min P.maxConsumption_pos.le (le_max_left _ _)

theorem clampedConsumption_le (p : (ℝ × Z) × ℝ) :
    P.clampedConsumption p ≤ P.maxConsumption := min_le_left _ _

theorem continuous_clampedConsumption : Continuous P.clampedConsumption := by
  refine continuous_const.min (continuous_const.max ?_)
  exact (P.continuous_resources.comp continuous_fst).sub continuous_snd

/-- The period reward. Real-valued, because utility is finite at zero consumption. -/
noncomputable def rewardFn (p : (ℝ × Z) × ℝ) : ℝ := P.u (P.clampedConsumption p)

theorem continuous_rewardFn : Continuous P.rewardFn :=
  P.continuousOn_u.comp_continuous P.continuous_clampedConsumption
    fun p => mem_Ici.mpr (P.clampedConsumption_nonneg p)

/-- The problem as a stochastic dynamic program. The reward happens to be finite everywhere, so
the extended-real machinery is used but never exercised. -/
noncomputable def toExtended : ExtendedStochasticProgram (ℝ × Z) ℝ Z where
  feasible s := Icc 0 (P.maxSaving s)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  reward := ⟨fun p => ((P.rewardFn p : ℝ) : EReal),
    continuous_coe_real_ereal.comp P.continuous_rewardFn⟩
  rewardMax := P.u P.maxConsumption
  reward_le := by
    intro s a _
    simp only [ContinuousMap.coe_mk, rewardFn, EReal.coe_le_coe_iff]
    exact P.monotoneOn_u (mem_Ici.mpr (P.clampedConsumption_nonneg _))
      (mem_Ici.mpr P.maxConsumption_pos.le) (P.clampedConsumption_le _)
  select := ⟨fun _ => 0, continuous_const⟩
  select_mem := fun _ => ⟨le_rfl, le_max_left _ _⟩
  rewardMin := P.u 0
  le_reward_select := by
    intro s
    simp only [ContinuousMap.coe_mk, rewardFn, EReal.coe_le_coe_iff]
    exact P.monotoneOn_u (mem_Ici.mpr le_rfl)
      (mem_Ici.mpr (P.clampedConsumption_nonneg _)) (P.clampedConsumption_nonneg _)
  transition z' := ⟨fun p => (p.2, z'), continuous_snd.prodMk continuous_const⟩
  prob z' := ⟨fun p => P.transitionMatrix p.1.2 z',
    (continuous_of_discreteTopology (f := fun z => P.transitionMatrix z z')).comp
      (continuous_snd.comp continuous_fst)⟩
  prob_nonneg _ _ := P.transitionMatrix_nonneg _ _
  prob_sum p := P.transitionMatrix_sum _
  discount := P.discount
  discount_lt_one := P.discount_lt_one

@[simp]
theorem feasible_eq (s : ℝ × Z) : P.toExtended.feasible s = Icc 0 (P.maxSaving s) := rfl

theorem consumption_nonneg {s : ℝ × Z} {a : ℝ} (ha : a ∈ P.toExtended.feasible s) :
    0 ≤ P.consumption s a := by
  simp only [consumption]
  linarith [le_trans ha.2 (P.maxSaving_le_resources s)]

/-- **The reward is the utility of consumption**, with no positivity side condition: the `-∞`
case that the unbounded structure has to dispatch everywhere simply does not arise. -/
theorem reward_eq_coe {s : ℝ × Z} {a : ℝ} (hs : s.1 ∈ Icc 0 assetCap)
    (ha : a ∈ P.toExtended.feasible s) :
    P.toExtended.reward (s, a) = ((P.u (P.consumption s a) : ℝ) : EReal) := by
  have hcl : P.clampedConsumption (s, a) = P.consumption s a := by
    simp only [clampedConsumption]
    rw [max_eq_right (P.consumption_nonneg ha),
      min_eq_right (P.consumption_le_maxConsumption hs ha.1)]
  simp only [toExtended, ContinuousMap.coe_mk, rewardFn, hcl]

/-- **An optimal action exists**, from the general machinery: the reward is continuous. -/
theorem exists_optimal_action (s : ℝ × Z) :
    ∃ a ∈ P.toExtended.feasible s, P.toExtended.objectiveE P.toExtended.valueFunction s a
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction s : ℝ) : EReal) :=
  P.toExtended.exists_optimal_action _ s

/-- The optimal saving choice. -/
noncomputable def policy (s : ℝ × Z) : ℝ := Classical.choose (P.exists_optimal_action s)

theorem policy_mem (s : ℝ × Z) : P.policy s ∈ P.toExtended.feasible s :=
  (Classical.choose_spec (P.exists_optimal_action s)).1

theorem policy_optimal (s : ℝ × Z) :
    P.toExtended.objectiveE P.toExtended.valueFunction s (P.policy s)
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction s : ℝ) : EReal) :=
  (Classical.choose_spec (P.exists_optimal_action s)).2

end BoundedIncomeFluctuation

/-! ### CES with `γ < 1` satisfies the axioms -/

theorem continuousOn_crraUtility_Ici {γ : ℝ} (_hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ContinuousOn (crraUtility γ) (Ici 0) := by
  have he : crraUtility γ = fun c : ℝ => c ^ (1 - γ) / (1 - γ) :=
    funext (crraUtility_of_ne (by linarith))
  rw [he]
  refine ContinuousOn.div_const (fun x _ => ?_) _
  exact (Real.continuousAt_rpow_const x (1 - γ) (Or.inr (by linarith))).continuousWithinAt

theorem monotoneOn_crraUtility_Ici {γ : ℝ} (_hγ0 : 0 < γ) (hγ1 : γ < 1) :
    MonotoneOn (crraUtility γ) (Ici 0) := by
  intro x hx y hy hxy
  rw [crraUtility_of_ne (by linarith), crraUtility_of_ne (by linarith)]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hx hxy (by linarith)) (by linarith)

theorem strictConcaveOn_crraUtility_Ici {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictConcaveOn ℝ (Ici 0) (crraUtility γ) := by
  have hpos : (0 : ℝ) < 1 - γ := by linarith
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have key := (Real.strictConcaveOn_rpow hpos (by linarith)).2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at key ⊢
  simp only [crraUtility_of_ne (show γ ≠ 1 by linarith)]
  rw [show a * (x ^ (1 - γ) / (1 - γ)) + b * (y ^ (1 - γ) / (1 - γ))
      = (a * x ^ (1 - γ) + b * y ^ (1 - γ)) / (1 - γ) from by ring]
  gcongr

/-! ### A CES economy with `γ = 1/2`

The point of the exercise, made concrete. `crraUtility (1/2) c = 2 √c`, which is finite at `c = 0`
and therefore inadmissible in `IncomeFluctuation` — `not_tendsto_atBot_crraUtility` is exactly the
obstruction. Here it is a legitimate primitive.
-/

/-- A household with CES utility at `γ = 1/2`: square-root utility, bounded below. The same
parameters as `dispersed`, so the two differ only in the curvature of `u`. -/
noncomputable def sqrtCES : BoundedIncomeFluctuation (Fin 2) 1 where
  income z := if z = 0 then 1 / 100 else 1
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 8
  u := crraUtility (1 / 2)
  minIncome := 1 / 100
  maxIncome := 1
  minIncome_pos := by norm_num
  minIncome_le z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  assetCap_nonneg := by norm_num
  discount_lt_one := by norm_num
  continuousOn_u := continuousOn_crraUtility_Ici (by norm_num) (by norm_num)
  monotoneOn_u := monotoneOn_crraUtility_Ici (by norm_num) (by norm_num)
  strictConcaveOn_u := strictConcaveOn_crraUtility_Ici (by norm_num) (by norm_num)

@[simp] theorem sqrtCES_u : sqrtCES.u = crraUtility (1 / 2) := rfl

/-- Utility at zero consumption is finite — `crraUtility (1/2) 0 = 0`. This is the fact that
`IncomeFluctuation` forbids. -/
theorem sqrtCES_u_zero : sqrtCES.u 0 = 0 := by
  rw [sqrtCES_u, crraUtility_of_ne (by norm_num)]
  rw [Real.zero_rpow (by norm_num)]
  norm_num

/-- The same utility function CANNOT be a primitive of `IncomeFluctuation`: it does not diverge
at zero consumption. Contrast `crra_pinch`, which is what confined that structure to log. -/
theorem sqrtCES_not_tendsto_atBot :
    ¬ Tendsto (crraUtility (1 / 2)) (𝓝[>] (0 : ℝ)) atBot :=
  not_tendsto_atBot_crraUtility (by norm_num)

/-- And the problem is still solvable: the reward is continuous and an optimum is attained at
every state, with a real — not merely extended-real — value. -/
theorem sqrtCES_exists_optimal (s : ℝ × Fin 2) :
    ∃ a ∈ sqrtCES.toExtended.feasible s,
      sqrtCES.toExtended.objectiveE sqrtCES.toExtended.valueFunction s a
        = ((sqrtCES.toExtended.bellmanFn sqrtCES.toExtended.valueFunction s : ℝ) : EReal) :=
  sqrtCES.exists_optimal_action s


end LeanEconomics
