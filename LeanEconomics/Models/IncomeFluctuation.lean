/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.Stochastic
import LeanEconomics.Topology.IccCorrespondence
import LeanEconomics.Models.ConsumptionSavingsUnbounded

/-!
# The income fluctuation problem

The canonical incomplete-markets household problem. Income follows a finite Markov chain,
assets earn interest, borrowing is ruled out, and the agent chooses savings:

  `a' + c = y z + (1 + r) a`,   `c ≥ 0`,   `0 ≤ a'`,   `z' ~ P z ·`

maximising `E ∑ βᵗ u cₜ`. The state is the pair `(a, z)` of assets and income state, and
the value function solves

  `V (a, z) = max { u c + β * ∑ z', P z z' * V (a', z') }`.

## Structure of the file

The deterministic model in `LeanEconomics.Models.ConsumptionSavingsUnbounded` carries over
almost unchanged, which is the point: only the operator differed, and that was dealt with
in `LeanEconomics.DynamicProgramming.Stochastic`.

The state space is `ℝ × Z` with `Z` finite and discrete. Discreteness is what makes every
function of the income state continuous, so the budget correspondence is continuous in the
pair and `LeanEconomics.upperHemicontinuous_Icc` applies as before.

Period utility is again floored and consumption clamped, and again both are proved
inactive at an optimum, so `exists_optimal_saving` carries honest `u` of actual
consumption. The bounds behind that argument need one change: in the deterministic model
the agent who saves nothing lands in a single known state, while here the successor is
random, so the lower bound is taken at an income state minimising the value at zero assets.

`minIncome` and `maxIncome` are supplied as fields with bounds rather than computed as
extrema over `Z`, which keeps the statement of `floor_lt` readable.
-/

open scoped NNReal
open Set BoundedContinuousFunction

namespace LeanEconomics

/-- The income fluctuation problem: parameters of a household facing Markov income. -/
structure IncomeFluctuation (Z : Type*) [Fintype Z] [Nonempty Z] [TopologicalSpace Z]
    [DiscreteTopology Z] where
  /-- Income in each state. -/
  income : Z → ℝ
  /-- The Markov transition matrix on income states. -/
  transitionMatrix : Z → Z → ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The upper bound imposed on asset holdings. -/
  assetCap : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  /-- Period utility, required to behave only on positive consumption. -/
  u : ℝ → ℝ
  /-- The constant that replaces `u` at very low consumption. -/
  floor : ℝ
  /-- A consumption level at which `u` has already fallen below `floor`. -/
  cFloor : ℝ
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
  continuousOn_u : ContinuousOn u (Ioi 0)
  monotoneOn_u : MonotoneOn u (Ioi 0)
  cFloor_pos : 0 < cFloor
  cFloor_le_minIncome : cFloor ≤ minIncome
  u_cFloor_le_floor : u cFloor ≤ floor
  /-- The floor is low enough that an optimising agent never reaches it. -/
  floor_lt : floor * (1 - discount)
    < u minIncome - discount * u (maxIncome + (1 + interest) * assetCap)

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable (P : IncomeFluctuation Z)

/-- Cash on hand in state `(a, z)`. -/
noncomputable def resources (s : ℝ × Z) : ℝ := P.income s.2 + (1 + P.interest) * s.1

/-- Consumption implied by the budget constraint. -/
noncomputable def consumption (s : ℝ × Z) (a' : ℝ) : ℝ := P.resources s - a'

/-- The largest asset holding that can be carried forward. -/
noncomputable def maxSaving (s : ℝ × Z) : ℝ := max 0 (min P.assetCap (P.resources s))

/-- The largest consumption attainable from the capped state space. -/
noncomputable def maxConsumption : ℝ := P.maxIncome + (1 + P.interest) * P.assetCap

/-- Consumption clamped into `[cFloor, maxConsumption]`. -/
noncomputable def clampC (c : ℝ) : ℝ := min P.maxConsumption (max P.cFloor c)

/-- The reward: utility of clamped consumption, floored. -/
noncomputable def rewardFn (p : (ℝ × Z) × ℝ) : ℝ :=
  max P.floor (P.u (P.clampC (P.consumption p.1 p.2)))

theorem discount_lt_one' : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one

theorem one_sub_discount_pos : 0 < 1 - (P.discount : ℝ) := by linarith [P.discount_lt_one']

theorem floor_lt' : P.floor * (1 - (P.discount : ℝ))
    < P.u P.minIncome - P.discount * P.u P.maxConsumption := by
  simpa [maxConsumption] using P.floor_lt

theorem minIncome_le_maxIncome : P.minIncome ≤ P.maxIncome :=
  (P.minIncome_le Classical.ofNonempty).trans (P.le_maxIncome _)

theorem minIncome_le_maxConsumption : P.minIncome ≤ P.maxConsumption := by
  have : 0 ≤ (1 + P.interest) * P.assetCap :=
    mul_nonneg P.interest_gt_neg_one.le P.assetCap_nonneg
  simp only [maxConsumption]; linarith [P.minIncome_le_maxIncome]

theorem minIncome_mem : P.minIncome ∈ Ioi (0 : ℝ) := P.minIncome_pos

theorem maxConsumption_mem : P.maxConsumption ∈ Ioi (0 : ℝ) :=
  lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxConsumption

theorem cFloor_le_maxConsumption : P.cFloor ≤ P.maxConsumption :=
  P.cFloor_le_minIncome.trans P.minIncome_le_maxConsumption

theorem clampC_mem_Icc (c : ℝ) : P.clampC c ∈ Icc P.cFloor P.maxConsumption :=
  ⟨le_min P.cFloor_le_maxConsumption (le_max_left _ _), min_le_left _ _⟩

theorem clampC_mem (c : ℝ) : P.clampC c ∈ Ioi (0 : ℝ) :=
  lt_of_lt_of_le P.cFloor_pos (P.clampC_mem_Icc c).1

theorem u_minIncome_le_u_maxConsumption : P.u P.minIncome ≤ P.u P.maxConsumption :=
  P.monotoneOn_u P.minIncome_mem P.maxConsumption_mem P.minIncome_le_maxConsumption

theorem floor_lt_u_minIncome : P.floor < P.u P.minIncome := by
  have h := P.floor_lt'
  have hβ := P.one_sub_discount_pos
  have hprod : (P.discount : ℝ) * P.u P.minIncome ≤ P.discount * P.u P.maxConsumption :=
    mul_le_mul_of_nonneg_left P.u_minIncome_le_u_maxConsumption P.discount.coe_nonneg
  have key : P.floor * (1 - (P.discount : ℝ)) < P.u P.minIncome * (1 - P.discount) := by
    nlinarith
  exact lt_of_mul_lt_mul_right key hβ.le

theorem floor_le_u_maxConsumption : P.floor ≤ P.u P.maxConsumption :=
  (P.floor_lt_u_minIncome.trans_le P.u_minIncome_le_u_maxConsumption).le

theorem u_clampC_le (c : ℝ) : P.u (P.clampC c) ≤ P.u P.maxConsumption :=
  P.monotoneOn_u (P.clampC_mem c) P.maxConsumption_mem (P.clampC_mem_Icc c).2

theorem rewardFn_le (p : (ℝ × Z) × ℝ) : P.rewardFn p ≤ P.u P.maxConsumption :=
  max_le P.floor_le_u_maxConsumption (P.u_clampC_le _)

theorem floor_le_rewardFn (p : (ℝ × Z) × ℝ) : P.floor ≤ P.rewardFn p := le_max_left _ _

/-- Every function of the income state is continuous, because `Z` is discrete. -/
theorem continuous_resources : Continuous P.resources :=
  (continuous_of_discreteTopology.comp continuous_snd).add
    (continuous_const.mul continuous_fst)

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max (continuous_const.min P.continuous_resources)

theorem continuous_rewardFn : Continuous P.rewardFn := by
  have hc : Continuous fun p : (ℝ × Z) × ℝ => P.clampC (P.consumption p.1 p.2) := by
    have : Continuous fun p : (ℝ × Z) × ℝ => P.consumption p.1 p.2 :=
      (P.continuous_resources.comp continuous_fst).sub continuous_snd
    exact continuous_const.min (continuous_const.max this)
  exact continuous_const.max (P.continuousOn_u.comp_continuous hc fun p => P.clampC_mem _)

theorem abs_rewardFn_le (p : (ℝ × Z) × ℝ) :
    |P.rewardFn p| ≤ max |P.floor| |P.u P.maxConsumption| := by
  rw [abs_le]
  refine ⟨?_, (P.rewardFn_le p).trans ((le_abs_self _).trans (le_max_right _ _))⟩
  have h1 : -|P.floor| ≤ P.floor := neg_abs_le _
  have h2 : -(max |P.floor| |P.u P.maxConsumption|) ≤ -|P.floor| := neg_le_neg (le_max_left _ _)
  linarith [P.floor_le_rewardFn p]

/-- The income fluctuation problem as a stochastic dynamic program. -/
noncomputable def toStochastic : StochasticDynamicProgram (ℝ × Z) ℝ Z where
  feasible s := Icc 0 (P.maxSaving s)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  reward := BoundedContinuousFunction.ofNormedAddCommGroup P.rewardFn P.continuous_rewardFn
    (max |P.floor| |P.u P.maxConsumption|) fun p => by
      simpa [Real.norm_eq_abs] using P.abs_rewardFn_le p
  transition z' := ⟨fun p => (p.2, z'), continuous_snd.prodMk continuous_const⟩
  prob z' := ⟨fun p => P.transitionMatrix p.1.2 z',
    (continuous_of_discreteTopology (f := fun z => P.transitionMatrix z z')).comp
      (continuous_snd.comp continuous_fst)⟩
  prob_nonneg z' p := P.transitionMatrix_nonneg _ _
  prob_sum p := P.transitionMatrix_sum _
  discount := P.discount
  discount_lt_one := P.discount_lt_one

@[simp]
theorem feasible_eq (s : ℝ × Z) : P.toStochastic.feasible s = Icc 0 (P.maxSaving s) := rfl

@[simp]
theorem objective_eq (v : (ℝ × Z) →ᵇ ℝ) (s : ℝ × Z) (a' : ℝ) :
    P.toStochastic.objective v s a'
      = P.rewardFn (s, a')
        + P.discount * ∑ z', P.transitionMatrix s.2 z' * v (a', z') := rfl

theorem zero_mem_feasible (s : ℝ × Z) : (0 : ℝ) ∈ P.toStochastic.feasible s :=
  ⟨le_refl 0, le_max_left _ _⟩

theorem valueFunction_eq_bellmanFn (s : ℝ × Z) :
    P.toStochastic.valueFunction s
      = P.toStochastic.bellmanFn P.toStochastic.valueFunction s := by
  conv_lhs => rw [← P.toStochastic.bellman_valueFunction]
  rfl

/-- **Upper bound on the value.** -/
theorem valueFunction_le (s : ℝ × Z) :
    P.toStochastic.valueFunction s ≤ P.u P.maxConsumption / (1 - P.discount) := by
  set V := P.toStochastic.valueFunction with hV
  have hbdd : BddAbove (Set.range fun t => V t) := by
    refine ⟨‖V‖, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (abs_le.mp (by simpa [Real.norm_eq_abs] using V.norm_coe_le_norm t)).2
  have hVM : ∀ t, V t ≤ ⨆ t, V t := fun t => le_ciSup hbdd t
  have hstep : ∀ t, V t ≤ P.u P.maxConsumption + P.discount * ⨆ t, V t := by
    intro t
    rw [hV, P.valueFunction_eq_bellmanFn t]
    refine P.toStochastic.bellmanFn_le _ fun a' _ => ?_
    rw [P.objective_eq]
    have hsum : ∑ z', P.transitionMatrix t.2 z' * V (a', z') ≤ ⨆ t, V t := by
      calc ∑ z', P.transitionMatrix t.2 z' * V (a', z')
          ≤ ∑ z', P.transitionMatrix t.2 z' * ⨆ t, V t := by
            refine Finset.sum_le_sum fun z' _ => ?_
            exact mul_le_mul_of_nonneg_left (hVM _) (P.transitionMatrix_nonneg _ _)
        _ = ⨆ t, V t := by rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]
    have := P.rewardFn_le (t, a')
    have hβ := P.discount.coe_nonneg
    nlinarith
  have hM : (⨆ t, V t) ≤ P.u P.maxConsumption + P.discount * ⨆ t, V t := ciSup_le hstep
  have hβ := P.one_sub_discount_pos
  have : (⨆ t, V t) ≤ P.u P.maxConsumption / (1 - P.discount) := by
    rw [le_div_iff₀ hβ]; nlinarith
  exact (hVM s).trans this

/-- Saving nothing always leaves consumption at least `minIncome`. -/
theorem u_minIncome_le_rewardFn {s : ℝ × Z} (hs : 0 ≤ s.1) :
    P.u P.minIncome ≤ P.rewardFn (s, 0) := by
  have hres : P.minIncome ≤ P.resources s := by
    have : 0 ≤ (1 + P.interest) * s.1 := mul_nonneg P.interest_gt_neg_one.le hs
    simp only [resources]; linarith [P.minIncome_le s.2]
  have hcl : P.minIncome ≤ P.clampC (P.consumption s 0) := by
    simp only [clampC, consumption, sub_zero]
    exact le_min P.minIncome_le_maxConsumption (le_max_of_le_right hres)
  exact le_trans (P.monotoneOn_u P.minIncome_mem (P.clampC_mem _) hcl) (le_max_right _ _)

/-- **Lower bound on the value.** Unlike the deterministic case the successor state is
random, so the bound is anchored at an income state minimising the value at zero assets. -/
theorem le_valueFunction {s : ℝ × Z} (hs : 0 ≤ s.1) :
    P.u P.minIncome / (1 - P.discount) ≤ P.toStochastic.valueFunction s := by
  set V := P.toStochastic.valueFunction with hV
  obtain ⟨z₀, -, hz₀⟩ :=
    Finset.exists_min_image Finset.univ (fun z => V (0, z)) Finset.univ_nonempty
  have hstep : ∀ t : ℝ × Z, 0 ≤ t.1 → P.u P.minIncome + P.discount * V (0, z₀) ≤ V t := by
    intro t ht
    rw [hV, P.valueFunction_eq_bellmanFn t]
    refine le_trans ?_ (P.toStochastic.le_bellmanFn _ (P.zero_mem_feasible t))
    rw [P.objective_eq]
    have hsum : V (0, z₀) ≤ ∑ z', P.transitionMatrix t.2 z' * V (0, z') := by
      calc V (0, z₀) = ∑ z', P.transitionMatrix t.2 z' * V (0, z₀) := by
            rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]
        _ ≤ _ := by
            refine Finset.sum_le_sum fun z' _ => ?_
            exact mul_le_mul_of_nonneg_left (hz₀ z' (Finset.mem_univ _))
              (P.transitionMatrix_nonneg _ _)
    have := P.u_minIncome_le_rewardFn ht
    have hβ := P.discount.coe_nonneg
    nlinarith
  have h0 := hstep (0, z₀) le_rfl
  have hβ := P.one_sub_discount_pos
  have hV0 : P.u P.minIncome / (1 - P.discount) ≤ V (0, z₀) := by
    rw [div_le_iff₀ hβ]; nlinarith
  refine le_trans ?_ (hstep s hs)
  have hβ' := P.discount.coe_nonneg
  rw [div_le_iff₀ hβ] at hV0 ⊢
  nlinarith

/-- **The floor never binds at an optimal choice.** -/
theorem floor_lt_rewardFn_optimal {s : ℝ × Z} {a' : ℝ} (hs : 0 ≤ s.1)
    (heq : P.toStochastic.valueFunction s
      = P.rewardFn (s, a')
        + P.discount * ∑ z', P.transitionMatrix s.2 z' * P.toStochastic.valueFunction (a', z')) :
    P.floor < P.rewardFn (s, a') := by
  set V := P.toStochastic.valueFunction with hV
  have hlo := P.le_valueFunction hs
  have hβ := P.discount.coe_nonneg
  have hβ1 := P.one_sub_discount_pos
  have hfl := P.floor_lt'
  -- the expected continuation is bounded above by the bound on `V`
  have hsum : ∑ z', P.transitionMatrix s.2 z' * V (a', z')
      ≤ P.u P.maxConsumption / (1 - P.discount) := by
    calc ∑ z', P.transitionMatrix s.2 z' * V (a', z')
        ≤ ∑ z', P.transitionMatrix s.2 z' * (P.u P.maxConsumption / (1 - P.discount)) := by
          refine Finset.sum_le_sum fun z' _ => ?_
          exact mul_le_mul_of_nonneg_left (P.valueFunction_le _) (P.transitionMatrix_nonneg _ _)
      _ = _ := by rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]
  rw [heq] at hlo
  rw [div_le_iff₀ hβ1] at hlo
  rw [le_div_iff₀ hβ1] at hsum
  have hprod : (P.discount : ℝ)
        * ((∑ z', P.transitionMatrix s.2 z' * V (a', z')) * (1 - P.discount))
      ≤ P.discount * P.u P.maxConsumption := mul_le_mul_of_nonneg_left hsum hβ
  have key : P.floor * (1 - (P.discount : ℝ))
      < P.rewardFn (s, a') * (1 - P.discount) := by nlinarith
  exact lt_of_mul_lt_mul_right key hβ1.le

theorem consumption_le_maxConsumption {s : ℝ × Z} {a' : ℝ} (hs : s.1 ≤ P.assetCap)
    (ha' : 0 ≤ a') : P.consumption s a' ≤ P.maxConsumption := by
  have : (1 + P.interest) * s.1 ≤ (1 + P.interest) * P.assetCap :=
    mul_le_mul_of_nonneg_left hs P.interest_gt_neg_one.le
  simp only [consumption, maxConsumption, resources]
  linarith [P.le_maxIncome s.2]

theorem cFloor_le_consumption_optimal {s : ℝ × Z} {a' : ℝ}
    (h : P.floor < P.u (P.clampC (P.consumption s a'))) : P.cFloor ≤ P.consumption s a' := by
  by_contra hlt
  push Not at hlt
  rw [show P.clampC (P.consumption s a') = P.cFloor by
    simp only [clampC, max_eq_left hlt.le, min_eq_right P.cFloor_le_maxConsumption]] at h
  exact absurd h (not_lt.mpr P.u_cFloor_le_floor)

/-- **The stochastic Bellman equation of the income fluctuation problem**, with honest
period utility of actual consumption: no floor and no clamp. -/
theorem exists_optimal_saving {s : ℝ × Z} (hs : s.1 ∈ Icc 0 P.assetCap) :
    ∃ a' ∈ Icc 0 (P.maxSaving s),
      P.toStochastic.valueFunction s
        = P.u (P.consumption s a')
          + P.discount * ∑ z', P.transitionMatrix s.2 z'
              * P.toStochastic.valueFunction (a', z') := by
  obtain ⟨a', ha', heq⟩ := P.toStochastic.exists_optimal_policy s
  have heq' : P.toStochastic.valueFunction s
      = P.rewardFn (s, a')
        + P.discount * ∑ z', P.transitionMatrix s.2 z'
            * P.toStochastic.valueFunction (a', z') := heq
  refine ⟨a', ha', ?_⟩
  have hlt : P.floor < P.u (P.clampC (P.consumption s a')) := by
    have h := P.floor_lt_rewardFn_optimal hs.1 heq'
    simp only [rewardFn] at h
    rcases lt_max_iff.mp h with h' | h'
    · exact absurd h' (lt_irrefl _)
    · exact h'
  have hclamp : P.clampC (P.consumption s a') = P.consumption s a' := by
    simp only [clampC]
    rw [max_eq_right (P.cFloor_le_consumption_optimal hlt),
      min_eq_right (P.consumption_le_maxConsumption hs.2 ha'.1)]
  rw [heq']
  simp only [rewardFn]
  rw [max_eq_right hlt.le, hclamp]

/-- A two-state calibration: income `1/2` or `3/2`, drawn i.i.d. with equal probability,
interest 5%, assets capped at 10, `β = 0.96`, and CRRA utility with `σ = 2`. Recorded to
witness that the hypotheses are satisfiable -- in particular that a genuinely stochastic
instance exists, which the theorems above would otherwise say nothing about. -/
noncomputable def calibrated : IncomeFluctuation (Fin 2) where
  income z := if z = 0 then 1 / 2 else 3 / 2
  transitionMatrix _ _ := 1 / 2
  interest := 1 / 20
  assetCap := 10
  discount := 24 / 25
  u := fun c => -c⁻¹
  floor := -100
  cFloor := 1 / 100
  minIncome := 1 / 2
  maxIncome := 3 / 2
  minIncome_pos := by norm_num
  minIncome_le z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  assetCap_nonneg := by norm_num
  discount_lt_one := by norm_num
  continuousOn_u := (continuousOn_id.inv₀ fun x hx => ne_of_gt hx).neg
  monotoneOn_u := by
    intro x hx y _ hxy
    have : (0 : ℝ) < x := hx
    simp only [neg_le_neg_iff]
    gcongr
  cFloor_pos := by norm_num
  cFloor_le_minIncome := by norm_num
  u_cFloor_le_floor := by norm_num
  floor_lt := by push_cast; norm_num

end IncomeFluctuation

end LeanEconomics
