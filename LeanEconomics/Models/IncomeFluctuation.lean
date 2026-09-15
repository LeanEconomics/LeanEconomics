/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.DynamicProgramming.ExtendedStochastic
import LeanEconomics.Topology.IccCorrespondence
import LeanEconomics.Models.ConsumptionSavingsUnbounded

/-!
# The income fluctuation problem

The canonical incomplete-markets household: income follows a finite Markov chain, assets
earn interest, borrowing is ruled out, and the household chooses savings. The state is the
pair `(a, z)` of assets and income state, and

  `V (a, z) = max { u c + β * ∑ z', P z z' * V (a', z') }`.

Period utility may fall to `-∞` at zero consumption, so this covers log and CRRA with
`σ ≥ 1`.

## Retrofitted onto extended-real rewards

This file used a floor, with the same apparatus as the deterministic models: `floor`,
`cFloor`, and a chain of results establishing that the floor never binds. All of it is
gone. The reward is `-∞` where consumption vanishes, and positive consumption at the
optimum follows from the value function being real rather than from an argument.

The stochastic case needed `LeanEconomics.DynamicProgramming.ExtendedStochastic`, since the
continuation here is an expectation over shocks rather than `v` at a single point. That
turned out to be routine: the expectation is a sum of reals, so the objective is again an
extended real plus a finite coercion, and the reward's `-∞` never meets the expectation's
arithmetic.

## Unchanged

Discreteness of the income state is still what makes every function of `z` continuous, so
the budget correspondence is continuous in the pair. Consumption is still clamped above and
assets still capped -- the ordinary boundedness requirement, unrelated to the floor. Cash on
hand is computed from `max 0 a`, as in the deterministic retrofits, so that the value stays
finite at every state.
-/

open scoped NNReal
open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

/-- The income fluctuation problem, with period utility unbounded below. -/
structure IncomeFluctuation (Z : Type*) [Fintype Z] [Nonempty Z] [TopologicalSpace Z]
    [DiscreteTopology Z] (assetCap : ℝ) where
  /-- Income in each state. -/
  income : Z → ℝ
  /-- The Markov transition matrix on income states. -/
  transitionMatrix : Z → Z → ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  /-- Period utility, required to behave only on positive consumption. -/
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
  continuousOn_u : ContinuousOn u (Ioi 0)
  monotoneOn_u : MonotoneOn u (Ioi 0)
  /-- Utility falls to `-∞` as consumption vanishes. -/
  tendsto_atBot_u : Tendsto u (𝓝[>] 0) atBot
  /-- Diminishing marginal utility, which makes the optimal policy unique. -/
  strictConcaveOn_u : StrictConcaveOn ℝ (Ioi 0) u

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ}
variable (P : IncomeFluctuation Z assetCap)

/-- Cash on hand, with assets read as nonnegative. -/
noncomputable def resources (s : ℝ × Z) : ℝ := P.income s.2 + (1 + P.interest) * max 0 s.1

/-- The largest consumption the capped problem allows. -/
noncomputable def maxConsumption : ℝ := P.maxIncome + (1 + P.interest) * assetCap

/-- The largest asset holding that can be carried forward. -/
noncomputable def maxSaving (s : ℝ × Z) : ℝ := max 0 (min assetCap (P.resources s))

/-- Consumption on the budget line. -/
noncomputable def consumption (s : ℝ × Z) (a' : ℝ) : ℝ := P.resources s - a'

/-- The reward: utility of consumption clamped above, and `-∞` where consumption vanishes.
No floor. -/
noncomputable def rewardFn (p : (ℝ × Z) × ℝ) : EReal :=
  extendBot P.u (min P.maxConsumption (P.consumption p.1 p.2))

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

/-- Discreteness of `Z` is what makes this continuous. -/
theorem continuous_resources : Continuous P.resources :=
  (continuous_of_discreteTopology.comp continuous_snd).add
    (continuous_const.mul (continuous_const.max continuous_fst))

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max (continuous_const.min P.continuous_resources)

theorem continuous_rewardFn : Continuous P.rewardFn := by
  refine (continuous_extendBot P.continuousOn_u P.tendsto_atBot_u).comp
    (continuous_const.min ?_)
  exact (P.continuous_resources.comp continuous_fst).sub continuous_snd

/-- The problem as a stochastic dynamic program with an extended-real reward. -/
noncomputable def toExtended : ExtendedStochasticProgram (ℝ × Z) ℝ Z where
  feasible s := Icc 0 (P.maxSaving s)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  reward := ⟨P.rewardFn, P.continuous_rewardFn⟩
  rewardMax := P.u P.maxConsumption
  reward_le := by
    intro s a _
    simp only [ContinuousMap.coe_mk, rewardFn]
    rcases le_or_gt (min P.maxConsumption (P.consumption s a)) 0 with h | h
    · rw [extendBot_of_nonpos h]
      exact bot_le
    · rw [extendBot_of_pos h, EReal.coe_le_coe_iff]
      exact P.monotoneOn_u h P.maxConsumption_pos (min_le_left _ _)
  select := ⟨fun _ => 0, continuous_const⟩
  select_mem := fun _ => ⟨le_rfl, le_max_left _ _⟩
  rewardMin := P.u P.minIncome
  le_reward_select := by
    intro s
    simp only [ContinuousMap.coe_mk, rewardFn]
    have h : P.minIncome ≤ min P.maxConsumption (P.consumption s 0) := by
      refine le_min P.minIncome_le_maxConsumption ?_
      simp only [consumption, sub_zero]
      exact P.minIncome_le_resources s
    rw [extendBot_of_pos (lt_of_lt_of_le P.minIncome_pos h), EReal.coe_le_coe_iff]
    exact P.monotoneOn_u P.minIncome_pos (lt_of_lt_of_le P.minIncome_pos h) h
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

theorem consumption_le_maxConsumption {s : ℝ × Z} {a' : ℝ} (hs : s.1 ∈ Icc 0 assetCap)
    (ha' : 0 ≤ a') : P.consumption s a' ≤ P.maxConsumption := by
  have hmax : max 0 s.1 = s.1 := max_eq_right hs.1
  have : (1 + P.interest) * s.1 ≤ (1 + P.interest) * assetCap :=
    mul_le_mul_of_nonneg_left hs.2 P.interest_gt_neg_one.le
  simp only [consumption, resources, maxConsumption, hmax]
  linarith [P.le_maxIncome s.2]

/-- **The stochastic Bellman equation, with honest utility and positive consumption.** That
consumption is positive at the optimum is a consequence of the value being real, not a
separate development. -/
theorem exists_optimal_saving {s : ℝ × Z} (hs : s.1 ∈ Icc 0 assetCap) :
    ∃ a' ∈ Icc 0 (P.maxSaving s), 0 < P.consumption s a' ∧
      P.toExtended.valueFunction s
        = P.u (P.consumption s a')
          + P.discount * ∑ z', P.transitionMatrix s.2 z'
              * P.toExtended.valueFunction (a', z') := by
  obtain ⟨a', ha', heq⟩ := P.toExtended.exists_optimal_policy s
  have hne : P.rewardFn (s, a') ≠ ⊥ := by
    intro hb
    rw [show P.toExtended.reward (s, a') = P.rewardFn (s, a') from rfl, hb,
      EReal.bot_add _] at heq
    exact EReal.coe_ne_bot _ heq
  have hpos : 0 < min P.maxConsumption (P.consumption s a') := by
    by_contra hle
    push Not at hle
    exact hne (extendBot_of_nonpos hle)
  have hc : 0 < P.consumption s a' := lt_of_lt_of_le hpos (min_le_right _ _)
  have hclamp : min P.maxConsumption (P.consumption s a') = P.consumption s a' :=
    min_eq_right (P.consumption_le_maxConsumption hs ha'.1)
  refine ⟨a', ha', hc, ?_⟩
  have hrw : P.toExtended.reward (s, a') = ((P.u (P.consumption s a') : ℝ) : EReal) :=
    calc P.toExtended.reward (s, a')
        = extendBot P.u (min P.maxConsumption (P.consumption s a')) := rfl
      _ = extendBot P.u (P.consumption s a') := by rw [hclamp]
      _ = _ := extendBot_of_pos hc
  rw [hrw, ← EReal.coe_add, EReal.coe_eq_coe_iff] at heq
  exact heq

/-! ### Concavity and the optimal policy

The state is a pair `(assets, income state)`, which is not a module over `ℝ`, so concavity
is stated along the asset slice for each income state -- see
`LeanEconomics.Blackwell.forall_concaveOn_valueFunction`. Everything else follows the
deterministic argument, with the continuation value now an expectation: it is concave in
next period's assets because each `V (·, z')` is, and the transition probabilities are
nonnegative. -/

theorem resources_eq_affine {s : ℝ × Z} (hs : 0 ≤ s.1) :
    P.resources s = P.income s.2 + (1 + P.interest) * s.1 := by
  simp only [resources, max_eq_right hs]

theorem resources_affine_comb {x y θ φ : ℝ} {z : Z} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hθφ : θ + φ = 1) :
    P.resources (θ * x + φ * y, z) = θ * P.resources (x, z) + φ * P.resources (y, z) := by
  have hmix : (0 : ℝ) ≤ θ * x + φ * y := add_nonneg (mul_nonneg hθ hx) (mul_nonneg hφ hy)
  rw [P.resources_eq_affine hmix, P.resources_eq_affine hx, P.resources_eq_affine hy]
  linear_combination (-(P.income z)) * hθφ

theorem maxSaving_le_assetCap (s : ℝ × Z) : P.maxSaving s ≤ assetCap :=
  max_le P.assetCap_nonneg (min_le_left _ _)

theorem feasible_subset_region {s : ℝ × Z} {a : ℝ} (ha : a ∈ P.toExtended.feasible s) :
    a ∈ Icc 0 assetCap :=
  ⟨ha.1, ha.2.trans (P.maxSaving_le_assetCap s)⟩

theorem maxSaving_eq (s : ℝ × Z) : P.maxSaving s = min assetCap (P.resources s) :=
  max_eq_right (le_min P.assetCap_nonneg (P.resources_pos s).le)

theorem feasible_convex {x y : ℝ} {z : Z} (hx : x ∈ Icc 0 assetCap)
    (hy : y ∈ Icc 0 assetCap) {ax ay θ φ : ℝ}
    (hax : ax ∈ P.toExtended.feasible (x, z)) (hay : ay ∈ P.toExtended.feasible (y, z))
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hθφ : θ + φ = 1) :
    θ * ax + φ * ay ∈ P.toExtended.feasible (θ * x + φ * y, z) := by
  obtain ⟨hax0, haxm⟩ := hax
  obtain ⟨hay0, haym⟩ := hay
  rw [P.maxSaving_eq (x, z)] at haxm
  rw [P.maxSaving_eq (y, z)] at haym
  refine ⟨add_nonneg (mul_nonneg hθ hax0) (mul_nonneg hφ hay0), ?_⟩
  rw [P.maxSaving_eq (θ * x + φ * y, z)]
  refine le_min ?_ ?_
  · have h1 : ax ≤ assetCap := haxm.trans (min_le_left _ _)
    have h2 : ay ≤ assetCap := haym.trans (min_le_left _ _)
    nlinarith
  · have h1 : ax ≤ P.resources (x, z) := haxm.trans (min_le_right _ _)
    have h2 : ay ≤ P.resources (y, z) := haym.trans (min_le_right _ _)
    rw [P.resources_affine_comb hx.1 hy.1 hθ hφ hθφ]
    nlinarith

theorem consumption_pos_of_ne_bot {s : ℝ × Z} {a : ℝ} (h : P.toExtended.reward (s, a) ≠ ⊥) :
    0 < P.consumption s a := by
  by_contra hle
  push Not at hle
  refine h ?_
  calc P.toExtended.reward (s, a)
      = extendBot P.u (min P.maxConsumption (P.consumption s a)) := rfl
    _ = ⊥ := extendBot_of_nonpos ((min_le_right _ _).trans hle)

theorem reward_eq_coe {s : ℝ × Z} {a : ℝ} (hs : s.1 ∈ Icc 0 assetCap)
    (ha : a ∈ P.toExtended.feasible s) (hc : 0 < P.consumption s a) :
    P.toExtended.reward (s, a) = ((P.u (P.consumption s a) : ℝ) : EReal) :=
  calc P.toExtended.reward (s, a)
      = extendBot P.u (min P.maxConsumption (P.consumption s a)) := rfl
    _ = extendBot P.u (P.consumption s a) := by
        rw [min_eq_right (P.consumption_le_maxConsumption hs ha.1)]
    _ = _ := extendBot_of_pos hc

theorem bellmanFn_eq_of_optimal {v : (ℝ × Z) →ᵇ ℝ} {s : ℝ × Z} {a : ℝ}
    (hs : s.1 ∈ Icc 0 assetCap) (ha : a ∈ P.toExtended.feasible s)
    (heq : P.toExtended.objectiveE v s a
      = ((P.toExtended.bellmanFn v s : ℝ) : EReal)) :
    0 < P.consumption s a ∧
      P.toExtended.bellmanFn v s
        = P.u (P.consumption s a) + P.discount * ∑ z', P.transitionMatrix s.2 z' * v (a, z') := by
  have hne : P.toExtended.reward (s, a) ≠ ⊥ := by
    intro hb
    rw [ExtendedStochasticProgram.objectiveE, hb, EReal.bot_add _] at heq
    exact EReal.coe_ne_bot _ heq.symm
  have hc := P.consumption_pos_of_ne_bot hne
  refine ⟨hc, ?_⟩
  rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_coe hs ha hc, ← EReal.coe_add,
    EReal.coe_eq_coe_iff] at heq
  exact heq.symm

/-- **The Bellman operator preserves concavity along each asset slice.** -/
theorem concaveOn_bellman (v : (ℝ × Z) →ᵇ ℝ)
    (hv : ∀ z : Z, ConcaveOn ℝ (Icc 0 assetCap) fun a => v (a, z)) (z : Z) :
    ConcaveOn ℝ (Icc 0 assetCap) fun a => (P.toExtended.bellman v) (a, z) := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  obtain ⟨ax, hax, heqx⟩ := P.toExtended.exists_optimal_action v (x, z)
  obtain ⟨ay, hay, heqy⟩ := P.toExtended.exists_optimal_action v (y, z)
  obtain ⟨hcx, hbx⟩ := P.bellmanFn_eq_of_optimal hx hax heqx
  obtain ⟨hcy, hby⟩ := P.bellmanFn_eq_of_optimal hy hay heqy
  have hxy : θ * x + φ * y ∈ Icc 0 assetCap := by
    simpa using convex_Icc (0 : ℝ) assetCap hx hy hθ hφ hθφ
  have hmix := P.feasible_convex hx hy hax hay hθ hφ hθφ
  have hcmix : P.consumption (θ * x + φ * y, z) (θ * ax + φ * ay)
      = θ * P.consumption (x, z) ax + φ * P.consumption (y, z) ay := by
    simp only [consumption]
    rw [P.resources_affine_comb hx.1 hy.1 hθ hφ hθφ]
    ring
  have hcm : 0 < P.consumption (θ * x + φ * y, z) (θ * ax + φ * ay) := by
    rw [hcmix]
    rcases lt_or_eq_of_le hθ with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos h hcx) (mul_nonneg hφ hcy.le)
    · have hφ1 : φ = 1 := by linarith
      rw [← h, hφ1]
      simpa using hcy
  have hle := P.toExtended.le_bellmanFn v hmix
  have hobj : P.toExtended.objectiveE v (θ * x + φ * y, z) (θ * ax + φ * ay)
      = ((P.u (P.consumption (θ * x + φ * y, z) (θ * ax + φ * ay))
          + P.discount * ∑ z', P.transitionMatrix z z' * v (θ * ax + φ * ay, z') : ℝ) : EReal) := by
    rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_coe hxy hmix hcm, ← EReal.coe_add]
    rfl
  rw [hobj] at hle
  have hle' : P.u (P.consumption (θ * x + φ * y, z) (θ * ax + φ * ay))
      + P.discount * ∑ z', P.transitionMatrix z z' * v (θ * ax + φ * ay, z')
      ≤ P.toExtended.bellmanFn v (θ * x + φ * y, z) := by exact_mod_cast hle
  -- utility is concave, and so is the expectation, termwise
  have hu := P.strictConcaveOn_u.concaveOn.2 hcx hcy hθ hφ hθφ
  have hexp : θ * (∑ z', P.transitionMatrix z z' * v (ax, z'))
      + φ * (∑ z', P.transitionMatrix z z' * v (ay, z'))
      ≤ ∑ z', P.transitionMatrix z z' * v (θ * ax + φ * ay, z') := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z' _ => ?_
    have hvz := (hv z').2 (P.feasible_subset_region hax) (P.feasible_subset_region hay) hθ hφ hθφ
    simp only [smul_eq_mul] at hvz
    nlinarith [P.transitionMatrix_nonneg z z']
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hexp hβ
  simp only [smul_eq_mul] at hu
  simp only [smul_eq_mul, ExtendedStochasticProgram.bellman_apply]
  rw [hbx, hby]
  rw [hcmix] at hle'
  linarith

/-- **The value function is concave in assets, for each income state.** -/
theorem concaveOn_valueFunction (z : Z) :
    ConcaveOn ℝ (Icc 0 assetCap) fun a => P.toExtended.valueFunction (a, z) :=
  Blackwell.forall_concaveOn_valueFunction (convex_Icc _ _) (fun (z : Z) (a : ℝ) => (a, z))
    P.toExtended.blackwell P.toExtended.discount_lt_one
    (fun v hv => P.concaveOn_bellman v hv) z

/-- **The optimal action is unique.** -/
theorem optimal_action_unique {s : ℝ × Z} (hs : s.1 ∈ Icc 0 assetCap) {a₀ a₁ : ℝ}
    (h₀ : a₀ ∈ P.toExtended.feasible s) (h₁ : a₁ ∈ P.toExtended.feasible s)
    (hm₀ : P.toExtended.objectiveE P.toExtended.valueFunction s a₀
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction s : ℝ) : EReal))
    (hm₁ : P.toExtended.objectiveE P.toExtended.valueFunction s a₁
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction s : ℝ) : EReal)) :
    a₀ = a₁ := by
  by_contra hne
  obtain ⟨hc₀, hb₀⟩ := P.bellmanFn_eq_of_optimal hs h₀ hm₀
  obtain ⟨hc₁, hb₁⟩ := P.bellmanFn_eq_of_optimal hs h₁ hm₁
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hsum : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
  have hmem : (1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁ ∈ P.toExtended.feasible s := by
    simpa using convex_Icc (0 : ℝ) (P.maxSaving s) h₀ h₁ hhalf.le hhalf.le hsum
  have hcmid : P.consumption s ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁)
      = (1 / 2 : ℝ) * P.consumption s a₀ + (1 / 2 : ℝ) * P.consumption s a₁ := by
    simp only [consumption]; ring
  have hcm : 0 < P.consumption s ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁) := by
    rw [hcmid]; linarith
  have hcne : P.consumption s a₀ ≠ P.consumption s a₁ := by
    simp only [consumption]
    intro h
    exact hne (by linarith)
  have hu := P.strictConcaveOn_u.2 hc₀ hc₁ hcne hhalf hhalf hsum
  have hexp : (1 / 2 : ℝ) * (∑ z', P.transitionMatrix s.2 z' * P.toExtended.valueFunction (a₀, z'))
      + (1 / 2 : ℝ) * (∑ z', P.transitionMatrix s.2 z' * P.toExtended.valueFunction (a₁, z'))
      ≤ ∑ z', P.transitionMatrix s.2 z'
          * P.toExtended.valueFunction ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁, z') := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z' _ => ?_
    have hvz := (P.concaveOn_valueFunction z').2 (P.feasible_subset_region h₀)
      (P.feasible_subset_region h₁) hhalf.le hhalf.le hsum
    simp only [smul_eq_mul] at hvz
    nlinarith [P.transitionMatrix_nonneg s.2 z']
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hexp hβ
  simp only [smul_eq_mul] at hu
  have hle := P.toExtended.le_bellmanFn P.toExtended.valueFunction hmem
  have hobj : P.toExtended.objectiveE P.toExtended.valueFunction s
        ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁)
      = ((P.u (P.consumption s ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁))
          + P.discount * ∑ z', P.transitionMatrix s.2 z'
              * P.toExtended.valueFunction ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁, z')
            : ℝ) : EReal) := by
    rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_coe hs hmem hcm, ← EReal.coe_add]
    rfl
  rw [hobj] at hle
  have hle' : P.u (P.consumption s ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁))
      + P.discount * ∑ z', P.transitionMatrix s.2 z'
          * P.toExtended.valueFunction ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁, z')
      ≤ P.toExtended.bellmanFn P.toExtended.valueFunction s := by exact_mod_cast hle
  rw [hcmid] at hle'
  linarith

/-- The optimal saving choice. -/
noncomputable def policy (s : ℝ × Z) : ℝ :=
  Classical.choose (P.toExtended.exists_optimal_action P.toExtended.valueFunction s)

theorem policy_mem (s : ℝ × Z) : P.policy s ∈ P.toExtended.feasible s :=
  (Classical.choose_spec
    (P.toExtended.exists_optimal_action P.toExtended.valueFunction s)).1

theorem policy_optimal (s : ℝ × Z) :
    P.toExtended.objectiveE P.toExtended.valueFunction s (P.policy s)
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction s : ℝ) : EReal) :=
  (Classical.choose_spec
    (P.toExtended.exists_optimal_action P.toExtended.valueFunction s)).2

theorem policy_mem_region (s : ℝ × Z) : P.policy s ∈ Icc 0 assetCap :=
  P.feasible_subset_region (P.policy_mem s)

theorem consumption_policy_pos {s : ℝ × Z} (hs : s.1 ∈ Icc 0 assetCap) :
    0 < P.consumption s (P.policy s) :=
  (P.bellmanFn_eq_of_optimal hs (P.policy_mem s) (P.policy_optimal s)).1

theorem eq_policy_of_optimal {s : ℝ × Z} (hs : s.1 ∈ Icc 0 assetCap) {a : ℝ}
    (ha : a ∈ P.toExtended.feasible s)
    (hopt : P.toExtended.objectiveE P.toExtended.valueFunction s a
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction s : ℝ) : EReal)) :
    a = P.policy s :=
  P.optimal_action_unique hs ha (P.policy_mem s) hopt (P.policy_optimal s)

theorem argmax_eq_singleton {s : ℝ × Z} (hs : s.1 ∈ Icc 0 assetCap) :
    argmax (P.toExtended.objectiveE P.toExtended.valueFunction) P.toExtended.feasible s
      = {P.policy s} := by
  ext a
  simp only [argmax, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ha, hmax⟩
    refine P.eq_policy_of_optimal hs ha (le_antisymm (P.toExtended.le_bellmanFn _ ha) ?_)
    rw [← P.policy_optimal s]
    exact isMaxOn_iff.mp hmax _ (P.policy_mem s)
  · rintro rfl
    refine ⟨P.policy_mem s, isMaxOn_iff.mpr fun b hb => ?_⟩
    rw [P.policy_optimal s]
    exact P.toExtended.le_bellmanFn _ hb

/-- **The optimal policy is continuous** on the region of states with assets in
`[0, assetCap]`. -/
theorem continuousOn_policy :
    ContinuousOn P.policy {s : ℝ × Z | s.1 ∈ Icc 0 assetCap} :=
  continuousOn_of_upperHemicontinuous_singleton
    (P.toExtended.upperHemicontinuous_argmax P.toExtended.valueFunction)
    fun _ hs => P.argmax_eq_singleton hs

/-- **The Bellman equation at the policy.** -/
theorem valueFunction_eq_policy {s : ℝ × Z} (hs : s.1 ∈ Icc 0 assetCap) :
    P.toExtended.valueFunction s
      = P.u (P.consumption s (P.policy s))
        + P.discount * ∑ z', P.transitionMatrix s.2 z'
            * P.toExtended.valueFunction (P.policy s, z') := by
  have h := (P.bellmanFn_eq_of_optimal hs (P.policy_mem s) (P.policy_optimal s)).2
  have hfix : P.toExtended.bellmanFn P.toExtended.valueFunction s
      = P.toExtended.valueFunction s := by
    conv_rhs => rw [← P.toExtended.bellman_valueFunction]
    rfl
  rw [← hfix, h]

/-- A two-state calibration with `σ = 2`, where CES utility is `-1 / c`. -/
noncomputable def calibrated : IncomeFluctuation (Fin 2) 10 where
  income z := if z = 0 then 1 / 2 else 3 / 2
  transitionMatrix _ _ := 1 / 2
  interest := 1 / 20
  discount := 24 / 25
  u := fun c => -c⁻¹
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
  tendsto_atBot_u := tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero
  strictConcaveOn_u := strictConcaveOn_neg_inv

end IncomeFluctuation

end LeanEconomics
