/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationEuler

/-!
# Positivity and monotonicity along the iteration

Carroll and Kimball's induction step needs the CONTINUATION's consumption function to be
positive, concave and nondecreasing. Concavity is the induction hypothesis; the other two are
facts, but they are proved in this development only at the FIXED POINT
(`positiveConsumption_of_unbounded`, `consumptionFn_mono`). This file restates them for an
arbitrary continuation, which is what the induction sees.

Both proofs are the fixed-point proofs with `objR` replaced by `objROf`: the objective read
against an arbitrary continuation. The one structural fact they use is that the continuation
value depends on the saving chosen and the income state, never on current assets, so shifting
both households' plans by their resource gap leaves consumption alone and moves only the
continuation. That is true of `objROf` for exactly the same reason it is true of `objR`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### The objective against an arbitrary continuation -/

/-- The continuation value of saving `x`, read against `v`. -/
noncomputable def contOf (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (x : ℝ) : ℝ :=
  ∑ z' : Z, P.transitionMatrix z z' * v (x, z')

/-- The objective, as a real number, read against `v`. -/
noncomputable def objROf (v : (ℝ × Z) →ᵇ ℝ) (s : ℝ × Z) (x : ℝ) : ℝ :=
  P.u (P.consumption s x) + P.discount * P.contOf v s.2 x

theorem concaveOn_contOf {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetFloor assetCap v) (z : Z) :
    ConcaveOn ℝ (Icc assetFloor assetCap) (P.contOf v z) := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  simp only [contOf, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z' _ => ?_
  have hz' := (hv z').2 hx hy hθ hφ hθφ
  simp only [smul_eq_mul] at hz'
  nlinarith [mul_le_mul_of_nonneg_left hz' (P.transitionMatrix_nonneg z z')]

/-! ### Positivity -/

/-- **Consumption never vanishes at the optimum, whatever the continuation.** With utility
unbounded below the reward at zero consumption is `⊥`, and the optimum is a real number. -/
theorem consumptionFnOf_pos (hd : P.Unbounded) (v : (ℝ × Z) →ᵇ ℝ) {z : Z} {a : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) : 0 < P.consumptionFnOf v z a := by
  have hopt := P.policyOf_optimal v (a, z)
  have hne : P.toExtended.reward ((a, z), P.policyOf v (a, z)) ≠ ⊥ := by
    intro hbot
    rw [ExtendedStochasticProgram.objectiveE, hbot, EReal.bot_add] at hopt
    exact (EReal.bot_ne_coe _) hopt
  have hmem := P.consumption_mem_dom_of_ne_bot (s := (a, z)) ha (P.policyOf_mem v (a, z)) hne
  rw [hd] at hmem
  exact hmem

/-- **Consumption is positive at the optimum against EVERY continuation.** The induction sees
the iterates, not the value function, so this is what it needs. With utility unbounded below it
is automatic; for the bounded CES family it has to be earned from a marginal Inada condition,
exactly as `PositiveConsumption` is. -/
def PositiveConsumptionAll : Prop :=
  ∀ (v : (ℝ × Z) →ᵇ ℝ) (z : Z), ∀ a ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z a

theorem positiveConsumptionAll_of_unbounded (hd : P.Unbounded) : P.PositiveConsumptionAll :=
  fun v _ _ ha => P.consumptionFnOf_pos hd v ha

/-- The objective in the reals agrees with the extended objective where consumption is
positive. -/
theorem objectiveE_eq_coe_of (v : (ℝ × Z) →ᵇ ℝ) {a : ℝ} {z : Z} {x : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) (hx : x ∈ P.toExtended.feasible (a, z))
    (hcx : 0 < P.consumption (a, z) x) :
    P.toExtended.objectiveE v (a, z) x = ((P.objROf v (a, z) x : ℝ) : EReal) := by
  rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_coe (s := (a, z)) ha hx hcx,
    ← EReal.coe_add]
  rfl

/-- **Any feasible action with positive consumption is worth at most the optimum**, whatever
the continuation. -/
theorem objROf_le_of_mem (hpc : P.PositiveConsumptionAll) (v : (ℝ × Z) →ᵇ ℝ)
    {a : ℝ} {z : Z} {x : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) (hx : x ∈ P.toExtended.feasible (a, z))
    (hcx : 0 < P.consumption (a, z) x) :
    P.objROf v (a, z) x ≤ P.objROf v (a, z) (P.policyOf v (a, z)) := by
  have hc : 0 < P.consumptionFnOf v z a := hpc v z a ha
  have h1 := P.lazyValue_le v z ha hx hcx
  have h2 := P.lazyValue_eq v z ha (P.policyOf_mem v (a, z)) hc (P.policyOf_optimal v (a, z))
  simp only [lazyValue] at h1 h2
  simp only [objROf, contOf, consumption]
  linarith

/-! ### Monotonicity of the saving policy -/

/-- **The optimal policy is increasing in assets, whatever the continuation.** The exchange
argument of `policy_mono`, run against `v`. -/
theorem policyOf_mono (hpc : P.PositiveConsumptionAll) {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices assetFloor assetCap v) {a a' : ℝ} {z : Z}
    (ha : a ∈ Icc assetFloor assetCap) (ha' : a' ∈ Icc assetFloor assetCap) (hle : a ≤ a') :
    P.policyOf v (a, z) ≤ P.policyOf v (a', z) := by
  by_contra hcon
  rw [not_le] at hcon
  have hR : P.resources (a, z) ≤ P.resources (a', z) := P.resources_mono hle
  have hys : P.policyOf v (a, z) ∈ P.toExtended.feasible (a, z) := P.policyOf_mem v _
  have hys' : P.policyOf v (a, z) ∈ P.toExtended.feasible (a', z) := P.feasible_mono hle hys
  have hy's' : P.policyOf v (a', z) ∈ P.toExtended.feasible (a', z) := P.policyOf_mem v _
  have hy's : P.policyOf v (a', z) ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq] at hys ⊢
    rw [P.feasible_eq] at hy's'
    exact ⟨hy's'.1, le_trans hcon.le hys.2⟩
  have hcsy : 0 < P.consumption (a, z) (P.policyOf v (a, z)) := hpc v z a ha
  have hcs'y' : 0 < P.consumption (a', z) (P.policyOf v (a', z)) := hpc v z a' ha'
  have hcsy' : 0 < P.consumption (a, z) (P.policyOf v (a', z)) := by
    simp only [consumption] at hcsy ⊢; linarith
  have hcs'y : 0 < P.consumption (a', z) (P.policyOf v (a, z)) := by
    simp only [consumption] at hcsy ⊢; linarith
  -- increasing differences, from concavity of `u` alone
  have hshift := P.strictConcaveOn_u_dom.concaveOn.sub_le_sub_of_shift
    (c₁ := P.resources (a, z) - P.policyOf v (a, z))
    (c₂ := P.resources (a, z) - P.policyOf v (a', z))
    (Δ := P.resources (a', z) - P.resources (a, z))
    (P.mem_dom_of_pos (by simpa only [consumption] using hcsy))
    (by
      have he : P.resources (a, z) - P.policyOf v (a', z)
          + (P.resources (a', z) - P.resources (a, z))
          = P.consumption (a', z) (P.policyOf v (a', z)) := by simp only [consumption]; ring
      rw [he]; exact P.mem_dom_of_pos hcs'y')
    (by simp only [consumption] at hcsy hcsy'; linarith) (by linarith)
  have hopt_s := P.objROf_le_of_mem hpc v ha hy's hcsy'
  have hge : P.objROf v (a', z) (P.policyOf v (a', z))
      ≤ P.objROf v (a', z) (P.policyOf v (a, z)) := by
    simp only [objROf, consumption] at hopt_s ⊢
    have e₁ : P.resources (a, z) - P.policyOf v (a', z)
        + (P.resources (a', z) - P.resources (a, z))
        = P.resources (a', z) - P.policyOf v (a', z) := by ring
    have e₂ : P.resources (a, z) - P.policyOf v (a, z)
        + (P.resources (a', z) - P.resources (a, z))
        = P.resources (a', z) - P.policyOf v (a, z) := by ring
    rw [e₁, e₂] at hshift
    linarith
  have hopt' : P.objROf v (a', z) (P.policyOf v (a, z))
      = P.objROf v (a', z) (P.policyOf v (a', z)) :=
    le_antisymm (P.objROf_le_of_mem hpc v ha' hys' hcs'y) hge
  have hbell : P.toExtended.objectiveE v (a', z) (P.policyOf v (a, z))
      = ((P.toExtended.bellmanFn v (a', z) : ℝ) : EReal) := by
    rw [P.objectiveE_eq_coe_of v ha' hys' hcs'y, hopt',
      ← P.objectiveE_eq_coe_of v ha' hy's' hcs'y']
    exact P.policyOf_optimal v _
  exact absurd (P.optimal_action_unique_of_concaveSlices hv (s := (a', z)) ha' hys' hy's'
    hbell (P.policyOf_optimal v _)) (by linarith)

/-! ### Monotonicity of the consumption function -/

/-- **Consumption rises with assets, whatever the continuation.** The exchange argument of
`consumptionFn_mono`, run against `v`. -/
theorem consumptionFnOf_mono (hpc : P.PositiveConsumptionAll) {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices assetFloor assetCap v) {a a' : ℝ} {z : Z}
    (ha : a ∈ Icc assetFloor assetCap) (ha' : a' ∈ Icc assetFloor assetCap) (hle : a ≤ a') :
    P.consumptionFnOf v z a ≤ P.consumptionFnOf v z a' := by
  set Δ : ℝ := P.resources (a', z) - P.resources (a, z) with hΔdef
  have hΔ : 0 ≤ Δ := by rw [hΔdef]; linarith [P.resources_mono (z := z) hle]
  set b : ℝ := P.policyOf v (a, z) with hbdef
  set b' : ℝ := P.policyOf v (a', z) with hb'def
  by_contra hcon
  rw [not_le] at hcon
  have hgap : b + Δ < b' := by
    simp only [consumptionFnOf, consumption] at hcon
    rw [hΔdef]; linarith
  have hbmem : b ∈ P.toExtended.feasible (a, z) := P.policyOf_mem v _
  have hb'mem : b' ∈ P.toExtended.feasible (a', z) := P.policyOf_mem v _
  rw [P.feasible_eq] at hbmem hb'mem
  have hshiftup : b + Δ ∈ P.toExtended.feasible (a', z) := by
    rw [P.feasible_eq]
    exact ⟨by linarith [hbmem.1], by linarith [hb'mem.2]⟩
  have hshiftdown : b' - Δ ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq]
    refine ⟨by linarith [hbmem.1], ?_⟩
    have hms := P.maxSaving_le_add_sub (z := z) hle
    rw [← hΔdef] at hms
    linarith [hb'mem.2]
  have hc1 : 0 < P.consumption (a, z) b := hpc v z a ha
  have hc2 : 0 < P.consumption (a', z) b' := hpc v z a' ha'
  have he1 : P.consumption (a', z) (b + Δ) = P.consumption (a, z) b := by
    simp only [consumption, hΔdef]; ring
  have he2 : P.consumption (a, z) (b' - Δ) = P.consumption (a', z) b' := by
    simp only [consumption, hΔdef]; ring
  have hI := P.objROf_le_of_mem hpc v ha hshiftdown (by rw [he2]; exact hc2)
  have hII := P.objROf_le_of_mem hpc v ha' hshiftup (by rw [he1]; exact hc1)
  have hbreg : b ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policyOf_mem v _)
  have hb'reg : b' ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policyOf_mem v _)
  have hshift := (P.concaveOn_contOf hv z).sub_le_sub_of_shift (c₁ := b) (c₂ := b' - Δ) (Δ := Δ)
    hbreg (by simpa using hb'reg) (by linarith) hΔ
  rw [sub_add_cancel] at hshift
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hshift hβ
  simp only [objROf, he1, he2] at hI hII
  have hIIeq : P.objROf v (a', z) (b + Δ) = P.objROf v (a', z) b' := by
    simp only [objROf, he1]
    nlinarith [hI, hII, hscaled]
  have hbell : P.toExtended.objectiveE v (a', z) (b + Δ)
      = ((P.toExtended.bellmanFn v (a', z) : ℝ) : EReal) := by
    rw [P.objectiveE_eq_coe_of v ha' hshiftup (by rw [he1]; exact hc1), hIIeq,
      ← P.objectiveE_eq_coe_of v ha' (P.policyOf_mem v _) hc2]
    exact P.policyOf_optimal v _
  exact absurd (P.optimal_action_unique_of_concaveSlices hv (s := (a', z)) ha' hshiftup
    (P.policyOf_mem v _) hbell (P.policyOf_optimal v _)) (by rw [← hb'def]; linarith)

/-! ### Saving stays strictly inside the feasible set

Positive consumption already keeps the saving below resources; what is left is the asset CAP,
and that is the single quantitative input the induction still needs. -/

theorem policyOf_lt_maxSaving (hpc : P.PositiveConsumptionAll) (v : (ℝ × Z) →ᵇ ℝ) {a : ℝ} {z : Z}
    (ha : a ∈ Icc assetFloor assetCap) (hcap : P.policyOf v (a, z) < assetCap) :
    P.policyOf v (a, z) < P.maxSaving (a, z) := by
  rw [P.maxSaving_eq]
  refine lt_min hcap ?_
  have hc := hpc v z a ha
  simp only [consumptionFnOf, consumption] at hc
  linarith

/-! ### A uniform bound on saving, and hence on the cap

The last input is quantitative: the household must not want to save all the way to the imposed
ceiling. `policy_le_of_marginal_bound` does this at the fixed point; the same deviation — save
half as far above the borrowing limit — works against any continuation, with `‖v‖` in place of
`‖V‖`. The iterates are uniformly bounded because the Bellman operator adds at most the reward
and contracts what it inherits, so one calibration inequality covers the whole iteration. -/

theorem abs_contOf_le (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (x : ℝ) : |P.contOf v z x| ≤ ‖v‖ := by
  have h1 : |∑ z' : Z, P.transitionMatrix z z' * v (x, z')|
      ≤ ∑ z' : Z, |P.transitionMatrix z z' * v (x, z')| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ z' : Z, |P.transitionMatrix z z' * v (x, z')|
      ≤ ∑ z' : Z, P.transitionMatrix z z' * ‖v‖ := by
    refine Finset.sum_le_sum fun z' _ => ?_
    rw [abs_mul, abs_of_nonneg (P.transitionMatrix_nonneg z z')]
    exact mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm (x, z'))
      (P.transitionMatrix_nonneg z z')
  rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul] at h2
  simp only [contOf]
  linarith

/-- **A uniform bound on saving from a uniform marginal bound**, against any continuation. -/
theorem policyOf_le_of_marginal_bound (hpc : P.PositiveConsumptionAll) {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices assetFloor assetCap v) {m : ℝ} (hm : 0 < m)
    (hmarg : ∀ c d : ℝ, d ∈ P.dom → d ≤ c → c ≤ P.maxConsumption → m * (c - d) ≤ P.u c - P.u d)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    P.policyOf v (a, z) ≤ assetFloor + 4 * (P.discount : ℝ) * ‖v‖ / m := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hbound : (0 : ℝ) ≤ 4 * (P.discount : ℝ) * ‖v‖ / m := by positivity
  set b : ℝ := P.policyOf v (a, z) with hbdef
  have hbreg : b ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policyOf_mem v _)
  rcases eq_or_lt_of_le hbreg.1 with hzero | hbpos
  · rw [← hzero]; linarith
  set c : ℝ := P.consumptionFnOf v z a with hcdef
  have hcpos : 0 < c := hpc v z a ha
  have hres : P.resources (a, z) = c + b := by
    simp only [hcdef, consumptionFnOf, consumption]; ring
  set w : ℝ := (b + assetFloor) / 2 with hwdef
  have hw0 : assetFloor < w := by rw [hwdef]; linarith
  have hwb : w < b := by rw [hwdef]; linarith
  have heq : b - w = w - assetFloor := by rw [hwdef]; ring
  have hfeas : w ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq]
    exact ⟨hw0.le, by linarith [(P.policyOf_mem v (a, z)).2]⟩
  have hcons : P.consumption (a, z) w = c + (b - assetFloor) / 2 := by
    simp only [consumption, hres, hwdef]; ring
  have hdev : 0 < P.consumption (a, z) w := by rw [hcons]; linarith
  have hopt := P.objROf_le_of_mem hpc v ha hfeas hdev
  simp only [objROf, hcons] at hopt
  rw [show P.consumption (a, z) (P.policyOf v (a, z)) = c from rfl,
    show P.policyOf v (a, z) = b from rfl] at hopt
  -- concavity of the continuation caps what the forgone saving could have repaid
  have hfloormem : assetFloor ∈ Icc assetFloor assetCap := ⟨le_rfl, P.assetFloor_le_assetCap⟩
  have hslope := (P.concaveOn_contOf hv z).slope_anti_adjacent hfloormem hbreg hw0 hwb
  have hb1 := abs_le.mp (P.abs_contOf_le v z w)
  have hb0 := abs_le.mp (P.abs_contOf_le v z assetFloor)
  have hloss : P.contOf v z b - P.contOf v z w ≤ 2 * ‖v‖ := by
    rw [div_le_div_iff₀ (by linarith) (by linarith), ← heq] at hslope
    have := le_of_mul_le_mul_right hslope (by linarith : (0 : ℝ) < b - w)
    linarith [hb1.2, hb0.1]
  have hcmax : c + (b - assetFloor) / 2 ≤ P.maxConsumption := by
    have hcm := P.consumption_le_maxConsumption (s := (a, z)) ha hw0.le
    rwa [hcons] at hcm
  have hmg := hmarg (c + (b - assetFloor) / 2) c (P.mem_dom_of_pos hcpos) (by linarith) hcmax
  rw [show c + (b - assetFloor) / 2 - c = (b - assetFloor) / 2 from by ring] at hmg
  rw [← sub_le_iff_le_add', le_div_iff₀ hm]
  nlinarith [hopt, hmg, mul_le_mul_of_nonneg_left hloss hβ]

/-- The Bellman operator adds at most the reward and contracts what it inherits. -/
theorem norm_bellman_le (v : (ℝ × Z) →ᵇ ℝ) :
    ‖P.toExtended.bellman v‖
      ≤ max |P.toExtended.rewardMin| |P.toExtended.rewardMax| + (P.discount : ℝ) * ‖v‖ := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hM : (0 : ℝ) ≤ max |P.toExtended.rewardMin| |P.toExtended.rewardMax| :=
    le_max_of_le_left (abs_nonneg _)
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun s => ?_
  have hb := P.toExtended.bellmanFn_bounds v s
  have hval : (P.toExtended.bellman v) s = P.toExtended.bellmanFn v s := rfl
  rw [hval, Real.norm_eq_abs, abs_le]
  simp only [ExtendedStochasticProgram.loBound, ExtendedStochasticProgram.hiBound] at hb
  have h1 : -|P.toExtended.rewardMin| ≤ P.toExtended.rewardMin := neg_abs_le _
  have h2 : P.toExtended.rewardMax ≤ |P.toExtended.rewardMax| := le_abs_self _
  have h3 : -max |P.toExtended.rewardMin| |P.toExtended.rewardMax|
      ≤ -|P.toExtended.rewardMin| := by
    simp only [neg_le_neg_iff]; exact le_max_left _ _
  have h4 : |P.toExtended.rewardMax|
      ≤ max |P.toExtended.rewardMin| |P.toExtended.rewardMax| := le_max_right _ _
  have hdx : (P.toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  rw [hdx] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- **The iterates are uniformly bounded**, so one calibration covers them all. -/
theorem norm_iterate_le (n : ℕ) :
    ‖(P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)‖
      ≤ max |P.toExtended.rewardMin| |P.toExtended.rewardMax| / (1 - P.discount) := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hβ1 : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
  have hM : (0 : ℝ) ≤ max |P.toExtended.rewardMin| |P.toExtended.rewardMax| :=
    le_max_of_le_left (abs_nonneg _)
  have hfix : max |P.toExtended.rewardMin| |P.toExtended.rewardMax|
      + (P.discount : ℝ) * (max |P.toExtended.rewardMin| |P.toExtended.rewardMax|
        / (1 - P.discount))
      = max |P.toExtended.rewardMin| |P.toExtended.rewardMax| / (1 - P.discount) := by
    have hne : (1 : ℝ) - (P.discount : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  induction n with
  | zero => simpa using by positivity
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine le_trans (P.norm_bellman_le _) ?_
      rw [← hfix]
      have := mul_le_mul_of_nonneg_left ih hβ
      linarith

/-! ### Carroll and Kimball, assembled along the iteration -/

/-- The limit step, split off from `concaveOn_consumptionFn_of_preserves`: concavity of the
consumption functions of the iterates passes to the fixed point, because optimal actions survive
a uniform limit. -/
theorem concaveOn_consumptionFn_of_iterates
    (hcons : ∀ n : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z)) (z : Z) :
    ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) := by
  set T := P.toExtended.bellman with hTdef
  have hlim : Tendsto (fun n => T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) atTop
      (𝓝 P.toExtended.valueFunction) := P.toExtended.tendsto_iterate_valueFunction 0
  have hpt : ∀ a ∈ Icc assetFloor assetCap,
      Tendsto (fun n => P.consumptionFnOf (T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a) atTop
        (𝓝 (P.consumptionFn z a)) := by
    intro a ha
    have hp := P.tendsto_policyOf hlim P.concaveSlices_valueFunction (s := (a, z)) ha
    have he : P.consumptionFn z a
        = P.resources (a, z) - P.policyOf P.toExtended.valueFunction (a, z) := rfl
    rw [he]
    simpa only [consumptionFnOf, consumption] using tendsto_const_nhds.sub hp
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  have hm : θ • x + φ • y ∈ Icc assetFloor assetCap := convex_Icc _ _ hx hy hθ hφ hθφ
  refine le_of_tendsto_of_tendsto
    (((hpt x hx).const_smul θ).add ((hpt y hy).const_smul φ)) (hpt _ hm)
    (Eventually.of_forall fun n => (hcons n z).2 hx hy hθ hφ hθφ)

/-- **Carroll and Kimball (1996) for CRRA.** The consumption function is concave.

Everything is now proved except the asset cap: `hslack` says the household never wants to save
all the way to the imposed ceiling, at any stage of the iteration. That is the artefact the cap
always was — `crra_policy_lt_assetCap` discharges it at the fixed point by calibration, and
`policy_assetCap_of_patient` shows it is exactly `β (1 + r) < 1` that makes it true. -/
theorem concaveOn_consumptionFn_of_crra {γ : ℝ} (hpc : P.PositiveConsumptionAll) (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ)
    (hslack : ∀ n : ℕ, ∀ a ∈ Icc assetFloor assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (z : Z) : ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) := by
  set T := P.toExtended.bellman with hTdef
  have hslices : ∀ n : ℕ, ConcaveSlices assetFloor assetCap (T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact P.concaveSlices_bellman ih
  have hcons : ∀ n : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z) := by
    intro n
    induction n with
    | zero => exact P.concaveOn_consumptionFnOf_zero
    | succ k ih =>
        intro z
        have hnext : ∀ a ∈ Icc assetFloor assetCap,
            P.policyOf (T (T^[k] (0 : (ℝ × Z) →ᵇ ℝ))) (a, z) < P.maxSaving (a, z) := by
          intro a ha
          have hs := hslack (k + 1) a ha z
          rw [Function.iterate_succ_apply'] at hs
          exact P.policyOf_lt_maxSaving hpc _ ha hs
        rw [Function.iterate_succ_apply']
        exact P.concaveOn_consumptionFnOf_bellman hγ0 hβ hu z
          (fun z' A hA => hpc _ z' A hA) ih
          (fun z' x hx y hy hxy => P.consumptionFnOf_mono hpc (hslices k) hx hy hxy)
          (fun a ha => hpc _ z a ha) hnext
          fun A hA z' => P.policyOf_lt_maxSaving hpc _ hA (hslack k A hA z')
  exact P.concaveOn_consumptionFn_of_iterates hcons z


/-- **Carroll and Kimball (1996) for CRRA, from a calibration.** Beyond CRRA utility and
marginal utility unbounded at zero, the only hypothesis left is one inequality: the asset cap
must sit above the uniform bound on saving that the marginal bound `m` produces. Nothing about
the borrowing limit, and nothing about interiority.

That inequality is the cap being an artefact, which is what it was always meant to be: by
`policy_assetCap_of_patient` it is exactly impatience that makes it true. -/
theorem concaveOn_consumptionFn_of_marginal {γ m : ℝ} (hpc : P.PositiveConsumptionAll)
    (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ) (hm : 0 < m)
    (hmarg : ∀ c d : ℝ, d ∈ P.dom → d ≤ c → c ≤ P.maxConsumption → m * (c - d) ≤ P.u c - P.u d)
    (hcap : assetFloor + 4 * (P.discount : ℝ)
        * (max |P.toExtended.rewardMin| |P.toExtended.rewardMax| / (1 - P.discount)) / m
      < assetCap)
    (z : Z) : ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) := by
  have hslices : ∀ n : ℕ, ConcaveSlices assetFloor assetCap
      ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact P.concaveSlices_bellman ih
  refine P.concaveOn_consumptionFn_of_crra hpc hγ0 hβ hu (fun n a ha z' => ?_) z
  have hb := P.policyOf_le_of_marginal_bound hpc (hslices n) hm hmarg ha z'
  have hn := P.norm_iterate_le n
  have h4 : (0 : ℝ) ≤ 4 * (P.discount : ℝ) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hn h4
  have hmono : 4 * (P.discount : ℝ) * ‖(P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)‖ / m
      ≤ 4 * (P.discount : ℝ) * (max |P.toExtended.rewardMin| |P.toExtended.rewardMax|
        / (1 - P.discount)) / m := by
    rw [div_le_div_iff₀ hm hm]; nlinarith [hstep, hm]
  linarith

end IncomeFluctuation

end LeanEconomics
