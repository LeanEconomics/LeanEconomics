/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationConsumption

/-!
# Concavity of the consumption function as a closed class

`IncomeFluctuationConsumption` showed that concavity of the consumption function cannot follow
from concavity of `u` and of the value function, and that it is a statement about the FIXED
POINT. This file supplies the machinery that statements about the fixed point need, and reduces
Carroll and Kimball (1996) to its single inductive step.

The pattern is the one used four times already — monotonicity, concavity, Lipschitz bounds and
increasing differences — but with one new difficulty. Those four are properties OF the value
function, closed in sup norm by `isClosed_concaveOn` and its relatives. Concavity of the
consumption function is a property of the value function's ARGMAX, and nothing says offhand
that an argmax survives a uniform limit. So the closure step has to be proved rather than
quoted, and that is what `tendsto_policyOf` does: along a uniformly convergent sequence of
continuation values the optimal actions converge, because a cluster point of the maximisers is
a maximiser of the limit and the maximiser of the limit is unique.

That gives `concaveOn_consumptionFn_of_preserves`: if the Bellman operator carries a concave
consumption function to a concave consumption function, the fixed point's consumption function
is concave. The iteration starts from `0`, whose consumption function is `resources`, affine on
the asset region — `policyOf_zero`, an agent with no future eats everything.

## What is left, and what it costs

The hypothesis `hT` is the whole of Carroll and Kimball. It is not proved here and it is not
cheap. On paper the argument runs through second derivatives: risk tolerances ADD across the
optimisation, `T_V(m) = T_u(c) + T_W(m - c)`, and the consumption function is concave exactly
when `T_V' ≥ T_u'`, which propagates from continuation to value provided `u` is HARA so that
`T_u' `is constant. Two of those steps are out of reach at present — the value function is not
known to be twice differentiable (we have one-sided first derivatives, conditionally, from
`IncomeFluctuationEnvelope`), and the propagation through the expectation over income states is
Kimball's risk-tolerance aggregation theorem, which is a body of theory in its own right.

**`hT` is not merely unproved: it is FALSE at this generality.** Toda (2021) shows that under
regularity conditions HARA is NECESSARY for the consumption function to be concave, and the
structure here assumes of `u` only that it is strictly concave. So no proof of `hT` can exist
against `IncomeFluctuation` as it stands; the structure would first have to be specialised to
HARA — in practice to CRRA, which is what Light's published version (2020) assumes anyway. The
theorem below is therefore conditional in the strong sense, and the hypothesis is where the
parametric commitment of the whole uniqueness argument is concentrated.

So this file does not claim Carroll and Kimball. It claims that everything AROUND it is done:
the single step `hT` is now the only thing standing between the development and Light (2018)
Theorem 1, whose remaining ingredients — `mul_marginal_le_of_scale`, `consumptionFn_mono`,
`RelativeRiskAversionLeOne` — are all in place.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ}
variable (P : IncomeFluctuation Z assetCap)

/-- Continuation values that are concave along each asset slice. This is what makes the optimal
action unique, and it is preserved by the Bellman operator. -/
def ConcaveSlices (assetCap : ℝ) (v : (ℝ × Z) →ᵇ ℝ) : Prop :=
  ∀ z : Z, ConcaveOn ℝ (Icc 0 assetCap) fun a => v (a, z)

omit [Fintype Z] [Nonempty Z] [DiscreteTopology Z] in
theorem concaveSlices_zero : ConcaveSlices assetCap (0 : (ℝ × Z) →ᵇ ℝ) :=
  fun _ => ⟨convex_Icc _ _, fun _ _ _ _ _ _ _ _ _ => by simp⟩

theorem concaveSlices_bellman {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetCap v) :
    ConcaveSlices assetCap (P.toExtended.bellman v) :=
  fun z => P.concaveOn_bellman v hv z

theorem concaveSlices_valueFunction : ConcaveSlices assetCap P.toExtended.valueFunction :=
  P.concaveOn_valueFunction

/-! ### The optimal action of an arbitrary continuation

`IncomeFluctuation` gives uniqueness of the optimal action at the value function. The closure
argument needs it along the whole approximating sequence, so the same proof is run with any
continuation whose slices are concave. -/

/-- **The optimal action is unique** for any continuation with concave slices. -/
theorem optimal_action_unique_of_concaveSlices {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetCap v)
    {s : ℝ × Z} (hs : s.1 ∈ Icc 0 assetCap) {a₀ a₁ : ℝ}
    (h₀ : a₀ ∈ P.toExtended.feasible s) (h₁ : a₁ ∈ P.toExtended.feasible s)
    (hm₀ : P.toExtended.objectiveE v s a₀ = ((P.toExtended.bellmanFn v s : ℝ) : EReal))
    (hm₁ : P.toExtended.objectiveE v s a₁ = ((P.toExtended.bellmanFn v s : ℝ) : EReal)) :
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
  have hexp : (1 / 2 : ℝ) * (∑ z', P.transitionMatrix s.2 z' * v (a₀, z'))
      + (1 / 2 : ℝ) * (∑ z', P.transitionMatrix s.2 z' * v (a₁, z'))
      ≤ ∑ z', P.transitionMatrix s.2 z' * v ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁, z') := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z' _ => ?_
    have hvz := (hv z').2 (P.feasible_subset_region h₀) (P.feasible_subset_region h₁)
      hhalf.le hhalf.le hsum
    simp only [smul_eq_mul] at hvz
    nlinarith [P.transitionMatrix_nonneg s.2 z']
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hexp hβ
  simp only [smul_eq_mul] at hu
  have hle := P.toExtended.le_bellmanFn v hmem
  have hobj : P.toExtended.objectiveE v s ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁)
      = ((P.u (P.consumption s ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁))
          + P.discount * ∑ z', P.transitionMatrix s.2 z'
              * v ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁, z') : ℝ) : EReal) := by
    rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_coe hs hmem hcm, ← EReal.coe_add]
    rfl
  rw [hobj] at hle
  have hle' : P.u (P.consumption s ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁))
      + P.discount * ∑ z', P.transitionMatrix s.2 z'
          * v ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁, z')
      ≤ P.toExtended.bellmanFn v s := by exact_mod_cast hle
  rw [hcmid] at hle'
  linarith

/-- The optimal saving choice under an arbitrary continuation. At the value function this is
definitionally `policy`. -/
noncomputable def policyOf (v : (ℝ × Z) →ᵇ ℝ) (s : ℝ × Z) : ℝ :=
  Classical.choose (P.toExtended.exists_optimal_action v s)

theorem policyOf_mem (v : (ℝ × Z) →ᵇ ℝ) (s : ℝ × Z) :
    P.policyOf v s ∈ P.toExtended.feasible s :=
  (Classical.choose_spec (P.toExtended.exists_optimal_action v s)).1

theorem policyOf_optimal (v : (ℝ × Z) →ᵇ ℝ) (s : ℝ × Z) :
    P.toExtended.objectiveE v s (P.policyOf v s)
      = ((P.toExtended.bellmanFn v s : ℝ) : EReal) :=
  (Classical.choose_spec (P.toExtended.exists_optimal_action v s)).2

theorem policyOf_valueFunction : P.policyOf P.toExtended.valueFunction = P.policy := rfl

/-- The consumption function implied by an arbitrary continuation. -/
noncomputable def consumptionFnOf (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (a : ℝ) : ℝ :=
  P.consumption (a, z) (P.policyOf v (a, z))

theorem consumptionFnOf_valueFunction :
    P.consumptionFnOf P.toExtended.valueFunction = P.consumptionFn := rfl

/-! ### The agent with no future eats everything

The iteration starts at the zero continuation, where saving buys nothing and the optimal plan
is to consume all cash on hand. Its consumption function is `resources`, affine on the asset
region, so the induction has a base. -/

/-- Saving more cannot raise the reward: consumption falls, and utility rises with it. -/
theorem reward_antitone {s : ℝ × Z} (hs : s.1 ∈ Icc 0 assetCap) {x y : ℝ}
    (hx : x ∈ P.toExtended.feasible s) (hy : y ∈ P.toExtended.feasible s) (hxy : x ≤ y) :
    P.toExtended.reward (s, y) ≤ P.toExtended.reward (s, x) := by
  rcases le_or_gt (P.consumption s y) 0 with h | h
  · have hb : P.toExtended.reward (s, y) = ⊥ := by
      by_contra hne
      exact absurd (P.consumption_pos_of_ne_bot hne) (not_lt.mpr h)
    rw [hb]; exact bot_le
  · have hcx : 0 < P.consumption s x := by
      simp only [consumption] at h ⊢; linarith
    rw [P.reward_eq_coe hs hx hcx, P.reward_eq_coe hs hy h, EReal.coe_le_coe_iff]
    exact P.monotoneOn_u (mem_Ioi.mpr h) (mem_Ioi.mpr hcx)
      (by simp only [consumption]; linarith)

/-- **With nothing to gain from saving, the household saves nothing.** -/
theorem policyOf_zero {s : ℝ × Z} (hs : s.1 ∈ Icc 0 assetCap) :
    P.policyOf 0 s = 0 := by
  have hmem0 : (0 : ℝ) ∈ P.toExtended.feasible s := ⟨le_rfl, le_max_left _ _⟩
  have hc0 : 0 < P.consumption s 0 := by
    simpa only [consumption, sub_zero] using P.resources_pos s
  have hobj : ∀ a : ℝ, P.toExtended.objectiveE (0 : (ℝ × Z) →ᵇ ℝ) s a
      = P.toExtended.reward (s, a) := by
    intro a
    simp [ExtendedStochasticProgram.objectiveE, ExtendedStochasticProgram.expect]
  have hle : ∀ a ∈ P.toExtended.feasible s,
      P.toExtended.objectiveE (0 : (ℝ × Z) →ᵇ ℝ) s a ≤ ((P.u (P.consumption s 0) : ℝ) : EReal) := by
    intro a ha
    rw [hobj a, ← P.reward_eq_coe hs hmem0 hc0]
    exact P.reward_antitone hs hmem0 ha ha.1
  have hb := P.toExtended.bellmanFn_le (0 : (ℝ × Z) →ᵇ ℝ) hle
  have hopt : P.toExtended.objectiveE (0 : (ℝ × Z) →ᵇ ℝ) s 0
      = ((P.toExtended.bellmanFn (0 : (ℝ × Z) →ᵇ ℝ) s : ℝ) : EReal) := by
    refine le_antisymm (P.toExtended.le_bellmanFn _ hmem0) ?_
    rw [hobj 0, P.reward_eq_coe hs hmem0 hc0, EReal.coe_le_coe_iff]
    exact hb
  exact optimal_action_unique_of_concaveSlices P concaveSlices_zero hs (P.policyOf_mem _ _) hmem0
    (P.policyOf_optimal _ _) hopt

theorem consumptionFnOf_zero {z : Z} {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.consumptionFnOf 0 z a = P.income z + (1 + P.interest) * a := by
  rw [consumptionFnOf, P.policyOf_zero (s := (a, z)) ha]
  simp only [consumption, resources, sub_zero, max_eq_right ha.1]

theorem concaveOn_consumptionFnOf_zero (z : Z) :
    ConcaveOn ℝ (Icc 0 assetCap) (P.consumptionFnOf 0 z) := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  have hm : θ • x + φ • y ∈ Icc (0 : ℝ) assetCap := convex_Icc _ _ hx hy hθ hφ hθφ
  simp only [smul_eq_mul] at hm ⊢
  rw [P.consumptionFnOf_zero hx, P.consumptionFnOf_zero hy, P.consumptionFnOf_zero hm]
  have hφ' : φ = 1 - θ := by linarith
  subst hφ'
  exact le_of_eq (by ring)

/-! ### The closure step: optimal actions survive a uniform limit

This is what the four earlier closed-class arguments got for free from `isClosed_concaveOn`.
Concavity of the consumption function is a property of the ARGMAX, so closure has to be proved:
a cluster point of maximisers of `vₙ` is a maximiser of the limit, and the maximiser of the
limit is unique. -/

theorem abs_expect_sub_le_norm (v w : (ℝ × Z) →ᵇ ℝ) (p : (ℝ × Z) × ℝ) :
    |P.toExtended.expect v p - P.toExtended.expect w p| ≤ ‖v - w‖ := by
  have h : P.toExtended.expect v p - P.toExtended.expect w p
      = P.toExtended.expect (v - w) p := by
    simp only [ExtendedStochasticProgram.expect, ← Finset.sum_sub_distrib,
      BoundedContinuousFunction.coe_sub, Pi.sub_apply, mul_sub]
  rw [h]
  exact P.toExtended.abs_expect_le _ _

theorem tendsto_expect {v : ℕ → (ℝ × Z) →ᵇ ℝ} {w : (ℝ × Z) →ᵇ ℝ} (hv : Tendsto v atTop (𝓝 w))
    {x : ℕ → ℝ} {y : ℝ} (hx : Tendsto x atTop (𝓝 y)) (s : ℝ × Z) :
    Tendsto (fun n => P.toExtended.expect (v n) (s, x n)) atTop
      (𝓝 (P.toExtended.expect w (s, y))) := by
  have hnorm : Tendsto (fun n => ‖v n - w‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hv
  have hcont : Tendsto (fun n => P.toExtended.expect w (s, x n)) atTop
      (𝓝 (P.toExtended.expect w (s, y))) :=
    ((P.toExtended.continuous_expect w).tendsto _).comp (tendsto_const_nhds.prodMk_nhds hx)
  have hdiff : Tendsto (fun n => P.toExtended.expect (v n) (s, x n)
      - P.toExtended.expect w (s, x n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hnorm
    simpa only [Real.norm_eq_abs] using P.abs_expect_sub_le_norm (v n) w (s, x n)
  simpa using hdiff.add hcont

theorem tendsto_objectiveE {v : ℕ → (ℝ × Z) →ᵇ ℝ} {w : (ℝ × Z) →ᵇ ℝ} (hv : Tendsto v atTop (𝓝 w))
    {x : ℕ → ℝ} {y : ℝ} (hx : Tendsto x atTop (𝓝 y)) (s : ℝ × Z) :
    Tendsto (fun n => P.toExtended.objectiveE (v n) s (x n)) atTop
      (𝓝 (P.toExtended.objectiveE w s y)) := by
  have hr : Tendsto (fun n => P.toExtended.reward (s, x n)) atTop
      (𝓝 (P.toExtended.reward (s, y))) :=
    (P.toExtended.reward.continuous.tendsto _).comp (tendsto_const_nhds.prodMk_nhds hx)
  have he : Tendsto (fun n =>
      ((P.toExtended.discount * P.toExtended.expect (v n) (s, x n) : ℝ) : EReal)) atTop
      (𝓝 ((P.toExtended.discount * P.toExtended.expect w (s, y) : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp
      (tendsto_const_nhds.mul (P.tendsto_expect hv hx s))
  exact Filter.Tendsto.comp
    (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))
    (hr.prodMk_nhds he)

/-- **Optimal actions survive a uniform limit.** -/
theorem tendsto_policyOf {v : ℕ → (ℝ × Z) →ᵇ ℝ} {w : (ℝ × Z) →ᵇ ℝ}
    (hv : Tendsto v atTop (𝓝 w)) (hw : ConcaveSlices assetCap w)
    {s : ℝ × Z} (hs : s.1 ∈ Icc 0 assetCap) :
    Tendsto (fun n => P.policyOf (v n) s) atTop (𝓝 (P.policyOf w s)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨L, hLK, φ, hφ, hφlim⟩ := (P.toExtended.isCompact_feasible s).tendsto_subseq
    (x := fun i => P.policyOf (v (ns i)) s) (fun i => P.policyOf_mem _ _)
  have hv' : Tendsto (fun i => v (ns (φ i))) atTop (𝓝 w) :=
    hv.comp (hns.comp hφ.tendsto_atTop)
  have hlim' : Tendsto (fun i => P.policyOf (v (ns (φ i))) s) atTop (𝓝 L) := hφlim
  -- every feasible action is beaten by the limit of the maximisers
  have key : ∀ x ∈ P.toExtended.feasible s,
      P.toExtended.objectiveE w s x ≤ P.toExtended.objectiveE w s L := by
    intro x hx
    refine le_of_tendsto_of_tendsto (P.tendsto_objectiveE hv' tendsto_const_nhds s)
      (P.tendsto_objectiveE hv' hlim' s) (Eventually.of_forall fun i => ?_)
    have hle := P.toExtended.le_bellmanFn (v (ns (φ i))) hx
    rwa [← P.policyOf_optimal (v (ns (φ i))) s] at hle
  have hLopt : P.toExtended.objectiveE w s L = ((P.toExtended.bellmanFn w s : ℝ) : EReal) := by
    refine le_antisymm (P.toExtended.le_bellmanFn w hLK) ?_
    rw [← P.policyOf_optimal w s]
    exact key _ (P.policyOf_mem w s)
  have hLeq : L = P.policyOf w s :=
    optimal_action_unique_of_concaveSlices P hw hs hLK (P.policyOf_mem w s) hLopt
      (P.policyOf_optimal w s)
  exact ⟨φ, by rw [← hLeq]; exact hlim'⟩

/-! ### Carroll and Kimball, reduced to one step -/

/-- **The consumption function of the fixed point is concave whenever the Bellman operator
preserves concavity of the consumption function.** Everything except the hypothesis `hT` is
discharged: the base case, the induction, the limit.

`hT` is Carroll and Kimball (1996) — see the module docstring for what proving it would take. -/
theorem concaveOn_consumptionFn_of_preserves
    (hT : ∀ v : (ℝ × Z) →ᵇ ℝ, ConcaveSlices assetCap v →
      (∀ z, ConcaveOn ℝ (Icc 0 assetCap) (P.consumptionFnOf v z)) →
      ∀ z, ConcaveOn ℝ (Icc 0 assetCap) (P.consumptionFnOf (P.toExtended.bellman v) z))
    (z : Z) : ConcaveOn ℝ (Icc 0 assetCap) (P.consumptionFn z) := by
  set T := P.toExtended.bellman with hTdef
  have hslices : ∀ n : ℕ, ConcaveSlices assetCap (T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact P.concaveSlices_bellman ih
  have hcons : ∀ n : ℕ, ∀ z, ConcaveOn ℝ (Icc 0 assetCap)
      (P.consumptionFnOf (T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z) := by
    intro n
    induction n with
    | zero => exact P.concaveOn_consumptionFnOf_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact hT _ (hslices k) ih
  have hlim : Tendsto (fun n => T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) atTop (𝓝 P.toExtended.valueFunction) :=
    P.toExtended.tendsto_iterate_valueFunction 0
  have hpt : ∀ a ∈ Icc (0 : ℝ) assetCap,
      Tendsto (fun n => P.consumptionFnOf (T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a) atTop
        (𝓝 (P.consumptionFn z a)) := by
    intro a ha
    have hp := P.tendsto_policyOf hlim P.concaveSlices_valueFunction (s := (a, z)) ha
    have he : P.consumptionFn z a
        = P.resources (a, z) - P.policyOf P.toExtended.valueFunction (a, z) := rfl
    rw [he]
    simpa only [consumptionFnOf, consumption] using tendsto_const_nhds.sub hp
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  have hm : θ • x + φ • y ∈ Icc (0 : ℝ) assetCap := convex_Icc _ _ hx hy hθ hφ hθφ
  refine le_of_tendsto_of_tendsto
    (((hpt x hx).const_smul θ).add ((hpt y hy).const_smul φ)) (hpt _ hm)
    (Eventually.of_forall fun n => (hcons n z).2 hx hy hθ hφ hθφ)

/-! ### The asset cap obstructs concavity, and `hT` is stated too strongly

Attempting `hT` for log utility — the one CRRA specification this structure admits with Light's
condition, by `crra_pinch` — turns up an obstruction that has nothing to do with Carroll and
Kimball and everything to do with the cap.

Where the cap binds the household cannot save more, so every extra unit of resources is consumed
and the consumption function has slope exactly `1 + r`. Below, wherever it saves strictly more,
the slope is strictly less. Increments therefore RISE across the kink, which concavity forbids.
`not_concaveOn_consumptionFn_of_cap_binds` proves it.

So `hT` as stated is not merely hard, it is FALSE for any calibration whose cap binds, quite
apart from the HARA question. Concavity of the consumption function on `Icc 0 assetCap` needs the
cap to be SLACK — above the natural asset bound, so that the household never wants to save that
much. That is exactly what `exists_decline_of_consumption_lower_bound` is about, and by
`one_sub_mpc_mul_of_asymptotic` the condition behind it is `β (1 + r) < 1`.

Which ties the two halves of the development together: the imposed `assetCap`, so far a
bookkeeping device for compactness, has to be justified economically before the Carroll–Kimball
hypothesis can even be true. -/

/-- Once the cap binds it binds for ever after, since the policy is monotone and capped. -/
theorem policy_eq_assetCap_of_le {y w : ℝ} {z : Z} (hy : y ∈ Icc 0 assetCap)
    (hw : w ∈ Icc 0 assetCap) (hyw : y ≤ w) (h : P.policy (y, z) = assetCap) :
    P.policy (w, z) = assetCap := by
  exact le_antisymm (P.policy_mem_region _).2
    (le_trans (le_of_eq h.symm) (P.policy_mono hy hw hyw))

/-- **A binding asset cap rules out a concave consumption function.** -/
theorem not_concaveOn_consumptionFn_of_cap_binds {x y w : ℝ} {z : Z}
    (hx : x ∈ Icc (0 : ℝ) assetCap) (hw : w ∈ Icc (0 : ℝ) assetCap)
    (hxy : x < y) (hyw : y < w)
    (hrise : P.policy (x, z) < P.policy (y, z))
    (hflat : P.policy (y, z) = P.policy (w, z)) :
    ¬ ConcaveOn ℝ (Icc 0 assetCap) (P.consumptionFn z) := by
  intro hconc
  have hy : y ∈ Icc (0 : ℝ) assetCap := ⟨le_trans hx.1 hxy.le, le_trans hyw.le hw.2⟩
  have h := hconc.slope_anti_adjacent hx hw hxy hyw
  have hres : ∀ a ∈ Icc (0 : ℝ) assetCap,
      P.resources (a, z) = P.income z + (1 + P.interest) * a :=
    fun a ha => by simp only [resources, max_eq_right ha.1]
  simp only [consumptionFn, consumption, hres x hx, hres y hy, hres w hw] at h
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at h
  nlinarith [h, hrise, hflat, sub_pos.mpr hxy, sub_pos.mpr hyw]

end IncomeFluctuation

end LeanEconomics
