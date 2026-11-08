/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CornerEconomy
import LeanEconomics.KrusellSmith.Euler

/-!
# The corner policy is optimal

Milestone C2 of `CORNER_PLAN.md`. Along a price path `P` from `z₀`, with smooth utility `U`:

* **(Feas)** `CornerFeas`: labour income clears the floor plus the corner saving, strictly, at
  every node and employment state;
* **(Emp)** `CornerEmp`: for savers, marginal utility today at the cap is at most the discounted
  expected return times marginal utility tomorrow under the corner policy;
* **(Unemp)** `CornerUnemp`: for non-savers, marginal utility today at zero saving is at least
  that.

Then:

* `cornerValue_split`: the corner value is utility of corner consumption plus a function of the
  label alone;
* `utility_le_tangent`: concave utility lies below its tangent line;
* **`objective_le_corner`**: against its own value, the corner choice beats every feasible choice
  — by the tangent lines today and tomorrow, the gain from moving away from the corner is
  `(g − a) [u'(c) − β E R' u'(c')]`, which has the right sign by (Emp) or (Unemp);
* **`cornerValue_eq_valueFunction`** (verification) and **`policy_eq_cornerPolicy`**: the
  household's optimal policy is the corner policy.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (saver : E → Prop) [DecidablePred saver] (U : M.SmoothUtility)
  (z₀ : Z) (P : List Z → ℝ × ℝ)

variable (M) in
/-- **(Feas)**: labour income clears the floor plus the corner saving, strictly. -/
def CornerFeas : Prop :=
  ∀ (h : List Z) (e : E),
    M.consFloor + (cornerSave M saver e : ℝ)
      < M.wageAt z₀ P h * M.efficiency e - M.returnAt z₀ P h * M.borrowLimit

/-- The state reached from `s` after the shock `ze`, under the corner policy. -/
noncomputable def cornerNext (s : M.State) (ze : Z × E) : M.State :=
  (M.clampAssets (cornerPolicy M saver s), ⟨ze.2, ze.1 :: s.2.node⟩)

/-- The discounted expected return-weighted marginal utility tomorrow under the corner policy. -/
noncomputable def cornerRHS (s : M.State) : ℝ :=
  M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, cornerPolicy M saver s)
    * M.returnAt z₀ P (ze.1 :: s.2.node)
    * U.du (M.cash z₀ P (cornerNext saver s ze) - cornerPolicy M saver (cornerNext saver s ze))

/-- **(Emp)**: saving the cap is optimal for savers. -/
def CornerEmp : Prop :=
  ∀ s : M.State, saver s.2.idio →
    U.du (M.cash z₀ P s - cornerPolicy M saver s) ≤ cornerRHS saver U z₀ P s

/-- **(Unemp)**: saving nothing is optimal for non-savers. -/
def CornerUnemp : Prop :=
  ∀ s : M.State, ¬ saver s.2.idio →
    cornerRHS saver U z₀ P s ≤ U.du (M.cash z₀ P s - cornerPolicy M saver s)

variable {saver U z₀ P}

omit [DecidablePred saver] in
theorem wage_le_cash (s : M.State) :
    M.wageAt z₀ P s.2.node * M.efficiency s.2.idio - M.returnAt z₀ P s.2.node * M.borrowLimit
      ≤ M.cash z₀ P s := by
  have := mul_nonneg (M.returnAt_nonneg z₀ P s.2.node) s.1.2.1
  simp only [cash]
  linarith

/-- Under (Feas), corner consumption is strictly above the floor. -/
theorem floor_lt_cornerCons (hF : CornerFeas M saver z₀ P) (s : M.State) :
    M.consFloor < M.cash z₀ P s - cornerPolicy M saver s := by
  have := hF s.2.node s.2.idio
  have := wage_le_cash (z₀ := z₀) (P := P) s
  change M.consFloor < M.cash z₀ P s - (cornerSave M saver s.2.idio : ℝ)
  linarith

/-- Under (Feas), the corner policy is feasible. -/
theorem cornerPolicy_mem_feasible (hF : CornerFeas M saver z₀ P) (s : M.State) :
    cornerPolicy M saver s ∈ (M.household z₀ P).feasible s := by
  refine ⟨(cornerSave M saver s.2.idio).2.1, le_min (cornerSave M saver s.2.idio).2.2 ?_⟩
  have := floor_lt_cornerCons hF s
  linarith

/-- **Concave utility lies below its tangent line.** -/
theorem utility_le_tangent {x y : ℝ} (hx : M.consFloor ≤ x) (hy : M.consFloor < y) :
    M.utility x ≤ M.utility y + U.du y * (x - y) := by
  rcases le_total y x with hyx | hxy
  · have := U.sub_le hy hyx
    linarith
  · have := U.le_sub hx hy hxy
    linarith

variable (M) in
/-- The reference state at a label. -/
noncomputable def refState (l : Label Z E) : M.State := (⟨0, le_rfl, M.assetCap_pos.le⟩, l)

/-- **The corner value is utility of corner consumption plus a function of the label.** -/
theorem cornerValue_split (hF : CornerFeas M saver z₀ P) (t : M.State) :
    cornerValue saver z₀ P t
      = M.utility (M.cash z₀ P t - cornerPolicy M saver t)
        + (cornerValue saver z₀ P (refState M t.2)
          - M.utility (M.cash z₀ P (refState M t.2) - cornerPolicy M saver (refState M t.2))) := by
  have h := cornerValue_sub_reward saver z₀ P (s := t) (s' := refState M t.2) rfl
  rw [M.reward_eq_of_mem_feasible z₀ P (cornerPolicy_mem_feasible hF t),
    M.reward_eq_of_mem_feasible z₀ P (cornerPolicy_mem_feasible hF _)] at h
  linarith

/-- **Against its own value, the corner choice beats every feasible choice.** -/
theorem objective_le_corner (hF : CornerFeas M saver z₀ P) (hE : CornerEmp saver U z₀ P)
    (hU : CornerUnemp saver U z₀ P) (s : M.State) (a : ℝ)
    (ha : a ∈ (M.household z₀ P).feasible s) :
    (M.household z₀ P).objective (cornerValue saver z₀ P) s a
      ≤ (M.household z₀ P).objective (cornerValue saver z₀ P) s (cornerPolicy M saver s) := by
  set g := cornerPolicy M saver s with hg
  have hgF := cornerPolicy_mem_feasible hF s
  have haI := M.mem_Icc_of_mem_feasible z₀ P ha
  have hgI := M.mem_Icc_of_mem_feasible z₀ P hgF
  rw [M.objective_eq z₀ P _ ha, M.objective_eq z₀ P _ hgF]
  -- today
  have hxa : M.consFloor ≤ M.cash z₀ P s - a := le_sub_comm.1 (ha.2.trans (min_le_right _ _))
  have hyg := floor_lt_cornerCons hF s
  have htoday := utility_le_tangent (U := U) hxa hyg
  -- tomorrow, for each shock
  have hnext : ∀ ze : Z × E,
      cornerValue saver z₀ P (M.clampAssets a, ⟨ze.2, ze.1 :: s.2.node⟩)
        - cornerValue saver z₀ P (M.clampAssets g, ⟨ze.2, ze.1 :: s.2.node⟩)
        ≤ (a - g) * M.returnAt z₀ P (ze.1 :: s.2.node)
          * U.du (M.cash z₀ P (cornerNext saver s ze)
            - cornerPolicy M saver (cornerNext saver s ze)) := by
    intro ze
    set l : Label Z E := ⟨ze.2, ze.1 :: s.2.node⟩
    rw [cornerValue_split hF (M.clampAssets a, l), cornerValue_split hF (M.clampAssets g, l)]
    have hca := M.cash_clampAssets z₀ P haI l
    have hcg := M.cash_clampAssets z₀ P hgI l
    have hpa : cornerPolicy M saver (M.clampAssets a, l)
        = cornerPolicy M saver (cornerNext saver s ze) := rfl
    have hpg : cornerPolicy M saver (M.clampAssets g, l)
        = cornerPolicy M saver (cornerNext saver s ze) := rfl
    have hx : M.consFloor
        ≤ M.cash z₀ P (M.clampAssets a, l) - cornerPolicy M saver (M.clampAssets a, l) :=
      (floor_lt_cornerCons hF _).le
    have hy := floor_lt_cornerCons hF (M.clampAssets g, l)
    have ht := utility_le_tangent (U := U) hx hy
    have hdiff : (M.cash z₀ P (M.clampAssets a, l) - cornerPolicy M saver (M.clampAssets a, l))
        - (M.cash z₀ P (M.clampAssets g, l) - cornerPolicy M saver (M.clampAssets g, l))
        = (a - g) * M.returnAt z₀ P (ze.1 :: s.2.node) := by
      rw [hca, hcg, hpa, hpg]
      ring
    have hn : cornerNext saver s ze = (M.clampAssets g, l) := rfl
    rw [hn]
    rw [hdiff] at ht
    linarith
  -- combine
  have hβ : 0 ≤ M.discount := M.discount_pos.le
  have hsum : ∑ ze : Z × E, M.shockProb z₀ ze (s, a)
        * cornerValue saver z₀ P (M.clampAssets a, ⟨ze.2, ze.1 :: s.2.node⟩)
      ≤ ∑ ze : Z × E, M.shockProb z₀ ze (s, g)
        * cornerValue saver z₀ P (M.clampAssets g, ⟨ze.2, ze.1 :: s.2.node⟩)
        + (a - g) * ∑ ze : Z × E, M.shockProb z₀ ze (s, g)
          * M.returnAt z₀ P (ze.1 :: s.2.node)
          * U.du (M.cash z₀ P (cornerNext saver s ze)
            - cornerPolicy M saver (cornerNext saver s ze)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ze _ => ?_
    have hp : M.shockProb z₀ ze (s, a) = M.shockProb z₀ ze (s, g) := rfl
    have hp0 : 0 ≤ M.shockProb z₀ ze (s, g) :=
      mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _)
    rw [hp]
    have := mul_le_mul_of_nonneg_left (hnext ze) hp0
    nlinarith
  have hR : (a - g) * cornerRHS saver U z₀ P s
      = M.discount * ((a - g) * ∑ ze : Z × E, M.shockProb z₀ ze (s, g)
          * M.returnAt z₀ P (ze.1 :: s.2.node)
          * U.du (M.cash z₀ P (cornerNext saver s ze)
            - cornerPolicy M saver (cornerNext saver s ze))) := by
    simp only [cornerRHS]
    ring
  -- the sign of `(g − a) (u'(c) − RHS)`
  have hsign : (g - a) * (U.du (M.cash z₀ P s - g) - cornerRHS saver U z₀ P s) ≤ 0 := by
    by_cases hs : saver s.2.idio
    · have hgv : g = M.assetCap := by
        simp [hg, cornerPolicy, cornerSave_val, hs]
      have h1 : 0 ≤ g - a := by rw [hgv]; exact sub_nonneg.2 haI.2
      have h2 := hE s hs
      exact mul_nonpos_of_nonneg_of_nonpos h1 (sub_nonpos.2 h2)
    · have hgv : g = 0 := by
        simp [hg, cornerPolicy, cornerSave_val, hs]
      have h1 : g - a ≤ 0 := by rw [hgv]; linarith [haI.1]
      have h2 := hU s hs
      exact mul_nonpos_of_nonpos_of_nonneg h1 (sub_nonneg.2 h2)
  have hsum' := mul_le_mul_of_nonneg_left hsum hβ
  nlinarith [hsum', htoday, hsign, hR]

/-- **Verification**: the corner value is the value function. -/
theorem cornerValue_eq_valueFunction (hF : CornerFeas M saver z₀ P) (hE : CornerEmp saver U z₀ P)
    (hU : CornerUnemp saver U z₀ P) :
    cornerValue saver z₀ P = (M.household z₀ P).valueFunction :=
  StochasticDynamicProgram.policyValue_eq_valueFunction (cornerPolicy_mem_feasible hF)
    (objective_le_corner hF hE hU)

/-- **The household's optimal policy is the corner policy.** -/
theorem policy_eq_cornerPolicy (hF : CornerFeas M saver z₀ P) (hE : CornerEmp saver U z₀ P)
    (hU : CornerUnemp saver U z₀ P) (s : M.State) :
    M.policy z₀ P s = cornerPolicy M saver s := by
  refine M.optimal_saving_unique z₀ P (M.policy_mem z₀ P s) (cornerPolicy_mem_feasible hF s)
    (M.policy_optimal z₀ P s).symm ?_
  exact StochasticDynamicProgram.bellman_eq_objective_policy (cornerPolicy_mem_feasible hF)
    (objective_le_corner hF hE hU) s

end KSModel

end KrusellSmith

end LeanEconomics
