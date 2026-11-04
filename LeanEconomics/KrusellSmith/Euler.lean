/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Policy
import Mathlib.Analysis.Convex.Deriv

/-!
# The Euler equation of the Krusell–Smith household, with corners

The first step of the uniqueness argument by contraction (`UNIQUENESS_PLAN.md`, milestone M1):
along a path of capital and labour, the household's optimal saving satisfies the Euler equation
at every node, as an inequality at the borrowing limit and at the asset cap.

The derivation needs no differentiability of the value function. As in
`IncomeFluctuation.bellman_sub_le` / `bellman_sub_ge`, the value at a richer state is sandwiched
by copying plans:

* the richer household can save what the poorer one saves and consume the difference
  (`valueFunction_sub_ge`);
* the poorer household can save what the richer one saves, if the floor allows
  (`valueFunction_sub_le`).

Comparing the optimum with saving a little more (`euler_ge`, unless saving is at the cap) or a
little less (`euler_le`, unless it is at the borrowing limit), and letting the deviation shrink,
gives

  `β E[R' u'(c')] ≤ u'(c)` and `u'(c) ≤ β E[R' u'(c')]`

respectively, where primes are next period, at the child nodes, with assets equal to today's
saving. Only continuity of `u'` is used in the limit.

**Hypotheses.** `SmoothUtility`: utility has a derivative `du` above the consumption floor, and
`du` is continuous there. `Slack`: optimal consumption is strictly above the floor along the path
(in `KSInada` it is at least `floorLevel`, twice the imposed floor).
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **Smooth utility**: a derivative above the consumption floor, continuous there. -/
structure SmoothUtility where
  /-- Marginal utility. -/
  du : ℝ → ℝ
  hasDerivAt : ∀ c, M.consFloor < c → HasDerivAt M.utility (du c) c
  continuousOn : ContinuousOn du (Ioi M.consFloor)

variable {M} (U : M.SmoothUtility)

namespace SmoothUtility

/-- Utility rises by at most marginal utility at the lower point, times the step. -/
theorem sub_le {x y : ℝ} (hy : M.consFloor < y) (hyx : y ≤ x) :
    M.utility x - M.utility y ≤ (x - y) * U.du y := by
  rcases hyx.lt_or_eq with hlt | rfl
  · have h := M.strictConcaveOn_utility.concaveOn.slope_le_of_hasDerivAt (mem_Ici.2 hy.le)
      (mem_Ici.2 (hy.le.trans hlt.le)) hlt (U.hasDerivAt y hy)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hlt)] at h
    linarith
  · simp

/-- Utility rises by at least marginal utility at the upper point, times the step. -/
theorem le_sub {x y : ℝ} (hy : M.consFloor ≤ y) (hx : M.consFloor < x) (hyx : y ≤ x) :
    (x - y) * U.du x ≤ M.utility x - M.utility y := by
  rcases hyx.lt_or_eq with hlt | rfl
  · have h := M.strictConcaveOn_utility.concaveOn.le_slope_of_hasDerivAt (mem_Ici.2 hy)
      (mem_Ici.2 hx.le) hlt (U.hasDerivAt x hx)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hlt)] at h
    linarith
  · simp

end SmoothUtility

variable (z₀ : Z) (K : List Z → ℝ × ℝ)

/-- Optimal consumption along the path `K` at the state `s`. -/
noncomputable def consumption (s : M.State) : ℝ := M.cash z₀ K s - M.policy z₀ K s

/-- **Slack**: optimal consumption is strictly above the floor at every state. -/
def Slack : Prop := ∀ s : M.State, M.consFloor < M.consumption z₀ K s

/-- The state at node `l` with assets `a`, clamped into `[0, assetCap]`. -/
noncomputable def stateAt (a : ℝ) (l : Label Z E) : M.State := (M.clampAssets a, l)

theorem cash_stateAt {a : ℝ} (ha : a ∈ Icc 0 M.assetCap) (l : Label Z E) :
    M.cash z₀ K (M.stateAt a l)
      = M.returnAt z₀ K l.node * a + M.wageAt z₀ K l.node * M.efficiency l.idio :=
  M.cash_clampAssets z₀ K ha l

theorem returnAt_nonneg (h : List Z) : 0 ≤ M.returnAt z₀ K h := M.grossReturn_nonneg _ _ _

/-- The value at a state, written through its optimal saving. -/
theorem valueFunction_eq (s : M.State) :
    (M.household z₀ K).valueFunction s
      = M.utility (M.consumption z₀ K s)
        + M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, M.policy z₀ K s)
            * (M.household z₀ K).valueFunction
                (M.clampAssets (M.policy z₀ K s), ⟨ze.2, ze.1 :: s.2.node⟩) := by
  have h := M.policy_optimal z₀ K s
  rw [(M.household z₀ K).bellman_valueFunction, M.objective_eq z₀ K _ (M.policy_mem z₀ K s)] at h
  exact h

/-- The value at a state is at least the objective of any feasible saving. -/
theorem objective_le_valueFunction' (s : M.State) {a : ℝ}
    (ha : a ∈ (M.household z₀ K).feasible s) :
    M.utility (M.cash z₀ K s - a)
        + M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, a)
            * (M.household z₀ K).valueFunction (M.clampAssets a, ⟨ze.2, ze.1 :: s.2.node⟩)
      ≤ (M.household z₀ K).valueFunction s := by
  have h := (M.household z₀ K).le_bellmanFn (M.household z₀ K).valueFunction ha
  rw [M.objective_eq z₀ K _ ha] at h
  change _ ≤ (M.household z₀ K).bellman _ s at h
  rwa [(M.household z₀ K).bellman_valueFunction] at h

theorem shockProb_eq (ze : Z × E) (s : M.State) (a b : ℝ) :
    M.shockProb z₀ ze (s, a) = M.shockProb z₀ ze (s, b) := rfl

theorem shockProb_stateAt (ze : Z × E) {a b : ℝ} (l : Label Z E) (c d : ℝ) :
    M.shockProb z₀ ze (M.stateAt a l, c) = M.shockProb z₀ ze (M.stateAt b l, d) := rfl

/-! ### Value sandwiches -/

/-- **Richer by `h`: at least the utility of consuming the extra cash**, keeping the poorer
household's saving. -/
theorem valueFunction_sub_ge {a h : ℝ} (ha : a ∈ Icc 0 M.assetCap) (hh : 0 ≤ h)
    (hah : a + h ≤ M.assetCap) (l : Label Z E) :
    M.utility (M.consumption z₀ K (M.stateAt a l) + M.returnAt z₀ K l.node * h)
        - M.utility (M.consumption z₀ K (M.stateAt a l))
      ≤ (M.household z₀ K).valueFunction (M.stateAt (a + h) l)
        - (M.household z₀ K).valueFunction (M.stateAt a l) := by
  have hah' : a + h ∈ Icc 0 M.assetCap := ⟨add_nonneg ha.1 hh, hah⟩
  set p := M.policy z₀ K (M.stateAt a l) with hp
  have hpm := M.policy_mem z₀ K (M.stateAt a l)
  have hcash : M.cash z₀ K (M.stateAt (a + h) l)
      = M.cash z₀ K (M.stateAt a l) + M.returnAt z₀ K l.node * h := by
    rw [M.cash_stateAt z₀ K hah' l, M.cash_stateAt z₀ K ha l]
    ring
  have hfeas : p ∈ (M.household z₀ K).feasible (M.stateAt (a + h) l) := by
    refine ⟨hpm.1, le_min (hpm.2.trans (min_le_left _ _)) ?_⟩
    have := hpm.2.trans (min_le_right _ _)
    rw [hcash]
    nlinarith [M.returnAt_nonneg z₀ K l.node]
  have h1 := M.objective_le_valueFunction' z₀ K (M.stateAt (a + h) l) hfeas
  have h2 := M.valueFunction_eq z₀ K (M.stateAt a l)
  rw [hcash] at h1
  have hsum : ∑ ze : Z × E, M.shockProb z₀ ze (M.stateAt (a + h) l, p)
        * (M.household z₀ K).valueFunction
            (M.clampAssets p, ⟨ze.2, ze.1 :: (M.stateAt (a + h) l).2.node⟩)
      = ∑ ze : Z × E, M.shockProb z₀ ze (M.stateAt a l, p)
        * (M.household z₀ K).valueFunction
            (M.clampAssets p, ⟨ze.2, ze.1 :: (M.stateAt a l).2.node⟩) :=
    rfl
  rw [hsum] at h1
  have hc : M.cash z₀ K (M.stateAt a l) + M.returnAt z₀ K l.node * h - p
      = M.consumption z₀ K (M.stateAt a l) + M.returnAt z₀ K l.node * h := by
    rw [consumption]
    ring
  rw [hc] at h1
  linarith

/-- **Richer by `h`: at most the utility lost by consuming `R h` less**, when the poorer
household can afford the richer one's saving above the floor. -/
theorem valueFunction_sub_le {a h : ℝ} (ha : a ∈ Icc 0 M.assetCap) (hh : 0 ≤ h)
    (hah : a + h ≤ M.assetCap) (l : Label Z E)
    (hfl : M.consFloor ≤ M.consumption z₀ K (M.stateAt (a + h) l) - M.returnAt z₀ K l.node * h) :
    (M.household z₀ K).valueFunction (M.stateAt (a + h) l)
        - (M.household z₀ K).valueFunction (M.stateAt a l)
      ≤ M.utility (M.consumption z₀ K (M.stateAt (a + h) l))
        - M.utility (M.consumption z₀ K (M.stateAt (a + h) l) - M.returnAt z₀ K l.node * h) := by
  have hah' : a + h ∈ Icc 0 M.assetCap := ⟨add_nonneg ha.1 hh, hah⟩
  set p := M.policy z₀ K (M.stateAt (a + h) l) with hp
  have hpm := M.policy_mem z₀ K (M.stateAt (a + h) l)
  have hcash : M.cash z₀ K (M.stateAt (a + h) l)
      = M.cash z₀ K (M.stateAt a l) + M.returnAt z₀ K l.node * h := by
    rw [M.cash_stateAt z₀ K hah' l, M.cash_stateAt z₀ K ha l]
    ring
  have hfeas : p ∈ (M.household z₀ K).feasible (M.stateAt a l) := by
    refine ⟨hpm.1, le_min (hpm.2.trans (min_le_left _ _)) ?_⟩
    have : M.consumption z₀ K (M.stateAt (a + h) l) = M.cash z₀ K (M.stateAt (a + h) l) - p := rfl
    rw [this, hcash] at hfl
    linarith
  have h1 := M.objective_le_valueFunction' z₀ K (M.stateAt a l) hfeas
  have h2 := M.valueFunction_eq z₀ K (M.stateAt (a + h) l)
  have hsum : ∑ ze : Z × E, M.shockProb z₀ ze (M.stateAt a l, p)
        * (M.household z₀ K).valueFunction (M.clampAssets p, ⟨ze.2, ze.1 :: (M.stateAt a l).2.node⟩)
      = ∑ ze : Z × E, M.shockProb z₀ ze (M.stateAt (a + h) l, p)
        * (M.household z₀ K).valueFunction
            (M.clampAssets p, ⟨ze.2, ze.1 :: (M.stateAt (a + h) l).2.node⟩) :=
    rfl
  rw [hsum] at h1
  have hc : M.cash z₀ K (M.stateAt a l) - p
      = M.consumption z₀ K (M.stateAt (a + h) l) - M.returnAt z₀ K l.node * h := by
    have : M.consumption z₀ K (M.stateAt (a + h) l) = M.cash z₀ K (M.stateAt (a + h) l) - p := rfl
    rw [this, hcash]
    ring
  rw [hc] at h1
  linarith

/-! ### The Euler inequalities -/

/-- The return-weighted expected marginal utility of next period's consumption when saving `a'`
at the state `s`: the right-hand side of the Euler equation, before discounting. -/
noncomputable def eulerRhs (s : M.State) (a' : ℝ) : ℝ :=
  ∑ ze : Z × E, M.shockProb z₀ ze (s, a') * M.returnAt z₀ K (ze.1 :: s.2.node)
    * U.du (M.consumption z₀ K (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩))

theorem shockProb_nonneg' (ze : Z × E) (p : M.State × ℝ) : 0 ≤ M.shockProb z₀ ze p :=
  mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _)

/-- `du` is continuous at every consumption level above the floor. -/
theorem SmoothUtility.continuousAt {c : ℝ} (hc : M.consFloor < c) : ContinuousAt U.du c :=
  U.continuousOn.continuousAt (Ioi_mem_nhds hc)

/-- The expected marginal value moves continuously when every child's consumption is shifted by
`R h`. -/
theorem tendsto_shifted (s : M.State) (a' : ℝ) (hsl : M.Slack z₀ K) (σ : ℝ) :
    Tendsto (fun h : ℝ => ∑ ze : Z × E, M.shockProb z₀ ze (s, a')
        * M.returnAt z₀ K (ze.1 :: s.2.node)
        * U.du (M.consumption z₀ K (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
          + σ * M.returnAt z₀ K (ze.1 :: s.2.node) * h))
      (𝓝[>] 0) (𝓝 (M.eulerRhs U z₀ K s a')) := by
  refine tendsto_finsetSum _ fun ze _ => ?_
  refine tendsto_const_nhds.mul ?_
  have hc := hsl (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
  have hlin : Tendsto (fun h : ℝ => M.consumption z₀ K (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
      + σ * M.returnAt z₀ K (ze.1 :: s.2.node) * h) (𝓝[>] 0)
      (𝓝 (M.consumption z₀ K (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩))) := by
    have : Tendsto (fun h : ℝ => M.consumption z₀ K (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
        + σ * M.returnAt z₀ K (ze.1 :: s.2.node) * h) (𝓝 0)
        (𝓝 (M.consumption z₀ K (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩))) := by
      have hcont : Continuous fun h : ℝ =>
          M.consumption z₀ K (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
          + σ * M.returnAt z₀ K (ze.1 :: s.2.node) * h :=
        continuous_const.add (continuous_const.mul continuous_id)
      simpa using hcont.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  exact (U.continuousAt hc).tendsto.comp hlin

/-- **Euler, saving more is not better**: unless saving is at the cap, marginal utility today is
at least the discounted return-weighted expected marginal utility tomorrow. -/
theorem euler_ge (hsl : M.Slack z₀ K) (s : M.State)
    (hcap : M.policy z₀ K s < M.assetCap) :
    M.discount * M.eulerRhs U z₀ K s (M.policy z₀ K s) ≤ U.du (M.consumption z₀ K s) := by
  set p := M.policy z₀ K s with hp
  set c := M.consumption z₀ K s with hc
  have hcf := hsl s
  have hpm := M.policy_mem z₀ K s
  have hpI : p ∈ Icc 0 M.assetCap := M.mem_Icc_of_mem_feasible z₀ K hpm
  have hβ := M.discount_pos.le
  -- the inequality for small positive deviations
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, p) * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + 1 * M.returnAt z₀ K (ze.1 :: s.2.node) * h)
        ≤ U.du (c - h) := by
    have hδ : 0 < min (M.assetCap - p) (c - M.consFloor) := lt_min (by linarith) (by linarith)
    filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
    obtain ⟨hh0, hh1⟩ := hh
    have hh2 : h < M.assetCap - p := hh1.trans_le (min_le_left _ _)
    have hh3 : h < c - M.consFloor := hh1.trans_le (min_le_right _ _)
    have hfeas : p + h ∈ (M.household z₀ K).feasible s := by
      refine ⟨by linarith [hpI.1], le_min (by linarith) ?_⟩
      have : c = M.cash z₀ K s - p := rfl
      linarith
    have hdev := M.objective_le_valueFunction' z₀ K s hfeas
    have hval := M.valueFunction_eq z₀ K s
    have hsum : ∀ a, ∑ ze : Z × E, M.shockProb z₀ ze (s, a)
          * (M.household z₀ K).valueFunction (M.clampAssets a, ⟨ze.2, ze.1 :: s.2.node⟩)
        = ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * (M.household z₀ K).valueFunction (M.stateAt a ⟨ze.2, ze.1 :: s.2.node⟩) :=
      fun a => rfl
    rw [hsum] at hdev hval
    have hcash : M.cash z₀ K s - (p + h) = c - h := by
      have : c = M.cash z₀ K s - p := rfl
      linarith
    rw [hcash] at hdev
    -- each child: the value gain from saving `h` more
    have hchild : ∀ ze : Z × E,
        M.returnAt z₀ K (ze.1 :: s.2.node) * h
            * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
              + 1 * M.returnAt z₀ K (ze.1 :: s.2.node) * h)
          ≤ (M.household z₀ K).valueFunction (M.stateAt (p + h) ⟨ze.2, ze.1 :: s.2.node⟩)
            - (M.household z₀ K).valueFunction (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩) := by
      intro ze
      have hR := M.returnAt_nonneg z₀ K (ze.1 :: s.2.node)
      have hcz := hsl (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
      have h1 := M.valueFunction_sub_ge z₀ K hpI hh0.le (by linarith) ⟨ze.2, ze.1 :: s.2.node⟩
      have h2 := U.le_sub (x := M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
          + M.returnAt z₀ K (ze.1 :: s.2.node) * h)
        (y := M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)) hcz.le
        (by nlinarith) (by nlinarith)
      rw [one_mul]
      nlinarith
    have hsumle : M.discount * (h * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + 1 * M.returnAt z₀ K (ze.1 :: s.2.node) * h))
        ≤ M.discount * (∑ ze : Z × E, M.shockProb z₀ ze (s, p)
            * (M.household z₀ K).valueFunction (M.stateAt (p + h) ⟨ze.2, ze.1 :: s.2.node⟩)
          - ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
            * (M.household z₀ K).valueFunction (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)) := by
      refine mul_le_mul_of_nonneg_left ?_ hβ
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun ze _ => ?_
      have := mul_le_mul_of_nonneg_left (hchild ze) (M.shockProb_nonneg' z₀ ze (s, p))
      nlinarith
    have hu := U.sub_le (x := c) (y := c - h) (by linarith) (by linarith)
    have hval' : (M.household z₀ K).valueFunction s = M.utility c + M.discount
        * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * (M.household z₀ K).valueFunction (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩) := hval
    have key : M.discount * (h * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + 1 * M.returnAt z₀ K (ze.1 :: s.2.node) * h)) ≤ h * U.du (c - h) := by
      have : c - (c - h) = h := by ring
      rw [this] at hu
      nlinarith
    have : h * (M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + 1 * M.returnAt z₀ K (ze.1 :: s.2.node) * h)) ≤ h * U.du (c - h) := by
      linarith
    exact le_of_mul_le_mul_left this hh0
  have hlim1 : Tendsto (fun h : ℝ => M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
      * M.returnAt z₀ K (ze.1 :: s.2.node)
      * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
        + 1 * M.returnAt z₀ K (ze.1 :: s.2.node) * h)) (𝓝[>] 0)
      (𝓝 (M.discount * M.eulerRhs U z₀ K s p)) :=
    tendsto_const_nhds.mul (M.tendsto_shifted U z₀ K s p hsl 1)
  have hlim2 : Tendsto (fun h : ℝ => U.du (c - h)) (𝓝[>] 0) (𝓝 (U.du c)) := by
    have hlin : Tendsto (fun h : ℝ => c - h) (𝓝[>] 0) (𝓝 c) := by
      have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds (x := c)).sub hid
    exact (U.continuousAt hcf).tendsto.comp hlin
  exact le_of_tendsto_of_tendsto hlim1 hlim2 hev

/-- **Euler, saving less is not better**: unless saving is at the borrowing limit, marginal
utility today is at most the discounted return-weighted expected marginal utility tomorrow. -/
theorem euler_le (hsl : M.Slack z₀ K) (s : M.State) (hpos : 0 < M.policy z₀ K s) :
    U.du (M.consumption z₀ K s) ≤ M.discount * M.eulerRhs U z₀ K s (M.policy z₀ K s) := by
  set p := M.policy z₀ K s with hp
  set c := M.consumption z₀ K s with hc
  have hcf := hsl s
  have hpm := M.policy_mem z₀ K s
  have hpI : p ∈ Icc 0 M.assetCap := M.mem_Icc_of_mem_feasible z₀ K hpm
  have hβ := M.discount_pos.le
  -- eventually every child can give up `R h` and stay above the floor
  have hfloor : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ ze : Z × E, M.consFloor
      < M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
        + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h := by
    rw [Filter.eventually_all]
    intro ze
    have hcz := hsl (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
    have hlin : Tendsto (fun h : ℝ => M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
        + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h) (𝓝[>] 0)
        (𝓝 (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩))) := by
      have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds
        (x := M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩))).add
        ((tendsto_const_nhds (x := (-1) * M.returnAt z₀ K (ze.1 :: s.2.node))).mul hid)
    exact hlin.eventually (lt_mem_nhds hcz)
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), U.du (c + h)
      ≤ M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, p) * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h) := by
    filter_upwards [Ioo_mem_nhdsGT hpos, hfloor] with h hh hfl
    obtain ⟨hh0, hh1⟩ := hh
    have hfeas : p - h ∈ (M.household z₀ K).feasible s :=
      ⟨by linarith, (by linarith : p - h ≤ p).trans hpm.2⟩
    have hdev := M.objective_le_valueFunction' z₀ K s hfeas
    have hval := M.valueFunction_eq z₀ K s
    have hsum : ∀ a, ∑ ze : Z × E, M.shockProb z₀ ze (s, a)
          * (M.household z₀ K).valueFunction (M.clampAssets a, ⟨ze.2, ze.1 :: s.2.node⟩)
        = ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * (M.household z₀ K).valueFunction (M.stateAt a ⟨ze.2, ze.1 :: s.2.node⟩) :=
      fun a => rfl
    rw [hsum] at hdev hval
    have hcash : M.cash z₀ K s - (p - h) = c + h := by
      have : c = M.cash z₀ K s - p := rfl
      linarith
    rw [hcash] at hdev
    have hchild : ∀ ze : Z × E,
        (M.household z₀ K).valueFunction (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            - (M.household z₀ K).valueFunction (M.stateAt (p - h) ⟨ze.2, ze.1 :: s.2.node⟩)
          ≤ M.returnAt z₀ K (ze.1 :: s.2.node) * h
            * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
              + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h) := by
      intro ze
      have hR := M.returnAt_nonneg z₀ K (ze.1 :: s.2.node)
      have hfz := hfl ze
      have hpI' : p - h ∈ Icc 0 M.assetCap := ⟨by linarith, by linarith [hpI.2]⟩
      have h1 := M.valueFunction_sub_le z₀ K hpI' hh0.le (by linarith [hpI.2])
        ⟨ze.2, ze.1 :: s.2.node⟩ (by rw [sub_add_cancel]; linarith)
      rw [sub_add_cancel] at h1
      have h2 := U.sub_le (x := M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩))
        (y := M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
          - M.returnAt z₀ K (ze.1 :: s.2.node) * h) (by linarith) (by nlinarith)
      have e1 : M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h
          = M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            - M.returnAt z₀ K (ze.1 :: s.2.node) * h := by ring
      rw [e1]
      have e2 : M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
          - (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            - M.returnAt z₀ K (ze.1 :: s.2.node) * h) = M.returnAt z₀ K (ze.1 :: s.2.node) * h := by
        ring
      rw [e2] at h2
      linarith
    have hsumle : M.discount * (∑ ze : Z × E, M.shockProb z₀ ze (s, p)
            * (M.household z₀ K).valueFunction (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
          - ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
            * (M.household z₀ K).valueFunction (M.stateAt (p - h) ⟨ze.2, ze.1 :: s.2.node⟩))
        ≤ M.discount * (h * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h)) := by
      refine mul_le_mul_of_nonneg_left ?_ hβ
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun ze _ => ?_
      have := mul_le_mul_of_nonneg_left (hchild ze) (M.shockProb_nonneg' z₀ ze (s, p))
      nlinarith
    have hu := U.le_sub (x := c + h) (y := c) hcf.le (by linarith) (by linarith)
    have : c + h - c = h := by ring
    rw [this] at hu
    have hval' : (M.household z₀ K).valueFunction s = M.utility c + M.discount
        * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * (M.household z₀ K).valueFunction (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩) := hval
    have key : h * U.du (c + h) ≤ h * (M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h)) := by
      nlinarith
    exact le_of_mul_le_mul_left key hh0
  have hlim1 : Tendsto (fun h : ℝ => M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
      * M.returnAt z₀ K (ze.1 :: s.2.node)
      * U.du (M.consumption z₀ K (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
        + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h)) (𝓝[>] 0)
      (𝓝 (M.discount * M.eulerRhs U z₀ K s p)) :=
    tendsto_const_nhds.mul (M.tendsto_shifted U z₀ K s p hsl (-1))
  have hlim2 : Tendsto (fun h : ℝ => U.du (c + h)) (𝓝[>] 0) (𝓝 (U.du c)) := by
    have hlin : Tendsto (fun h : ℝ => c + h) (𝓝[>] 0) (𝓝 c) := by
      have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds (x := c)).add hid
    exact (U.continuousAt hcf).tendsto.comp hlin
  exact le_of_tendsto_of_tendsto hlim2 hlim1 hev

end KSModel

end KrusellSmith

end LeanEconomics
