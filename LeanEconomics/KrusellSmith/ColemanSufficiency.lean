/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ColemanBridge
import LeanEconomics.KrusellSmith.CornerVerification
import LeanEconomics.KrusellSmith.MinimalMPC
import LeanEconomics.KrusellSmith.Sensitivity
import LeanEconomics.DynamicProgramming.StochasticOptimality

/-!
# Euler sufficiency on the tree

Milestone CO4c of `COLEMAN_PLAN.md`. In the Krusell–Smith household problem along a price path
(no borrowing), a feasible contingent plan whose consumption satisfies the Euler conditions with
the corners at every history is optimal, and the household's policy is its first action.

* Bookkeeping: two plans from the same state pass through the same labels (`plan_label`), so they
  face the same prices and attach the same probability to every history (`histProb_eq`); next
  period's assets are this period's saving (`plan_assets_succ`).
* **`value_le_of_euler`**: for every feasible plan `q`, `value q ≤ value p + gap₀`, where `gap₀` is
  the date-0 concavity gap `u(c'₀) − u(c₀) − u'(c₀)(c'₀ − c₀)`. Concavity bounds later dates by
  `u'(c)(c' − c)`; with `c' − c = R Δa − Δs` and `Δa_{n+1} = Δs_n` the sum telescopes, each step
  `βⁿ E[(β E_n[R' u'(c')] − u'(c)) Δs]` is `≤ 0` by the Euler conditions, and the carried term
  `βᴺ E[u'(c_N) R_N Δa_N]` vanishes.
* **`policy_eq_of_euler`**: the greedy plan attains the value function, so its date-0 gap is
  nonnegative; strict concavity forces the same consumption, hence the household's policy at the
  initial state is the candidate's first saving.
-/

open Set Filter Topology BoundedContinuousFunction
open LeanEconomics.StochasticDynamicProgram

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (z₀ : Z) (P : List Z → ℝ × ℝ)

/-- The label reached after a history of shocks, from the label `l₀`. -/
def labelOf (l₀ : Label Z E) : ∀ n : ℕ, (Fin n → Z × E) → Label Z E
  | 0, _ => l₀
  | n + 1, h => ⟨(h (Fin.last n)).2, (h (Fin.last n)).1 :: (labelOf l₀ n (Fin.init h)).node⟩

theorem labelOf_snoc (l₀ : Label Z E) (n : ℕ) (h : Fin n → Z × E) (ze : Z × E) :
    labelOf l₀ (n + 1) (Fin.snoc h ze) = ⟨ze.2, ze.1 :: (labelOf l₀ n h).node⟩ := by
  simp only [labelOf, Fin.init_snoc, Fin.snoc_last]

/-- **Every plan passes through the same labels.** -/
theorem plan_label {s₀ : M.State} (p : (M.household z₀ P).Plan s₀) :
    ∀ (n : ℕ) (h : Fin n → Z × E), (p.state n h).2 = labelOf s₀.2 n h
  | 0, h => by rw [p.state_zero]; rfl
  | n + 1, h => by
    conv_lhs => rw [← Fin.snoc_init_self h]
    rw [p.state_succ]
    change (⟨(h (Fin.last n)).2, (h (Fin.last n)).1 :: (p.state n (Fin.init h)).2.node⟩ :
      Label Z E) = _
    rw [plan_label p n (Fin.init h)]
    rfl

/-- **Plans from the same state attach the same probability to every history.** -/
theorem histProb_eq {s₀ : M.State} (p q : (M.household z₀ P).Plan s₀) :
    ∀ (n : ℕ) (h : Fin n → Z × E), p.histProb n h = q.histProb n h
  | 0, _ => rfl
  | n + 1, h => by
    simp only [Plan.histProb]
    rw [histProb_eq p q n]
    congr 1
    change M.shockProb z₀ _ (_, _) = M.shockProb z₀ _ (_, _)
    simp only [shockProb, ContinuousMap.coe_mk, plan_label]

/-- **Next period's assets are this period's saving.** -/
theorem plan_assets_succ {s₀ : M.State} (p : (M.household z₀ P).Plan s₀) (n : ℕ)
    (h : Fin n → Z × E) (ze : Z × E) :
    ((p.state (n + 1) (Fin.snoc h ze)).1 : ℝ) = p.action n h := by
  rw [p.state_succ]
  change ((M.clampAssets (p.action n h)) : ℝ) = _
  rw [M.clampAssets_of_mem (M.mem_Icc_of_mem_feasible z₀ P (p.action_mem n h))]

/-- Consumption along a plan. -/
noncomputable def planCons {s₀ : M.State} (p : (M.household z₀ P).Plan s₀) (n : ℕ)
    (h : Fin n → Z × E) : ℝ :=
  M.cash z₀ P (p.state n h) - p.action n h

theorem reward_planCons {s₀ : M.State} (p : (M.household z₀ P).Plan s₀) (n : ℕ)
    (h : Fin n → Z × E) :
    (M.household z₀ P).reward (p.state n h, p.action n h) = M.utility (planCons z₀ P p n h) :=
  M.reward_eq_of_mem_feasible z₀ P (p.action_mem n h)

theorem planCons_floor {s₀ : M.State} (p : (M.household z₀ P).Plan s₀) (n : ℕ)
    (h : Fin n → Z × E) : M.consFloor ≤ planCons z₀ P p n h := by
  have := (p.action_mem n h).2.trans (min_le_right _ _)
  unfold planCons
  linarith

/-- **Consumption differences**: with the same label and no borrowing, the difference in
consumption is the return on the asset difference less the saving difference. -/
theorem planCons_sub (hb : M.borrowLimit = 0) {s₀ : M.State} (p q : (M.household z₀ P).Plan s₀)
    (n : ℕ) (h : Fin n → Z × E) :
    planCons z₀ P q n h - planCons z₀ P p n h
      = M.returnAt z₀ P (labelOf s₀.2 n h).node * ((q.state n h).1 - (p.state n h).1)
        - (q.action n h - p.action n h) := by
  have hq := plan_label z₀ P q n h
  have hp := plan_label z₀ P p n h
  simp only [planCons, cash, hb, mul_zero, sub_zero]
  rw [hq, hp]
  ring

variable (U : M.SmoothUtility)

/-- **The strict tangent line**: strict concavity of utility. -/
theorem utility_lt_tangent {x y : ℝ} (hx : M.consFloor ≤ x) (hy : M.consFloor < y) (hxy : x ≠ y) :
    M.utility x < M.utility y + U.du y * (x - y) := by
  have hm : M.consFloor < (x + y) / 2 := by linarith
  have hstrict := M.strictConcaveOn_utility.2 (mem_Ici.2 hx) (mem_Ici.2 hy.le) hxy
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hstrict
  have heq : 1 / 2 * x + 1 / 2 * y = (x + y) / 2 := by ring
  rw [heq] at hstrict
  have htan := utility_le_tangent (U := U) hm.le hy
  linarith

/-- Next period's expected return times marginal utility, along a plan. -/
noncomputable def nextMU {s₀ : M.State} (p : (M.household z₀ P).Plan s₀) (n : ℕ)
    (h : Fin n → Z × E) : ℝ :=
  ∑ ze : Z × E, (M.household z₀ P).prob ze (p.state n h, p.action n h)
    * (M.returnAt z₀ P (ze.1 :: (labelOf s₀.2 n h).node)
      * U.du (planCons z₀ P p (n + 1) (Fin.snoc h ze)))

/-- **The Euler conditions of a plan**, with the corners at zero saving and at the cap. -/
def PlanEuler {s₀ : M.State} (p : (M.household z₀ P).Plan s₀) : Prop :=
  ∀ (n : ℕ) (h : Fin n → Z × E), M.consFloor < planCons z₀ P p n h ∧
    (0 < p.action n h → U.du (planCons z₀ P p n h) ≤ M.discount * nextMU z₀ P U p n h) ∧
    (p.action n h < M.assetCap → M.discount * nextMU z₀ P U p n h ≤ U.du (planCons z₀ P p n h))

/-- **The Euler conditions sign each telescoping step.** -/
theorem euler_step {s₀ : M.State} {p q : (M.household z₀ P).Plan s₀} (hE : PlanEuler z₀ P U p)
    (n : ℕ) (h : Fin n → Z × E) :
    (M.discount * nextMU z₀ P U p n h - U.du (planCons z₀ P p n h))
      * (q.action n h - p.action n h) ≤ 0 := by
  obtain ⟨-, h1, h2⟩ := hE n h
  have hp := M.mem_Icc_of_mem_feasible z₀ P (p.action_mem n h)
  have hq := M.mem_Icc_of_mem_feasible z₀ P (q.action_mem n h)
  rcases le_total (p.action n h) (q.action n h) with hle | hle
  · rcases hp.2.lt_or_eq with hlt | heq
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [h2 hlt]) (by linarith)
    · have : q.action n h - p.action n h = 0 := by linarith [hq.2]
      rw [this, mul_zero]
  · rcases hp.1.lt_or_eq with hlt | heq
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith [h1 hlt]) (by linarith)
    · have : q.action n h - p.action n h = 0 := by linarith [hq.1]
      rw [this, mul_zero]

/-- The carried term of the telescoping sum. -/
noncomputable def carried {s₀ : M.State} (p q : (M.household z₀ P).Plan s₀) (N : ℕ) : ℝ :=
  ∑ h : Fin N → Z × E, p.histProb N h * (U.du (planCons z₀ P p N h)
    * (M.returnAt z₀ P (labelOf s₀.2 N h).node * ((q.state N h).1 - (p.state N h).1)))

/-- The date-`n` first-order term. -/
noncomputable def firstOrder {s₀ : M.State} (p q : (M.household z₀ P).Plan s₀) (n : ℕ) : ℝ :=
  ∑ h : Fin n → Z × E, p.histProb n h
    * (U.du (planCons z₀ P p n h) * (planCons z₀ P q n h - planCons z₀ P p n h))

theorem carried_succ {s₀ : M.State} (p q : (M.household z₀ P).Plan s₀) (N : ℕ) :
    carried z₀ P U p q (N + 1) = ∑ h : Fin N → Z × E, p.histProb N h
      * (nextMU z₀ P U p N h * (q.action N h - p.action N h)) := by
  rw [carried, sum_snoc]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [nextMU, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ze _ => ?_
  rw [Plan.histProb_snoc, labelOf_snoc, plan_assets_succ z₀ P q, plan_assets_succ z₀ P p]
  ring

theorem firstOrder_eq (hb : M.borrowLimit = 0) {s₀ : M.State} (p q : (M.household z₀ P).Plan s₀)
    (N : ℕ) :
    firstOrder z₀ P U p q N = carried z₀ P U p q N
      - ∑ h : Fin N → Z × E, p.histProb N h
        * (U.du (planCons z₀ P p N h) * (q.action N h - p.action N h)) := by
  rw [firstOrder, carried, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [planCons_sub z₀ P hb p q N h]
  ring

/-- **The telescoping sum is nonpositive.** -/
theorem telescope_le (hb : M.borrowLimit = 0) {s₀ : M.State} {p : (M.household z₀ P).Plan s₀}
    (hE : PlanEuler z₀ P U p) (q : (M.household z₀ P).Plan s₀) :
    ∀ N : ℕ, ∑ n ∈ Finset.range N, M.discount ^ n * firstOrder z₀ P U p q n
      + M.discount ^ N * carried z₀ P U p q N ≤ 0
  | 0 => by
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add, carried]
    refine (Finset.sum_eq_zero fun h _ => ?_).le
    rw [p.state_zero, q.state_zero, sub_self, mul_zero, mul_zero, mul_zero]
  | N + 1 => by
    have ih := telescope_le hb hE q N
    rw [Finset.sum_range_succ, firstOrder_eq z₀ P U hb p q N, carried_succ z₀ P U p q N]
    have hstep : ∑ h : Fin N → Z × E, p.histProb N h
        * ((M.discount * nextMU z₀ P U p N h - U.du (planCons z₀ P p N h))
          * (q.action N h - p.action N h)) ≤ 0 :=
      Finset.sum_nonpos fun h _ =>
        mul_nonpos_of_nonneg_of_nonpos (p.histProb_nonneg N h) (euler_step z₀ P U hE N h)
    have e : M.discount ^ (N + 1) * ∑ h : Fin N → Z × E, p.histProb N h
          * (nextMU z₀ P U p N h * (q.action N h - p.action N h))
        - M.discount ^ N * ∑ h : Fin N → Z × E, p.histProb N h
          * (U.du (planCons z₀ P p N h) * (q.action N h - p.action N h))
        = M.discount ^ N * ∑ h : Fin N → Z × E, p.histProb N h
          * ((M.discount * nextMU z₀ P U p N h - U.du (planCons z₀ P p N h))
            * (q.action N h - p.action N h)) := by
      rw [pow_succ, mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    have hβ : 0 ≤ M.discount ^ N := pow_nonneg M.discount_pos.le N
    have := mul_nonpos_of_nonneg_of_nonpos hβ hstep
    linarith

/-- The carried term is bounded. -/
theorem abs_carried_le {s₀ : M.State} {p : (M.household z₀ P).Plan s₀} {Dbar : ℝ}
    (hE : PlanEuler z₀ P U p) (hD : ∀ n h, U.du (planCons z₀ P p n h) ≤ Dbar)
    (q : (M.household z₀ P).Plan s₀) (N : ℕ) :
    |carried z₀ P U p q N| ≤ Dbar * (M.returnBound * M.assetCap) := by
  rw [carried]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ h : Fin N → Z × E, |p.histProb N h * (U.du (planCons z₀ P p N h)
        * (M.returnAt z₀ P (labelOf s₀.2 N h).node * ((q.state N h).1 - (p.state N h).1)))|
      ≤ ∑ h : Fin N → Z × E, p.histProb N h * (Dbar * (M.returnBound * M.assetCap)) := by
        refine Finset.sum_le_sum fun h _ => ?_
        rw [abs_mul, abs_of_nonneg (p.histProb_nonneg N h)]
        refine mul_le_mul_of_nonneg_left ?_ (p.histProb_nonneg N h)
        have hu0 := U.du_nonneg (hE N h).1
        have hR0 := M.returnAt_nonneg z₀ P (labelOf s₀.2 N h).node
        have hR1 := M.returnAt_le_returnBound z₀ P (labelOf s₀.2 N h).node
        have hqa := (q.state N h).1.2
        have hpa := (p.state N h).1.2
        have hΔ : |((q.state N h).1 : ℝ) - (p.state N h).1| ≤ M.assetCap := by
          rw [abs_le]; constructor <;> linarith [hqa.1, hqa.2, hpa.1, hpa.2]
        rw [abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_nonneg hR0]
        exact mul_le_mul (hD N h) (mul_le_mul hR1 hΔ (abs_nonneg _) (hR0.trans hR1))
          (mul_nonneg hR0 (abs_nonneg _)) (hu0.trans (hD N h))
    _ = Dbar * (M.returnBound * M.assetCap) := by rw [← Finset.sum_mul, p.sum_histProb, one_mul]

/-- The date-`n` concavity gaps (nonpositive). -/
noncomputable def concGap {s₀ : M.State} (p q : (M.household z₀ P).Plan s₀) (n : ℕ) : ℝ :=
  ∑ h : Fin n → Z × E, p.histProb n h * (M.utility (planCons z₀ P q n h)
    - M.utility (planCons z₀ P p n h)
    - U.du (planCons z₀ P p n h) * (planCons z₀ P q n h - planCons z₀ P p n h))

theorem concGap_nonpos {s₀ : M.State} {p : (M.household z₀ P).Plan s₀} (hE : PlanEuler z₀ P U p)
    (q : (M.household z₀ P).Plan s₀) (n : ℕ) : concGap z₀ P U p q n ≤ 0 :=
  Finset.sum_nonpos fun h _ => mul_nonpos_of_nonneg_of_nonpos (p.histProb_nonneg n h) (by
    have := utility_le_tangent (U := U) (planCons_floor z₀ P q n h) (hE n h).1
    linarith)

theorem payoff_sub {s₀ : M.State} (p q : (M.household z₀ P).Plan s₀) (n : ℕ) :
    q.payoff n - p.payoff n
      = M.discount ^ n * firstOrder z₀ P U p q n + M.discount ^ n * concGap z₀ P U p q n := by
  simp only [Plan.payoff, Plan.expect, firstOrder, concGap, reward_planCons]
  change M.discount ^ n * _ - M.discount ^ n * _ = _
  rw [← mul_sub, ← mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [histProb_eq z₀ P q p n h]
  ring

/-- **Euler sufficiency**: every feasible plan's value is at most the candidate's plus the date-0
concavity gap. -/
theorem value_le_of_euler (hb : M.borrowLimit = 0) {s₀ : M.State}
    {p : (M.household z₀ P).Plan s₀} (hE : PlanEuler z₀ P U p) {Dbar : ℝ}
    (hD : ∀ n h, U.du (planCons z₀ P p n h) ≤ Dbar) (q : (M.household z₀ P).Plan s₀) :
    q.value ≤ p.value + concGap z₀ P U p q 0 := by
  have hβ0 := M.discount_pos
  have hβ1 := M.discount_lt_one
  set K₀ := Dbar * (M.returnBound * M.assetCap)
  -- partial sums of the payoff differences
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), (q.payoff n - p.payoff n)
      ≤ concGap z₀ P U p q 0 + M.discount ^ (N + 1) * K₀ := by
    intro N
    simp only [payoff_sub z₀ P U p q, Finset.sum_add_distrib]
    have h1 := telescope_le z₀ P U hb hE q (N + 1)
    have h2 := abs_carried_le z₀ P U hE hD q (N + 1)
    have h3 : ∑ n ∈ Finset.range (N + 1), M.discount ^ n * concGap z₀ P U p q n
        ≤ concGap z₀ P U p q 0 := by
      rw [Finset.sum_range_succ']
      have : ∑ n ∈ Finset.range N, M.discount ^ (n + 1) * concGap z₀ P U p q (n + 1) ≤ 0 :=
        Finset.sum_nonpos fun n _ => mul_nonpos_of_nonneg_of_nonpos
          (pow_nonneg hβ0.le _) (concGap_nonpos z₀ P U hE q (n + 1))
      simp only [pow_zero, one_mul]
      linarith
    have hβN : 0 ≤ M.discount ^ (N + 1) := pow_nonneg hβ0.le _
    have h4 := mul_le_mul_of_nonneg_left (neg_le_of_abs_le h2) hβN
    linarith
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), (q.payoff n - p.payoff n)) atTop
      (𝓝 (q.value - p.value)) :=
    ((q.summable_payoff.hasSum.sub p.summable_payoff.hasSum).tendsto_sum_nat).comp
      (tendsto_add_atTop_nat 1)
  have hbound : Tendsto (fun N : ℕ => concGap z₀ P U p q 0 + M.discount ^ (N + 1) * K₀) atTop
      (𝓝 (concGap z₀ P U p q 0 + 0 * K₀)) :=
    tendsto_const_nhds.add (((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
      (tendsto_add_atTop_nat 1)).mul_const K₀)
  rw [zero_mul, add_zero] at hbound
  have := le_of_tendsto_of_tendsto' hlim hbound hpart
  linarith

/-- The household's policy is the dynamic program's greedy action (both maximise the Bellman
objective at the value function; the maximiser is unique). -/
theorem policy_eq_policyAction (s : M.State) :
    M.policy z₀ P s = (M.household z₀ P).policyAction s := by
  set D := M.household z₀ P
  refine M.optimal_saving_unique z₀ P (M.policy_mem z₀ P s) (D.policyAction_mem s) ?_ ?_
  · exact (M.policy_optimal z₀ P s).symm
  · have h1 := D.valueFunction_eq_policyAction s
    have h2 : D.bellmanFn D.valueFunction s = D.valueFunction s :=
      congrFun (congrArg DFunLike.coe D.bellman_valueFunction) s
    rw [h2, h1]
    rfl

/-- **Euler sufficiency, the policy**: at the root of a plan satisfying the Euler conditions
(with the corners) and with bounded marginal utility, the household's optimal saving is the plan's
first action. -/
theorem policy_eq_of_euler (hb : M.borrowLimit = 0) {s₀ : M.State}
    {p : (M.household z₀ P).Plan s₀} (hE : PlanEuler z₀ P U p) {Dbar : ℝ}
    (hD : ∀ n h, U.du (planCons z₀ P p n h) ≤ Dbar) (h : Fin 0 → Z × E) :
    M.policy z₀ P s₀ = p.action 0 h := by
  let q := (M.household z₀ P).policyPlan s₀
  have hle := value_le_of_euler z₀ P U hb hE hD q
  have hq : q.value = (M.household z₀ P).valueFunction s₀ :=
    (M.household z₀ P).policyPlan_value s₀
  have hp := p.value_le
  have hgap : 0 ≤ concGap z₀ P U p q 0 := by linarith
  have hgap' : concGap z₀ P U p q 0 = M.utility (planCons z₀ P q 0 h)
      - M.utility (planCons z₀ P p 0 h)
      - U.du (planCons z₀ P p 0 h) * (planCons z₀ P q 0 h - planCons z₀ P p 0 h) := by
    rw [concGap, Fintype.sum_eq_single h fun h' hh => absurd (Subsingleton.elim h' h) hh,
      Plan.histProb_zero, one_mul]
  have hcons : planCons z₀ P q 0 h = planCons z₀ P p 0 h := by
    by_contra hne
    have := utility_lt_tangent (U := U) (planCons_floor z₀ P q 0 h) (hE 0 h).1 hne
    linarith
  have hact : q.action 0 h = p.action 0 h := by
    simp only [planCons, p.state_zero, q.state_zero] at hcons
    linarith
  rw [policy_eq_policyAction, ← hact]
  rfl

end KSModel

end KrusellSmith

end LeanEconomics
