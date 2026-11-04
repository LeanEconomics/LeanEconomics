/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.AgainstContinuation

/-!
# The Euler inequalities along the Bellman iterates

Milestone MR4b, step b3, of `MINIMAL_STATE_PLAN.md`. `Euler.lean` proves the Euler inequalities
at the household's fixed point. Carroll–Kimball runs along the Bellman iterates, so the same
inequalities are needed one step at a time: a household whose continuation value is
`v = T w₀`, one Bellman step from `w₀`, compared with the households at the children, who
consume against `w₀`.

* `bellman_sub_ge`, `bellman_sub_le`: **value sandwiches for `T w`**, by copying plans (the
  richer household can save what the poorer one saves; the poorer can save what the richer one
  saves if the floor allows). The proofs of `valueFunction_sub_ge/le` with `w` as the
  continuation.
* `eulerRhsOf w₀ s a'`: the return-weighted expected marginal utility of the children's
  consumption against `w₀`.
* **`eulerOf_ge`** (saving more is not better, unless at the cap) and **`eulerOf_le`** (saving
  less is not better, unless at the borrowing limit), for the household with continuation
  `T w₀`.

At the fixed point (`w₀ = v = ` the value function) these are `euler_ge`, `euler_le`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (U : M.SmoothUtility) (z₀ : Z) (K : List Z → ℝ × ℝ)

/-- **Slack against `w`**: consumption against the continuation `w` is strictly above the floor at
every state. -/
def SlackOf (w : M.State →ᵇ ℝ) : Prop := ∀ s : M.State, M.consFloor < M.consumptionOf z₀ K w s

/-! ### Value sandwiches for one Bellman step -/

/-- **Richer by `h`: at least the utility of consuming the extra cash.** -/
theorem bellman_sub_ge (w : M.State →ᵇ ℝ) {a h : ℝ} (ha : a ∈ Icc 0 M.assetCap) (hh : 0 ≤ h)
    (hah : a + h ≤ M.assetCap) (l : Label Z E) :
    M.utility (M.consumptionOf z₀ K w (M.stateAt a l) + M.returnAt z₀ K l.node * h)
        - M.utility (M.consumptionOf z₀ K w (M.stateAt a l))
      ≤ (M.household z₀ K).bellman w (M.stateAt (a + h) l)
        - (M.household z₀ K).bellman w (M.stateAt a l) := by
  have hah' : a + h ∈ Icc 0 M.assetCap := ⟨add_nonneg ha.1 hh, hah⟩
  set p := M.policyOf z₀ K w (M.stateAt a l) with hp
  have hpm := M.policyOf_mem z₀ K w (M.stateAt a l)
  have hcash : M.cash z₀ K (M.stateAt (a + h) l)
      = M.cash z₀ K (M.stateAt a l) + M.returnAt z₀ K l.node * h := by
    rw [M.cash_stateAt z₀ K hah' l, M.cash_stateAt z₀ K ha l]
    ring
  have hfeas : p ∈ (M.household z₀ K).feasible (M.stateAt (a + h) l) := by
    refine ⟨hpm.1, le_min (hpm.2.trans (min_le_left _ _)) ?_⟩
    have := hpm.2.trans (min_le_right _ _)
    rw [hcash]
    nlinarith [M.returnAt_nonneg z₀ K l.node]
  have h1 := M.le_bellman_contOf z₀ K w hfeas
  have h2 := M.bellman_eq_contOf z₀ K w (M.stateAt a l)
  rw [hcash, M.contOf_label z₀ w (a + h) a l] at h1
  have hc : M.cash z₀ K (M.stateAt a l) + M.returnAt z₀ K l.node * h - p
      = M.consumptionOf z₀ K w (M.stateAt a l) + M.returnAt z₀ K l.node * h := by
    rw [consumptionOf]
    ring
  rw [hc] at h1
  linarith

/-- **Richer by `h`: at most the utility lost by consuming `R h` less**, when the poorer
household can afford the richer one's saving above the floor. -/
theorem bellman_sub_le (w : M.State →ᵇ ℝ) {a h : ℝ} (ha : a ∈ Icc 0 M.assetCap) (hh : 0 ≤ h)
    (hah : a + h ≤ M.assetCap) (l : Label Z E)
    (hfl : M.consFloor
      ≤ M.consumptionOf z₀ K w (M.stateAt (a + h) l) - M.returnAt z₀ K l.node * h) :
    (M.household z₀ K).bellman w (M.stateAt (a + h) l)
        - (M.household z₀ K).bellman w (M.stateAt a l)
      ≤ M.utility (M.consumptionOf z₀ K w (M.stateAt (a + h) l))
        - M.utility (M.consumptionOf z₀ K w (M.stateAt (a + h) l)
          - M.returnAt z₀ K l.node * h) := by
  have hah' : a + h ∈ Icc 0 M.assetCap := ⟨add_nonneg ha.1 hh, hah⟩
  set p := M.policyOf z₀ K w (M.stateAt (a + h) l) with hp
  have hpm := M.policyOf_mem z₀ K w (M.stateAt (a + h) l)
  have hcash : M.cash z₀ K (M.stateAt (a + h) l)
      = M.cash z₀ K (M.stateAt a l) + M.returnAt z₀ K l.node * h := by
    rw [M.cash_stateAt z₀ K hah' l, M.cash_stateAt z₀ K ha l]
    ring
  have hcons : M.consumptionOf z₀ K w (M.stateAt (a + h) l)
      = M.cash z₀ K (M.stateAt (a + h) l) - p := rfl
  have hfeas : p ∈ (M.household z₀ K).feasible (M.stateAt a l) := by
    refine ⟨hpm.1, le_min (hpm.2.trans (min_le_left _ _)) ?_⟩
    rw [hcons, hcash] at hfl
    linarith
  have h1 := M.le_bellman_contOf z₀ K w hfeas
  have h2 := M.bellman_eq_contOf z₀ K w (M.stateAt (a + h) l)
  rw [M.contOf_label z₀ w a (a + h) l] at h1
  have hc : M.cash z₀ K (M.stateAt a l) - p
      = M.consumptionOf z₀ K w (M.stateAt (a + h) l) - M.returnAt z₀ K l.node * h := by
    rw [hcons, hcash]
    ring
  rw [hc] at h1
  linarith

/-! ### The Euler inequalities one step from `w₀` -/

/-- The return-weighted expected marginal utility of the children's consumption against `w₀`,
when saving `a'` at `s`. -/
noncomputable def eulerRhsOf (w₀ : M.State →ᵇ ℝ) (s : M.State) (a' : ℝ) : ℝ :=
  ∑ ze : Z × E, M.shockProb z₀ ze (s, a') * M.returnAt z₀ K (ze.1 :: s.2.node)
    * U.du (M.consumptionOf z₀ K w₀ (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩))

theorem tendsto_shiftedOf (w₀ : M.State →ᵇ ℝ) (s : M.State) (a' : ℝ)
    (hsl : M.SlackOf z₀ K w₀) (σ : ℝ) :
    Tendsto (fun h : ℝ => ∑ ze : Z × E, M.shockProb z₀ ze (s, a')
        * M.returnAt z₀ K (ze.1 :: s.2.node)
        * U.du (M.consumptionOf z₀ K w₀ (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
          + σ * M.returnAt z₀ K (ze.1 :: s.2.node) * h))
      (𝓝[>] 0) (𝓝 (M.eulerRhsOf U z₀ K w₀ s a')) := by
  refine tendsto_finsetSum _ fun ze _ => ?_
  refine tendsto_const_nhds.mul ?_
  have hc := hsl (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
  have hcont : Continuous fun h : ℝ =>
      M.consumptionOf z₀ K w₀ (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
      + σ * M.returnAt z₀ K (ze.1 :: s.2.node) * h :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hlin := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [mul_zero, add_zero] at hlin
  exact (U.continuousAt hc).tendsto.comp hlin

/-- **Euler, saving more is not better**, one step from `w₀`: unless saving is at the cap,
marginal utility today is at least the discounted return-weighted expected marginal utility of
the children's consumption against `w₀`. -/
theorem eulerOf_ge (w₀ : M.State →ᵇ ℝ) (hsl₀ : M.SlackOf z₀ K w₀) (s : M.State)
    (hsl : M.consFloor < M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s)
    (hcap : M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s < M.assetCap) :
    M.discount * M.eulerRhsOf U z₀ K w₀ s (M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s)
      ≤ U.du (M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s) := by
  set v := (M.household z₀ K).bellman w₀ with hv
  set p := M.policyOf z₀ K v s with hp
  set c := M.consumptionOf z₀ K v s with hc
  have hpm := M.policyOf_mem z₀ K v s
  have hpI : p ∈ Icc 0 M.assetCap := M.mem_Icc_of_mem_feasible z₀ K hpm
  have hβ := M.discount_pos.le
  have hsum : ∀ a, M.contOf z₀ v s a = ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
      * v (M.stateAt a ⟨ze.2, ze.1 :: s.2.node⟩) := fun a => rfl
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, p) * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + 1 * M.returnAt z₀ K (ze.1 :: s.2.node) * h)
        ≤ U.du (c - h) := by
    have hδ : 0 < min (M.assetCap - p) (c - M.consFloor) := lt_min (by linarith) (by linarith)
    filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
    obtain ⟨hh0, hh1⟩ := hh
    have hh2 : h < M.assetCap - p := hh1.trans_le (min_le_left _ _)
    have hh3 : h < c - M.consFloor := hh1.trans_le (min_le_right _ _)
    have hcp : c = M.cash z₀ K s - p := rfl
    have hfeas : p + h ∈ (M.household z₀ K).feasible s :=
      ⟨by linarith [hpI.1], le_min (by linarith) (by linarith)⟩
    have hdev := M.le_bellman_contOf z₀ K v hfeas
    have hval := M.bellman_eq_contOf z₀ K v s
    rw [hsum] at hdev hval
    have hcash : M.cash z₀ K s - (p + h) = c - h := by linarith
    rw [hcash] at hdev
    have hchild : ∀ ze : Z × E,
        M.returnAt z₀ K (ze.1 :: s.2.node) * h
            * U.du (M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
              + 1 * M.returnAt z₀ K (ze.1 :: s.2.node) * h)
          ≤ v (M.stateAt (p + h) ⟨ze.2, ze.1 :: s.2.node⟩)
            - v (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩) := by
      intro ze
      have hR := M.returnAt_nonneg z₀ K (ze.1 :: s.2.node)
      have hcz := hsl₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
      have h1 := M.bellman_sub_ge z₀ K w₀ hpI hh0.le (by linarith) ⟨ze.2, ze.1 :: s.2.node⟩
      have h2 := U.le_sub (x := M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
          + M.returnAt z₀ K (ze.1 :: s.2.node) * h)
        (y := M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)) hcz.le
        (by nlinarith) (by nlinarith)
      rw [one_mul]
      nlinarith
    have hsumle : M.discount * (h * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + 1 * M.returnAt z₀ K (ze.1 :: s.2.node) * h))
        ≤ M.discount * (∑ ze : Z × E, M.shockProb z₀ ze (s, p)
            * v (M.stateAt (p + h) ⟨ze.2, ze.1 :: s.2.node⟩)
          - ∑ ze : Z × E, M.shockProb z₀ ze (s, p) * v (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)) := by
      refine mul_le_mul_of_nonneg_left ?_ hβ
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun ze _ => ?_
      have := mul_le_mul_of_nonneg_left (hchild ze) (M.shockProb_nonneg' z₀ ze (s, p))
      nlinarith
    have hu := U.sub_le (x := c) (y := c - h) (by linarith) (by linarith)
    have key : M.discount * (h * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + 1 * M.returnAt z₀ K (ze.1 :: s.2.node) * h)) ≤ h * U.du (c - h) := by
      have : c - (c - h) = h := by ring
      rw [this] at hu
      nlinarith
    have : h * (M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + 1 * M.returnAt z₀ K (ze.1 :: s.2.node) * h)) ≤ h * U.du (c - h) := by
      linarith
    exact le_of_mul_le_mul_left this hh0
  have hlim1 := tendsto_const_nhds (x := M.discount).mul (M.tendsto_shiftedOf U z₀ K w₀ s p hsl₀ 1)
  have hlim2 : Tendsto (fun h : ℝ => U.du (c - h)) (𝓝[>] 0) (𝓝 (U.du c)) := by
    have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hlin : Tendsto (fun h : ℝ => c - h) (𝓝[>] 0) (𝓝 c) := by
      simpa using (tendsto_const_nhds (x := c)).sub hid
    exact (U.continuousAt hsl).tendsto.comp hlin
  exact le_of_tendsto_of_tendsto hlim1 hlim2 hev

/-- **Euler, saving less is not better**, one step from `w₀`: unless saving is at the borrowing
limit, marginal utility today is at most the discounted return-weighted expected marginal utility
of the children's consumption against `w₀`. -/
theorem eulerOf_le (w₀ : M.State →ᵇ ℝ) (hsl₀ : M.SlackOf z₀ K w₀) (s : M.State)
    (hsl : M.consFloor < M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s)
    (hpos : 0 < M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s) :
    U.du (M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s)
      ≤ M.discount * M.eulerRhsOf U z₀ K w₀ s
          (M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s) := by
  set v := (M.household z₀ K).bellman w₀ with hv
  set p := M.policyOf z₀ K v s with hp
  set c := M.consumptionOf z₀ K v s with hc
  have hpm := M.policyOf_mem z₀ K v s
  have hpI : p ∈ Icc 0 M.assetCap := M.mem_Icc_of_mem_feasible z₀ K hpm
  have hβ := M.discount_pos.le
  have hsum : ∀ a, M.contOf z₀ v s a = ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
      * v (M.stateAt a ⟨ze.2, ze.1 :: s.2.node⟩) := fun a => rfl
  have hfloor : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ ze : Z × E, M.consFloor
      < M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
        + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h := by
    rw [Filter.eventually_all]
    intro ze
    have hcz := hsl₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
    have hcont : Continuous fun h : ℝ =>
        M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
        + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h :=
      continuous_const.add (continuous_const.mul continuous_id)
    have hlin := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [mul_zero, add_zero] at hlin
    exact hlin.eventually (lt_mem_nhds hcz)
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), U.du (c + h)
      ≤ M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, p) * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h) := by
    filter_upwards [Ioo_mem_nhdsGT hpos, hfloor] with h hh hfl
    obtain ⟨hh0, hh1⟩ := hh
    have hfeas : p - h ∈ (M.household z₀ K).feasible s :=
      ⟨by linarith, (by linarith : p - h ≤ p).trans hpm.2⟩
    have hdev := M.le_bellman_contOf z₀ K v hfeas
    have hval := M.bellman_eq_contOf z₀ K v s
    rw [hsum] at hdev hval
    have hcp : c = M.cash z₀ K s - p := rfl
    have hcash : M.cash z₀ K s - (p - h) = c + h := by linarith
    rw [hcash] at hdev
    have hchild : ∀ ze : Z × E,
        v (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩) - v (M.stateAt (p - h) ⟨ze.2, ze.1 :: s.2.node⟩)
          ≤ M.returnAt z₀ K (ze.1 :: s.2.node) * h
            * U.du (M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
              + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h) := by
      intro ze
      have hR := M.returnAt_nonneg z₀ K (ze.1 :: s.2.node)
      have hfz := hfl ze
      have hpI' : p - h ∈ Icc 0 M.assetCap := ⟨by linarith, by linarith [hpI.2]⟩
      have h1 := M.bellman_sub_le z₀ K w₀ hpI' hh0.le (by linarith [hpI.2])
        ⟨ze.2, ze.1 :: s.2.node⟩ (by rw [sub_add_cancel]; linarith)
      rw [sub_add_cancel] at h1
      have h2 := U.sub_le (x := M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩))
        (y := M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
          - M.returnAt z₀ K (ze.1 :: s.2.node) * h) (by linarith) (by nlinarith)
      have e1 : M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h
          = M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            - M.returnAt z₀ K (ze.1 :: s.2.node) * h := by ring
      rw [e1]
      have e2 : M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
          - (M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            - M.returnAt z₀ K (ze.1 :: s.2.node) * h) = M.returnAt z₀ K (ze.1 :: s.2.node) * h := by
        ring
      rw [e2] at h2
      linarith
    have hsumle : M.discount * (∑ ze : Z × E, M.shockProb z₀ ze (s, p)
            * v (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
          - ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
            * v (M.stateAt (p - h) ⟨ze.2, ze.1 :: s.2.node⟩))
        ≤ M.discount * (h * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h)) := by
      refine mul_le_mul_of_nonneg_left ?_ hβ
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun ze _ => ?_
      have := mul_le_mul_of_nonneg_left (hchild ze) (M.shockProb_nonneg' z₀ ze (s, p))
      nlinarith
    have hu := U.le_sub (x := c + h) (y := c) hsl.le (by linarith) (by linarith)
    have : c + h - c = h := by ring
    rw [this] at hu
    have key : h * U.du (c + h) ≤ h * (M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, p)
          * M.returnAt z₀ K (ze.1 :: s.2.node)
          * U.du (M.consumptionOf z₀ K w₀ (M.stateAt p ⟨ze.2, ze.1 :: s.2.node⟩)
            + (-1) * M.returnAt z₀ K (ze.1 :: s.2.node) * h)) := by
      nlinarith
    exact le_of_mul_le_mul_left key hh0
  have hlim1 := tendsto_const_nhds (x := M.discount).mul
    (M.tendsto_shiftedOf U z₀ K w₀ s p hsl₀ (-1))
  have hlim2 : Tendsto (fun h : ℝ => U.du (c + h)) (𝓝[>] 0) (𝓝 (U.du c)) := by
    have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hlin : Tendsto (fun h : ℝ => c + h) (𝓝[>] 0) (𝓝 c) := by
      simpa using (tendsto_const_nhds (x := c)).add hid
    exact (U.continuousAt hsl).tendsto.comp hlin
  exact le_of_tendsto_of_tendsto hlim2 hlim1 hev

end KSModel

end KrusellSmith

end LeanEconomics
