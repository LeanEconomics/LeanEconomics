/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.HomotheticLog
import LeanEconomics.Models.CRRA
import Mathlib.Analysis.Convex.Deriv

/-!
# The homothetic economy with CRRA utility: reduction to a saving-rate equation in `(z, K)`

`HomotheticLog.lean` treats log utility, where every household saves the fraction `β` of cash.
With CRRA utility `γ > 0` the saving rate depends on the aggregate state, but it is still common
to all households, whatever their wealth and idiosyncratic history.

**Rate trees** (`IsRateTree`). A saving rate `s` at every aggregate node, with `0 < s ≤ s̄ < 1`,
solving the **rate equation**

    (1 − s)^{−γ} s^γ = β Σ_{z'} π(z, z') m(z, z') g(z', K')^{1−γ} (1 − s')^{−γ},

where `m(z, z') = E[θ^{1−γ} | z, z']` is the same from every idiosyncratic state (`moment`).

* **`ratePlan_isOptimal`**: against the capital path, saving the fraction `s` of cash is optimal
  in the overtaking sense. Euler sufficiency: the plan's marginal utility solves the household's
  Euler equation at every history (`mu_step`), and the transversality term decays like `s̄^N`
  (`crraValue_sub_le`).
* **`condMean_rateWealth`**: mean wealth at an aggregate node is initial wealth times the product
  of `s g(z, K)` along the history.

**Rate functions** (`IsRateFunction`). A function `σ(z, K)` on a set of capital levels invariant
under `K' = σ(z, K) g(z, K) K`, solving the rate equation there.

* **`isSequentialEquilibriumCRRA_ratePath`**: the path of `K' = σ(z, K) g(z, K) K` is a sequential
  equilibrium from every initial shock and every initial distribution with finitely many wealth
  levels and mean in the set. It is recursive on `(z, K)`, and each household's saving is
  `σ(z, K) θ(e) g(z, K) a`.

So the heterogeneous economy reduces to one functional equation in `(z, K)`. Existence of a rate
function is in `HomotheticRate.lean`.
-/

open Finset

namespace LeanEconomics

namespace KrusellSmith

/-- **The tangent line of CRRA utility lies above it.** -/
theorem crraUtility_le_tangent {γ : ℝ} (hγ : 0 < γ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    crraUtility γ y ≤ crraUtility γ x + x ^ (-γ) * (y - x) := by
  have hc := (strictConcaveOn_crraUtility hγ).concaveOn
  rcases lt_trichotomy x y with h | h | h
  · have := hc.slope_le_of_hasDerivAt (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) h
      (hasDerivAt_crraUtility γ hx)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at this
    linarith
  · subst h
    simp
  · have := hc.le_slope_of_hasDerivAt (Set.mem_Ioi.2 hy) (Set.mem_Ioi.2 hx) h
      (hasDerivAt_crraUtility γ hx)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    linarith

theorem rpow_neg_mul_self {γ a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a * b * c) ^ (-γ) * b = a ^ (-γ) * b ^ (1 - γ) * c ^ (-γ) := by
  rw [Real.mul_rpow (mul_pos ha hb).le hc.le, Real.mul_rpow ha.le hb.le,
    show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add hb, Real.rpow_one]
  ring

theorem rpow_rate_fold {γ s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx : 0 < x) :
    (1 - s) ^ (-γ) * s ^ γ * (s * x) ^ (-γ) = ((1 - s) * x) ^ (-γ) := by
  have h1 : s ^ γ * s ^ (-γ) = 1 := by
    rw [← Real.rpow_add hs0, add_neg_cancel, Real.rpow_zero]
  rw [Real.mul_rpow hs0.le hx.le, Real.mul_rpow (sub_pos.2 hs1).le hx.le]
  linear_combination ((1 - s) ^ (-γ) * x ^ (-γ)) * h1

namespace HomotheticEconomy

variable {Z E : Type*} [Fintype Z] [Fintype E] (M : HomotheticEconomy Z E)

/-- **CRRA utility over `N + 1` periods** from the history `h`, under the plan `a`. -/
noncomputable def crraValue (γ : ℝ) (z₀ : Z) (e₀ : E) (K : List Z → ℝ) (a₀ : ℝ)
    (a : List (Z × E) → ℝ) : ℕ → List (Z × E) → ℝ
  | 0, h => crraUtility γ (M.cash z₀ K a₀ a h - a h)
  | N + 1, h => crraUtility γ (M.cash z₀ K a₀ a h - a h)
      + M.discount * ∑ ze, M.stepProb z₀ e₀ h ze * crraValue γ z₀ e₀ K a₀ a N (ze :: h)

/-- **Optimality in the overtaking sense**, CRRA utility. -/
def IsOptimalCRRA (γ : ℝ) (z₀ : Z) (e₀ : E) (K : List Z → ℝ) (a₀ : ℝ)
    (a : List (Z × E) → ℝ) : Prop :=
  M.Feasible z₀ K a₀ a ∧ ∀ b, M.Feasible z₀ K a₀ b → ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    M.crraValue γ z₀ e₀ K a₀ b N [] ≤ M.crraValue γ z₀ e₀ K a₀ a N [] + ε

/-- Wealth under the plan that saves the fraction `s` of cash at each aggregate node. -/
noncomputable def rateWealth (z₀ : Z) (K s : List Z → ℝ) (a₀ : ℝ) : List (Z × E) → ℝ
  | [] => a₀
  | _ :: h => s (h.map Prod.fst) * M.ret z₀ K h * rateWealth z₀ K s a₀ h

/-- **The plan**: save the fraction `s` of cash. -/
noncomputable def ratePlan (z₀ : Z) (K s : List Z → ℝ) (a₀ : ℝ) (h : List (Z × E)) : ℝ :=
  s (h.map Prod.fst) * M.ret z₀ K h * M.rateWealth z₀ K s a₀ h

variable (z₀ : Z) (e₀ : E) (K s : List Z → ℝ) (a₀ : ℝ)

theorem wealth_ratePlan : wealth a₀ (M.ratePlan z₀ K s a₀) = M.rateWealth z₀ K s a₀ := by
  funext h
  cases h <;> rfl

theorem cash_ratePlan (h : List (Z × E)) :
    M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h = M.ret z₀ K h * M.rateWealth z₀ K s a₀ h := by
  rw [cash, wealth_ratePlan]

/-- **Saving is the fraction `s` of cash.** -/
theorem ratePlan_eq (h : List (Z × E)) :
    M.ratePlan z₀ K s a₀ h = s (h.map Prod.fst) * M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h := by
  rw [cash_ratePlan, ratePlan, mul_assoc]

theorem cash_ratePlan_cons (ze : Z × E) (h : List (Z × E)) :
    M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) (ze :: h)
      = M.ret z₀ K (ze :: h)
        * (s (h.map Prod.fst) * M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h) := by
  change M.ret z₀ K (ze :: h) * M.ratePlan z₀ K s a₀ h = _
  rw [ratePlan_eq]

omit [Fintype Z] [Fintype E] in
theorem cur_fst (h : List (Z × E)) : (cur z₀ e₀ h).1 = shockAt z₀ (h.map Prod.fst) := by
  cases h <;> rfl

/-- **A rate tree**: positive capital, saving rates in `(0, s̄]` with `s̄ < 1`, a common moment
`m(z, z') = E[θ^{1−γ}]` of the idiosyncratic shock, and the rate equation at every node. -/
structure IsRateTree (γ : ℝ) (m : Z → Z → ℝ) (z₀ : Z) (K s : List Z → ℝ) (sbar : ℝ) : Prop where
  K_pos : ∀ zs, 0 < K zs
  s_pos : ∀ zs, 0 < s zs
  s_le : ∀ zs, s zs ≤ sbar
  sbar_lt : sbar < 1
  moment : ∀ z z' e, ∑ e', M.idioProb z z' e e' * M.shock e' ^ (1 - γ) = m z z'
  euler : ∀ zs, M.discount * ∑ z', M.aggProb (shockAt z₀ zs) z' * m (shockAt z₀ zs) z'
      * M.resources z' (K (z' :: zs)) ^ (1 - γ) * (1 - s (z' :: zs)) ^ (-γ)
    = (1 - s zs) ^ (-γ) * s zs ^ γ

namespace IsRateTree

variable {M z₀ K s} {γ sbar : ℝ} {m : Z → Z → ℝ} (R : M.IsRateTree γ m z₀ K s sbar)

include R in
theorem s_lt (zs : List Z) : s zs < 1 := (R.s_le zs).trans_lt R.sbar_lt

include R in
theorem rateWealth_pos {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∀ h : List (Z × E), 0 < M.rateWealth z₀ K s a₀ h
  | [] => ha₀
  | _ :: h => mul_pos (mul_pos (R.s_pos _) (M.ret_pos z₀ R.K_pos h)) (rateWealth_pos ha₀ h)

include R in
theorem cash_pos {a₀ : ℝ} (ha₀ : 0 < a₀) (h : List (Z × E)) :
    0 < M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h := by
  rw [cash_ratePlan]
  exact mul_pos (M.ret_pos z₀ R.K_pos h) (R.rateWealth_pos ha₀ h)

include R in
theorem feasible {a₀ : ℝ} (ha₀ : 0 < a₀) : M.Feasible z₀ K a₀ (M.ratePlan z₀ K s a₀) := by
  intro h
  have hx := R.cash_pos ha₀ h
  rw [ratePlan_eq]
  exact ⟨mul_pos (R.s_pos _) hx, by nlinarith [R.s_lt (h.map Prod.fst)]⟩

/-- The plan's consumption: the fraction `1 − s` of cash. -/
theorem cons_eq (a₀ : ℝ) (h : List (Z × E)) :
    M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h - M.ratePlan z₀ K s a₀ h
      = (1 - s (h.map Prod.fst)) * M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h := by
  rw [ratePlan_eq]
  ring

/-- The plan's marginal utility of consumption. -/
noncomputable def mu (_ : M.IsRateTree γ m z₀ K s sbar) (a₀ : ℝ) (h : List (Z × E)) : ℝ :=
  (M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h - M.ratePlan z₀ K s a₀ h) ^ (-γ)

include R in
theorem mu_pos {a₀ : ℝ} (ha₀ : 0 < a₀) (h : List (Z × E)) : 0 < R.mu a₀ h :=
  Real.rpow_pos_of_pos (sub_pos.2 (R.feasible ha₀ h).2) _

/-- **The household's Euler equation along the plan**: marginal utility is the discounted expected
return times next period's marginal utility. -/
theorem mu_step (e₀ : E) {a₀ : ℝ} (ha₀ : 0 < a₀) (h : List (Z × E)) :
    M.discount * ∑ ze, M.stepProb z₀ e₀ h ze * (R.mu a₀ (ze :: h) * M.ret z₀ K (ze :: h))
      = R.mu a₀ h := by
  set zs := h.map Prod.fst with hzs
  set x := M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h with hx
  have hxpos : 0 < x := R.cash_pos ha₀ h
  have hσ0 := R.s_pos zs
  have hσ1 := R.s_lt zs
  have hterm : ∀ ze : Z × E,
      M.stepProb z₀ e₀ h ze * (R.mu a₀ (ze :: h) * M.ret z₀ K (ze :: h))
        = M.aggProb (shockAt z₀ zs) ze.1
          * (M.idioProb (shockAt z₀ zs) ze.1 (cur z₀ e₀ h).2 ze.2 * M.shock ze.2 ^ (1 - γ))
          * (M.resources ze.1 (K (ze.1 :: zs)) ^ (1 - γ) * (1 - s (ze.1 :: zs)) ^ (-γ)
            * (s zs * x) ^ (-γ)) := by
    intro ze
    have hr : M.ret z₀ K (ze :: h) = M.shock ze.2 * M.resources ze.1 (K (ze.1 :: zs)) := rfl
    have hg : 0 < M.resources ze.1 (K (ze.1 :: zs)) := M.resources_pos _ _ (R.K_pos _)
    have hθ := M.shock_pos ze.2
    have h1 : 0 < 1 - s (ze.1 :: zs) := sub_pos.2 (R.s_lt _)
    have hmu : R.mu a₀ (ze :: h) * M.ret z₀ K (ze :: h)
        = (1 - s (ze.1 :: zs)) ^ (-γ) * M.ret z₀ K (ze :: h) ^ (1 - γ) * (s zs * x) ^ (-γ) := by
      rw [mu, cons_eq, cash_ratePlan_cons]
      change ((1 - s (ze.1 :: zs)) * (M.ret z₀ K (ze :: h) * (s zs * x))) ^ (-γ) * _ = _
      rw [← mul_assoc]
      exact rpow_neg_mul_self h1 (M.ret_pos z₀ R.K_pos _) (mul_pos hσ0 hxpos)
    rw [hmu, hr, Real.mul_rpow hθ.le hg.le, stepProb, cur_fst]
    ring
  rw [Finset.sum_congr rfl fun ze _ => hterm ze, Fintype.sum_prod_type]
  have hinner : ∀ z' : Z, ∑ e', M.aggProb (shockAt z₀ zs) z'
        * (M.idioProb (shockAt z₀ zs) z' (cur z₀ e₀ h).2 e' * M.shock e' ^ (1 - γ))
        * (M.resources z' (K (z' :: zs)) ^ (1 - γ) * (1 - s (z' :: zs)) ^ (-γ)
          * (s zs * x) ^ (-γ))
      = M.aggProb (shockAt z₀ zs) z' * m (shockAt z₀ zs) z'
          * M.resources z' (K (z' :: zs)) ^ (1 - γ) * (1 - s (z' :: zs)) ^ (-γ)
        * (s zs * x) ^ (-γ) := by
    intro z'
    rw [← Finset.sum_mul, ← Finset.mul_sum, R.moment]
    ring
  rw [Finset.sum_congr rfl fun z' _ => hinner z', ← Finset.sum_mul, ← mul_assoc, R.euler zs,
    rpow_rate_fold hσ0 hσ1 hxpos, mu, cons_eq]

/-- **Euler sufficiency.** From every history, a feasible plan `b` beats the plan over `N + 1`
periods by at most its advantage in cash, valued at the plan's marginal utility, plus a
transversality term that decays like `s̄^N`. -/
theorem crraValue_sub_le (hγ : 0 < γ) (e₀ : E) {a₀ : ℝ} (ha₀ : 0 < a₀) {b : List (Z × E) → ℝ}
    (hb : M.Feasible z₀ K a₀ b) : ∀ (N : ℕ) (h : List (Z × E)),
    M.crraValue γ z₀ e₀ K a₀ b N h - M.crraValue γ z₀ e₀ K a₀ (M.ratePlan z₀ K s a₀) N h
      ≤ R.mu a₀ h * (M.cash z₀ K a₀ b h - M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h)
        + sbar ^ N * (R.mu a₀ h * M.ratePlan z₀ K s a₀ h) := by
  have hβ := M.discount_pos
  have hsb0 : 0 ≤ sbar := (R.s_pos []).le.trans (R.s_le [])
  -- the first-period comparison
  have hfirst : ∀ h : List (Z × E),
      crraUtility γ (M.cash z₀ K a₀ b h - b h)
          - crraUtility γ (M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h - M.ratePlan z₀ K s a₀ h)
        ≤ R.mu a₀ h * ((M.cash z₀ K a₀ b h - b h)
          - (M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h - M.ratePlan z₀ K s a₀ h)) := by
    intro h
    have := crraUtility_le_tangent hγ (sub_pos.2 (R.feasible ha₀ h).2) (sub_pos.2 (hb h).2)
    rw [mu]
    linarith
  -- next period's marginal value of the plan's saving
  have hnext : ∀ h : List (Z × E),
      M.discount * ∑ ze, M.stepProb z₀ e₀ h ze
          * (R.mu a₀ (ze :: h) * M.ratePlan z₀ K s a₀ (ze :: h))
        ≤ sbar * (R.mu a₀ h * M.ratePlan z₀ K s a₀ h) := by
    intro h
    have hle : ∀ ze : Z × E, M.stepProb z₀ e₀ h ze
          * (R.mu a₀ (ze :: h) * M.ratePlan z₀ K s a₀ (ze :: h))
        ≤ sbar * (M.stepProb z₀ e₀ h ze * (R.mu a₀ (ze :: h) * M.ret z₀ K (ze :: h)))
          * M.ratePlan z₀ K s a₀ h := by
      intro ze
      have e1 : M.ratePlan z₀ K s a₀ (ze :: h)
          = s ((ze :: h).map Prod.fst) * (M.ret z₀ K (ze :: h) * M.ratePlan z₀ K s a₀ h) := by
        rw [ratePlan_eq]
        rfl
      rw [e1]
      have hnn : 0 ≤ M.stepProb z₀ e₀ h ze * (R.mu a₀ (ze :: h) * M.ret z₀ K (ze :: h))
          * M.ratePlan z₀ K s a₀ h :=
        mul_nonneg (mul_nonneg (M.stepProb_nonneg z₀ e₀ h ze)
          (mul_nonneg (R.mu_pos ha₀ _).le (M.ret_pos z₀ R.K_pos _).le)) (R.feasible ha₀ h).1.le
      have := mul_le_mul_of_nonneg_right (R.s_le ((ze :: h).map Prod.fst)) hnn
      nlinarith
    calc _ ≤ M.discount * ∑ ze, sbar
            * (M.stepProb z₀ e₀ h ze * (R.mu a₀ (ze :: h) * M.ret z₀ K (ze :: h)))
            * M.ratePlan z₀ K s a₀ h :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ze _ => hle ze) hβ.le
      _ = sbar * (R.mu a₀ h * M.ratePlan z₀ K s a₀ h) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, ← R.mu_step e₀ ha₀ h]
          ring
  intro N
  induction N with
  | zero =>
    intro h
    have h1 := hfirst h
    have hb0 := mul_pos (R.mu_pos ha₀ h) (hb h).1
    change crraUtility γ (M.cash z₀ K a₀ b h - b h)
        - crraUtility γ (M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h - M.ratePlan z₀ K s a₀ h) ≤ _
    rw [pow_zero, one_mul]
    nlinarith
  | succ N ih =>
    intro h
    have h1 := hfirst h
    have hchild : ∀ ze : Z × E,
        M.crraValue γ z₀ e₀ K a₀ b N (ze :: h)
            - M.crraValue γ z₀ e₀ K a₀ (M.ratePlan z₀ K s a₀) N (ze :: h)
          ≤ R.mu a₀ (ze :: h) * M.ret z₀ K (ze :: h) * (b h - M.ratePlan z₀ K s a₀ h)
            + sbar ^ N * (R.mu a₀ (ze :: h) * M.ratePlan z₀ K s a₀ (ze :: h)) := by
      intro ze
      refine (ih (ze :: h)).trans (le_of_eq ?_)
      have e1 : M.cash z₀ K a₀ b (ze :: h) = M.ret z₀ K (ze :: h) * b h := rfl
      have e2 : M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) (ze :: h)
          = M.ret z₀ K (ze :: h) * M.ratePlan z₀ K s a₀ h := rfl
      rw [e1, e2]
      ring
    have hsum : ∑ ze, M.stepProb z₀ e₀ h ze
          * (M.crraValue γ z₀ e₀ K a₀ b N (ze :: h)
            - M.crraValue γ z₀ e₀ K a₀ (M.ratePlan z₀ K s a₀) N (ze :: h))
        ≤ (∑ ze, M.stepProb z₀ e₀ h ze * (R.mu a₀ (ze :: h) * M.ret z₀ K (ze :: h)))
            * (b h - M.ratePlan z₀ K s a₀ h)
          + sbar ^ N * ∑ ze, M.stepProb z₀ e₀ h ze
            * (R.mu a₀ (ze :: h) * M.ratePlan z₀ K s a₀ (ze :: h)) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun ze _ => ?_
      have := mul_le_mul_of_nonneg_left (hchild ze) (M.stepProb_nonneg z₀ e₀ h ze)
      nlinarith
    have hsplit : M.crraValue γ z₀ e₀ K a₀ b (N + 1) h
          - M.crraValue γ z₀ e₀ K a₀ (M.ratePlan z₀ K s a₀) (N + 1) h
        = crraUtility γ (M.cash z₀ K a₀ b h - b h)
          - crraUtility γ (M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) h - M.ratePlan z₀ K s a₀ h)
          + M.discount * ∑ ze, M.stepProb z₀ e₀ h ze
            * (M.crraValue γ z₀ e₀ K a₀ b N (ze :: h)
              - M.crraValue γ z₀ e₀ K a₀ (M.ratePlan z₀ K s a₀) N (ze :: h)) := by
      simp only [crraValue, mul_sub, Finset.sum_sub_distrib]
      ring
    have hscaled := mul_le_mul_of_nonneg_left hsum hβ.le
    have hstep := R.mu_step e₀ ha₀ h
    have hn := mul_le_mul_of_nonneg_left (hnext h) (pow_nonneg hsb0 N)
    rw [hsplit, pow_succ]
    have e3 : M.discount * ((∑ ze, M.stepProb z₀ e₀ h ze
          * (R.mu a₀ (ze :: h) * M.ret z₀ K (ze :: h))) * (b h - M.ratePlan z₀ K s a₀ h)
        + sbar ^ N * ∑ ze, M.stepProb z₀ e₀ h ze
          * (R.mu a₀ (ze :: h) * M.ratePlan z₀ K s a₀ (ze :: h)))
        = R.mu a₀ h * (b h - M.ratePlan z₀ K s a₀ h)
          + sbar ^ N * (M.discount * ∑ ze, M.stepProb z₀ e₀ h ze
            * (R.mu a₀ (ze :: h) * M.ratePlan z₀ K s a₀ (ze :: h))) := by
      rw [← hstep]
      ring
    rw [e3] at hscaled
    nlinarith

include R in
/-- **Saving the fraction `s` of cash is optimal.** -/
theorem ratePlan_isOptimal (hγ : 0 < γ) (e₀ : E) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    M.IsOptimalCRRA γ z₀ e₀ K a₀ (M.ratePlan z₀ K s a₀) := by
  refine ⟨R.feasible ha₀, fun b hb ε hε => ?_⟩
  have hsb0 : 0 ≤ sbar := (R.s_pos []).le.trans (R.s_le [])
  set C := R.mu a₀ [] * M.ratePlan z₀ K s a₀ [] with hC
  have hC0 : 0 < C := mul_pos (R.mu_pos ha₀ []) (R.feasible ha₀ []).1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hC0) R.sbar_lt
  refine ⟨n, fun N hN => ?_⟩
  have h := R.crraValue_sub_le hγ e₀ ha₀ hb N []
  have hroot : M.cash z₀ K a₀ b [] - M.cash z₀ K a₀ (M.ratePlan z₀ K s a₀) [] = 0 := sub_self _
  rw [hroot, mul_zero, zero_add] at h
  have hpow : sbar ^ N ≤ sbar ^ n := pow_le_pow_of_le_one hsb0 R.sbar_lt.le hN
  have : sbar ^ N * C < ε := by
    rw [lt_div_iff₀ hC0] at hn
    nlinarith
  linarith

/-! ### Aggregation -/

theorem condMean_cons_rateWealth (e₀ : E) (a₀ : ℝ) (z' : Z) (zs : List Z) :
    M.condMean z₀ e₀ (z' :: zs) (M.rateWealth z₀ K s a₀)
      = s zs * M.condMean z₀ e₀ zs fun h => M.ret z₀ K h * M.rateWealth z₀ K s a₀ h := by
  rw [← M.condMean_mul]
  change M.condMean z₀ e₀ zs _ = _
  refine M.condMean_congr z₀ e₀ zs fun h hh => ?_
  change ∑ e', M.idioProb (cur z₀ e₀ h).1 z' (cur z₀ e₀ h).2 e'
    * (s (h.map Prod.fst) * M.ret z₀ K h * M.rateWealth z₀ K s a₀ h) = _
  rw [← Finset.sum_mul, M.idioProb_sum, one_mul, hh, mul_assoc]

/-- The idiosyncratic shock averages out. -/
theorem condMean_ret_mul_rateWealth (e₀ : E) (a₀ : ℝ) : ∀ zs : List Z,
    M.condMean z₀ e₀ zs (fun h => M.ret z₀ K h * M.rateWealth z₀ K s a₀ h)
      = M.resources (shockAt z₀ zs) (K zs) * M.condMean z₀ e₀ zs (M.rateWealth z₀ K s a₀)
  | [] => rfl
  | z :: zs => by
    rw [shockAt_cons, condMean_cons_rateWealth, ← M.condMean_mul, ← M.condMean_mul]
    change M.condMean z₀ e₀ zs _ = _
    refine M.condMean_congr z₀ e₀ zs fun h hh => ?_
    change ∑ e', M.idioProb (cur z₀ e₀ h).1 z (cur z₀ e₀ h).2 e'
      * (M.shock e' * M.resources z (K (z :: h.map Prod.fst))
        * (s (h.map Prod.fst) * M.ret z₀ K h * M.rateWealth z₀ K s a₀ h)) = _
    rw [hh]
    have : ∀ e', M.idioProb (cur z₀ e₀ h).1 z (cur z₀ e₀ h).2 e'
        * (M.shock e' * M.resources z (K (z :: zs))
          * (s zs * M.ret z₀ K h * M.rateWealth z₀ K s a₀ h))
        = M.idioProb (cur z₀ e₀ h).1 z (cur z₀ e₀ h).2 e' * M.shock e'
          * (M.resources z (K (z :: zs))
            * (s zs * (M.ret z₀ K h * M.rateWealth z₀ K s a₀ h))) := fun e' => by ring
    simp only [this]
    rw [← Finset.sum_mul, M.shock_mean, one_mul]

end IsRateTree

/-- The growth of mean wealth along an aggregate history. -/
noncomputable def rateGrowth (z₀ : Z) (K s : List Z → ℝ) : List Z → ℝ
  | [] => 1
  | _ :: zs => s zs * M.resources (shockAt z₀ zs) (K zs) * rateGrowth z₀ K s zs

/-- **Mean wealth at an aggregate node** is initial wealth times the growth along the history. -/
theorem condMean_rateWealth : ∀ zs : List Z,
    M.condMean z₀ e₀ zs (M.rateWealth z₀ K s a₀) = a₀ * M.rateGrowth z₀ K s zs
  | [] => (mul_one a₀).symm
  | z' :: zs => by
    rw [IsRateTree.condMean_cons_rateWealth, IsRateTree.condMean_ret_mul_rateWealth,
      condMean_rateWealth zs]
    change _ = a₀ * (s zs * M.resources (shockAt z₀ zs) (K zs) * M.rateGrowth z₀ K s zs)
    ring

/-! ### Equilibrium -/

variable {ι : Type*} [Fintype ι]

/-- **Sequential equilibrium**, CRRA utility. -/
def IsSequentialEquilibriumCRRA (γ : ℝ) (z₀ : Z) (ν w : ι → ℝ) (t : ι → E)
    (K : List Z → ℝ) : Prop :=
  (∀ zs, 0 < K zs) ∧ ∃ plan : ι → List (Z × E) → ℝ,
    (∀ i, M.IsOptimalCRRA γ z₀ (t i) K (w i) (plan i)) ∧
      ∀ zs, K zs = ∑ i, ν i * M.condMean z₀ (t i) zs (wealth (w i) (plan i))

/-- **The capital path** of a saving-rate function from `(z₀, k₀)`. -/
noncomputable def ratePath (σ : Z → ℝ → ℝ) (z₀ : Z) (k₀ : ℝ) : List Z → ℝ
  | [] => k₀
  | _ :: zs => σ (shockAt z₀ zs) (ratePath σ z₀ k₀ zs)
      * M.resources (shockAt z₀ zs) (ratePath σ z₀ k₀ zs) * ratePath σ z₀ k₀ zs

/-- The saving rates along the path. -/
noncomputable def rateAt (σ : Z → ℝ → ℝ) (z₀ : Z) (k₀ : ℝ) (zs : List Z) : ℝ :=
  σ (shockAt z₀ zs) (M.ratePath σ z₀ k₀ zs)

/-- **A saving-rate function** on a set `I` of positive capital levels, invariant under
`K' = σ(z, K) g(z, K) K`: rates in `(0, s̄]`, `s̄ < 1`, solving the rate equation on `I`. -/
structure IsRateFunction (γ : ℝ) (m : Z → Z → ℝ) (I : Set ℝ) (σ : Z → ℝ → ℝ) (sbar : ℝ) :
    Prop where
  pos : ∀ k ∈ I, 0 < k
  σ_pos : ∀ z, ∀ k ∈ I, 0 < σ z k
  σ_le : ∀ z, ∀ k ∈ I, σ z k ≤ sbar
  sbar_lt : sbar < 1
  inv : ∀ z, ∀ k ∈ I, σ z k * M.resources z k * k ∈ I
  moment : ∀ z z' e, ∑ e', M.idioProb z z' e e' * M.shock e' ^ (1 - γ) = m z z'
  euler : ∀ z, ∀ k ∈ I, M.discount * ∑ z', M.aggProb z z' * m z z'
      * M.resources z' (σ z k * M.resources z k * k) ^ (1 - γ)
      * (1 - σ z' (σ z k * M.resources z k * k)) ^ (-γ)
    = (1 - σ z k) ^ (-γ) * σ z k ^ γ

namespace IsRateFunction

variable {M} {γ sbar : ℝ} {m : Z → Z → ℝ} {I : Set ℝ} {σ : Z → ℝ → ℝ}
  (F : M.IsRateFunction γ m I σ sbar)

include F in
theorem ratePath_mem {k₀ : ℝ} (hk : k₀ ∈ I) : ∀ zs, M.ratePath σ z₀ k₀ zs ∈ I
  | [] => hk
  | _ :: zs => F.inv _ _ (ratePath_mem hk zs)

include F in
/-- A rate function gives a rate tree along its capital path. -/
theorem isRateTree {k₀ : ℝ} (hk : k₀ ∈ I) :
    M.IsRateTree γ m z₀ (M.ratePath σ z₀ k₀) (M.rateAt σ z₀ k₀) sbar where
  K_pos zs := F.pos _ (F.ratePath_mem z₀ hk zs)
  s_pos zs := F.σ_pos _ _ (F.ratePath_mem z₀ hk zs)
  s_le zs := F.σ_le _ _ (F.ratePath_mem z₀ hk zs)
  sbar_lt := F.sbar_lt
  moment := F.moment
  euler zs := F.euler _ _ (F.ratePath_mem z₀ hk zs)

theorem ratePath_eq (k₀ : ℝ) : ∀ zs,
    M.ratePath σ z₀ k₀ zs
      = k₀ * M.rateGrowth z₀ (M.ratePath σ z₀ k₀) (M.rateAt σ z₀ k₀) zs
  | [] => (mul_one k₀).symm
  | z' :: zs => by
    change M.rateAt σ z₀ k₀ zs * M.resources (shockAt z₀ zs) (M.ratePath σ z₀ k₀ zs)
        * M.ratePath σ z₀ k₀ zs
      = k₀ * (M.rateAt σ z₀ k₀ zs * M.resources (shockAt z₀ zs) (M.ratePath σ z₀ k₀ zs)
        * M.rateGrowth z₀ (M.ratePath σ z₀ k₀) (M.rateAt σ z₀ k₀) zs)
    have h := ratePath_eq k₀ zs
    have : k₀ * (M.rateAt σ z₀ k₀ zs * M.resources (shockAt z₀ zs) (M.ratePath σ z₀ k₀ zs)
          * M.rateGrowth z₀ (M.ratePath σ z₀ k₀) (M.rateAt σ z₀ k₀) zs)
        = M.rateAt σ z₀ k₀ zs * M.resources (shockAt z₀ zs) (M.ratePath σ z₀ k₀ zs)
          * (k₀ * M.rateGrowth z₀ (M.ratePath σ z₀ k₀) (M.rateAt σ z₀ k₀) zs) := by ring
    rw [this, ← h]

include F in
/-- **Recursive equilibrium on `(z, K)` with CRRA utility and uninsured idiosyncratic risk.** From
every initial shock and every initial distribution of positive wealth levels with mean in `I`,
the path of `K' = σ(z, K) g(z, K) K` is a sequential equilibrium, in which every household saves
the fraction `σ(z, K)` of its cash. -/
theorem isSequentialEquilibriumCRRA_ratePath (hγ : 0 < γ) (ν w : ι → ℝ) (t : ι → E)
    (hw : ∀ i, 0 < w i) (hk : ∑ i, ν i * w i ∈ I) :
    M.IsSequentialEquilibriumCRRA γ z₀ ν w t (M.ratePath σ z₀ (∑ i, ν i * w i)) := by
  have R := F.isRateTree z₀ hk
  refine ⟨R.K_pos, fun i => M.ratePlan z₀ (M.ratePath σ z₀ (∑ i, ν i * w i))
      (M.rateAt σ z₀ (∑ i, ν i * w i)) (w i),
    fun i => R.ratePlan_isOptimal hγ (t i) (hw i), fun zs => ?_⟩
  simp only [wealth_ratePlan, condMean_rateWealth]
  rw [ratePath_eq z₀ _ zs, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end IsRateFunction

end HomotheticEconomy

end KrusellSmith

end LeanEconomics
