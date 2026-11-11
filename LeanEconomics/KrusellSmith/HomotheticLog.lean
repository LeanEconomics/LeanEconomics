/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Model
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A homothetic economy with uninsured idiosyncratic risk: recursive equilibrium on `(z, K)`

Route 2 of the heterogeneous-household programme (`CROSS_SECTION_PLAN.md`). The proportional
economy (`ProportionalEquilibrium.lean`) has permanent types only. Here households face genuine
uninsured idiosyncratic risk, the wealth distribution spreads out over time, prices feed back
through aggregate capital, and still the equilibrium is recursive in the aggregate shock and
aggregate capital alone.

**The economy** (`HomotheticEconomy`). Aggregate shocks follow a Markov chain. A household holding
wealth `a` at a node with aggregate capital `K` and shock `z` has cash

    x = θ(e) · g(z, K) · a,

where `g(z, K)` is gross resources per unit of capital (with Cobb–Douglas,
`g = 1 − δ + z K^{α−1} L^{1−α}`: capital and labour income, the household's share of labour income
being its share of wealth) and `θ(e) > 0` is an idiosyncratic shock, Markov in `e`, with
conditional mean one from every state (`shock_mean`). Persistence in the higher moments of `θ` is
allowed. There is no insurance and no borrowing; utility is logarithmic.

**The household** (`logPlan_isOptimal`). Against *any* positive capital path, saving the fraction
`β` of cash is optimal in the overtaking sense (`IsOptimal`: no feasible plan does better by more
than `ε` on long horizons). The proof is Euler sufficiency with the transversality term in closed
form: `W_N(b) − W_N(p) ≤ β^{N+1} / (1 − β)` (`partialValue_sub_le`).

**Aggregation** (`condMean_logWealth`). Mean wealth at an aggregate node, conditional on the
aggregate history, is `a₀` times the product of `β g(z, K)` along the history: the idiosyncratic
shocks average out by `shock_mean`, whatever the household's history.

**Equilibrium** (`isSequentialEquilibrium_logPath`). From every initial shock and every initial
distribution with finitely many wealth levels, the path

    K' = β · g(z, K) · K

is a sequential equilibrium. It is recursive on `(z, K)` (`logPath_cons`), and every household's
saving is `β θ(e) g(z, K) a`: a function of the aggregate state `(z, K)` and its own state.
-/

open Finset

namespace LeanEconomics

namespace KrusellSmith

/-- **A homothetic economy**: all of a household's income is proportional to its wealth, and
subject to an idiosyncratic shock with conditional mean one. -/
structure HomotheticEconomy (Z E : Type*) [Fintype Z] [Fintype E] where
  /-- The aggregate chain. -/
  aggProb : Z → Z → ℝ
  aggProb_nonneg : ∀ z z', 0 ≤ aggProb z z'
  aggProb_sum : ∀ z, ∑ z', aggProb z z' = 1
  /-- The idiosyncratic chain, given the aggregate transition. -/
  idioProb : Z → Z → E → E → ℝ
  idioProb_nonneg : ∀ z z' e e', 0 ≤ idioProb z z' e e'
  idioProb_sum : ∀ z z' e, ∑ e', idioProb z z' e e' = 1
  /-- The idiosyncratic shock to income. -/
  shock : E → ℝ
  shock_pos : ∀ e, 0 < shock e
  /-- The shock has conditional mean one from every state. -/
  shock_mean : ∀ z z' e, ∑ e', idioProb z z' e e' * shock e' = 1
  discount : ℝ
  discount_pos : 0 < discount
  discount_lt_one : discount < 1
  /-- Gross resources per unit of capital. -/
  resources : Z → ℝ → ℝ
  resources_pos : ∀ z k, 0 < k → 0 < resources z k

namespace HomotheticEconomy

variable {Z E : Type*} [Fintype Z] [Fintype E] (M : HomotheticEconomy Z E)

/-- The current shocks at a joint history (newest first). -/
def cur (z₀ : Z) (e₀ : E) (h : List (Z × E)) : Z × E := h.headD (z₀, e₀)

/-- The gross return on wealth at a joint history, along the capital path `K`: at the root the
initial wealth is already net of the idiosyncratic shock. -/
noncomputable def ret (z₀ : Z) (K : List Z → ℝ) : List (Z × E) → ℝ
  | [] => M.resources z₀ (K [])
  | ze :: h => M.shock ze.2 * M.resources ze.1 (K (ze.1 :: h.map Prod.fst))

/-- Wealth entering a history, under the saving plan `a`. -/
def wealth (a₀ : ℝ) (a : List (Z × E) → ℝ) : List (Z × E) → ℝ
  | [] => a₀
  | _ :: h => a h

/-- Cash on hand. -/
noncomputable def cash (z₀ : Z) (K : List Z → ℝ) (a₀ : ℝ) (a : List (Z × E) → ℝ)
    (h : List (Z × E)) : ℝ :=
  M.ret z₀ K h * wealth a₀ a h

/-- **Feasible plans**: positive saving and positive consumption at every history. -/
def Feasible (z₀ : Z) (K : List Z → ℝ) (a₀ : ℝ) (a : List (Z × E) → ℝ) : Prop :=
  ∀ h, 0 < a h ∧ a h < M.cash z₀ K a₀ a h

/-- The probability of the next joint shock. -/
noncomputable def stepProb (z₀ : Z) (e₀ : E) (h : List (Z × E)) (ze : Z × E) : ℝ :=
  M.aggProb (cur z₀ e₀ h).1 ze.1 * M.idioProb (cur z₀ e₀ h).1 ze.1 (cur z₀ e₀ h).2 ze.2

theorem stepProb_nonneg (z₀ : Z) (e₀ : E) (h : List (Z × E)) (ze : Z × E) :
    0 ≤ M.stepProb z₀ e₀ h ze :=
  mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _)

theorem stepProb_sum (z₀ : Z) (e₀ : E) (h : List (Z × E)) : ∑ ze, M.stepProb z₀ e₀ h ze = 1 := by
  simp only [stepProb]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, M.idioProb_sum, mul_one, M.aggProb_sum]

/-- **Utility over `N + 1` periods** from the history `h`, under the plan `a`. -/
noncomputable def partialValue (z₀ : Z) (e₀ : E) (K : List Z → ℝ) (a₀ : ℝ)
    (a : List (Z × E) → ℝ) : ℕ → List (Z × E) → ℝ
  | 0, h => Real.log (M.cash z₀ K a₀ a h - a h)
  | N + 1, h => Real.log (M.cash z₀ K a₀ a h - a h)
      + M.discount * ∑ ze, M.stepProb z₀ e₀ h ze * partialValue z₀ e₀ K a₀ a N (ze :: h)

/-- **Optimality in the overtaking sense**: feasible, and no feasible plan does better by more than
`ε` on long horizons. -/
def IsOptimal (z₀ : Z) (e₀ : E) (K : List Z → ℝ) (a₀ : ℝ) (a : List (Z × E) → ℝ) : Prop :=
  M.Feasible z₀ K a₀ a ∧ ∀ b, M.Feasible z₀ K a₀ b → ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    M.partialValue z₀ e₀ K a₀ b N [] ≤ M.partialValue z₀ e₀ K a₀ a N [] + ε

/-! ### The plan: save the fraction `β` of cash -/

/-- Wealth under the plan. -/
noncomputable def logWealth (z₀ : Z) (K : List Z → ℝ) (a₀ : ℝ) : List (Z × E) → ℝ
  | [] => a₀
  | _ :: h => M.discount * M.ret z₀ K h * logWealth z₀ K a₀ h

/-- **The plan**: save the fraction `β` of cash. -/
noncomputable def logPlan (z₀ : Z) (K : List Z → ℝ) (a₀ : ℝ) (h : List (Z × E)) : ℝ :=
  M.discount * M.ret z₀ K h * M.logWealth z₀ K a₀ h

variable (z₀ : Z) (e₀ : E) (K : List Z → ℝ) (a₀ : ℝ)

theorem wealth_logPlan : wealth a₀ (M.logPlan z₀ K a₀) = M.logWealth z₀ K a₀ := by
  funext h
  cases h <;> rfl

theorem cash_logPlan (h : List (Z × E)) :
    M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h = M.ret z₀ K h * M.logWealth z₀ K a₀ h := by
  rw [cash, wealth_logPlan]

/-- **Saving is the fraction `β` of cash.** -/
theorem logPlan_eq (h : List (Z × E)) :
    M.logPlan z₀ K a₀ h = M.discount * M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h := by
  rw [cash_logPlan, logPlan, mul_assoc]

variable {K a₀}

theorem ret_pos (hK : ∀ zs, 0 < K zs) : ∀ h : List (Z × E), 0 < M.ret z₀ K h
  | [] => M.resources_pos _ _ (hK _)
  | ze :: _ => mul_pos (M.shock_pos ze.2) (M.resources_pos _ _ (hK _))

theorem logWealth_pos (hK : ∀ zs, 0 < K zs) (ha₀ : 0 < a₀) :
    ∀ h : List (Z × E), 0 < M.logWealth z₀ K a₀ h
  | [] => ha₀
  | _ :: h => mul_pos (mul_pos M.discount_pos (M.ret_pos z₀ hK h)) (logWealth_pos hK ha₀ h)

theorem cash_logPlan_pos (hK : ∀ zs, 0 < K zs) (ha₀ : 0 < a₀) (h : List (Z × E)) :
    0 < M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h := by
  rw [cash_logPlan]
  exact mul_pos (M.ret_pos z₀ hK h) (M.logWealth_pos z₀ hK ha₀ h)

theorem feasible_logPlan (hK : ∀ zs, 0 < K zs) (ha₀ : 0 < a₀) :
    M.Feasible z₀ K a₀ (M.logPlan z₀ K a₀) := by
  intro h
  have hx := M.cash_logPlan_pos z₀ hK ha₀ h
  rw [logPlan_eq]
  exact ⟨mul_pos M.discount_pos hx, by nlinarith [M.discount_lt_one]⟩

/-- **Euler sufficiency with the transversality term in closed form.** From every history, a
feasible plan `b` beats the plan over `N + 1` periods by at most its advantage in cash, valued at
the plan's marginal utility, plus `β^{N+1} / (1 − β)`. -/
theorem partialValue_sub_le (hK : ∀ zs, 0 < K zs) (ha₀ : 0 < a₀) {b : List (Z × E) → ℝ}
    (hb : M.Feasible z₀ K a₀ b) : ∀ (N : ℕ) (h : List (Z × E)),
    M.partialValue z₀ e₀ K a₀ b N h - M.partialValue z₀ e₀ K a₀ (M.logPlan z₀ K a₀) N h
      ≤ (M.cash z₀ K a₀ b h - M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h)
          / ((1 - M.discount) * M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h)
        + M.discount ^ (N + 1) / (1 - M.discount) := by
  have hβ := M.discount_pos
  have hβ1 : 0 < 1 - M.discount := sub_pos.2 M.discount_lt_one
  -- the first-period comparison, common to both cases
  have hfirst : ∀ h : List (Z × E),
      Real.log (M.cash z₀ K a₀ b h - b h)
          - Real.log (M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h - M.logPlan z₀ K a₀ h)
        ≤ (M.cash z₀ K a₀ b h - b h)
          / ((1 - M.discount) * M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h) - 1 := by
    intro h
    have hx := M.cash_logPlan_pos z₀ hK ha₀ h
    have hc : 0 < M.cash z₀ K a₀ b h - b h := sub_pos.2 (hb h).2
    have ht : 0 < (1 - M.discount) * M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h := mul_pos hβ1 hx
    have he : M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h - M.logPlan z₀ K a₀ h
        = (1 - M.discount) * M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h := by
      rw [logPlan_eq]
      ring
    rw [he, ← Real.log_div hc.ne' ht.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hc ht)
  intro N
  induction N with
  | zero =>
    intro h
    have hx := M.cash_logPlan_pos z₀ hK ha₀ h
    have ht : 0 < (1 - M.discount) * M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h := mul_pos hβ1 hx
    have h1 := hfirst h
    have hb0 := (hb h).1
    change Real.log (M.cash z₀ K a₀ b h - b h)
        - Real.log (M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h - M.logPlan z₀ K a₀ h) ≤ _
    refine h1.trans ?_
    rw [zero_add, pow_one, div_add_div _ _ ht.ne' hβ1.ne', div_sub_one ht.ne',
      div_le_div_iff₀ ht (mul_pos ht hβ1)]
    nlinarith [mul_pos hb0 hβ1, mul_pos ht hβ1, mul_pos (mul_pos hb0 hβ1) ht]
  | succ N ih =>
    intro h
    set xp := M.cash z₀ K a₀ (M.logPlan z₀ K a₀) h with hxp
    set xb := M.cash z₀ K a₀ b h with hxb
    have hx : 0 < xp := M.cash_logPlan_pos z₀ hK ha₀ h
    have ht : 0 < (1 - M.discount) * xp := mul_pos hβ1 hx
    have h1 := hfirst h
    have hb0 := (hb h).1
    -- the children
    have hchild : ∀ ze : Z × E,
        M.partialValue z₀ e₀ K a₀ b N (ze :: h)
            - M.partialValue z₀ e₀ K a₀ (M.logPlan z₀ K a₀) N (ze :: h)
          ≤ (b h - M.discount * xp) / (M.discount * ((1 - M.discount) * xp))
            + M.discount ^ (N + 1) / (1 - M.discount) := by
      intro ze
      refine (ih (ze :: h)).trans (le_of_eq ?_)
      have hr := M.ret_pos z₀ hK (ze :: h)
      have e1 : M.cash z₀ K a₀ b (ze :: h) = M.ret z₀ K (ze :: h) * b h := rfl
      have e2 : M.cash z₀ K a₀ (M.logPlan z₀ K a₀) (ze :: h)
          = M.ret z₀ K (ze :: h) * (M.discount * xp) := by
        change M.ret z₀ K (ze :: h) * M.logPlan z₀ K a₀ h = _
        rw [logPlan_eq]
      rw [e1, e2]
      congr 1
      field_simp
    have hsum : ∑ ze, M.stepProb z₀ e₀ h ze
          * (M.partialValue z₀ e₀ K a₀ b N (ze :: h)
            - M.partialValue z₀ e₀ K a₀ (M.logPlan z₀ K a₀) N (ze :: h))
        ≤ (b h - M.discount * xp) / (M.discount * ((1 - M.discount) * xp))
            + M.discount ^ (N + 1) / (1 - M.discount) := by
      calc _ ≤ ∑ ze, M.stepProb z₀ e₀ h ze
              * ((b h - M.discount * xp) / (M.discount * ((1 - M.discount) * xp))
                + M.discount ^ (N + 1) / (1 - M.discount)) :=
            Finset.sum_le_sum fun ze _ =>
              mul_le_mul_of_nonneg_left (hchild ze) (M.stepProb_nonneg z₀ e₀ h ze)
        _ = _ := by rw [← Finset.sum_mul, M.stepProb_sum, one_mul]
    have hsplit : M.partialValue z₀ e₀ K a₀ b (N + 1) h
          - M.partialValue z₀ e₀ K a₀ (M.logPlan z₀ K a₀) (N + 1) h
        = Real.log (xb - b h) - Real.log (xp - M.logPlan z₀ K a₀ h)
          + M.discount * ∑ ze, M.stepProb z₀ e₀ h ze
            * (M.partialValue z₀ e₀ K a₀ b N (ze :: h)
              - M.partialValue z₀ e₀ K a₀ (M.logPlan z₀ K a₀) N (ze :: h)) := by
      simp only [partialValue, mul_sub, Finset.sum_sub_distrib]
      ring
    have hscaled := mul_le_mul_of_nonneg_left hsum hβ.le
    have halg : (xb - b h) / ((1 - M.discount) * xp) - 1
          + M.discount * ((b h - M.discount * xp) / (M.discount * ((1 - M.discount) * xp))
            + M.discount ^ (N + 1) / (1 - M.discount))
        = (xb - xp) / ((1 - M.discount) * xp) + M.discount ^ (N + 1 + 1) / (1 - M.discount) := by
      field_simp
      ring
    rw [hsplit]
    linarith

/-- **Saving the fraction `β` of cash is optimal**, against every positive capital path. -/
theorem logPlan_isOptimal (hK : ∀ zs, 0 < K zs) (ha₀ : 0 < a₀) :
    M.IsOptimal z₀ e₀ K a₀ (M.logPlan z₀ K a₀) := by
  refine ⟨M.feasible_logPlan z₀ hK ha₀, fun b hb ε hε => ?_⟩
  have hβ1 : 0 < 1 - M.discount := sub_pos.2 M.discount_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hβ1) M.discount_lt_one
  refine ⟨n, fun N hN => ?_⟩
  have h := M.partialValue_sub_le z₀ e₀ hK ha₀ hb N []
  have hroot : M.cash z₀ K a₀ b [] - M.cash z₀ K a₀ (M.logPlan z₀ K a₀) [] = 0 := sub_self _
  rw [hroot, zero_div, zero_add] at h
  have hpow : M.discount ^ (N + 1) ≤ M.discount ^ n :=
    pow_le_pow_of_le_one M.discount_pos.le M.discount_lt_one.le (by omega)
  have : M.discount ^ (N + 1) / (1 - M.discount) < ε := by
    rw [div_lt_iff₀ hβ1]
    linarith
  linarith

/-! ### Aggregation -/

/-- **The mean of `F` at an aggregate node**, over the idiosyncratic histories, conditional on the
aggregate history. -/
noncomputable def condMean (z₀ : Z) (e₀ : E) : List Z → (List (Z × E) → ℝ) → ℝ
  | [], F => F []
  | z' :: zs, F => condMean z₀ e₀ zs fun h =>
      ∑ e', M.idioProb (cur z₀ e₀ h).1 z' (cur z₀ e₀ h).2 e' * F ((z', e') :: h)

/-- The mean at a node depends only on the histories over that node. -/
theorem condMean_congr : ∀ (zs : List Z) {F G : List (Z × E) → ℝ},
    (∀ h, h.map Prod.fst = zs → F h = G h) → M.condMean z₀ e₀ zs F = M.condMean z₀ e₀ zs G
  | [], _, _, hFG => hFG [] rfl
  | z' :: zs, _, _, hFG => by
    refine condMean_congr zs fun h hh => Finset.sum_congr rfl fun e' _ => ?_
    rw [hFG ((z', e') :: h) (by rw [List.map_cons, hh])]

theorem condMean_mul (c : ℝ) : ∀ (zs : List Z) (F : List (Z × E) → ℝ),
    M.condMean z₀ e₀ zs (fun h => c * F h) = c * M.condMean z₀ e₀ zs F
  | [], _ => rfl
  | z' :: zs, F => by
    change M.condMean z₀ e₀ zs _ = c * M.condMean z₀ e₀ zs _
    rw [← condMean_mul c zs]
    congr 1
    funext h
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e' _ => by ring

variable (K a₀)

theorem condMean_cons_logWealth (z' : Z) (zs : List Z) :
    M.condMean z₀ e₀ (z' :: zs) (M.logWealth z₀ K a₀)
      = M.condMean z₀ e₀ zs fun h => M.discount * (M.ret z₀ K h * M.logWealth z₀ K a₀ h) := by
  change M.condMean z₀ e₀ zs _ = _
  congr 1
  funext h
  change ∑ e', M.idioProb (cur z₀ e₀ h).1 z' (cur z₀ e₀ h).2 e'
    * (M.discount * M.ret z₀ K h * M.logWealth z₀ K a₀ h) = _
  rw [← Finset.sum_mul, M.idioProb_sum, one_mul, mul_assoc]

/-- **The idiosyncratic shock averages out**: mean cash at a node is resources per unit of capital
times mean wealth. -/
theorem condMean_ret_mul_logWealth : ∀ zs : List Z,
    M.condMean z₀ e₀ zs (fun h => M.ret z₀ K h * M.logWealth z₀ K a₀ h)
      = M.resources (shockAt z₀ zs) (K zs) * M.condMean z₀ e₀ zs (M.logWealth z₀ K a₀)
  | [] => rfl
  | z :: zs => by
    rw [shockAt_cons, M.condMean_cons_logWealth, ← M.condMean_mul]
    change M.condMean z₀ e₀ zs _ = _
    refine M.condMean_congr z₀ e₀ zs fun h hh => ?_
    change ∑ e', M.idioProb (cur z₀ e₀ h).1 z (cur z₀ e₀ h).2 e'
      * (M.shock e' * M.resources z (K (z :: h.map Prod.fst))
        * (M.discount * M.ret z₀ K h * M.logWealth z₀ K a₀ h)) = _
    rw [hh]
    have : ∀ e', M.idioProb (cur z₀ e₀ h).1 z (cur z₀ e₀ h).2 e'
        * (M.shock e' * M.resources z (K (z :: zs))
          * (M.discount * M.ret z₀ K h * M.logWealth z₀ K a₀ h))
        = M.idioProb (cur z₀ e₀ h).1 z (cur z₀ e₀ h).2 e' * M.shock e'
          * (M.resources z (K (z :: zs))
            * (M.discount * (M.ret z₀ K h * M.logWealth z₀ K a₀ h))) := fun e' => by ring
    simp only [this]
    rw [← Finset.sum_mul, M.shock_mean, one_mul]

/-- The growth of mean wealth along an aggregate history. -/
noncomputable def logGrowth (z₀ : Z) (K : List Z → ℝ) : List Z → ℝ
  | [] => 1
  | _ :: zs => M.discount * M.resources (shockAt z₀ zs) (K zs) * logGrowth z₀ K zs

/-- **Mean wealth at an aggregate node** is initial wealth times the growth along the history,
whatever the idiosyncratic history. -/
theorem condMean_logWealth : ∀ zs : List Z,
    M.condMean z₀ e₀ zs (M.logWealth z₀ K a₀) = a₀ * M.logGrowth z₀ K zs
  | [] => (mul_one a₀).symm
  | z' :: zs => by
    rw [M.condMean_cons_logWealth, M.condMean_mul, M.condMean_ret_mul_logWealth,
      condMean_logWealth zs]
    change _ = a₀ * (M.discount * M.resources (shockAt z₀ zs) (K zs) * M.logGrowth z₀ K zs)
    ring

/-! ### Equilibrium -/

variable {ι : Type*} [Fintype ι]

/-- **Sequential equilibrium** from the shock `z₀` and an initial distribution with weights `ν` on
households with wealth `w i` and idiosyncratic state `s i`: a positive capital path, and an
optimal plan for each household, such that capital at every node is mean wealth there. -/
def IsSequentialEquilibrium (z₀ : Z) (ν w : ι → ℝ) (s : ι → E) (K : List Z → ℝ) : Prop :=
  (∀ zs, 0 < K zs) ∧ ∃ plan : ι → List (Z × E) → ℝ,
    (∀ i, M.IsOptimal z₀ (s i) K (w i) (plan i)) ∧
      ∀ zs, K zs = ∑ i, ν i * M.condMean z₀ (s i) zs (wealth (w i) (plan i))

/-- **The law of motion**: next period's capital is the fraction `β` of resources. -/
noncomputable def lawK (z : Z) (k : ℝ) : ℝ := M.discount * M.resources z k * k

/-- **The capital path** of the law of motion from `(z₀, k₀)`. -/
noncomputable def logPath (z₀ : Z) (k₀ : ℝ) : List Z → ℝ
  | [] => k₀
  | _ :: zs => M.lawK (shockAt z₀ zs) (logPath z₀ k₀ zs)

/-- **The path is recursive on `(z, K)`.** -/
theorem logPath_cons (k₀ : ℝ) (z' : Z) (zs : List Z) :
    M.logPath z₀ k₀ (z' :: zs) = M.lawK (shockAt z₀ zs) (M.logPath z₀ k₀ zs) := rfl

theorem logPath_pos {k₀ : ℝ} (hk : 0 < k₀) : ∀ zs, 0 < M.logPath z₀ k₀ zs
  | [] => hk
  | _ :: zs => mul_pos (mul_pos M.discount_pos (M.resources_pos _ _ (logPath_pos hk zs)))
      (logPath_pos hk zs)

theorem logPath_eq (k₀ : ℝ) : ∀ zs,
    M.logPath z₀ k₀ zs = k₀ * M.logGrowth z₀ (M.logPath z₀ k₀) zs
  | [] => (mul_one k₀).symm
  | z' :: zs => by
    change M.discount * M.resources (shockAt z₀ zs) (M.logPath z₀ k₀ zs) * M.logPath z₀ k₀ zs
      = k₀ * (M.discount * M.resources (shockAt z₀ zs) (M.logPath z₀ k₀ zs)
        * M.logGrowth z₀ (M.logPath z₀ k₀) zs)
    have h := logPath_eq k₀ zs
    have : k₀ * (M.discount * M.resources (shockAt z₀ zs) (M.logPath z₀ k₀ zs)
          * M.logGrowth z₀ (M.logPath z₀ k₀) zs)
        = M.discount * M.resources (shockAt z₀ zs) (M.logPath z₀ k₀ zs)
          * (k₀ * M.logGrowth z₀ (M.logPath z₀ k₀) zs) := by ring
    rw [this, ← h]

/-- **Recursive equilibrium on `(z, K)` with uninsured idiosyncratic risk.** From every initial
shock and every initial distribution of positive wealth levels, the path of the law of motion
`K' = β g(z, K) K` from mean initial wealth is a sequential equilibrium, in which every household
saves the fraction `β` of its cash. -/
theorem isSequentialEquilibrium_logPath (ν w : ι → ℝ) (s : ι → E) (hw : ∀ i, 0 < w i)
    (hk : 0 < ∑ i, ν i * w i) :
    M.IsSequentialEquilibrium z₀ ν w s (M.logPath z₀ (∑ i, ν i * w i)) := by
  have hK := M.logPath_pos z₀ hk
  refine ⟨hK, fun i => M.logPlan z₀ (M.logPath z₀ (∑ i, ν i * w i)) (w i),
    fun i => M.logPlan_isOptimal z₀ (s i) hK (hw i), fun zs => ?_⟩
  simp only [wealth_logPlan, condMean_logWealth]
  rw [M.logPath_eq z₀ _ zs, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end HomotheticEconomy

end KrusellSmith

end LeanEconomics
