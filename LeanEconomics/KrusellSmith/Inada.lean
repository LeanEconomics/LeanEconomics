/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Labour
import LeanEconomics.Models.ConsumptionFloor

/-!
# Krusell–Smith with log utility and CRRA `σ ≥ 1`

Log utility and CRRA with `σ ≥ 1` fall to `-∞` at zero consumption, so the household's reward
is not a bounded continuous function and `KSModel` does not apply directly. This module removes
the obstacle without leaving real-valued dynamic programming.

**The economy** (`KSInada`) is a Krusell–Smith economy whose utility is defined, continuous,
strictly concave and increasing on `(0, ∞)` with unbounded marginal value at zero
(`MarginalInada`, which CRRA satisfies for every `σ > 0`: `marginalInada_crraUtility`), and whose
labour income never falls below `incomeFloor > 0`.

**The floored economy** (`toModel c`). For `0 < c ≤ incomeFloor`, requiring consumption at least
`c` gives a `KSModel`, to which every result so far applies. Its value function is bounded
independently of `c` and of the path of capital (`abs_valueFunction_le`): consuming all of
cash on hand, which is at least `incomeFloor`, gives the lower bound, and cash on hand below
`maxCash` gives the upper one.

**The floor never binds** (`floorLevel_le_consumption`). With that bound, the continuation is
concave and its slope is at most `L = 4B / incomeFloor` wherever savings exceed half the income
floor (`cont_sub_le`). If optimal consumption were below `floorLevel`, saving a little less would
raise utility by more than `β L` per unit (marginal Inada) and lower the continuation by at most
`β L` per unit, contradicting optimality. This is the argument of
`IncomeFluctuation.exists_consumption_floor_of_marginalInada`, with a level `floorLevel` that
depends on neither `c` nor the path.

**Optimality in the unfloored problem** (`objective_le_valueFunction`). Take the floor
`floor = floorLevel / 2`. The objective is concave in savings; its maximum over the floored
choices is interior to the floor constraint, so it is a maximum over every saving with positive
consumption.

**Existence** (`exists_sequentialEquilibrium`): a sequential equilibrium of the floored economy
at `floor` is one of the original economy: households' savings are optimal among all savings
with positive consumption, and their consumption is strictly above the floor.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

/-- A **Krusell–Smith economy with utility unbounded below**: utility on `(0, ∞)` with unbounded
marginal value at zero, and labour income bounded away from zero. -/
structure KSInada (Z E : Type*) [Fintype Z] [Fintype E] where
  aggProb : Z → Z → ℝ
  aggProb_nonneg : ∀ z z', 0 ≤ aggProb z z'
  aggProb_sum : ∀ z, ∑ z', aggProb z z' = 1
  idioProb : Z → Z → E → E → ℝ
  idioProb_nonneg : ∀ z z' e e', 0 ≤ idioProb z z' e e'
  idioProb_sum : ∀ z z' e, ∑ e', idioProb z z' e e' = 1
  efficiency : E → ℝ
  efficiency_nonneg : ∀ e, 0 ≤ efficiency e
  assetCap : ℝ
  assetCap_pos : 0 < assetCap
  discount : ℝ
  discount_pos : 0 < discount
  discount_lt_one : discount < 1
  grossReturn : Z → ℝ → ℝ → ℝ
  continuous_grossReturn : ∀ z, Continuous fun p : ℝ × ℝ => grossReturn z p.1 p.2
  grossReturn_nonneg : ∀ z K L, 0 ≤ grossReturn z K L
  returnBound : ℝ
  grossReturn_le : ∀ z K L, grossReturn z K L ≤ returnBound
  wage : Z → ℝ → ℝ → ℝ
  continuous_wage : ∀ z, Continuous fun p : ℝ × ℝ => wage z p.1 p.2
  wage_nonneg : ∀ z K L, 0 ≤ wage z K L
  wageBound : ℝ
  wage_le : ∀ z K L, wage z K L ≤ wageBound
  /-- A positive lower bound on labour income. -/
  incomeFloor : ℝ
  incomeFloor_pos : 0 < incomeFloor
  incomeFloor_le : ∀ z K L e, incomeFloor ≤ wage z K L * efficiency e
  /-- Period utility, defined on positive consumption. -/
  utility : ℝ → ℝ
  continuousOn_utility : ContinuousOn utility (Ioi 0)
  strictConcaveOn_utility : StrictConcaveOn ℝ (Ioi 0) utility
  monotoneOn_utility : MonotoneOn utility (Ioi 0)
  /-- Unbounded marginal value at zero consumption. -/
  marginalInada : MarginalInada utility

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSInada

variable (P : KSInada Z E)

/-- **The floored economy**: consumption at least `c`, with `0 < c ≤ incomeFloor`. -/
noncomputable def toModel (c : ℝ) (hc : 0 < c) (hcy : c ≤ P.incomeFloor) : KSModel Z E where
  aggProb := P.aggProb
  aggProb_nonneg := P.aggProb_nonneg
  aggProb_sum := P.aggProb_sum
  idioProb := P.idioProb
  idioProb_nonneg := P.idioProb_nonneg
  idioProb_sum := P.idioProb_sum
  efficiency := P.efficiency
  efficiency_nonneg := P.efficiency_nonneg
  assetCap := P.assetCap
  assetCap_pos := P.assetCap_pos
  discount := P.discount
  discount_pos := P.discount_pos
  discount_lt_one := P.discount_lt_one
  grossReturn := P.grossReturn
  continuous_grossReturn := P.continuous_grossReturn
  grossReturn_nonneg := P.grossReturn_nonneg
  returnBound := P.returnBound
  grossReturn_le := P.grossReturn_le
  wage := P.wage
  continuous_wage := P.continuous_wage
  wage_nonneg := P.wage_nonneg
  wageBound := P.wageBound
  wage_le := P.wage_le
  consFloor := c
  consFloor_nonneg := hc.le
  consFloor_le_income z K L e := hcy.trans (P.incomeFloor_le z K L e)
  utility := P.utility
  continuousOn_utility := P.continuousOn_utility.mono (Ici_subset_Ioi.2 hc)
  strictConcaveOn_utility := P.strictConcaveOn_utility.subset (Ici_subset_Ioi.2 hc) (convex_Ici c)
  monotoneOn_utility := P.monotoneOn_utility.mono (Ici_subset_Ioi.2 hc)

/-- The largest cash on hand anywhere. -/
noncomputable def maxCash : ℝ := P.returnBound * P.assetCap + P.wageBound * ∑ e, P.efficiency e

/-- The largest consumption anywhere, at least the income floor. -/
noncomputable def topCons : ℝ := max P.incomeFloor P.maxCash

/-- A bound on the value function that holds for every floor and every path of capital. -/
noncomputable def valueBound : ℝ :=
  max |P.utility P.incomeFloor / (1 - P.discount)| |P.utility P.topCons / (1 - P.discount)|

theorem valueBound_nonneg : 0 ≤ P.valueBound := (abs_nonneg _).trans (le_max_left _ _)

variable {c : ℝ} (hc : 0 < c) (hcy : c ≤ P.incomeFloor) (z₀ : Z) (m₀ : E → ℝ)
  (K : List Z → ℝ)

theorem incomeFloor_le_cash (s : (P.toModel c hc hcy).State) :
    P.incomeFloor ≤ (P.toModel c hc hcy).cash z₀ m₀ K s :=
  (P.incomeFloor_le _ _ _ _).trans
    (le_add_of_nonneg_left (mul_nonneg (P.grossReturn_nonneg _ _ _) s.1.2.1))

theorem cash_le_topCons (s : (P.toModel c hc hcy).State) :
    (P.toModel c hc hcy).cash z₀ m₀ K s ≤ P.topCons :=
  ((P.toModel c hc hcy).cash_le_maxCash z₀ m₀ K s).trans (le_max_right _ _)

/-- **The value function is bounded independently of the floor and the path.** -/
theorem valueFunction_mem (s : (P.toModel c hc hcy).State) :
    P.utility P.incomeFloor / (1 - P.discount)
        ≤ ((P.toModel c hc hcy).household z₀ m₀ K).valueFunction s ∧
      ((P.toModel c hc hcy).household z₀ m₀ K).valueFunction s
        ≤ P.utility P.topCons / (1 - P.discount) := by
  set M := P.toModel c hc hcy with hM
  set D := M.household z₀ m₀ K with hD
  set V := D.valueFunction with hV
  have hβ1 : 0 < 1 - P.discount := sub_pos.2 P.discount_lt_one
  have hβ0 : 0 ≤ P.discount := P.discount_pos.le
  have hy := P.incomeFloor_pos
  have : Nonempty M.State := ⟨s⟩
  have hMu : M.utility = P.utility := rfl
  have hMd : M.discount = P.discount := rfl
  have hbdd : BddBelow (range V) := ⟨-‖V‖, by
    rintro _ ⟨t, rfl⟩
    exact neg_le_of_abs_le (by simpa [Real.norm_eq_abs] using V.norm_coe_le_norm t)⟩
  have hbdd' : BddAbove (range V) := ⟨‖V‖, by
    rintro _ ⟨t, rfl⟩
    exact le_of_abs_le (by simpa [Real.norm_eq_abs] using V.norm_coe_le_norm t)⟩
  have hfix : ∀ t, D.bellman V t = V t := fun t => by rw [D.bellman_valueFunction]
  -- the expected continuation lies between the infimum and the supremum
  have hexp_lo : ∀ t a, (⨅ t, V t) ≤ ∑ ze : Z × E, M.shockProb z₀ ze (t, a)
      * V (M.clampAssets a, ⟨ze.2, ze.1 :: t.2.node⟩) := by
    intro t a
    calc (⨅ t, V t) = ∑ ze : Z × E, M.shockProb z₀ ze (t, a) * ⨅ t, V t := by
          rw [← Finset.sum_mul, M.shockProb_sum z₀, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun ze _ => mul_le_mul_of_nonneg_left (ciInf_le hbdd _)
          (mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _))
  have hexp_hi : ∀ t a, ∑ ze : Z × E, M.shockProb z₀ ze (t, a)
      * V (M.clampAssets a, ⟨ze.2, ze.1 :: t.2.node⟩) ≤ ⨆ t, V t := by
    intro t a
    calc _ ≤ ∑ ze : Z × E, M.shockProb z₀ ze (t, a) * ⨆ t, V t :=
          Finset.sum_le_sum fun ze _ => mul_le_mul_of_nonneg_left (le_ciSup hbdd' _)
            (mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _))
      _ = ⨆ t, V t := by rw [← Finset.sum_mul, M.shockProb_sum z₀, one_mul]
  -- lower bound: consume all of cash on hand
  have hlo : P.utility P.incomeFloor + P.discount * (⨅ t, V t) ≤ ⨅ t, V t := by
    refine le_ciInf fun t => ?_
    have h0 : (0 : ℝ) ∈ D.feasible t := ⟨le_rfl, M.maxSaving_nonneg z₀ m₀ K t⟩
    have hle := D.le_bellmanFn V h0
    rw [M.objective_eq z₀ m₀ K V h0, sub_zero] at hle
    have hu : P.utility P.incomeFloor ≤ P.utility (M.cash z₀ m₀ K t) :=
      P.monotoneOn_utility hy (hy.trans_le (P.incomeFloor_le_cash hc hcy z₀ m₀ K t))
        (P.incomeFloor_le_cash hc hcy z₀ m₀ K t)
    have h2 := mul_le_mul_of_nonneg_left (hexp_lo t 0) hβ0
    change _ ≤ D.bellman V t at hle
    rw [hfix, hMu, hMd] at hle
    linarith
  -- upper bound: consumption never exceeds `topCons`
  have hhi : ⨆ t, V t ≤ P.utility P.topCons + P.discount * (⨆ t, V t) := by
    refine ciSup_le fun t => ?_
    rw [← hfix]
    refine D.bellmanFn_le V fun a ha => ?_
    rw [M.objective_eq z₀ m₀ K V ha]
    have hc0 : c ≤ M.cash z₀ m₀ K t - a := le_sub_comm.1 (ha.2.trans (min_le_right _ _))
    have hu : P.utility (M.cash z₀ m₀ K t - a) ≤ P.utility P.topCons :=
      P.monotoneOn_utility (hc.trans_le hc0) (hy.trans_le (le_max_left _ _))
        ((sub_le_self _ ha.1).trans (P.cash_le_topCons hc hcy z₀ m₀ K t))
    have h2 := mul_le_mul_of_nonneg_left (hexp_hi t a) hβ0
    rw [hMu, hMd]
    linarith
  constructor
  · rw [div_le_iff₀ hβ1]
    calc P.utility P.incomeFloor ≤ (⨅ t, V t) * (1 - P.discount) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (ciInf_le hbdd _) hβ1.le
  · rw [le_div_iff₀ hβ1]
    calc _ ≤ (⨆ t, V t) * (1 - P.discount) := mul_le_mul_of_nonneg_right (le_ciSup hbdd' _) hβ1.le
      _ ≤ P.utility P.topCons := by linarith

theorem abs_valueFunction_le (s : (P.toModel c hc hcy).State) :
    |((P.toModel c hc hcy).household z₀ m₀ K).valueFunction s| ≤ P.valueBound := by
  obtain ⟨h1, h2⟩ := P.valueFunction_mem hc hcy z₀ m₀ K s
  rw [abs_le]
  constructor
  · have := neg_abs_le (P.utility P.incomeFloor / (1 - P.discount))
    have := le_max_left |P.utility P.incomeFloor / (1 - P.discount)|
      |P.utility P.topCons / (1 - P.discount)|
    rw [valueBound]
    linarith
  · have := le_abs_self (P.utility P.topCons / (1 - P.discount))
    have := le_max_right |P.utility P.incomeFloor / (1 - P.discount)|
      |P.utility P.topCons / (1 - P.discount)|
    rw [valueBound]
    linarith

/-! ### The continuation and its slope -/

/-- The expected continuation value of saving `a'` at the state `s`. -/
noncomputable def cont (s : (P.toModel c hc hcy).State) (a' : ℝ) : ℝ :=
  ∑ ze : Z × E, (P.toModel c hc hcy).shockProb z₀ ze (s, a')
    * ((P.toModel c hc hcy).household z₀ m₀ K).valueFunction
        ((P.toModel c hc hcy).clampAssets a', ⟨ze.2, ze.1 :: s.2.node⟩)

theorem abs_cont_le (s : (P.toModel c hc hcy).State) (a' : ℝ) :
    |P.cont hc hcy z₀ m₀ K s a'| ≤ P.valueBound := by
  revert s
  set M := P.toModel c hc hcy
  intro s
  calc |P.cont hc hcy z₀ m₀ K s a'|
      ≤ ∑ ze : Z × E, |M.shockProb z₀ ze (s, a') * (M.household z₀ m₀ K).valueFunction
          (M.clampAssets a', ⟨ze.2, ze.1 :: s.2.node⟩)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ze : Z × E, M.shockProb z₀ ze (s, a') * P.valueBound := by
        refine Finset.sum_le_sum fun ze _ => ?_
        have hp : 0 ≤ M.shockProb z₀ ze (s, a') :=
          mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _)
        rw [abs_mul, abs_of_nonneg hp]
        exact mul_le_mul_of_nonneg_left (P.abs_valueFunction_le hc hcy z₀ m₀ K _) hp
    _ = P.valueBound := by rw [← Finset.sum_mul, M.shockProb_sum z₀, one_mul]

/-- The continuation is concave in savings. -/
theorem concaveOn_cont (s : (P.toModel c hc hcy).State) :
    ConcaveOn ℝ (Icc 0 P.assetCap) (P.cont hc hcy z₀ m₀ K s) := by
  revert s
  set M := P.toModel c hc hcy
  intro s
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [cont, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ze _ => ?_
  have hvz := (M.concaveOn_valueFunction z₀ m₀ K ⟨ze.2, ze.1 :: s.2.node⟩).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hvz
  have hp : 0 ≤ M.shockProb z₀ ze (s, x) :=
    mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _)
  change a * (M.shockProb z₀ ze (s, x) * _) + b * (M.shockProb z₀ ze (s, x) * _)
    ≤ M.shockProb z₀ ze (s, x) * _
  nlinarith

omit hc hcy in
/-- The slope bound on the continuation, away from zero savings. -/
noncomputable def slopeConst : ℝ := 4 * P.valueBound / P.incomeFloor

omit hc hcy in
theorem slopeConst_nonneg : 0 ≤ P.slopeConst :=
  div_nonneg (mul_nonneg (by norm_num) P.valueBound_nonneg) P.incomeFloor_pos.le

/-- **The continuation's slope is at most `slopeConst`** where savings exceed half the income
floor. -/
theorem cont_sub_le (s : (P.toModel c hc hcy).State) {x y : ℝ} (hx : P.incomeFloor / 2 ≤ x)
    (hxy : x < y) (hy : y ≤ P.assetCap) :
    P.cont hc hcy z₀ m₀ K s y - P.cont hc hcy z₀ m₀ K s x ≤ P.slopeConst * (y - x) := by
  have hyf := P.incomeFloor_pos
  have hx0 : 0 < x := by linarith
  have hslope := (P.concaveOn_cont hc hcy z₀ m₀ K s).slope_anti_adjacent
    (mem_Icc.2 ⟨le_rfl, P.assetCap_pos.le⟩) (mem_Icc.2 ⟨by linarith, hy⟩) hx0 hxy
  have hb1 := abs_le.mp (P.abs_cont_le hc hcy z₀ m₀ K s x)
  have hb2 := abs_le.mp (P.abs_cont_le hc hcy z₀ m₀ K s 0)
  have hhalf : P.slopeConst * (P.incomeFloor / 2) = 2 * P.valueBound := by
    rw [slopeConst]
    field_simp
    ring
  have hbig : P.cont hc hcy z₀ m₀ K s x - P.cont hc hcy z₀ m₀ K s 0 ≤ P.slopeConst * x := by
    have hstep : P.slopeConst * (P.incomeFloor / 2) ≤ P.slopeConst * x :=
      mul_le_mul_of_nonneg_left hx P.slopeConst_nonneg
    linarith [hb1.2, hb2.1]
  rw [sub_zero, div_le_div_iff₀ (by linarith) hx0] at hslope
  have hprod : (P.cont hc hcy z₀ m₀ K s y - P.cont hc hcy z₀ m₀ K s x) * x
      ≤ (P.slopeConst * x) * (y - x) := by
    nlinarith [hslope, hbig, (show (0 : ℝ) < y - x by linarith)]
  nlinarith [hprod, hx0]

/-! ### The floor never binds -/

omit hc hcy in
/-- The radius below which marginal utility beats `β · slopeConst + 1`. -/
noncomputable def inadaRadius : ℝ :=
  (P.marginalInada (P.discount * P.slopeConst + 1)).choose

omit hc hcy in
theorem inadaRadius_pos : 0 < P.inadaRadius :=
  (P.marginalInada (P.discount * P.slopeConst + 1)).choose_spec.1

omit hc hcy in
theorem inadaRadius_spec {c₁ c₂ : ℝ} (h₁ : c₁ ∈ Ioi 0) (h₁₂ : c₁ < c₂) (h₂ : c₂ ≤ P.inadaRadius) :
    (P.discount * P.slopeConst + 1) * (c₂ - c₁) ≤ P.utility c₂ - P.utility c₁ :=
  (P.marginalInada (P.discount * P.slopeConst + 1)).choose_spec.2 c₁ c₂ h₁ h₁₂ h₂

omit hc hcy in
/-- **The consumption floor** that optimal consumption never goes below, whatever the imposed
floor (up to the income floor) and the path of capital. -/
noncomputable def floorLevel : ℝ := min P.inadaRadius (P.incomeFloor / 4)

omit hc hcy in
theorem floorLevel_pos : 0 < P.floorLevel :=
  lt_min P.inadaRadius_pos (by linarith [P.incomeFloor_pos])

/-- **Optimal consumption is at least `floorLevel`**, along every path of capital and for every
imposed floor `c ≤ incomeFloor`. -/
theorem floorLevel_le_consumption (s : (P.toModel c hc hcy).State) :
    P.floorLevel ≤ (P.toModel c hc hcy).cash z₀ m₀ K s
      - (P.toModel c hc hcy).policy z₀ m₀ K s := by
  revert s
  set M := P.toModel c hc hcy with hM
  intro s
  have hMu : M.utility = P.utility := rfl
  have hMd : M.discount = P.discount := rfl
  have hyf := P.incomeFloor_pos
  have hβ : 0 ≤ P.discount := P.discount_pos.le
  by_contra hlt
  rw [not_le] at hlt
  set fl := P.floorLevel with hfl
  set p := M.policy z₀ m₀ K s with hpdef
  set cash := M.cash z₀ m₀ K s with hcash
  have hfδ : fl ≤ P.inadaRadius := min_le_left _ _
  have hf4 : fl ≤ P.incomeFloor / 4 := min_le_right _ _
  have hpm := M.policy_mem z₀ m₀ K s
  have hcons : c ≤ cash - p := le_sub_comm.1 (hpm.2.trans (min_le_right _ _))
  have hcashy : P.incomeFloor ≤ cash := P.incomeFloor_le_cash hc hcy z₀ m₀ K s
  have hpA : p ≤ P.assetCap := hpm.2.trans (min_le_left _ _)
  set h := fl - (cash - p) with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  have hlow : P.incomeFloor / 2 ≤ p - h := by rw [hh]; linarith
  have hfeas : p - h ∈ (M.household z₀ m₀ K).feasible s :=
    ⟨by linarith, (by linarith : p - h ≤ p).trans hpm.2⟩
  have hdev := (M.household z₀ m₀ K).le_bellmanFn (M.household z₀ m₀ K).valueFunction hfeas
  rw [M.objective_eq z₀ m₀ K _ hfeas, hMu, hMd] at hdev
  have hopt := M.policy_optimal z₀ m₀ K s
  rw [M.objective_eq z₀ m₀ K _ hpm, hMu, hMd] at hopt
  change _ ≤ (M.household z₀ m₀ K).bellman (M.household z₀ m₀ K).valueFunction s at hdev
  rw [hopt] at hdev
  have hcfl : cash - (p - h) = fl := by rw [hh]; ring
  rw [hcfl] at hdev
  have hslope := P.cont_sub_le hc hcy z₀ m₀ K s hlow (by linarith) hpA
  rw [show p - (p - h) = h by ring] at hslope
  change P.utility fl + P.discount * P.cont hc hcy z₀ m₀ K s (p - h)
    ≤ P.utility (cash - p) + P.discount * P.cont hc hcy z₀ m₀ K s p at hdev
  have hscaled := mul_le_mul_of_nonneg_left hslope hβ
  have hmarg := P.inadaRadius_spec (mem_Ioi.2 (hc.trans_le hcons)) (by linarith) hfδ
  have he : fl - (cash - p) = h := by rw [hh]
  rw [he] at hmarg
  nlinarith [P.slopeConst_nonneg]

/-- **Optimality among all savings with positive consumption.** When the imposed floor is below
`floorLevel`, no saving with positive consumption beats the household's value. -/
theorem objective_le_valueFunction (hcf : c < P.floorLevel) (s : (P.toModel c hc hcy).State)
    {a : ℝ} (ha0 : 0 ≤ a) (haA : a ≤ P.assetCap)
    (hac : a < (P.toModel c hc hcy).cash z₀ m₀ K s) :
    P.utility ((P.toModel c hc hcy).cash z₀ m₀ K s - a) + P.discount * P.cont hc hcy z₀ m₀ K s a
      ≤ ((P.toModel c hc hcy).household z₀ m₀ K).valueFunction s := by
  revert s
  set M := P.toModel c hc hcy with hM
  intro s hac
  have hMu : M.utility = P.utility := rfl
  have hMd : M.discount = P.discount := rfl
  set D := M.household z₀ m₀ K with hD
  set V := D.valueFunction with hV
  have hfixV : D.bellmanFn V s = V s := by
    change D.bellman V s = V s
    rw [D.bellman_valueFunction]
  set cash := M.cash z₀ m₀ K s with hcash
  -- the value is the objective at any feasible saving's upper bound
  have hfeasible_le : ∀ b, b ∈ D.feasible s →
      P.utility (cash - b) + P.discount * P.cont hc hcy z₀ m₀ K s b ≤ V s := by
    intro b hb
    have hle := D.le_bellmanFn V hb
    rw [M.objective_eq z₀ m₀ K V hb, hMu, hMd, hfixV] at hle
    exact hle
  by_cases hab : a ≤ cash - c
  · exact hfeasible_le a ⟨ha0, le_min haA hab⟩
  -- otherwise the policy lies strictly inside the floor, and concavity does the rest
  rw [not_le] at hab
  set p := M.policy z₀ m₀ K s with hpdef
  have hpm := M.policy_mem z₀ m₀ K s
  have hpA : p ≤ P.assetCap := hpm.2.trans (min_le_left _ _)
  have hfl := P.floorLevel_le_consumption hc hcy z₀ m₀ K s
  have hpb : p < cash - c := by linarith
  have hcashy : P.incomeFloor ≤ cash := P.incomeFloor_le_cash hc hcy z₀ m₀ K s
  set b := cash - c with hbdef
  have hb0 : 0 ≤ b := by rw [hbdef]; linarith
  have hfeasb : b ∈ D.feasible s := ⟨hb0, le_min (show b ≤ P.assetCap by linarith) le_rfl⟩
  have hpV : P.utility (cash - p) + P.discount * P.cont hc hcy z₀ m₀ K s p = V s := by
    have hopt := M.policy_optimal z₀ m₀ K s
    rw [M.objective_eq z₀ m₀ K _ hpm, hMu, hMd] at hopt
    change D.bellmanFn V s = _ at hopt
    rw [hfixV] at hopt
    exact hopt.symm
  -- weights writing `b` between `p` and `a`
  have hap : 0 < a - p := by linarith
  set θ := (a - b) / (a - p) with hθ
  set φ := (b - p) / (a - p) with hφ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hap.le
  have hφ0 : 0 < φ := div_pos (by linarith) hap
  have hθφ : θ + φ = 1 := by rw [hθ, hφ, ← add_div, div_eq_one_iff_eq hap.ne']; ring
  have hbmix : θ * p + φ * a = b := by
    rw [hθ, hφ]
    field_simp
    ring
  have hcmix : θ * (cash - p) + φ * (cash - a) = cash - b := by
    rw [← hbmix]
    linear_combination cash * hθφ
  -- concavity of utility and of the continuation
  have hu := P.strictConcaveOn_utility.concaveOn.2 (mem_Ioi.2 (show 0 < cash - p by linarith))
    (mem_Ioi.2 (show 0 < cash - a by linarith)) hθ0 hφ0.le hθφ
  simp only [smul_eq_mul] at hu
  rw [hcmix] at hu
  have hcont := (P.concaveOn_cont hc hcy z₀ m₀ K s).2 (mem_Icc.2 ⟨hpm.1, hpA⟩)
    (mem_Icc.2 ⟨ha0, haA⟩) hθ0 hφ0.le hθφ
  simp only [smul_eq_mul] at hcont
  rw [hbmix, ← hpdef] at hcont
  have hβ : 0 ≤ P.discount := P.discount_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hcont hβ
  have hbV := hfeasible_le b hfeasb
  -- `θ V + φ f(a) ≤ f(b) ≤ V`, and `φ > 0`
  have hθV : θ * V s + φ * V s = V s := by rw [← add_mul, hθφ, one_mul]
  have hpV' : θ * (P.utility (cash - p) + P.discount * P.cont hc hcy z₀ m₀ K s p) = θ * V s := by
    rw [hpV]
  have hkey : φ * (P.utility (cash - a) + P.discount * P.cont hc hcy z₀ m₀ K s a) ≤ φ * V s := by
    nlinarith [hu, hscaled, hbV, hpV', hθV]
  exact le_of_mul_le_mul_left hkey hφ0

/-! ### Existence -/

omit hc hcy in
/-- The floor imposed: half of `floorLevel`, so that it never binds. -/
noncomputable def floor : ℝ := P.floorLevel / 2

omit hc hcy in
theorem floor_pos : 0 < P.floor := half_pos P.floorLevel_pos

omit hc hcy in
theorem floor_lt_floorLevel : P.floor < P.floorLevel := half_lt_self P.floorLevel_pos

omit hc hcy in
theorem floor_le_incomeFloor : P.floor ≤ P.incomeFloor := by
  have h1 : P.floorLevel ≤ P.incomeFloor / 4 := min_le_right _ _
  have h2 := P.incomeFloor_pos
  rw [floor]
  linarith

omit hc hcy in
/-- The floored economy that solves the original one. -/
noncomputable abbrev floored : KSModel Z E := P.toModel P.floor P.floor_pos P.floor_le_incomeFloor

omit hc hcy z₀ m₀ K in
/-- **Existence of sequential equilibrium in a Krusell–Smith economy with log or CRRA `σ ≥ 1`
utility.** There is a path of aggregate capital such that, at every node, capital is mean assets
and labour is mean efficiency of the households there; every household's saving is optimal among
all savings with positive consumption, and its consumption is bounded away from zero. -/
theorem exists_sequentialEquilibrium (z₀ : Z) (μ₀ : Measure P.floored.AState)
    [IsProbabilityMeasure μ₀] :
    ∃ K ∈ P.floored.capitalPaths (P.floored.initCapital μ₀),
      P.floored.IsSequentialEquilibrium z₀ μ₀ K ∧
      (∀ h, P.floored.labour z₀ (P.floored.initMass μ₀) h
        = ∫ x, P.efficiency x.2.idio ∂(P.floored.nodeDist z₀ (P.floored.initMass μ₀) μ₀ K h)) ∧
      ∀ s : P.floored.State,
        P.floorLevel ≤ P.floored.cash z₀ (P.floored.initMass μ₀) K s
          - P.floored.policy z₀ (P.floored.initMass μ₀) K s ∧
        ∀ a, 0 ≤ a → a ≤ P.assetCap → a < P.floored.cash z₀ (P.floored.initMass μ₀) K s →
          P.utility (P.floored.cash z₀ (P.floored.initMass μ₀) K s - a)
              + P.discount
                * P.cont P.floor_pos P.floor_le_incomeFloor z₀ (P.floored.initMass μ₀) K s a
            ≤ (P.floored.household z₀ (P.floored.initMass μ₀) K).valueFunction s := by
  obtain ⟨K, hK, heq, hlab⟩ := P.floored.exists_sequentialEquilibrium_labour z₀ μ₀
  refine ⟨K, hK, heq, hlab, fun s => ⟨?_, fun a ha0 haA hac => ?_⟩⟩
  · exact P.floorLevel_le_consumption P.floor_pos P.floor_le_incomeFloor z₀ _ K s
  · exact P.objective_le_valueFunction P.floor_pos P.floor_le_incomeFloor z₀ _ K
      P.floor_lt_floorLevel s ha0 haA hac

omit hc hcy z₀ m₀ K in
/-- **CRRA utility qualifies for every `γ > 0`**, log (`γ = 1`) and `γ > 1` included: it is
continuous, strictly concave and increasing on `(0, ∞)` with unbounded marginal value at zero. -/
theorem crraUtility_qualifies {γ : ℝ} (hγ : 0 < γ) :
    ContinuousOn (crraUtility γ) (Ioi 0) ∧ StrictConcaveOn ℝ (Ioi 0) (crraUtility γ) ∧
      MonotoneOn (crraUtility γ) (Ioi 0) ∧ MarginalInada (crraUtility γ) :=
  ⟨continuousOn_crraUtility γ, strictConcaveOn_crraUtility hγ, monotoneOn_crraUtility γ,
    marginalInada_crraUtility hγ⟩

end KSInada

end KrusellSmith

end LeanEconomics
