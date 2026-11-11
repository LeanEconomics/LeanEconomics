/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ColemanEquilibrium
import LeanEconomics.KrusellSmith.CrossSectionEuler
import LeanEconomics.KrusellSmith.Labour
import LeanEconomics.KrusellSmith.ColemanUnique

/-!
# Heterogeneous households without redistribution: the proportional economy

Route 2 of `CROSS_SECTION_PLAN.md`: the equality case of the dispersion bound. Households differ
in **permanent** labour efficiency (`hperm`: the idiosyncratic state never changes) and hold assets
**proportional to efficiency**: type `e` holds the share `θ_e = efficiency e / L` of aggregate
capital, `L` mean efficiency. A change in capital then moves every household's cash by the same
factor, so prices redistribute nothing and the Coleman argument goes through with CRRA utility,
at every capital share.

* `aggData`: the aggregate economy as Coleman data (labour `L`, capital cap `cap`).
* `propRule`: type `e` saves the share `θ_e` of the Coleman saving while on the proportional path
  (`OnPath`), zero off it; `onPath_of_pos`: histories of positive probability stay on the path.
* `propPlan_euler`: the plan satisfies the household's Euler conditions on those histories —
  homogeneity of CRRA marginal utility scales the aggregate Euler root to each type — when the
  capital cap is slack (`hslack`; `Data.saving_lt_cap_of` gives it from `y − m < cap`).
* **`policy_eq_prop`**: type `e`'s optimal saving at assets `θ_e k` is `θ_e s*(z, k)`
  (`policy_eq_of_eulerOn`).
* `propDist`, `nodeDist_propDist`: the proportional cross-section stays proportional.
* **`isSequentialEquilibrium_prop`**: from every proportional cross-section the Coleman capital
  path of the aggregate economy is a sequential equilibrium; capital follows the law
  `K' = s*(z, K)` on the state `(z, K)`.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction
open LeanEconomics.StochasticDynamicProgram
open scoped NNReal ENNReal

namespace LeanEconomics

namespace KrusellSmith

namespace Coleman

variable {Z E : Type*} [Fintype Z] [Fintype E]

/-- **The aggregate CRRA, Cobb–Douglas economy as Coleman data**, with labour `L` and a cap on
aggregate capital. -/
noncomputable def aggData (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ) {L : ℝ}
    (hL : 0 < L) (hLbox : T.clampLab L = L) (hβR : V.discount * T.returnBound ≤ 1) {cap : ℝ}
    (hcap : 0 < cap) : Data Z where
  π := V.aggProb
  π_nonneg := V.aggProb_nonneg
  π_sum := V.aggProb_sum
  β := V.discount
  β_pos := V.discount_pos
  cap := cap
  cap_pos := hcap
  du c := c ^ (-γ)
  du_anti _ ha _ _ hab := Real.rpow_lt_rpow_of_neg ha hab (by linarith)
  du_cont x hx := (Real.continuousAt_rpow_const x (-γ) (Or.inl (ne_of_gt hx))).continuousWithinAt
  du_pos _ hc := Real.rpow_pos_of_pos hc _
  du_inada := tendsto_rpow_neg_nhdsGT_zero (by linarith)
  R z k := T.grossReturn z k L
  R_cont z := (T.continuous_grossReturn z).comp (continuous_id.prodMk continuous_const)
  R_nonneg z k := T.grossReturn_nonneg z _ _
  R_anti z _ _ _ _ hab := T.grossReturn_anti z hab _
  Rbar := T.returnBound
  R_le z k := T.grossReturn_le z _ _
  βR_le := hβR
  y z k := T.grossReturn z k L * k + T.wage z k L * L
  y_cont z := (((T.continuous_grossReturn z).comp (continuous_id.prodMk continuous_const)).mul
    continuous_id).add (((T.continuous_wage z).comp (continuous_id.prodMk continuous_const)).mul
    continuous_const)
  y_mono z _ ha _ _ hab := T.repCash_mono z hLbox ha.1 hab
  m := T.wageLo * L
  m_pos := mul_pos T.wageLo_pos hL
  m_le_y z k hk := by
    have h1 := mul_nonneg (T.grossReturn_nonneg z k L) hk.1
    have h2 := mul_le_mul_of_nonneg_right (T.wageLo_le_wage z k L) hL.le
    linarith

/-- The cap is slack at the Coleman fixed point when cash less the consumption floor is below it. -/
theorem Data.saving_lt_cap_of {Z : Type*} [Fintype Z] (D : Data Z)
    (h : ∀ z (k : D.Box), D.y z k - D.m < D.cap) (z : Z) (k : D.Box) :
    D.saving (OrderHom.gfp D.T) z k < D.cap := by
  have h1 := D.gfp_cons z k
  have h2 := (OrderHom.gfp D.T).2.1 z k
  linarith [h z k]

/-- With permanent types the idiosyncratic masses are constant on the tree. -/
theorem stateMass_perm [DecidableEq E] (M : KSModel Z E)
    (hperm : ∀ z z' e e', M.idioProb z z' e e' = if e = e' then 1 else 0) (z₀ : Z) (m₀ : E → ℝ) :
    ∀ (h : List Z) (e : E), M.stateMass z₀ m₀ h e = m₀ e
  | [], _ => rfl
  | z' :: h, e' => by
    change ∑ e, M.stateMass z₀ m₀ h e * M.idioProb (shockAt z₀ h) z' e e' = m₀ e'
    rw [Finset.sum_eq_single e' (fun e _ he => by rw [hperm, ite_eq_right he, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), hperm, ite_eq_left rfl, mul_one,
      stateMass_perm M hperm z₀ m₀ h e']

variable [DecidableEq E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ) {L : ℝ}
  (hL : 0 < L) (hLbox : T.clampLab L = L) (hβR : V.discount * T.returnBound ≤ 1) {cap : ℝ}
  (hcap : 0 < cap)

local notation "𝒟" => aggData V T hγ hL hLbox hβR hcap
local notation "𝒸" => OrderHom.gfp (Data.T (aggData V T hγ hL hLbox hβR hcap))
local notation "𝕄" => crraModel V T hγ

/-- Type `e`'s share of aggregate capital. -/
noncomputable def scale (L : ℝ) (e : E) : ℝ := V.efficiency e / L

include hL in
theorem scale_pos (e : E) : 0 < scale V L e :=
  div_pos (V.effLo_pos.trans_le (V.effLo_le e)) hL

include hL in
theorem scale_mul (e : E) : scale V L e * L = V.efficiency e := div_mul_cancel₀ _ hL.ne'

/-- The prices of the Coleman capital path of the aggregate economy from `(z, k)`. -/
noncomputable def propPrices (z : Z) (k : (𝒟).Box) : List Z → ℝ × ℝ :=
  fun g => (((𝒟).capPath 𝒸 z k g : ℝ), L)

/-- A household state on the proportional path: type `e` holding its share of the node's
capital. -/
def OnPath (z : Z) (k : (𝒟).Box) (e : E) (s : (𝕄).State) : Prop :=
  s.2.idio = e ∧ (s.1 : ℝ) = scale V L e * ((𝒟).capPath 𝒸 z k s.2.node : ℝ)

open Classical in
/-- **The proportional saving rule** of type `e`: its share of the Coleman saving on the path,
zero off it. -/
noncomputable def propRule (z : Z) (k : (𝒟).Box) (e : E) (s : (𝕄).State) : ℝ :=
  if OnPath V T hγ hL hLbox hβR hcap z k e s then
    scale V L e * (𝒟).saving 𝒸 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node)
  else 0

local notation "𝐏" => propPrices V T hγ hL hLbox hβR hcap
local notation "𝐑" => propRule V T hγ hL hLbox hβR hcap
local notation "𝐎" => OnPath V T hγ hL hLbox hβR hcap

theorem propRule_onPath {z : Z} {k : (𝒟).Box} {e : E} {s : (𝕄).State} (hs : 𝐎 z k e s) :
    𝐑 z k e s = scale V L e
      * (𝒟).saving 𝒸 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node) :=
  ite_eq_left hs

/-- The CRRA model's consumption floor lies below every type's share of the Coleman floor. -/
theorem consFloor_lt_scale_m (e : E) : (𝕄).consFloor < scale V L e * (𝒟).m := by
  have h1 : crraFloorLevel V T hγ ≤ T.wageLo * V.effLo / 4 := min_le_right _ _
  have h2 : T.wageLo * V.effLo ≤ T.wageLo * V.efficiency e :=
    mul_le_mul_of_nonneg_left (V.effLo_le e) T.wageLo_pos.le
  have h3 := crraFloorLevel_pos V T hγ
  have h4 := mul_pos T.wageLo_pos V.effLo_pos
  have h5 : scale V L e * (T.wageLo * L) = T.wageLo * V.efficiency e := by
    rw [← scale_mul V hL e]; ring
  change crraFloorLevel V T hγ / 2 < scale V L e * (T.wageLo * L)
  rw [h5]
  linarith

/-- On the path, cash is the type's share of aggregate cash. -/
theorem cash_onPath {z : Z} {k : (𝒟).Box} {e : E} {s : (𝕄).State} (hs : 𝐎 z k e s) :
    (𝕄).cash z (𝐏 z k) s
      = scale V L e * (𝒟).y (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node) := by
  simp only [KSModel.cash, KSModel.returnAt, KSModel.wageAt, propPrices]
  rw [hs.2, hs.1]
  change T.grossReturn _ _ L * (scale V L e * _) + T.wage _ _ L * V.efficiency e
      - T.grossReturn _ _ L * 0
    = scale V L e * (T.grossReturn _ _ L * _ + T.wage _ _ L * L)
  rw [← scale_mul V hL e]
  ring

/-- On the path, consumption under the rule is the type's share of Coleman consumption. -/
theorem ruleCons_onPath {z : Z} {k : (𝒟).Box} {e : E} {s : (𝕄).State} (hs : 𝐎 z k e s) :
    KSModel.ruleCons z (𝐏 z k) (𝐑 z k e) s
      = scale V L e * (𝒸).1 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node) := by
  rw [KSModel.ruleCons, cash_onPath V T hγ hL hLbox hβR hcap hs,
    propRule_onPath V T hγ hL hLbox hβR hcap hs, (𝒟).gfp_cons]
  ring

variable (hθ : ∀ e, scale V L e * cap ≤ V.assetCap)

include hL hθ in
theorem scale_mul_mem (e : E) {x : ℝ} (hx : x ∈ Icc 0 cap) :
    scale V L e * x ∈ Icc 0 V.assetCap :=
  ⟨mul_nonneg (scale_pos V hL e).le hx.1,
    (mul_le_mul_of_nonneg_left hx.2 (scale_pos V hL e).le).trans (hθ e)⟩

include hθ in
/-- **The proportional rule is feasible.** -/
theorem propRule_mem (z : Z) (k : (𝒟).Box) (e : E) (s : (𝕄).State) :
    𝐑 z k e s ∈ ((𝕄).household z (𝐏 z k)).feasible s := by
  by_cases hs : 𝐎 z k e s
  · have hsp := (𝒟).saving_spec 𝒸 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node)
    have hmem := scale_mul_mem V hL hθ e (x := (𝒟).saving 𝒸 (shockAt z s.2.node)
      ((𝒟).capPath 𝒸 z k s.2.node)) ⟨hsp.1, hsp.2.1⟩
    have hc := ruleCons_onPath V T hγ hL hLbox hβR hcap hs
    have hm := (𝒸).2.1 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node)
    have hfl := consFloor_lt_scale_m V T hγ hL hLbox hβR hcap e
    have hmul := mul_le_mul_of_nonneg_left hm (scale_pos V hL e).le
    rw [propRule_onPath V T hγ hL hLbox hβR hcap hs]
    refine ⟨hmem.1, le_min hmem.2 ?_⟩
    rw [KSModel.ruleCons, propRule_onPath V T hγ hL hLbox hβR hcap hs] at hc
    linarith
  · rw [propRule, ite_eq_right hs]
    exact ⟨le_rfl, le_min (𝕄).assetCap_pos.le (sub_nonneg.2 ((𝕄).consFloor_le_cash z _ s))⟩

/-- Type `e`'s root state at capital `k`. -/
noncomputable def propRoot (e : E) (k : (𝒟).Box) : (𝕄).State :=
  (⟨scale V L e * k, scale_mul_mem V hL hθ e k.2⟩, ⟨e, []⟩)

/-- **The proportional plan** of type `e` from `(z, k)`. -/
noncomputable def propPlan (z : Z) (k : (𝒟).Box) (e : E) :
    ((𝕄).household z (𝐏 z k)).Plan (propRoot V T hγ hL hLbox hβR hcap hθ e k) :=
  KSModel.rulePlan z (𝐏 z k) (propRule_mem V T hγ hL hLbox hβR hcap hθ z k e) _

include hθ in
/-- From a state on the path, the next state stays on it when the type is unchanged. -/
theorem onPath_next {z : Z} {k : (𝒟).Box} {e : E} {s : (𝕄).State} (hs : 𝐎 z k e s) (z' : Z) :
    𝐎 z k e ((𝕄).transition (z', e) (s, 𝐑 z k e s)) := by
  refine ⟨rfl, ?_⟩
  have hsp := (𝒟).saving_spec 𝒸 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node)
  change (((𝕄).clampAssets (𝐑 z k e s) : ↥(Icc (0 : ℝ) (𝕄).assetCap)) : ℝ)
    = scale V L e * ((𝒟).capPath 𝒸 z k (z' :: s.2.node) : ℝ)
  rw [propRule_onPath V T hγ hL hLbox hβR hcap hs,
    (𝕄).clampAssets_of_mem (scale_mul_mem V hL hθ e ⟨hsp.1, hsp.2.1⟩)]
  rfl

variable (hperm : ∀ z z' e e', V.idioProb z z' e e' = if e = e' then 1 else 0)

include hperm in
/-- **Histories of positive probability stay on the proportional path.** -/
theorem onPath_of_pos (z : Z) (k : (𝒟).Box) (e : E) :
    ∀ (n : ℕ) (h : Fin n → Z × E),
      0 < (propPlan V T hγ hL hLbox hβR hcap hθ z k e).histProb n h →
      𝐎 z k e (KSModel.ruleState (𝐑 z k e) (propRoot V T hγ hL hLbox hβR hcap hθ e k) n h)
  | 0, _, _ => ⟨rfl, rfl⟩
  | n + 1, h, hpos => by
    obtain ⟨h', ze, rfl⟩ : ∃ h' ze, h = Fin.snoc h' ze :=
      ⟨Fin.init h, h (Fin.last n), (Fin.snoc_init_self h).symm⟩
    rw [Plan.histProb_snoc] at hpos
    have hp0 := (propPlan V T hγ hL hLbox hβR hcap hθ z k e).histProb_nonneg n h'
    rcases hp0.eq_or_lt with h0 | h1
    · rw [← h0, zero_mul] at hpos
      exact absurd hpos (lt_irrefl _)
    have hprob := (mul_pos_iff_of_pos_left h1).1 hpos
    have ih := onPath_of_pos z k e n h' h1
    obtain ⟨z', e'⟩ := ze
    have he' : e' = e := by
      change 0 < V.aggProb _ z' * V.idioProb _ z'
        (KSModel.ruleState (𝐑 z k e) (propRoot V T hγ hL hLbox hβR hcap hθ e k) n h').2.idio e'
        at hprob
      rw [hperm, ih.1] at hprob
      by_contra hne
      rw [ite_eq_right (fun h => hne h.symm), mul_zero] at hprob
      exact lt_irrefl _ hprob
    subst he'
    rw [KSModel.ruleState_snoc]
    exact onPath_next V T hγ hL hLbox hβR hcap hθ ih z'

include hθ hperm in
/-- **On the path the household's expected marginal value is its scaled Coleman continuation.** -/
theorem ruleRhs_onPath {z : Z} {k : (𝒟).Box} {e : E} {s : (𝕄).State} (hs : 𝐎 z k e s) :
    V.discount * KSModel.ruleRhs z (𝐏 z k) (crraSmoothUtility V T hγ) (𝐑 z k e) s
      = scale V L e ^ (-γ) * (𝒟).cont 𝒸 (shockAt z s.2.node)
        ((𝒟).saving 𝒸 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node)) := by
  set sav := (𝒟).saving 𝒸 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node) with hsav
  have hsp := (𝒟).saving_spec 𝒸 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node)
  have hθ0 := (scale_pos V hL e).le
  rw [KSModel.ruleRhs, Data.cont, Fintype.sum_prod_type, mul_left_comm (scale V L e ^ (-γ))]
  change V.discount * _ = V.discount * (_ * _)
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [Finset.sum_eq_single e]
  · have hnext : KSModel.ruleCons z (𝐏 z k) (𝐑 z k e)
          ((𝕄).stateAt (𝐑 z k e s) ⟨e, z' :: s.2.node⟩)
        = scale V L e * (𝒸).1 z' ((𝒟).capPath 𝒸 z k (z' :: s.2.node)) :=
      ruleCons_onPath V T hγ hL hLbox hβR hcap
        (onPath_next V T hγ hL hLbox hβR hcap hθ hs z')
    have hext : (𝒟).ext 𝒸 z' sav = (𝒸).1 z' ((𝒟).capPath 𝒸 z k (z' :: s.2.node)) := by
      rw [Data.ext, projIcc_of_mem _ (show sav ∈ Icc 0 (𝒟).cap from ⟨hsp.1, hsp.2.1⟩)]
      rfl
    have hP : (𝕄).shockProb z (z', e) (s, 𝐑 z k e s) = V.aggProb (shockAt z s.2.node) z' := by
      change V.aggProb _ z' * V.idioProb _ z' s.2.idio e = _
      rw [hperm, hs.1, ite_eq_left rfl, mul_one]
    have hpol := (𝒟).pol_pos 𝒸 z' ((𝒟).capPath 𝒸 z k (z' :: s.2.node))
    dsimp only
    rw [hP, hnext, hext]
    change V.aggProb (shockAt z s.2.node) z' * T.grossReturn z' sav L
        * (scale V L e * (𝒸).1 z' ((𝒟).capPath 𝒸 z k (z' :: s.2.node))) ^ (-γ)
      = scale V L e ^ (-γ) * (V.aggProb (shockAt z s.2.node) z' * T.grossReturn z' sav L
        * ((𝒸).1 z' ((𝒟).capPath 𝒸 z k (z' :: s.2.node))) ^ (-γ))
    rw [Real.mul_rpow hθ0 hpol.le]
    ring
  · intro e' _ he'
    change V.aggProb _ z' * V.idioProb _ z' s.2.idio e' * _ * _ = 0
    rw [hperm, hs.1, ite_eq_right (fun h => he' h.symm)]
    ring
  · exact fun h => absurd (Finset.mem_univ _) h

include hperm in
/-- **The proportional plan satisfies the household's Euler conditions** on the histories of
positive probability. -/
theorem propPlan_euler (hslack : ∀ (z : Z) (k : (𝒟).Box), (𝒟).saving 𝒸 z k < cap)
    (z : Z) (k : (𝒟).Box) (e : E) :
    KSModel.PlanEulerOn z (𝐏 z k) (crraSmoothUtility V T hγ)
      (propPlan V T hγ hL hLbox hβR hcap hθ z k e) := by
  intro n h hpos
  have hs := onPath_of_pos V T hγ hL hLbox hβR hcap hθ hperm z k e n h hpos
  set s := KSModel.ruleState (𝐑 z k e) (propRoot V T hγ hL hLbox hβR hcap hθ e k) n h with hsdef
  have hmu : KSModel.nextMU z (𝐏 z k) (crraSmoothUtility V T hγ)
      (propPlan V T hγ hL hLbox hβR hcap hθ z k e) n h
      = KSModel.ruleRhs z (𝐏 z k) (crraSmoothUtility V T hγ) (𝐑 z k e) s :=
    KSModel.rulePlan_nextMU z _ _ _ _ n h
  have hc : KSModel.planCons z (𝐏 z k) (propPlan V T hγ hL hLbox hβR hcap hθ z k e) n h
      = scale V L e * (𝒸).1 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node) :=
    ruleCons_onPath V T hγ hL hLbox hβR hcap hs
  have ha : (propPlan V T hγ hL hLbox hβR hcap hθ z k e).action n h
      = scale V L e * (𝒟).saving 𝒸 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node) :=
    propRule_onPath V T hγ hL hLbox hβR hcap hs
  have hrhs := ruleRhs_onPath V T hγ hL hLbox hβR hcap hθ hperm hs
  obtain ⟨hs0, -, -, h1, h2⟩ :=
    (𝒟).saving_spec 𝒸 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node)
  have hgfp := (𝒟).gfp_cons (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node)
  have hm := (𝒸).2.1 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node)
  have hθ0 := scale_pos V hL e
  have hpol := (𝒟).pol_pos 𝒸 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node)
  have hdu : (crraSmoothUtility V T hγ).du (scale V L e
        * (𝒸).1 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node))
      = scale V L e ^ (-γ)
        * (𝒟).du ((𝒸).1 (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node)) :=
    Real.mul_rpow hθ0.le hpol.le
  have hθγ : 0 ≤ scale V L e ^ (-γ) := Real.rpow_nonneg hθ0.le _
  have hdisc : (𝕄).discount = V.discount := rfl
  rw [hmu, hc, ha, hdu, hdisc, hrhs]
  refine ⟨?_, fun hpos' => ?_, fun _ => ?_⟩
  · have := consFloor_lt_scale_m V T hγ hL hLbox hβR hcap e
    have := mul_le_mul_of_nonneg_left hm hθ0.le
    linarith
  · refine mul_le_mul_of_nonneg_left ?_ hθγ
    rw [hgfp]
    exact h1 (pos_of_mul_pos_right hpos' hθ0.le)
  · refine mul_le_mul_of_nonneg_left ?_ hθγ
    rw [hgfp]
    exact h2 (hslack _ _)

include hperm in
/-- **Each type saves its share of the Coleman saving**: at the prices of the aggregate Coleman
path from `(z, k)`, type `e` holding `θ_e k` optimally saves `θ_e s*(z, k)`. -/
theorem policy_eq_prop (hslack : ∀ (z : Z) (k : (𝒟).Box), (𝒟).saving 𝒸 z k < cap)
    (z : Z) (k : (𝒟).Box) (e : E) :
    (𝕄).policy z (𝐏 z k) (propRoot V T hγ hL hLbox hβR hcap hθ e k)
      = scale V L e * (𝒟).saving 𝒸 z k := by
  have hD : ∀ n h, 0 < (propPlan V T hγ hL hLbox hβR hcap hθ z k e).histProb n h →
      (crraSmoothUtility V T hγ).du (KSModel.planCons z (𝐏 z k)
        (propPlan V T hγ hL hLbox hβR hcap hθ z k e) n h) ≤ (scale V L e * (𝒟).m) ^ (-γ) := by
    intro n h hpos
    have hs := onPath_of_pos V T hγ hL hLbox hβR hcap hθ hperm z k e n h hpos
    have hc : KSModel.planCons z (𝐏 z k) (propPlan V T hγ hL hLbox hβR hcap hθ z k e) n h
        = scale V L e * (𝒸).1 _ _ := ruleCons_onPath V T hγ hL hLbox hβR hcap hs
    rw [hc]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos (scale_pos V hL e) (𝒟).m_pos)
      (mul_le_mul_of_nonneg_left ((𝒸).2.1 _ _) (scale_pos V hL e).le) (by linarith)
  have h := KSModel.policy_eq_of_eulerOn z _ _ rfl
    (propPlan_euler V T hγ hL hLbox hβR hcap hθ hperm hslack z k e) hD Fin.elim0
  rw [h]
  exact propRule_onPath V T hγ hL hLbox hβR hcap (s := propRoot V T hγ hL hLbox hβR hcap hθ e k)
    ⟨rfl, rfl⟩

/-! ### The proportional cross-section on the tree -/

variable (p : E → ℝ≥0)

/-- Type `e` holding its share of capital `K`. -/
noncomputable def propPoint (e : E) (K : (𝒟).Box) : (𝕄).AState :=
  (⟨scale V L e * K, scale_mul_mem V hL hθ e K.2⟩, ⟨e⟩)

/-- **The proportional cross-section** at capital `K`: mass `p e` of type `e`, each holding its
share. -/
noncomputable def propDist (K : (𝒟).Box) : Measure (𝕄).AState :=
  ∑ e, p e • Measure.dirac (propPoint V T hγ hL hLbox hβR hcap hθ e K)

theorem integral_propDist (K : (𝒟).Box) (f : (𝕄).AState →ᵇ ℝ) :
    ∫ x, f x ∂(propDist V T hγ hL hLbox hβR hcap hθ p K)
      = ∑ e, (p e : ℝ) * f (propPoint V T hγ hL hLbox hβR hcap hθ e K) := by
  rw [propDist, integral_finsetSum_measure fun e _ => f.integrable _]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_smul_nnreal_measure, integral_dirac]
  rfl

variable (hp : ∑ e, p e = 1)

include hp in
theorem isProbabilityMeasure_propDist (K : (𝒟).Box) :
    IsProbabilityMeasure (propDist V T hγ hL hLbox hβR hcap hθ p K) := by
  constructor
  rw [propDist, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
  rw [← ENNReal.ofNNReal_finsetSum, hp, ENNReal.coe_one]

variable (hLsum : ∑ e, (p e : ℝ) * V.efficiency e = L)

include hp hLsum in
/-- Mean assets of the proportional cross-section are `K`. -/
theorem integral_assets_propDist (K : (𝒟).Box) :
    ∫ x, (𝕄).assets x ∂(propDist V T hγ hL hLbox hβR hcap hθ p K) = K := by
  rw [integral_propDist]
  change ∑ e, (p e : ℝ) * (scale V L e * (K : ℝ)) = K
  have : ∀ e, (p e : ℝ) * (scale V L e * (K : ℝ)) = (p e : ℝ) * V.efficiency e * (K / L) :=
    fun e => by rw [scale]; ring
  rw [Finset.sum_congr rfl fun e _ => this e, ← Finset.sum_mul, hLsum, mul_div_cancel₀ _ hL.ne']

include hp hperm hLsum in
/-- Labour on the tree from a proportional cross-section is `L`. -/
theorem labour_propDist (z₀ : Z) (K : (𝒟).Box) (h : List Z) :
    (𝕄).labour z₀ ((𝕄).initMass (propDist V T hγ hL hLbox hβR hcap hθ p K)) h = L := by
  have hmass : ∀ e, (𝕄).initMass (propDist V T hγ hL hLbox hβR hcap hθ p K) e = p e := by
    intro e
    change (propDist V T hγ hL hLbox hβR hcap hθ p K).real ((𝕄).idioSet e) = _
    rw [← (𝕄).integral_idioInd, integral_propDist,
      Finset.sum_eq_single e (fun e' _ he' => by
        rw [(𝕄).idioInd_of_ne (x := propPoint V T hγ hL hLbox hβR hcap hθ e' K) he', mul_zero])
      (fun h => absurd (Finset.mem_univ _) h),
      (𝕄).idioInd_of_eq (e := e) (x := propPoint V T hγ hL hLbox hβR hcap hθ e K) rfl, mul_one]
  simp only [KSModel.labour, stateMass_perm (𝕄) hperm z₀ _ h, hmass]
  exact hLsum

include hp hperm hLsum in
/-- **The proportional cross-section stays proportional** along the Coleman capital path. -/
theorem nodeDist_propDist (hslack : ∀ (z : Z) (k : (𝒟).Box), (𝒟).saving 𝒸 z k < cap)
    (z₀ : Z) (k₀ : (𝒟).Box) :
    ∀ h, (𝕄).nodeDist z₀ (propDist V T hγ hL hLbox hβR hcap hθ p k₀) (𝐏 z₀ k₀) h
      = propDist V T hγ hL hLbox hβR hcap hθ p ((𝒟).capPath 𝒸 z₀ k₀ h)
  | [] => rfl
  | z' :: h => by
    have hprob₀ := isProbabilityMeasure_propDist V T hγ hL hLbox hβR hcap hθ p hp
    have := hprob₀ ((𝒟).capPath 𝒸 z₀ k₀ h)
    have := hprob₀ ((𝒟).capPath 𝒸 z₀ k₀ (z' :: h))
    change (𝕄).pushNode z₀ (𝐏 z₀ k₀) h z'
      ((𝕄).nodeDist z₀ (propDist V T hγ hL hLbox hβR hcap hθ p k₀) (𝐏 z₀ k₀) h) = _
    rw [nodeDist_propDist hslack z₀ k₀ h]
    have : IsProbabilityMeasure ((𝕄).pushNode z₀ (𝐏 z₀ k₀) h z'
        (propDist V T hγ hL hLbox hβR hcap hθ p ((𝒟).capPath 𝒸 z₀ k₀ h))) :=
      (𝕄).isProbabilityMeasure_pushNode _ _ _ _ _
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [(𝕄).integral_pushNode]
    change ∫ x, (𝕄).expectedNext z₀ (𝐏 z₀ k₀) h z' f x ∂_ = _
    rw [integral_propDist, integral_propDist]
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    -- the household's saving at node `h`
    have hshift : shiftPath (𝐏 z₀ k₀) h = 𝐏 (shockAt z₀ h) ((𝒟).capPath 𝒸 z₀ k₀ h) := by
      funext g
      simp only [shiftPath_apply, propPrices, Data.capPath_append (𝒟) 𝒸 z₀ k₀ g h]
    have hpol : (𝕄).policy z₀ (𝐏 z₀ k₀)
        ((propPoint V T hγ hL hLbox hβR hcap hθ e ((𝒟).capPath 𝒸 z₀ k₀ h)).1, ⟨e, h⟩)
        = scale V L e * (𝒟).saving 𝒸 (shockAt z₀ h) ((𝒟).capPath 𝒸 z₀ k₀ h) := by
      have h1 := (𝕄).policy_shift z₀ (𝐏 z₀ k₀) h
        (propRoot V T hγ hL hLbox hβR hcap hθ e ((𝒟).capPath 𝒸 z₀ k₀ h))
      rw [hshift, policy_eq_prop V T hγ hL hLbox hβR hcap hθ hperm hslack] at h1
      exact h1.symm
    have hsp := (𝒟).saving_spec 𝒸 (shockAt z₀ h) ((𝒟).capPath 𝒸 z₀ k₀ h)
    have hnext : (𝕄).nextA z₀ (𝐏 z₀ k₀) h e
        (propPoint V T hγ hL hLbox hβR hcap hθ e ((𝒟).capPath 𝒸 z₀ k₀ h))
        = propPoint V T hγ hL hLbox hβR hcap hθ e ((𝒟).capPath 𝒸 z₀ k₀ (z' :: h)) := by
      refine Prod.ext (Subtype.ext ?_) rfl
      change (((𝕄).clampAssets ((𝕄).policy z₀ (𝐏 z₀ k₀)
        ((propPoint V T hγ hL hLbox hβR hcap hθ e ((𝒟).capPath 𝒸 z₀ k₀ h)).1, ⟨e, h⟩)) :
        ↥(Icc (0 : ℝ) (𝕄).assetCap)) : ℝ) = _
      rw [hpol, (𝕄).clampAssets_of_mem (scale_mul_mem V hL hθ e ⟨hsp.1, hsp.2.1⟩)]
      rfl
    change ∑ e', (𝕄).nextProb z₀ h z' e'
        (propPoint V T hγ hL hLbox hβR hcap hθ e ((𝒟).capPath 𝒸 z₀ k₀ h))
      * f ((𝕄).nextA z₀ (𝐏 z₀ k₀) h e'
        (propPoint V T hγ hL hLbox hβR hcap hθ e ((𝒟).capPath 𝒸 z₀ k₀ h))) = _
    rw [Finset.sum_eq_single e, hnext]
    · change V.idioProb _ z' e e * _ = _
      rw [hperm, ite_eq_left rfl, one_mul]
    · intro e' _ he'
      change V.idioProb _ z' e e' * _ = 0
      rw [hperm, ite_eq_right (fun h => he' h.symm), zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h

include hp hperm hLsum in
/-- **A sequential equilibrium from every proportional cross-section**, at every capital share:
households with permanent efficiency types and assets proportional to efficiency, CRRA utility,
Cobb–Douglas prices, mean efficiency inside the labour box, `β R̄ ≤ 1` and a slack capital cap.
Aggregate capital follows the Coleman path of the aggregate economy, `K' = s*(z, K)`. -/
theorem isSequentialEquilibrium_prop (hslack : ∀ (z : Z) (k : (𝒟).Box), (𝒟).saving 𝒸 z k < cap)
    (z₀ : Z) (k₀ : (𝒟).Box) :
    (𝕄).IsSequentialEquilibrium z₀ (propDist V T hγ hL hLbox hβR hcap hθ p k₀)
      (fun h => ((𝒟).capPath 𝒸 z₀ k₀ h : ℝ)) := by
  have hQ : (𝕄).pricePath z₀ ((𝕄).initMass (propDist V T hγ hL hLbox hβR hcap hθ p k₀))
      (fun h => ((𝒟).capPath 𝒸 z₀ k₀ h : ℝ)) = 𝐏 z₀ k₀ := by
    funext g
    simp only [KSModel.pricePath, propPrices,
      labour_propDist V T hγ hL hLbox hβR hcap hθ hperm p hp hLsum z₀ k₀ g]
  intro h
  rw [KSModel.meanCapital, hQ,
    nodeDist_propDist V T hγ hL hLbox hβR hcap hθ hperm p hp hLsum hslack z₀ k₀ h,
    integral_assets_propDist V T hγ hL hLbox hβR hcap hθ p hp hLsum]

end Coleman

end KrusellSmith

end LeanEconomics
