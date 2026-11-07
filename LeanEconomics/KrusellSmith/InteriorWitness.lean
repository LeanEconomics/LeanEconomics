/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.InteriorSaving
import LeanEconomics.KrusellSmith.EmploymentMarginals
import LeanEconomics.KrusellSmith.ComplementarityWitness

/-!
# An economy with interior saving in which `(z, K)` is sufficient

Milestone OI5 of `ORDER_STRUCTURE_PLAN.md` (OS4(b)): the order route with a household that saves
strictly inside its constraints.

* Two aggregate shocks (`true` good), i.i.d. `1/2`; two efficiency levels `1` and `3/4`, i.i.d.
  `1/2` across households and periods.
* **Linear technology** `Y = A K + B(z) L`: gross return `6/5`, wage `1` (good) or `1/3` (bad),
  the exact marginal products. Log utility, `β = 1/2`, asset cap `ā = 25/72`, consumption floor
  `1/100`.
* **Ordered cash**: after a bad shock cash is at most `6/5 · 25/72 + 1/3 = 3/4`, after a good one
  at least `3/4` (`orderedCash`).

**`interiorWitness`**: in every sequence-state equilibrium (one exists,
`exists_seqStateEquilibrium`), `(z, K)` is a sufficient state, and after every good shock the
low-efficiency households — half of all households — save strictly between `0` and `ā`
(`saving_interior`). Their saving responds to their own assets, so the cross-section carries
its whole history; capital encodes that history (the chain argument), which is why `(z, K)`
suffices.

Interiority is checked by two corner deviations with `δ = 1/3000`: raising saving from `0` gains
at least `β Σ ¼ · Rδ/(w'e' + Rδ)` (`value_sub_ge`) against a utility cost at most
`δ/(3/4 − δ)`; lowering it from `ā` gains at least `δ/(59/72 + δ)` against a continuation loss at
most `β Σ ¼ · Rδ/((R − 1)ā + w'e' − Rδ)` (`value_sub_le`).
-/

open MeasureTheory Set

namespace LeanEconomics

namespace KrusellSmith

namespace InteriorWitness

/-- The wage: `1` after a good shock, `1/3` after a bad one. -/
noncomputable def wageOf (z : Bool) : ℝ := if z then 1 else 1 / 3

/-- Efficiency: `1` (high) or `3/4` (low). -/
noncomputable def effOf (e : Bool) : ℝ := if e then 1 else 3 / 4

/-- **The economy**: i.i.d. shocks, a linear technology, log utility. -/
noncomputable def econ : KSInada Bool Bool where
  aggProb _ _ := 1 / 2
  aggProb_nonneg _ _ := by norm_num
  aggProb_sum _ := by norm_num [Fintype.sum_bool]
  idioProb _ _ _ _ := 1 / 2
  idioProb_nonneg _ _ _ _ := by norm_num
  idioProb_sum _ _ _ := by norm_num [Fintype.sum_bool]
  efficiency := effOf
  efficiency_nonneg e := by cases e <;> norm_num [effOf]
  assetCap := 25 / 72
  assetCap_pos := by norm_num
  discount := 1 / 2
  discount_pos := by norm_num
  discount_lt_one := by norm_num
  grossReturn _ _ _ := 6 / 5
  continuous_grossReturn _ := continuous_const
  grossReturn_nonneg _ _ _ := by norm_num
  returnBound := 6 / 5
  grossReturn_le _ _ _ := le_rfl
  wage z _ _ := wageOf z
  continuous_wage _ := continuous_const
  wage_nonneg z _ _ := by cases z <;> norm_num [wageOf]
  wageBound := 1
  wage_le z _ _ := by cases z <;> norm_num [wageOf]
  incomeFloor := 1 / 4
  incomeFloor_pos := by norm_num
  incomeFloor_le z _ _ e := by cases z <;> cases e <;> norm_num [wageOf, effOf]
  utility := crraUtility 1
  continuousOn_utility := continuousOn_crraUtility 1
  strictConcaveOn_utility := strictConcaveOn_crraUtility one_pos
  monotoneOn_utility := monotoneOn_crraUtility 1
  marginalInada := marginalInada_crraUtility one_pos

/-- The model, with consumption floor `1/100`. -/
noncomputable abbrev model : KSModel Bool Bool :=
  econ.toModel (1 / 100) (by norm_num) (by change (1 / 100 : ℝ) ≤ 1 / 4; norm_num)

theorem pricesExogenous : model.PricesExogenous := fun _ _ _ _ _ => ⟨rfl, rfl⟩

theorem iidShocks : model.IIDShocks := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem cap_eq : model.assetCap = 25 / 72 := rfl

/-- **Ordered cash**: at most `3/4` after a bad shock, at least `3/4` after a good one. -/
theorem orderedCash : model.OrderedCash := by
  intro y y' hlt K L K' L' a b e f
  obtain ⟨rfl, rfl⟩ : y = false ∧ y' = true := by
    revert hlt
    cases y <;> cases y' <;> decide
  have ha : (a : ℝ) ≤ 25 / 72 := a.2.2
  have hb : (0 : ℝ) ≤ b := b.2.1
  change 6 / 5 * (a : ℝ) + wageOf false * effOf e ≤ 6 / 5 * (b : ℝ) + wageOf true * effOf f
  cases e <;> cases f <;> norm_num [wageOf, effOf] <;> linarith

theorem log_eq (c : ℝ) (_ : model.consFloor ≤ c) : model.utility c = Real.log c := by
  change crraUtility 1 c = Real.log c
  simp [crraUtility]

theorem floor_pos : 0 < model.consFloor := by
  change (0 : ℝ) < 1 / 100
  norm_num

/-- The step of the corner deviations. -/
noncomputable def δ : ℝ := 1 / 3000

theorem δ_pos : 0 < δ := by norm_num [δ]

/-- The continuation at a root state, as a sum over next period's shocks. -/
theorem cont_sub (P : List Bool → ℝ × ℝ) (s : model.State) (hs : s.2.node = []) (a b : ℝ) :
    model.cont true P s b - model.cont true P s a
      = ∑ ze : Bool × Bool, 1 / 4 * ((model.household true P).valueFunction
          (model.stateAt b ⟨ze.2, [ze.1]⟩)
        - (model.household true P).valueFunction (model.stateAt a ⟨ze.2, [ze.1]⟩)) := by
  simp only [KSModel.cont, ← Finset.sum_sub_distrib, hs]
  refine Finset.sum_congr rfl fun ze _ => ?_
  change (1 / 2 : ℝ) * (1 / 2) * _ - (1 / 2 : ℝ) * (1 / 2) * _ = _
  ring

theorem cash_low (P : List Bool → ℝ × ℝ) (a : ↥(Icc (0 : ℝ) model.assetCap)) :
    model.cash true P (a, ⟨false, []⟩) = 6 / 5 * a + 3 / 4 := by
  change 6 / 5 * (a : ℝ) + wageOf true * effOf false = _
  norm_num [wageOf, effOf]

theorem discount_eq : model.discount = 1 / 2 := rfl

/-- **Low-efficiency households save a positive amount after a good shock.** -/
theorem policy_pos (P : List Bool → ℝ × ℝ) (a : ↥(Icc (0 : ℝ) model.assetCap)) :
    0 < model.policy true P (a, ⟨false, []⟩) := by
  set s : model.State := (a, ⟨false, []⟩)
  have ha0 : (0 : ℝ) ≤ a := a.2.1
  have ha1 : (a : ℝ) ≤ 25 / 72 := a.2.2
  have hx := cash_low P a
  have hd : δ = 1 / 3000 := rfl
  have hδf : δ ∈ (model.household true P).feasible s := by
    refine ⟨δ_pos.le, le_min ?_ ?_⟩
    · change δ ≤ 25 / 72
      rw [hd]; norm_num
    · change δ ≤ model.cash true P s - 1 / 100
      rw [hx, hd]; linarith
  refine KSModel.policy_pos_of true P hδf ?_
  -- the gain of the continuation
  have key : ∀ z' e' : Bool, 6 / 5 * δ / (6 / 5 * 0 + wageOf z' * effOf e' + 6 / 5 * δ)
      ≤ (model.household true P).valueFunction (model.stateAt δ ⟨e', [z']⟩)
        - (model.household true P).valueFunction (model.stateAt 0 ⟨e', [z']⟩) := by
    intro z' e'
    have h := KSModel.value_sub_ge true P log_eq floor_pos (a := 0) (δ := δ) le_rfl δ_pos.le
      (by rw [zero_add]; change δ ≤ 25 / 72; rw [hd]; norm_num) ⟨e', [z']⟩
    rw [zero_add] at h
    exact h
  have hc := cont_sub P s rfl 0 δ
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool] at hc
  dsimp only at hc
  have k1 := key true true
  have k2 := key true false
  have k3 := key false true
  have k4 := key false false
  have n1 : 6 / 5 * δ / (6 / 5 * 0 + wageOf true * effOf true + 6 / 5 * δ) = 1 / 2501 := by
    norm_num [wageOf, effOf, hd]
  have n2 : 6 / 5 * δ / (6 / 5 * 0 + wageOf true * effOf false + 6 / 5 * δ) = 1 / 1876 := by
    norm_num [wageOf, effOf, hd]
  have n3 : 6 / 5 * δ / (6 / 5 * 0 + wageOf false * effOf true + 6 / 5 * δ) = 3 / 2503 := by
    norm_num [wageOf, effOf, hd]
  have n4 : 6 / 5 * δ / (6 / 5 * 0 + wageOf false * effOf false + 6 / 5 * δ) = 1 / 626 := by
    norm_num [wageOf, effOf, hd]
  rw [n1] at k1
  rw [n2] at k2
  rw [n3] at k3
  rw [n4] at k4
  -- the utility cost
  have hxδ : model.consFloor ≤ 6 / 5 * (a : ℝ) + 3 / 4 - δ := by
    change (1 / 100 : ℝ) ≤ _
    rw [hd]; linarith
  rw [hx, log_eq _ (by change (1 / 100 : ℝ) ≤ _; linarith), log_eq _ hxδ, discount_eq]
  have hl := KSModel.log_sub_le δ_pos.le (show δ < 6 / 5 * (a : ℝ) + 3 / 4 by rw [hd]; linarith)
  have hm : δ / (6 / 5 * (a : ℝ) + 3 / 4 - δ) ≤ δ / (3 / 4 - δ) :=
    div_le_div_of_nonneg_left δ_pos.le (by rw [hd]; norm_num) (by linarith)
  have n0 : δ / (3 / 4 - δ) = 1 / 2249 := by norm_num [hd]
  rw [n0] at hm
  linarith

/-- **Low-efficiency households save less than the cap after a good shock.** -/
theorem policy_lt_cap (P : List Bool → ℝ × ℝ) (a : ↥(Icc (0 : ℝ) model.assetCap)) :
    model.policy true P (a, ⟨false, []⟩) < model.assetCap := by
  set s : model.State := (a, ⟨false, []⟩)
  have ha0 : (0 : ℝ) ≤ a := a.2.1
  have ha1 : (a : ℝ) ≤ 25 / 72 := a.2.2
  have hx := cash_low P a
  have hd : δ = 1 / 3000 := rfl
  have hA : model.assetCap = 25 / 72 := rfl
  have hδf : model.assetCap - δ ∈ (model.household true P).feasible s := by
    refine ⟨?_, le_min ?_ ?_⟩
    · change (0 : ℝ) ≤ 25 / 72 - δ
      rw [hd]; norm_num
    · change (25 / 72 : ℝ) - δ ≤ 25 / 72
      rw [hd]; norm_num
    · change (25 / 72 : ℝ) - δ ≤ model.cash true P s - 1 / 100
      rw [hx, hd]; linarith
  refine KSModel.policy_lt_cap_of true P hδf ?_
  -- the loss of the continuation
  have key : ∀ z' e' : Bool,
      (model.household true P).valueFunction (model.stateAt model.assetCap ⟨e', [z']⟩)
        - (model.household true P).valueFunction (model.stateAt (model.assetCap - δ) ⟨e', [z']⟩)
      ≤ 6 / 5 * δ / (6 / 5 * (25 / 72) + wageOf z' * effOf e' - 25 / 72 - 6 / 5 * δ) := by
    intro z' e'
    exact KSModel.value_sub_le true P log_eq floor_pos (b := model.assetCap) (δ := δ) δ_pos.le
      (by change δ ≤ 25 / 72; rw [hd]; norm_num) le_rfl ⟨e', [z']⟩ (by
        change (1 / 100 : ℝ) ≤ 6 / 5 * (25 / 72) + wageOf z' * effOf e' - 25 / 72 - 6 / 5 * δ
        cases z' <;> cases e' <;> norm_num [wageOf, effOf, hd])
  have hc := cont_sub P s rfl (model.assetCap - δ) model.assetCap
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool] at hc
  dsimp only at hc
  have k1 := key true true
  have k2 := key true false
  have k3 := key false true
  have k4 := key false false
  have n1 : 6 / 5 * δ / (6 / 5 * (25 / 72) + wageOf true * effOf true - 25 / 72 - 6 / 5 * δ)
      = 18 / 48107 := by norm_num [wageOf, effOf, hd]
  have n2 : 6 / 5 * δ / (6 / 5 * (25 / 72) + wageOf true * effOf false - 25 / 72 - 6 / 5 * δ)
      = 18 / 36857 := by norm_num [wageOf, effOf, hd]
  have n3 : 6 / 5 * δ / (6 / 5 * (25 / 72) + wageOf false * effOf true - 25 / 72 - 6 / 5 * δ)
      = 18 / 18107 := by norm_num [wageOf, effOf, hd]
  have n4 : 6 / 5 * δ / (6 / 5 * (25 / 72) + wageOf false * effOf false - 25 / 72 - 6 / 5 * δ)
      = 18 / 14357 := by norm_num [wageOf, effOf, hd]
  rw [n1] at k1
  rw [n2] at k2
  rw [n3] at k3
  rw [n4] at k4
  -- the utility gain
  have hc0 : 0 < 6 / 5 * (a : ℝ) + 3 / 4 - model.assetCap := by linarith [hA]
  have e1 : 6 / 5 * (a : ℝ) + 3 / 4 - (model.assetCap - δ)
      = 6 / 5 * (a : ℝ) + 3 / 4 - model.assetCap + δ := by ring
  rw [hx, e1, log_eq _ (by change (1 / 100 : ℝ) ≤ _; linarith [hA]),
    log_eq _ (by change (1 / 100 : ℝ) ≤ _; linarith [hA, δ_pos]), discount_eq]
  have hl := KSModel.le_log_sub hc0 δ_pos.le
  have hm : δ / (59 / 72 + δ) ≤ δ / (6 / 5 * (a : ℝ) + 3 / 4 - model.assetCap + δ) :=
    div_le_div_of_nonneg_left δ_pos.le (by linarith [δ_pos]) (by linarith [hA])
  have n0 : δ / (59 / 72 + δ) = 3 / 7378 := by norm_num [hd]
  rw [n0] at hm
  linarith

/-- **Saving is strictly interior** for low-efficiency households after a good shock, along every
price path. -/
theorem saving_interior (P : List Bool → ℝ × ℝ) (x : model.AState) (hx : x.2.idio = false) :
    0 < model.policy true P (x.1, ⟨x.2.idio, []⟩)
      ∧ model.policy true P (x.1, ⟨x.2.idio, []⟩) < model.assetCap := by
  rw [hx]
  exact ⟨policy_pos P x.1, policy_lt_cap P x.1⟩

/-- The i.i.d. employment design: each efficiency level has mass `1/2`. -/
noncomputable def design : EmploymentDesign model.idioProb where
  m _ _ := 1 / 2
  m_nonneg _ _ := by norm_num
  sum_m _ := by norm_num [Fintype.sum_bool]
  consistent _ _ _ := by
    change ∑ _e : Bool, (1 / 2 : ℝ) * (1 / 2) = 1 / 2
    norm_num [Fintype.sum_bool]
  ε := 1 / 2
  ε_pos := by norm_num
  minor _ _ _ _ := le_rfl

/-- **An economy with interior saving in which `(z, K)` is a sufficient state.** In every
sequence-state equilibrium of the linear-technology economy above, `(z, K)` is sufficient, and
after every good shock at least half of the households save strictly between `0` and the cap. -/
theorem interiorWitness {μ : History Bool → ProbabilityMeasure model.AState}
    (hμ : model.IsSeqStateEquilibrium μ) :
    KSModel.KSufficient μ ∧ ∀ ω : History Bool, ω 0 = true →
      1 / 2 ≤ (μ ω : Measure model.AState).real
        {x | 0 < model.policy (ω 0) (model.seqPrices μ ω) (x.1, ⟨x.2.idio, []⟩)
          ∧ model.policy (ω 0) (model.seqPrices μ ω) (x.1, ⟨x.2.idio, []⟩) < model.assetCap} := by
  refine ⟨KSModel.kSufficient_of_orderedCash pricesExogenous iidShocks orderedCash hμ,
    fun ω hω => ?_⟩
  have hm := congrFun (hμ.initMass_eq_design design ω) false
  change (μ ω : Measure model.AState).real {x | x.2.idio = false} = 1 / 2 at hm
  rw [← hm]
  refine measureReal_mono fun x hx => ?_
  rw [hω]
  exact saving_interior _ x hx

/-- **Existence**: the economy has a sequence-state equilibrium, and in it `(z, K)` is sufficient
while half of the households save strictly inside their constraints after every good shock. -/
theorem exists_interiorWitness : ∃ μ : History Bool → ProbabilityMeasure model.AState,
    model.IsSeqStateEquilibrium μ ∧ KSModel.KSufficient μ ∧ ∀ ω : History Bool, ω 0 = true →
      1 / 2 ≤ (μ ω : Measure model.AState).real
        {x | 0 < model.policy (ω 0) (model.seqPrices μ ω) (x.1, ⟨x.2.idio, []⟩)
          ∧ model.policy (ω 0) (model.seqPrices μ ω) (x.1, ⟨x.2.idio, []⟩) < model.assetCap} := by
  obtain ⟨μ, hμ⟩ := model.exists_seqStateEquilibrium
  exact ⟨μ, hμ, interiorWitness hμ⟩

end InteriorWitness

end KrusellSmith

end LeanEconomics
