/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.LightTree
import LeanEconomics.KrusellSmith.CobbDouglas

/-!
# A complementarity economy with a recursive equilibrium on the minimal state

Milestone MR4d of `MINIMAL_STATE_PLAN.md`: discharge the slackness hypotheses of
`exists_consistentSelection_of_complementarity` for a concrete class of economies.

**Slackness of the consumption floor along the iterates** (`KSInada`, any utility with the
marginal Inada condition). The argument of `KSInada.floorLevel_le_consumption` works against any
continuation with concave slices bounded by `valueBound`, not only the value function
(`floorLevel_le_consumptionOf`), and every Bellman iterate from `0` is so bounded
(`abs_iterate_le`). So with the floor at `floorLevel / 2`, consumption is strictly above it along
every iterate of every price path.

**Slackness of the asset cap** (`policyOf_lt_assetCap`): if the largest cash on hand, less the
floor, is below the cap, no saving can reach it. That holds when gross returns are below one and
the cap is large: `Rhi · cap + w̄ Σ e < cap`.

**The economy** (`compEconomy`): log utility, a constant wage `w̄ > 0`, and a gross return
`R(K) = Rlo + (Rhi − Rlo) · clamp(K / cap)` rising in aggregate capital, with
`0 < Rlo ≤ Rhi < 1`. **Theorem** (`compEconomy_exists_consistentSelection`): it has a recursive
equilibrium on the minimal state `(z, μ)`, with no uniqueness assumption.

What is not claimed: gross returns above one (a cap-slack calibration through the oscillation of
the continuation, as `crra_policyOf_lt_assetCap` does for the income-fluctuation problem, would
be needed), and any statement that sequential equilibrium is non-unique in these economies.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

/-! ### The asset cap, from the budget constraint -/

namespace KSModel

variable {M : KSModel Z E} (z₀ : Z) (K : List Z → ℝ × ℝ)

/-- **No saving reaches the cap** when the largest cash on hand, less the floor, is below it. -/
theorem policyOf_lt_assetCap (hbig : M.maxCash - M.consFloor < M.assetCap)
    (w : M.State →ᵇ ℝ) (s : M.State) : M.policyOf z₀ K w s < M.assetCap := by
  have hp := M.policyOf_mem z₀ K w s
  have h1 : M.policyOf z₀ K w s ≤ M.cash z₀ K s - M.consFloor := hp.2.trans (min_le_right _ _)
  have h2 := M.cash_le_maxCash z₀ K s
  linarith

end KSModel

/-! ### The consumption floor, along the iterates -/

namespace KSInada

variable (P : KSInada Z E) {c : ℝ} (hc : 0 < c) (hcy : c ≤ P.incomeFloor) (z₀ : Z)
  (K : List Z → ℝ × ℝ)

omit hc hcy in
theorem abs_utility_le_of {x : ℝ} (hx : |P.utility x / (1 - P.discount)| ≤ P.valueBound) :
    |P.utility x| ≤ (1 - P.discount) * P.valueBound := by
  have hβ1 : 0 < 1 - P.discount := sub_pos.2 P.discount_lt_one
  rw [abs_div, abs_of_pos hβ1, div_le_iff₀ hβ1] at hx
  linarith

theorem abs_contOf_le (w : (P.toModel c hc hcy).State →ᵇ ℝ)
    (hw : ∀ s, |w s| ≤ P.valueBound) (s : (P.toModel c hc hcy).State) (a' : ℝ) :
    |(P.toModel c hc hcy).contOf z₀ w s a'| ≤ P.valueBound := by
  calc |(P.toModel c hc hcy).contOf z₀ w s a'|
      ≤ ∑ ze : Z × E, |(P.toModel c hc hcy).shockProb z₀ ze (s, a')
          * w ((P.toModel c hc hcy).stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ze : Z × E, (P.toModel c hc hcy).shockProb z₀ ze (s, a') * P.valueBound := by
        refine Finset.sum_le_sum fun ze _ => ?_
        have hp := (P.toModel c hc hcy).shockProb_nonneg' z₀ ze (s, a')
        rw [abs_mul, abs_of_nonneg hp]
        exact mul_le_mul_of_nonneg_left (hw _) hp
    _ = P.valueBound := by rw [← Finset.sum_mul, (P.toModel c hc hcy).shockProb_sum z₀, one_mul]

/-- **The Bellman operator preserves the bound `valueBound`.** -/
theorem abs_bellman_le (w : (P.toModel c hc hcy).State →ᵇ ℝ)
    (hw : ∀ s, |w s| ≤ P.valueBound) (s : (P.toModel c hc hcy).State) :
    |((P.toModel c hc hcy).household z₀ K).bellman w s| ≤ P.valueBound := by
  have hβ0 : 0 ≤ P.discount := P.discount_pos.le
  have hβ1 : 0 < 1 - P.discount := sub_pos.2 P.discount_lt_one
  have hy := P.incomeFloor_pos
  have hlo := P.abs_utility_le_of (x := P.incomeFloor) (le_max_left _ _)
  have hhi := P.abs_utility_le_of (x := P.topCons) (le_max_right _ _)
  rw [abs_le]
  constructor
  · have h0 : (0 : ℝ) ∈ ((P.toModel c hc hcy).household z₀ K).feasible s :=
      ⟨le_rfl, (P.toModel c hc hcy).maxSaving_nonneg z₀ K s⟩
    have hle := (P.toModel c hc hcy).le_bellman_contOf z₀ K w h0
    rw [sub_zero] at hle
    have hcash := P.incomeFloor_le_cash hc hcy z₀ K s
    have hu : P.utility P.incomeFloor ≤ P.utility ((P.toModel c hc hcy).cash z₀ K s) :=
      P.monotoneOn_utility hy (hy.trans_le hcash) hcash
    have hcont := (abs_le.1 (P.abs_contOf_le hc hcy z₀ w hw s 0)).1
    have := mul_le_mul_of_nonneg_left hcont hβ0
    have hMu : (P.toModel c hc hcy).utility = P.utility := rfl
    have hMd : (P.toModel c hc hcy).discount = P.discount := rfl
    rw [hMu, hMd] at hle
    nlinarith [(abs_le.1 hlo).1]
  · change ((P.toModel c hc hcy).household z₀ K).bellmanFn w s ≤ _
    refine ((P.toModel c hc hcy).household z₀ K).bellmanFn_le w fun a ha => ?_
    rw [(P.toModel c hc hcy).objective_eq_contOf z₀ K w ha]
    have hc0 : c ≤ (P.toModel c hc hcy).cash z₀ K s - a :=
      le_sub_comm.1 (ha.2.trans (min_le_right _ _))
    have hu : P.utility ((P.toModel c hc hcy).cash z₀ K s - a) ≤ P.utility P.topCons :=
      P.monotoneOn_utility (hc.trans_le hc0) (hy.trans_le (le_max_left _ _))
        ((sub_le_self _ ha.1).trans (P.cash_le_topCons hc hcy z₀ K s))
    have hcont := (abs_le.1 (P.abs_contOf_le hc hcy z₀ w hw s a)).2
    have := mul_le_mul_of_nonneg_left hcont hβ0
    change P.utility _ + P.discount * _ ≤ _
    nlinarith [(abs_le.1 hhi).2]

/-- **Every Bellman iterate from `0` is bounded by `valueBound`.** -/
theorem abs_iterate_le (n : ℕ) (s : (P.toModel c hc hcy).State) :
    |(((P.toModel c hc hcy).household z₀ K).bellman^[n] 0) s| ≤ P.valueBound := by
  induction n generalizing s with
  | zero => simpa using P.valueBound_nonneg
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact P.abs_bellman_le hc hcy z₀ K _ ih s

/-- The continuation's slope bound away from zero savings, against any bounded continuation with
concave slices. -/
theorem contOf_sub_le (w : (P.toModel c hc hcy).State →ᵇ ℝ) (hw : ∀ s, |w s| ≤ P.valueBound)
    (hwc : (P.toModel c hc hcy).ConcaveSlices w) (s : (P.toModel c hc hcy).State) {x y : ℝ}
    (hx : P.incomeFloor / 2 ≤ x) (hxy : x < y) (hy : y ≤ P.assetCap) :
    (P.toModel c hc hcy).contOf z₀ w s y - (P.toModel c hc hcy).contOf z₀ w s x
      ≤ P.slopeConst * (y - x) := by
  have hyf := P.incomeFloor_pos
  have hx0 : 0 < x := by linarith
  have hslope := ((P.toModel c hc hcy).concaveOn_contOf z₀ hwc s).slope_anti_adjacent
    (mem_Icc.2 ⟨le_rfl, P.assetCap_pos.le⟩) (mem_Icc.2 ⟨by linarith, hy⟩) hx0 hxy
  have hb1 := abs_le.mp (P.abs_contOf_le hc hcy z₀ w hw s x)
  have hb2 := abs_le.mp (P.abs_contOf_le hc hcy z₀ w hw s 0)
  have hhalf : P.slopeConst * (P.incomeFloor / 2) = 2 * P.valueBound := by
    rw [slopeConst]
    field_simp
    ring
  have hbig : (P.toModel c hc hcy).contOf z₀ w s x - (P.toModel c hc hcy).contOf z₀ w s 0
      ≤ P.slopeConst * x := by
    have hstep : P.slopeConst * (P.incomeFloor / 2) ≤ P.slopeConst * x :=
      mul_le_mul_of_nonneg_left hx P.slopeConst_nonneg
    linarith [hb1.2, hb2.1]
  rw [sub_zero, div_le_div_iff₀ (by linarith) hx0] at hslope
  have hprod : ((P.toModel c hc hcy).contOf z₀ w s y - (P.toModel c hc hcy).contOf z₀ w s x) * x
      ≤ (P.slopeConst * x) * (y - x) := by
    nlinarith [hslope, hbig, (show (0 : ℝ) < y - x by linarith)]
  nlinarith [hprod, hx0]

/-- **Consumption against any bounded continuation with concave slices is at least
`floorLevel`.** -/
theorem floorLevel_le_consumptionOf (w : (P.toModel c hc hcy).State →ᵇ ℝ)
    (hw : ∀ s, |w s| ≤ P.valueBound) (hwc : (P.toModel c hc hcy).ConcaveSlices w)
    (s : (P.toModel c hc hcy).State) :
    P.floorLevel ≤ (P.toModel c hc hcy).consumptionOf z₀ K w s := by
  have hMu : (P.toModel c hc hcy).utility = P.utility := rfl
  have hMd : (P.toModel c hc hcy).discount = P.discount := rfl
  have hyf := P.incomeFloor_pos
  have hβ : 0 ≤ P.discount := P.discount_pos.le
  by_contra hlt
  rw [not_le] at hlt
  set fl := P.floorLevel with hfl
  set p := (P.toModel c hc hcy).policyOf z₀ K w s with hpdef
  set cash := (P.toModel c hc hcy).cash z₀ K s with hcash
  have hcons : (P.toModel c hc hcy).consumptionOf z₀ K w s = cash - p := rfl
  rw [hcons] at hlt
  have hfδ : fl ≤ P.inadaRadius := min_le_left _ _
  have hf4 : fl ≤ P.incomeFloor / 4 := min_le_right _ _
  have hpm := (P.toModel c hc hcy).policyOf_mem z₀ K w s
  have hcons' : c ≤ cash - p := le_sub_comm.1 (hpm.2.trans (min_le_right _ _))
  have hcashy : P.incomeFloor ≤ cash := P.incomeFloor_le_cash hc hcy z₀ K s
  have hpA : p ≤ P.assetCap := hpm.2.trans (min_le_left _ _)
  set h := fl - (cash - p) with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  have hlow : P.incomeFloor / 2 ≤ p - h := by rw [hh]; linarith
  have hfeas : p - h ∈ ((P.toModel c hc hcy).household z₀ K).feasible s :=
    ⟨by linarith, (by linarith : p - h ≤ p).trans hpm.2⟩
  have hdev := (P.toModel c hc hcy).le_bellman_contOf z₀ K w hfeas
  have hopt := (P.toModel c hc hcy).bellman_eq_contOf z₀ K w s
  rw [hopt, hcons] at hdev
  have hcfl : cash - (p - h) = fl := by rw [hh]; ring
  rw [hcfl, hMu, hMd] at hdev
  have hslope := P.contOf_sub_le hc hcy z₀ w hw hwc s hlow (by linarith) hpA
  rw [show p - (p - h) = h by ring] at hslope
  have hscaled := mul_le_mul_of_nonneg_left hslope hβ
  have hmarg := P.inadaRadius_spec (mem_Ioi.2 (hc.trans_le hcons')) (by linarith) hfδ
  have he : fl - (cash - p) = h := by rw [hh]
  rw [he] at hmarg
  nlinarith [P.slopeConst_nonneg]

/-- **The floor is slack along every Bellman iterate**, when it is below `floorLevel`. -/
theorem slackOf_iterate (hcf : c < P.floorLevel) (n : ℕ) :
    (P.toModel c hc hcy).SlackOf z₀ K
      ((((P.toModel c hc hcy).household z₀ K).bellman)^[n] 0) := fun s =>
  hcf.trans_le (P.floorLevel_le_consumptionOf hc hcy z₀ K _ (P.abs_iterate_le hc hcy z₀ K n)
    ((P.toModel c hc hcy).concaveSlices_iterate z₀ K n) s)

/-! ### The complementarity economy -/

/-- The gross return of the complementarity economy: rising linearly from `Rlo` to `Rhi` as
aggregate capital rises from `0` to the asset cap. -/
noncomputable def compReturn (Rlo Rhi cap : ℝ) (K : ℝ) : ℝ :=
  Rlo + (Rhi - Rlo) * (projIcc (0 : ℝ) 1 zero_le_one (K / cap) : ℝ)

theorem compReturn_mem {Rlo Rhi cap : ℝ} (hle : Rlo ≤ Rhi) (K : ℝ) :
    compReturn Rlo Rhi cap K ∈ Icc Rlo Rhi := by
  have ht := (projIcc (0 : ℝ) 1 zero_le_one (K / cap)).2
  constructor
  · have := mul_nonneg (sub_nonneg.2 hle) ht.1
    simp only [compReturn]
    linarith
  · have := mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.2 hle)
    simp only [compReturn]
    linarith

theorem compReturn_mono {Rlo Rhi cap : ℝ} (hle : Rlo ≤ Rhi) (hcap : 0 < cap) {K K' : ℝ}
    (hK : K ≤ K') : compReturn Rlo Rhi cap K ≤ compReturn Rlo Rhi cap K' := by
  have h := monotone_projIcc (zero_le_one (α := ℝ)) (div_le_div_of_nonneg_right hK hcap.le)
  have h' : (projIcc (0 : ℝ) 1 zero_le_one (K / cap) : ℝ)
      ≤ (projIcc (0 : ℝ) 1 zero_le_one (K' / cap) : ℝ) := h
  simp only [compReturn]
  nlinarith [mul_le_mul_of_nonneg_left h' (sub_nonneg.2 hle)]

theorem continuous_compReturn (Rlo Rhi cap : ℝ) : Continuous (compReturn Rlo Rhi cap) :=
  continuous_const.add (continuous_const.mul
    (continuous_subtype_val.comp (continuous_projIcc.comp (continuous_id.div_const _))))

/-- **A Krusell–Smith economy with complementarity**: log utility, a constant wage `w̄`, and a
gross return rising in aggregate capital from `Rlo` to `Rhi`. -/
noncomputable def compEconomy (V : KSEnvironment Z E) {w Rlo Rhi : ℝ} (hw : 0 < w)
    (hlo : 0 < Rlo) (hle : Rlo ≤ Rhi) : KSInada Z E where
  aggProb := V.aggProb
  aggProb_nonneg := V.aggProb_nonneg
  aggProb_sum := V.aggProb_sum
  idioProb := V.idioProb
  idioProb_nonneg := V.idioProb_nonneg
  idioProb_sum := V.idioProb_sum
  efficiency := V.efficiency
  efficiency_nonneg e := V.effLo_pos.le.trans (V.effLo_le e)
  assetCap := V.assetCap
  assetCap_pos := V.assetCap_pos
  discount := V.discount
  discount_pos := V.discount_pos
  discount_lt_one := V.discount_lt_one
  grossReturn _ K _ := compReturn Rlo Rhi V.assetCap K
  continuous_grossReturn _ := (continuous_compReturn _ _ _).comp continuous_fst
  grossReturn_nonneg _ K _ := hlo.le.trans (compReturn_mem hle K).1
  returnBound := Rhi
  grossReturn_le _ K _ := (compReturn_mem hle K).2
  wage _ _ _ := w
  continuous_wage _ := continuous_const
  wage_nonneg _ _ _ := hw.le
  wageBound := w
  wage_le _ _ _ := le_rfl
  incomeFloor := w * V.effLo
  incomeFloor_pos := mul_pos hw V.effLo_pos
  borrowLimit := 0
  borrowLimit_nonneg := le_rfl
  incomeFloor_le _ _ _ e := by
    rw [mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left (V.effLo_le e) hw.le
  utility := crraUtility 1
  continuousOn_utility := continuousOn_crraUtility 1
  strictConcaveOn_utility := strictConcaveOn_crraUtility one_pos
  monotoneOn_utility := monotoneOn_crraUtility 1
  marginalInada := marginalInada_crraUtility one_pos

variable (V : KSEnvironment Z E) {w Rlo Rhi : ℝ} (hw : 0 < w) (hlo : 0 < Rlo) (hle : Rlo ≤ Rhi)

/-- Log marginal utility `c ↦ c^{-1}` in the floored complementarity economy. -/
noncomputable def compSmoothUtility : (compEconomy V hw hlo hle).floored.SmoothUtility where
  du c := c ^ (-1 : ℝ)
  hasDerivAt _ hc := hasDerivAt_crraUtility 1 ((compEconomy V hw hlo hle).floor_pos.trans hc)
  continuousOn c hc :=
    (Real.continuousAt_rpow_const c (-1)
      (Or.inl ((compEconomy V hw hlo hle).floor_pos.trans hc).ne')).continuousWithinAt

/-- **A recursive equilibrium on the minimal state, without uniqueness, in an economy with
complementarity.** With log utility, a constant wage, a gross return rising in aggregate capital
within `[Rlo, Rhi] ⊂ (0, 1)`, and an asset cap with `Rhi · cap + w̄ Σ e < cap`, the greatest
sequential equilibrium is a consistent selection: a recursive equilibrium on `(z, μ)` exists. -/
theorem compEconomy_exists_consistentSelection
    (hbig : Rhi * V.assetCap + w * ∑ e, V.efficiency e < V.assetCap) :
    Nonempty (compEconomy V hw hlo hle).floored.ConsistentSelection := by
  set P := compEconomy V hw hlo hle
  refine KSModel.exists_consistentSelection_of_complementarity (compSmoothUtility V hw hlo hle)
    one_pos le_rfl (fun _ _ => by simp [compSmoothUtility]) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ hK => compReturn_mono hle V.assetCap_pos hK) rfl (fun z m₀ K h => ?_)
    (fun z m₀ K n => P.slackOf_iterate P.floor_pos P.floor_le_incomeFloor z _
      P.floor_lt_floorLevel n) (fun z m₀ K n s => KSModel.policyOf_lt_assetCap z _ ?_ _ s)
  · exact hlo.trans_le (compReturn_mem hle _).1
  · have hf := P.floor_pos
    change Rhi * V.assetCap + w * ∑ e, V.efficiency e - P.floor < V.assetCap
    linarith

/-! ### A concrete instance -/

/-- Two aggregate shocks and two idiosyncratic states, each i.i.d. with probability one half;
efficiencies `1/2` and `1`; asset cap `10`; discount `9/10`. -/
noncomputable def exampleEnv : KSEnvironment Bool Bool where
  aggProb _ _ := 1 / 2
  aggProb_nonneg _ _ := by norm_num
  aggProb_sum _ := by simp
  idioProb _ _ _ _ := 1 / 2
  idioProb_nonneg _ _ _ _ := by norm_num
  idioProb_sum _ _ _ := by simp
  efficiency e := if e then 1 else 1 / 2
  effLo := 1 / 2
  effHi := 1
  effLo_pos := by norm_num
  effLo_le e := by cases e <;> norm_num
  le_effHi e := by cases e <;> norm_num
  assetCap := 10
  assetCap_pos := by norm_num
  discount := 9 / 10
  discount_pos := by norm_num
  discount_lt_one := by norm_num

/-- **The class is not empty**: with wage `1` and a gross return rising from `1/2` to `3/4` with
aggregate capital, the example economy has a recursive equilibrium on the minimal state. -/
theorem example_exists_consistentSelection :
    Nonempty (compEconomy exampleEnv (w := 1) (Rlo := 1 / 2) (Rhi := 3 / 4) one_pos
      (by norm_num) (by norm_num)).floored.ConsistentSelection :=
  compEconomy_exists_consistentSelection exampleEnv one_pos (by norm_num) (by norm_num) (by
    change (3 / 4 : ℝ) * 10 + 1 * ∑ e : Bool, (if e then (1 : ℝ) else 1 / 2) < 10
    simp
    norm_num)

end KSInada

end KrusellSmith

end LeanEconomics
