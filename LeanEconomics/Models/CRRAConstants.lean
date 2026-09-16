/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.BoundedIncomeFluctuation
import LeanEconomics.Models.NaturalAssetBound

/-!
# The quantitative constants for CES

The equilibrium programme runs on four explicit constants: a lower bound on the secant slope of
`u` (which drives the corner condition and the precautionary gain), an upper bound on it (which
gives the value function its Lipschitz constant), a bound on saving (which gives the decline
condition), and the calibration arithmetic that checks they fit together. All four were computed
for `Real.log`, and `hu : P.u = Real.log` propagated through the whole chain.

This file does them for CES. The pleasant surprise is that most of it is not a duplication:
`hasDerivAt_crraUtility` already covers every `γ > 0`, log included, so the CES lemmas here
GENERALISE their log counterparts rather than sitting beside them. `crra_marginal_bound` at
`γ = 1` is `log_marginal_bound`, and `crraSlopeBound` at `γ = 1` is `2 log 2 / m`.

## The one place the shape changes

For log, marginal utility is `1/c`, so the slope bound available at resources `R` is `1/R` — it
DEGRADES as resources grow, and the multiplicative bound `c ≥ R / (1 + 2G)` is the right output.
For CES with `γ < 1` marginal utility is `c^{-γ}`, and on a capped problem `c ≤ maxConsumption`,
so there is a single slope `maxConsumption ^ (-γ)` that works everywhere. That turns the same
deviation argument into a UNIFORM bound on saving — `policy s ≤ K` for one constant `K` — which
is a cleaner route to the decline condition than the multiplicative bound, and the natural asset
bound falls straight out of it.

`policy_le_of_marginal_bound` is stated for any `u` with a uniform slope bound, so log gets the
uniform version too, with `m = 1 / maxConsumption`.
-/

open scoped NNReal
open Set Filter Topology

namespace LeanEconomics

/-! ### Secant slopes of CRRA, bounded below -/

/-- **The secant slope of CRRA on `(0, R]` is at least `R ^ (-γ)`.** This is
`log_marginal_bound` for every `γ > 0` at once: at `γ = 1` the bound `R ^ (-1)` is `1 / R`. -/
theorem crra_marginal_bound {γ R : ℝ} (hγ : 0 < γ) {c d : ℝ} (hd : 0 < d) (hdc : d ≤ c)
    (hcR : c ≤ R) : R ^ (-γ) * (c - d) ≤ crraUtility γ c - crraUtility γ d := by
  rcases eq_or_lt_of_le hdc with rfl | hlt
  · simp
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (crraUtility γ)
    (fun x => x ^ (-γ)) hlt
    ((continuousOn_crraUtility γ).mono fun x hx => lt_of_lt_of_le hd hx.1)
    (fun x hx => hasDerivAt_crraUtility γ (hd.trans hx.1))
  have hmono : R ^ (-γ) ≤ ξ ^ (-γ) :=
    rpow_neg_antitone hγ (hd.trans hξ.1) (hξ.2.le.trans hcR)
  rw [hslope, le_div_iff₀ (by linarith)] at hmono
  linarith

/-- **The bound reaches `d = 0` when `γ < 1`.** Utility is finite there, so the statement makes
sense, and the first unit of consumption is worth at least as much as any later one. This is the
case log cannot have. -/
theorem crra_marginal_bound_zero {γ R : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {c : ℝ}
    (hc : 0 < c) (hcR : c ≤ R) :
    R ^ (-γ) * (c - 0) ≤ crraUtility γ c - crraUtility γ 0 := by
  have hM : R ^ (-γ) ≤ c ^ (-γ) := rpow_neg_antitone hγ0 hc hcR
  have hmul : c ^ (-γ) * c = c ^ (1 - γ) := by
    have hadd := Real.rpow_add hc (-γ) 1
    rw [Real.rpow_one] at hadd
    rw [← hadd, show -γ + 1 = 1 - γ from by ring]
  have h1 : R ^ (-γ) * c ≤ c ^ (1 - γ) := by
    rw [← hmul]; exact mul_le_mul_of_nonneg_right hM hc.le
  have h2 : (0 : ℝ) ≤ c ^ (1 - γ) := (Real.rpow_pos_of_pos hc _).le
  rw [crraUtility_zero hγ1, crraUtility_of_ne (show γ ≠ 1 by linarith), sub_zero, sub_zero,
    le_div_iff₀ (show (0 : ℝ) < 1 - γ by linarith)]
  nlinarith

/-- The slope bound on all of `Ici 0`, which is the domain CES with `γ < 1` uses. -/
theorem crra_marginal_bound_Ici {γ R : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {c d : ℝ}
    (hd : d ∈ Ici (0 : ℝ)) (hdc : d ≤ c) (hcR : c ≤ R) :
    R ^ (-γ) * (c - d) ≤ crraUtility γ c - crraUtility γ d := by
  rcases (mem_Ici.mp hd).lt_or_eq with hdpos | hd0
  · exact crra_marginal_bound hγ0 hdpos hdc hcR
  rcases eq_or_lt_of_le (hd0 ▸ hdc : (0 : ℝ) ≤ c) with hc0 | hcpos
  · rw [← hd0, ← hc0]; simp
  · rw [← hd0]; exact crra_marginal_bound_zero hγ0 hγ1 hcpos hcR

/-- **The gain from `d` extra consumption, bounded below.** Taking `R = c + d` in
`crra_marginal_bound` gives the CES form of `log_sub_log_ge`. -/
theorem crra_sub_ge {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (c + d) ^ (-γ) * d ≤ crraUtility γ (c + d) - crraUtility γ c := by
  have := crra_marginal_bound_Ici hγ0 hγ1 (mem_Ici.mpr hc) (le_add_of_nonneg_right hd)
    (le_refl (c + d))
  simpa using this

/-! ### Secant slopes of CRRA, bounded above -/

/-- The closed form of `slopeBound (crraUtility γ)` at the income floor. At `γ = 1` this is
`2 log 2 / m`, which is `log_slopeBoundU`. -/
noncomputable def crraSlopeBound (γ m : ℝ) : ℝ :=
  2 * m ^ (-γ) * (1 - ((2 : ℝ) ^ (1 - γ))⁻¹) / (1 - γ)

theorem slopeBound_crraUtility {γ m : ℝ} (hγ : γ ≠ 1) (hm : 0 < m) :
    slopeBound (crraUtility γ) m = crraSlopeBound γ m := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 - γ) := Real.rpow_pos_of_pos (by norm_num) _
  have hhalf : (m / 2) ^ (1 - γ) = m ^ (1 - γ) / (2 : ℝ) ^ (1 - γ) :=
    Real.div_rpow hm.le (by norm_num : (0 : ℝ) ≤ 2) (1 - γ)
  have hexp : m ^ (1 - γ) = m * m ^ (-γ) := by
    have h := Real.rpow_add hm 1 (-γ)
    rw [Real.rpow_one, show (1 : ℝ) + -γ = 1 - γ from by ring] at h
    exact h
  have hγ' : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  simp only [slopeBound, crraSlopeBound, crraUtility_of_ne hγ, hhalf, hexp]
  field_simp

theorem crraSlopeBound_nonneg {γ m : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hm : 0 < m) :
    0 ≤ crraSlopeBound γ m := by
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 - γ) :=
    Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
  have hinv : ((2 : ℝ) ^ (1 - γ))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by linarith)]; exact h2
  have hmp : (0 : ℝ) < m ^ (-γ) := Real.rpow_pos_of_pos hm _
  refine div_nonneg ?_ (by linarith)
  have : (0 : ℝ) ≤ 1 - ((2 : ℝ) ^ (1 - γ))⁻¹ := by linarith
  positivity

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z assetCap)

/-- **A uniform bound on saving from a uniform marginal bound.** Deviate to half the optimal
saving: the extra consumption is worth at least `m` per unit, and concavity of the continuation
caps what the forgone saving could have repaid at `deviationGap`, whatever the state.

The log development could not use this, because for log the available `m` at resources `R` is
`1 / R`, which is not uniform. It is stated generically anyway — log gets the version with
`m = 1 / maxConsumption`, which is uniform after all, just weaker than what the multiplicative
argument extracts. For CES with `γ < 1` the uniform `m = maxConsumption ^ (-γ)` is all there is,
and it is enough. -/
theorem policy_le_of_marginal_bound {m : ℝ} (hm : 0 < m)
    (hmarg : ∀ c d : ℝ, d ∈ P.dom → d ≤ c → c ≤ P.maxConsumption → m * (c - d) ≤ P.u c - P.u d)
    (hpc : P.PositiveConsumption) {a : ℝ} (ha : a ∈ Icc 0 assetCap) (z : Z) :
    P.policy (a, z) ≤ 2 * P.deviationGap / m := by
  have hG : 0 ≤ P.deviationGap := P.deviationGap_nonneg
  set b : ℝ := P.policy (a, z) with hbdef
  set c : ℝ := P.consumptionFn z a with hcdef
  rcases eq_or_lt_of_le (P.policy_mem_region (a, z)).1 with hzero | hbpos
  · rw [← hbdef] at hzero
    rw [← hzero]
    positivity
  rw [← hbdef] at hbpos
  have hcpos : 0 < c := P.consumptionFn_pos hpc ha z
  have hres : P.resources (a, z) = c + b := by simp only [hcdef, consumptionFn, consumption]; ring
  -- the deviation: save half as much
  have hhalf0 : 0 < b / 2 := by linarith
  have hhalfb : b / 2 < b := by linarith
  have hbreg : b ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region _
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) assetCap := ⟨le_rfl, P.assetCap_nonneg⟩
  have hfeas : b / 2 ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq]
    exact ⟨hhalf0.le, by linarith [(P.policy_mem (a, z)).2]⟩
  have hcons : P.consumption (a, z) (b / 2) = c + b / 2 := by
    simp only [consumption]; rw [hres]; ring
  have hdev : 0 < P.consumption (a, z) (b / 2) := by rw [hcons]; linarith
  have hopt := P.objR_le_of_mem ha hfeas (P.mem_dom_of_pos hdev)
  simp only [objR, hcons] at hopt
  rw [show P.consumption (a, z) (P.policy (a, z)) = c from rfl,
    show P.policy (a, z) = b from rfl] at hopt
  -- concavity of the continuation caps the forgone repayment
  have hslope := (P.concaveOn_cont z).slope_anti_adjacent hmem0 hbreg hhalf0 hhalfb
  have hb1 := abs_le.mp (P.abs_cont_le z (b / 2))
  have hb0 := abs_le.mp (P.abs_cont_le z 0)
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hloss : P.cont z b - P.cont z (b / 2) ≤ 2 * ‖P.toExtended.valueFunction‖ := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)] at hslope
    nlinarith [hslope, hb1.1, hb0.2]
  have hscaled : (P.discount : ℝ) * (P.cont z b - P.cont z (b / 2)) ≤ P.deviationGap := by
    simp only [deviationGap]
    nlinarith [hloss, hβ]
  -- the marginal gain from the extra consumption
  have hcmax : c + b / 2 ≤ P.maxConsumption := by
    have := P.consumption_le_maxConsumption (s := (a, z)) ha (le_refl (0 : ℝ))
    simp only [consumption, sub_zero] at this
    rw [hres] at this
    linarith
  have hmg := hmarg (c + b / 2) c (P.mem_dom_of_pos hcpos) (by linarith) hcmax
  rw [show c + b / 2 - c = b / 2 from by ring] at hmg
  rw [le_div_iff₀ hm]
  nlinarith [hopt, hscaled, hmg]

/-- The Lipschitz constant of the value function under CES, mirroring `logLipschitz`. -/
noncomputable def crraLipschitz (γ : ℝ) : ℝ :=
  crraSlopeBound γ P.minIncome * (1 + P.interest) / (1 - P.discount * (1 + P.interest))

theorem crraLipschitz_nonneg {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hβR : P.discount * (1 + P.interest) < 1) : 0 ≤ P.crraLipschitz γ := by
  have hs := crraSlopeBound_nonneg hγ0 hγ1 P.minIncome_pos
  have hr := P.interest_gt_neg_one
  exact div_nonneg (by positivity) (by linarith)

/-- **The value function is Lipschitz with the explicit CES constant.** -/
theorem crra_valueFunction_lipschitz {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hu : P.u = crraUtility γ) (hβR : P.discount * (1 + P.interest) < 1) :
    ∀ z : Z, ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ y ∈ Icc (0 : ℝ) assetCap,
      |P.toExtended.valueFunction (x, z) - P.toExtended.valueFunction (y, z)|
        ≤ P.crraLipschitz γ * |x - y| := by
  refine P.valueFunction_lipschitz (P.crraLipschitz_nonneg hγ0 hγ1 hβR) (le_of_eq ?_)
  have hne : (1 : ℝ) - P.discount * (1 + P.interest) ≠ 0 := by linarith
  simp only [crraLipschitz, slopeBoundU, hu,
    slopeBound_crraUtility (show γ ≠ 1 by linarith) P.minIncome_pos]
  field_simp
  ring

/-- **The borrowing constraint binds where resources are small**, CES version. The threshold is
`resources ^ (-γ)` where the log version had `1 / resources`. -/
theorem crra_policy_eq_zero_of_resources {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hb : P.Bounded) (hu : P.u = crraUtility γ)
    (hβR : P.discount * (1 + P.interest) < 1) {s : ℝ × Z} (hs : s.1 ∈ Icc (0 : ℝ) assetCap)
    (hlt : P.discount * P.crraLipschitz γ < P.resources s ^ (-γ)) :
    P.policy s = 0 :=
  P.policy_eq_zero_of_corner_at (P.crra_valueFunction_lipschitz hγ0 hγ1 hu hβR) hs
    (fun c d hd hdc hc => by
      rw [hu]
      exact crra_marginal_bound_Ici hγ0 hγ1 (by rw [hb] at hd; exact hd) hdc hc)
    hlt

/-- **The CES saving bound in closed form.** Saving never exceeds `2 · deviationGap ·
maxConsumption ^ γ`, whatever the state. -/
theorem crra_policy_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : P.Bounded)
    (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumption) {a : ℝ} (ha : a ∈ Icc 0 assetCap)
    (z : Z) : P.policy (a, z) ≤ 2 * P.deviationGap * P.maxConsumption ^ γ := by
  have hmc := P.maxConsumption_pos
  have hm : (0 : ℝ) < P.maxConsumption ^ (-γ) := Real.rpow_pos_of_pos hmc _
  have hkey := P.policy_le_of_marginal_bound hm
    (fun c d hd hdc hc => by
      rw [hu]
      exact crra_marginal_bound_Ici hγ0 hγ1 (by rw [hb] at hd; exact hd) hdc hc)
    hpc ha z
  have hinv : P.maxConsumption ^ (-γ) = (P.maxConsumption ^ γ)⁻¹ := Real.rpow_neg hmc.le γ
  rw [hinv, div_eq_mul_inv, inv_inv] at hkey
  exact hkey

/-- **The natural asset bound for CES.** A uniform cap on saving is a decline condition outright:
above it, assets fall. No linear consumption bound and no `exp` in sight. -/
theorem crra_exists_decline {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : P.Bounded)
    (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumption) (z : Z) :
    ∃ ā : ℝ, ∀ a ∈ Icc (0 : ℝ) assetCap, ā < a → P.policy (a, z) < a :=
  ⟨2 * P.deviationGap * P.maxConsumption ^ γ, fun a ha hlt =>
    lt_of_le_of_lt (P.crra_policy_le hγ0 hγ1 hb hu hpc ha z) hlt⟩

/-- **The continuation's gain between two saving levels, CES version.** Where the log form carries
`log (1 + R·(y-x) / (income + R·x))`, this carries `(income + R·y) ^ (-γ) · R·(y-x)`: the extra
resources, valued at the marginal utility of the largest consumption they could buy. -/
theorem crra_cont_sub_ge_gen {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : P.Bounded)
    (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumption) (z z₀ : Z) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) assetCap) (hy : y ∈ Icc (0 : ℝ) assetCap) (hxy : x ≤ y) :
    P.transitionMatrix z z₀ * ((P.income z₀ + (1 + P.interest) * y) ^ (-γ)
        * ((1 + P.interest) * (y - x)))
      ≤ P.cont z y - P.cont z x := by
  have hRh : 0 ≤ (1 + P.interest) * (y - x) :=
    mul_nonneg P.interest_gt_neg_one.le (by linarith)
  have hsum : P.cont z y - P.cont z x = ∑ z' : Z, P.transitionMatrix z z' *
      (P.toExtended.valueFunction (y, z') - P.toExtended.valueFunction (x, z')) := by
    simp only [cont, ← Finset.sum_sub_distrib, ← mul_sub]
  have hterm : P.transitionMatrix z z₀ *
      (P.toExtended.valueFunction (y, z₀) - P.toExtended.valueFunction (x, z₀))
        ≤ P.cont z y - P.cont z x := by
    rw [hsum]
    refine Finset.single_le_sum (f := fun z' : Z => P.transitionMatrix z z' *
      (P.toExtended.valueFunction (y, z') - P.toExtended.valueFunction (x, z')))
      (fun z' _ => ?_) (Finset.mem_univ z₀)
    exact mul_nonneg (P.transitionMatrix_nonneg _ _)
      (by linarith [P.valueFunction_le_of_le hpc (z := z') hx hy hxy])
  have hc0 : 0 < P.consumption (x, z₀) (P.policy (x, z₀)) := P.consumption_policy_pos hpc hx
  have hresx : P.resources (x, z₀) = P.income z₀ + (1 + P.interest) * x := by
    simp only [resources, max_eq_right hx.1]
  have hcle : P.consumption (x, z₀) (P.policy (x, z₀))
      ≤ P.income z₀ + (1 + P.interest) * x := by
    simp only [consumption, hresx]
    linarith [(P.policy_mem_region (x, z₀)).1]
  have hgain := P.valueFunction_sub_ge hpc hx hy hxy z₀
  rw [hu] at hgain
  -- the marginal bound, at the largest consumption the richer state could reach
  have hbound : (P.income z₀ + (1 + P.interest) * y) ^ (-γ) * ((1 + P.interest) * (y - x))
      ≤ crraUtility γ (P.consumption (x, z₀) (P.policy (x, z₀)) + (1 + P.interest) * (y - x))
        - crraUtility γ (P.consumption (x, z₀) (P.policy (x, z₀))) := by
    have hR : P.consumption (x, z₀) (P.policy (x, z₀)) + (1 + P.interest) * (y - x)
        ≤ P.income z₀ + (1 + P.interest) * y := by nlinarith [hcle]
    have := crra_marginal_bound_Ici hγ0 hγ1 (mem_Ici.mpr hc0.le)
      (le_add_of_nonneg_right hRh) hR
    simpa using this
  exact le_trans (mul_le_mul_of_nonneg_left (le_trans hbound hgain)
    (P.transitionMatrix_nonneg z z₀)) hterm

/-- **The continuation's gain from zero, CES version.** -/
theorem crra_cont_sub_ge {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : P.Bounded)
    (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumption) (z z₀ : Z) {h : ℝ}
    (hh : h ∈ Icc (0 : ℝ) assetCap) :
    P.transitionMatrix z z₀ * ((P.income z₀ + (1 + P.interest) * h) ^ (-γ)
        * ((1 + P.interest) * h))
      ≤ P.cont z h - P.cont z 0 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) assetCap := ⟨le_rfl, P.assetCap_nonneg⟩
  have := P.crra_cont_sub_ge_gen hγ0 hγ1 hb hu hpc z z₀ h0 hh hh.1
  simpa using this

end IncomeFluctuation

end LeanEconomics
