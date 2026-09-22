/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.Retirement

/-!
# Means-tested pensions and the non-monotonicity of the policy

A pension is **means-tested** when the amount paid falls with the recipient's assets. It is
widely argued that this makes the household's policy function non-monotone. This file settles
the claim, and finds that it is true for a precise reason, and false for the reason usually
given.

## Three results

**Monotonicity in cash on hand is never lost.** For any continuation whatever — concave or not,
continuous or not, produced by a means test or by anything else — optimal saving rises with cash
on hand (`isOptimalSaving_mono`). The proof is Topkis: the only structure used is strict
concavity of period utility, which makes `(m, a') ↦ u(m - a')` have strictly increasing
differences. So a non-concave value function, which a means test certainly produces, cannot by
itself make saving fall with wealth. The usual informal argument is wrong.

**Consumption is not monotone.** What a non-concave continuation does produce is a jump: at the
wealth level where the household switches from keeping the pension to giving it up, saving jumps
up, and since the jump in saving exceeds the increase in wealth, consumption jumps *down*. The
witness is a two-period retiree with log utility, unit gross return, and a pension of one
withdrawn entirely above assets of one (`exists_consumption_decrease`): at cash on hand `6` the
household saves `1` and consumes `5`; at cash on hand `8` it saves `4` and consumes `4`. Both
optima are exact and verified, and the saving of `1` and `4` is increasing, as the first result
requires.

**Saving falls with assets when the test is on current assets.** The pension of a retiree is
assessed each period on the assets then held, so cash on hand is `m(a) = R a + p(a)` and the
means test enters it directly. A gentle taper is harmless: if the pension falls by `τ` per unit
of assets with `τ < R`, cash on hand is still strictly increasing (`cash_strictMono_tapered`)
and saving is still monotone in assets. But a cliff reverses it (`cash_lt_cash_of_cliff`), and
then a household with more assets saves strictly less: at assets `1` it saves `1/2`, at assets
`3/2` it saves `1/4` (`exists_saving_decrease_in_assets`). This is the genuine non-monotonicity,
and it lives in the budget, not in the value function.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace OLG

/-! ### Pension schedules -/

/-- A lump-sum pension: the same amount whatever the recipient holds. -/
def lumpSum (p : ℝ) : ℝ → ℝ := fun _ => p

/-- A **tapered** pension: withdrawn at rate `τ` per unit of assets above `cap`, never negative. -/
noncomputable def tapered (p τ cap : ℝ) : ℝ → ℝ := fun a => max 0 (p - τ * max 0 (a - cap))

/-- A **cliff**: the pension is withdrawn entirely above `cap`. -/
noncomputable def cliff (p cap : ℝ) : ℝ → ℝ := fun a => if a ≤ cap then p else 0

/-- Cash on hand of a household holding `a` at gross return `R` with pension schedule `pen`. -/
def cash (R : ℝ) (pen : ℝ → ℝ) (a : ℝ) : ℝ := R * a + pen a

@[simp] theorem cash_lumpSum (R p a : ℝ) : cash R (lumpSum p) a = R * a + p := rfl

theorem cliff_of_le {p cap a : ℝ} (h : a ≤ cap) : cliff p cap a = p := by simp [cliff, h]

theorem cliff_of_gt {p cap a : ℝ} (h : cap < a) : cliff p cap a = 0 := by
  simp [cliff, not_le.2 h]

/-- **A lump-sum pension leaves cash on hand increasing.** -/
theorem cash_strictMono_lumpSum {R p : ℝ} (hR : 0 < R) : StrictMono (cash R (lumpSum p)) := by
  intro a b hab
  simp only [cash_lumpSum]
  have := mul_lt_mul_of_pos_left hab hR
  linarith

/-- One-sided Lipschitz bound for the positive part. -/
theorem max_zero_sub_le {u v : ℝ} (h : v ≤ u) : max 0 u - max 0 v ≤ u - v := by
  rcases le_or_gt u 0 with hu | hu
  · have h1 : max 0 u = 0 := max_eq_left hu
    have h2 : (0 : ℝ) ≤ max 0 v := le_max_left _ _
    linarith
  · have h1 : max 0 u = u := max_eq_right hu.le
    have h2 : v ≤ max 0 v := le_max_right _ _
    linarith

/-- **A taper gentler than the return leaves cash on hand increasing.** The pension falls by at
most `τ` per unit of assets, so cash on hand rises by at least `R - τ`. -/
theorem cash_strictMono_tapered {R p τ cap : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ < R) :
    StrictMono (cash R (tapered p τ cap)) := by
  intro a b hab
  simp only [cash, tapered]
  set sa : ℝ := max 0 (a - cap) with hsa
  set sb : ℝ := max 0 (b - cap) with hsb
  have hs : sa ≤ sb := max_le_max le_rfl (by linarith)
  have hsb' : sb - sa ≤ b - a := by
    rcases le_or_gt (b - cap) 0 with hb | hb
    · have h1 : sb = 0 := max_eq_left hb
      have h2 : sa = 0 := max_eq_left (by linarith)
      rw [h1, h2]; linarith
    · have h1 : sb = b - cap := max_eq_right hb.le
      have h2 : sa ≥ a - cap := le_max_right _ _
      rw [h1]; linarith
  have hpen : max 0 (p - τ * sa) - max 0 (p - τ * sb) ≤ τ * (b - a) := by
    have hle : p - τ * sb ≤ p - τ * sa := by nlinarith [mul_le_mul_of_nonneg_left hs hτ0]
    have := max_zero_sub_le hle
    nlinarith [mul_le_mul_of_nonneg_left hsb' hτ0]
  have hRab : R * a + (R - τ) * (b - a) ≤ R * b := by nlinarith
  nlinarith [hpen, hab]

/-- **A cliff reverses it**: just above the threshold, a household with more assets has less to
spend. -/
theorem cash_lt_cash_of_cliff {R p cap a b : ℝ} (hac : a ≤ cap) (hcb : cap < b)
    (hgap : R * (b - a) < p) : cash R (cliff p cap) b < cash R (cliff p cap) a := by
  simp only [cash, cliff_of_le hac, cliff_of_gt hcb]
  linarith

/-! ### One step of the household's problem -/

/-- `x` is an optimal saving choice for a household with cash on hand `m`, period utility `u`
and continuation value `W`. Feasibility is `x ∈ [0, m)`, so consumption is positive. -/
def IsOptimalSaving (u W : ℝ → ℝ) (m x : ℝ) : Prop :=
  x ∈ Ico 0 m ∧ ∀ b ∈ Ico (0 : ℝ) m, u (m - b) + W b ≤ u (m - x) + W x

/-- **Topkis: optimal saving rises with cash on hand, whatever the continuation.** Only strict
concavity of period utility is used; the continuation `W` is arbitrary, so a value function made
non-concave by a means test cannot make saving fall with cash on hand. -/
theorem isOptimalSaving_mono {u W : ℝ → ℝ} (hu : StrictConcaveOn ℝ (Ioi (0 : ℝ)) u)
    {m₁ m₂ x₁ x₂ : ℝ} (hm : m₁ < m₂)
    (h₁ : IsOptimalSaving u W m₁ x₁) (h₂ : IsOptimalSaving u W m₂ x₂) : x₁ ≤ x₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨hx₁0, hx₁m⟩, hopt₁⟩ := h₁
  obtain ⟨⟨hx₂0, hx₂m⟩, hopt₂⟩ := h₂
  have e₁ := hopt₁ x₂ ⟨hx₂0, by linarith⟩
  have e₂ := hopt₂ x₁ ⟨hx₁0, by linarith⟩
  have hp0 : (0 : ℝ) < m₁ - x₁ := by linarith
  have hq0 : (0 : ℝ) < m₂ - x₂ := by linarith
  have hpq : m₁ - x₁ < m₂ - x₂ := by linarith
  have hlow : m₁ - x₁ < m₁ - x₂ := by linarith
  have hhigh : m₁ - x₂ < m₂ - x₂ := by linarith
  have hd0 : (0 : ℝ) < (m₂ - x₂) - (m₁ - x₁) := by linarith
  set lam : ℝ := ((m₂ - x₂) - (m₁ - x₂)) / ((m₂ - x₂) - (m₁ - x₁)) with hlam
  set mu : ℝ := ((m₁ - x₂) - (m₁ - x₁)) / ((m₂ - x₂) - (m₁ - x₁)) with hmu
  have hlam0 : 0 < lam := div_pos (by linarith) hd0
  have hmu0 : 0 < mu := div_pos (by linarith) hd0
  have hdne : (m₂ - x₂) - (m₁ - x₁) ≠ 0 := hd0.ne'
  have hsum : lam + mu = 1 := by
    have hadd : ((m₂ - x₂) - (m₁ - x₂)) + ((m₁ - x₂) - (m₁ - x₁))
        = (m₂ - x₂) - (m₁ - x₁) := by ring
    rw [hlam, hmu, ← add_div, hadd, div_self hdne]
  have hcomb1 : lam * (m₁ - x₁) + mu * (m₂ - x₂) = m₁ - x₂ := by
    rw [hlam, hmu, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdne]
    ring
  have hcomb2 : mu * (m₁ - x₁) + lam * (m₂ - x₂) = m₂ - x₁ := by
    rw [hlam, hmu, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdne]
    ring
  have hne : m₁ - x₁ ≠ m₂ - x₂ := ne_of_lt hpq
  have k1 := hu.2 (mem_Ioi.2 hp0) (mem_Ioi.2 hq0) hne hlam0 hmu0 hsum
  have k2 := hu.2 (mem_Ioi.2 hp0) (mem_Ioi.2 hq0) hne hmu0 hlam0 (by linarith)
  simp only [smul_eq_mul, hcomb1, hcomb2] at k1 k2
  have hid : lam * u (m₁ - x₁) + mu * u (m₂ - x₂) + (mu * u (m₁ - x₁) + lam * u (m₂ - x₂))
      = u (m₁ - x₁) + u (m₂ - x₂) := by
    linear_combination (u (m₁ - x₁) + u (m₂ - x₂)) * hsum
  linarith [e₁, e₂, k1, k2, hid]

/-- **Saving is monotone in assets whenever cash on hand is.** -/
theorem isOptimalSaving_mono_assets {u W : ℝ → ℝ} (hu : StrictConcaveOn ℝ (Ioi (0 : ℝ)) u)
    {R : ℝ} {pen : ℝ → ℝ} {a₁ a₂ x₁ x₂ : ℝ} (hcash : cash R pen a₁ < cash R pen a₂)
    (h₁ : IsOptimalSaving u W (cash R pen a₁) x₁)
    (h₂ : IsOptimalSaving u W (cash R pen a₂) x₂) : x₁ ≤ x₂ :=
  isOptimalSaving_mono hu hcash h₁ h₂

/-! ### The witnesses -/

theorem log_add_log_le {A B C D : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (h : A * B ≤ C * D) : Real.log A + Real.log B ≤ Real.log C + Real.log D := by
  rw [← Real.log_mul hA.ne' hB.ne', ← Real.log_mul hC.ne' hD.ne']
  exact Real.log_le_log (by positivity) h

/-- Next period's cash on hand in the example: a unit gross return and a pension of one
withdrawn entirely above assets of one. -/
noncomputable def exCash : ℝ → ℝ := cash 1 (cliff 1 1)

theorem exCash_of_le {x : ℝ} (h : x ≤ 1) : exCash x = x + 1 := by
  simp only [exCash, cash, cliff_of_le h]; ring

theorem exCash_of_gt {x : ℝ} (h : 1 < x) : exCash x = x := by
  simp only [exCash, cash, cliff_of_gt h]; ring

theorem exCash_pos {x : ℝ} (hx : 0 ≤ x) : 0 < exCash x := by
  rcases le_or_gt x 1 with h | h
  · rw [exCash_of_le h]; linarith
  · rw [exCash_of_gt h]; linarith

/-- The continuation value of the two-period example: log utility over next period's cash on
hand, which the means test makes non-concave at the threshold. -/
noncomputable def exW : ℝ → ℝ := fun x => Real.log (exCash x)

/-- **At cash on hand `6` the household keeps the pension**: it saves exactly `1`, the largest
amount that leaves the pension intact, and consumes `5`. -/
theorem isOptimalSaving_six : IsOptimalSaving Real.log exW 6 1 := by
  refine ⟨⟨by norm_num, by norm_num⟩, fun b hb => ?_⟩
  obtain ⟨hb0, hbm⟩ := hb
  simp only [exW]
  have h1 : exCash 1 = 2 := by rw [exCash_of_le le_rfl]; norm_num
  refine log_add_log_le (by linarith) (exCash_pos hb0) (by norm_num) (by rw [h1]; norm_num) ?_
  rw [h1]
  rcases le_or_gt b 1 with h | h
  · rw [exCash_of_le h]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - b) (by linarith : (0:ℝ) ≤ 4 - b)]
  · rw [exCash_of_gt h]
    nlinarith [sq_nonneg (b - 3)]

/-- **At cash on hand `8` the household gives the pension up**: it saves `4` and consumes `4`. -/
theorem isOptimalSaving_eight : IsOptimalSaving Real.log exW 8 4 := by
  refine ⟨⟨by norm_num, by norm_num⟩, fun b hb => ?_⟩
  obtain ⟨hb0, hbm⟩ := hb
  simp only [exW]
  have h1 : exCash 4 = 4 := by rw [exCash_of_gt (by norm_num)]
  refine log_add_log_le (by linarith) (exCash_pos hb0) (by norm_num) (by rw [h1]; norm_num) ?_
  rw [h1]
  rcases le_or_gt b 1 with h | h
  · rw [exCash_of_le h]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - b) (by linarith : (0:ℝ) ≤ 6 - b)]
  · rw [exCash_of_gt h]
    nlinarith [sq_nonneg (b - 4)]

/-- **Consumption falls when wealth rises.** With a means-tested pension there are two levels of
cash on hand, the second larger, at which the household's optimal consumption is strictly
smaller: it gives up the pension, saves the proceeds, and eats less today. Saving still rises,
as `isOptimalSaving_mono` says it must. -/
theorem exists_consumption_decrease :
    ∃ (W : ℝ → ℝ) (m₁ m₂ x₁ x₂ : ℝ), m₁ < m₂
      ∧ IsOptimalSaving Real.log W m₁ x₁ ∧ IsOptimalSaving Real.log W m₂ x₂
      ∧ m₂ - x₂ < m₁ - x₁ ∧ x₁ < x₂ :=
  ⟨exW, 6, 8, 1, 4, by norm_num, isOptimalSaving_six, isOptimalSaving_eight, by norm_num,
    by norm_num⟩

/-! ### The test on current assets -/

/-- The continuation of the second example: next period the pension is a lump sum, so the
continuation is concave and nothing is hidden in it. -/
noncomputable def exW' : ℝ → ℝ := fun x => Real.log (x + 1)

/-- With cash on hand `2` the household saves `1/2`. -/
theorem isOptimalSaving_two : IsOptimalSaving Real.log exW' 2 (1 / 2) := by
  refine ⟨⟨by norm_num, by norm_num⟩, fun b hb => ?_⟩
  obtain ⟨hb0, hbm⟩ := hb
  simp only [exW']
  refine log_add_log_le (by linarith) (by linarith) (by norm_num) (by norm_num) ?_
  nlinarith [sq_nonneg (2 * b - 1)]

/-- With cash on hand `3/2` the household saves only `1/4`. -/
theorem isOptimalSaving_threeHalves : IsOptimalSaving Real.log exW' (3 / 2) (1 / 4) := by
  refine ⟨⟨by norm_num, by norm_num⟩, fun b hb => ?_⟩
  obtain ⟨hb0, hbm⟩ := hb
  simp only [exW']
  refine log_add_log_le (by linarith) (by linarith) (by norm_num) (by norm_num) ?_
  nlinarith [sq_nonneg (4 * b - 1)]

/-- **The saving policy falls with assets.** When the means test is assessed on the assets the
household currently holds, cash on hand itself falls as assets cross the threshold, and with it
the household's saving: at assets `1` it saves `1/2`, at assets `3/2` only `1/4`. This is the
non-monotonicity of the policy function, and its source is the budget constraint, not the shape
of the value function: the continuation here is concave. -/
theorem exists_saving_decrease_in_assets :
    ∃ (W : ℝ → ℝ) (a₁ a₂ x₁ x₂ : ℝ), a₁ < a₂
      ∧ cash 1 (cliff 1 1) a₂ < cash 1 (cliff 1 1) a₁
      ∧ IsOptimalSaving Real.log W (cash 1 (cliff 1 1) a₁) x₁
      ∧ IsOptimalSaving Real.log W (cash 1 (cliff 1 1) a₂) x₂
      ∧ x₂ < x₁ := by
  have h₁ : cash 1 (cliff 1 1) 1 = 2 := by
    simp only [cash, cliff_of_le le_rfl]; norm_num
  have h₂ : cash 1 (cliff (1 : ℝ) 1) (3 / 2) = 3 / 2 := by
    simp only [cash, cliff_of_gt (by norm_num : (1 : ℝ) < 3 / 2)]; norm_num
  refine ⟨exW', 1, 3 / 2, 1 / 2, 1 / 4, by norm_num, by rw [h₁, h₂]; norm_num, ?_, ?_,
    by norm_num⟩
  · rw [h₁]; exact isOptimalSaving_two
  · rw [h₂]; exact isOptimalSaving_threeHalves

end OLG

/-! ### The same statement in the `(a, z)` state space

The household's state is assets `a` and the income shock `z`. In that language the positive
result reads: **next period's assets rise with this period's assets, at each `z`**, and it needs
no concavity of the continuation value at all. The repository already has this
(`policyOf_mono`), but with concave slices of the continuation as a hypothesis, which a
means-tested pension destroys. The Topkis argument removes the hypothesis: only strict concavity
of period utility is used, and the continuation cancels between the two optimality inequalities.

The dividing line is therefore exactly whether cash on hand rises with assets. It does whenever
the pension does not fall faster than the gross return, and the policy is then monotone in assets
for every continuation; it does not under a cliff or a taper steeper than the gross return, and
then the policy is not monotone, as `exists_saving_decrease_in_assets` shows. -/

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **Next period's assets rise with this period's assets, whatever the continuation.** No
concavity of `v` is assumed: the continuation cancels, and the only structure used is strict
concavity of period utility. This is `policyOf_mono` with its hypothesis removed, at the cost of
requiring the two asset levels to be distinct. -/
theorem policyOf_mono_of_lt {v : (ℝ × Z) →ᵇ ℝ} {a a' : ℝ} {z : Z}
    (ha : a ∈ Icc assetFloor assetCap) (ha' : a' ∈ Icc assetFloor assetCap) (hlt : a < a') :
    P.policyOf v (a, z) ≤ P.policyOf v (a', z) := by
  by_contra hcon
  rw [not_le] at hcon
  -- cash on hand rises strictly
  have hres : P.resources (a, z) < P.resources (a', z) := by
    simp only [resources, max_eq_right ha.1, max_eq_right ha'.1]
    have := mul_lt_mul_of_pos_left hlt P.interest_gt_neg_one
    linarith
  -- both choices are feasible at both states
  have hys : P.policyOf v (a, z) ∈ P.toExtended.feasible (a, z) := P.policyOf_mem v _
  have hys' : P.policyOf v (a, z) ∈ P.toExtended.feasible (a', z) :=
    P.feasible_mono hlt.le hys
  have hy's' : P.policyOf v (a', z) ∈ P.toExtended.feasible (a', z) := P.policyOf_mem v _
  have hy's : P.policyOf v (a', z) ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq] at hys ⊢
    rw [P.feasible_eq] at hy's'
    exact ⟨hy's'.1, le_trans hcon.le hys.2⟩
  -- the four consumption levels, all in the domain of utility
  have hcsy : P.consumption (a, z) (P.policyOf v (a, z)) ∈ P.dom :=
    P.consumption_policyOf_mem_dom v ha
  have hcs'y' : P.consumption (a', z) (P.policyOf v (a', z)) ∈ P.dom :=
    P.consumption_policyOf_mem_dom v ha'
  have hcsy' : P.consumption (a, z) (P.policyOf v (a', z)) ∈ P.dom := by
    refine P.dom_upward hcsy ?_
    simp only [consumption]; linarith
  have hcs'y : P.consumption (a', z) (P.policyOf v (a, z)) ∈ P.dom := by
    refine P.dom_upward hcsy ?_
    simp only [consumption]; linarith
  set p : ℝ := P.resources (a, z) - P.policyOf v (a, z) with hp
  set q : ℝ := P.resources (a', z) - P.policyOf v (a', z) with hq
  set r : ℝ := P.resources (a, z) - P.policyOf v (a', z) with hr
  have hpr : p < r := by rw [hp, hr]; linarith
  have hrq : r < q := by rw [hr, hq]; linarith
  have hdne : q - p ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  have hd0 : 0 < q - p := by linarith
  set lam : ℝ := (q - r) / (q - p) with hlam
  set mu : ℝ := (r - p) / (q - p) with hmu
  have hlam0 : 0 < lam := div_pos (by linarith) hd0
  have hmu0 : 0 < mu := div_pos (by linarith) hd0
  have hsum : lam + mu = 1 := by
    have hadd : (q - r) + (r - p) = q - p := by ring
    rw [hlam, hmu, ← add_div, hadd, div_self hdne]
  have hcomb1 : lam * p + mu * q = r := by
    rw [hlam, hmu, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdne]; ring
  have hcomb2 : mu * p + lam * q = P.resources (a', z) - P.policyOf v (a, z) := by
    rw [hlam, hmu, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdne]
    rw [hp, hq, hr]; ring
  have hpq : p ≠ q := ne_of_lt (by linarith)
  have hpdom : p ∈ P.dom := by rw [hp]; exact hcsy
  have hqdom : q ∈ P.dom := by rw [hq]; exact hcs'y'
  have k1 := P.strictConcaveOn_u_dom.2 hpdom hqdom hpq hlam0 hmu0 hsum
  have k2 := P.strictConcaveOn_u_dom.2 hpdom hqdom hpq hmu0 hlam0 (by linarith)
  simp only [smul_eq_mul, hcomb1, hcomb2] at k1 k2
  -- the two optimality inequalities; the continuation cancels
  have e₁ := P.objROf_le_of_mem v ha hy's hcsy'
  have e₂ := P.objROf_le_of_mem v ha' hys' hcs'y
  simp only [objROf, consumption, contOf] at e₁ e₂
  have hid : lam * P.u p + mu * P.u q + (mu * P.u p + lam * P.u q) = P.u p + P.u q := by
    linear_combination (P.u p + P.u q) * hsum
  rw [← hp, ← hr] at e₁
  rw [← hq] at e₂
  linarith [e₁, e₂, k1, k2, hid]

/-- **Consumption is different.** The same argument does not carry over to consumption, and it
cannot: `exists_consumption_decrease` is a household whose consumption falls as cash on hand
rises. Monotone consumption genuinely needs concavity of the continuation, which is what
`consumptionFnOf_mono` assumes; monotone saving does not. -/
theorem consumptionFnOf_eq_sub (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (a : ℝ) :
    P.consumptionFnOf v z a = P.resources (a, z) - P.policyOf v (a, z) := rfl

end IncomeFluctuation

end LeanEconomics
