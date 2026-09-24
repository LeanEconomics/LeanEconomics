/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.Equilibrium

/-!
# The deterministic life cycle

Drop earnings risk, by making income the same in every state, and assume the household is interior
at every age: it saves something and stops short of the artefactual cap. Then the finite-horizon
sandwich closes. Consumption is exactly

  `c_k(a, z) = κ_k (m + H_k)`   (`stageConsumption_eq_of_interior`),

the permanent-income rule with the finite-horizon propensity, and saving is exactly
`(1 - κ_k)(y + Ra) - κ_k H_k`. Everything the stochastic model can only bound is available in
closed form, and Light's Theorem 1 becomes algebra.

At logarithmic utility that algebra is immediate. The propensity `κ_k` is then a ratio of sums of
powers of `β` alone and does not depend on the interest rate at all (`stageMPC_one_eq_of_rate`),
while human wealth falls as the rate rises. Saving therefore rises with the rate at every age and
every asset level, with no condition (`stagePolicy_mono_det_log`), so aggregate capital rises with
it and the stationary equilibrium is unique (`olgEquilibriumRate_unique_det_log`).

Above logarithmic utility the propensity does move with the rate, and the comparative static turns
into the duration comparison the write-up reports: consumption at zero assets falls with the rate
exactly when the duration of income exceeds `(1 - 1/γ)` times the duration of consumption, which
at Aiyagari's calibration holds up to a risk aversion of about `4.33`. Here that criterion is
carried as an explicit hypothesis, `detSlack`, and `stagePolicy_mono_det` shows it is all that is
needed: positive assets only help.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### Consumption in closed form -/

/-- Income does not depend on the state. -/
def ConstantIncome : Prop := ∀ z w : Z, P.income z = P.income w

theorem stageHumanWealth_const (hconst : P.ConstantIncome) (k : ℕ) (z w : Z) :
    P.stageHumanWealth k z = P.stageHumanWealth k w := by
  induction k generalizing z w with
  | zero => rfl
  | succ k ih =>
    rw [stageHumanWealth_succ, stageHumanWealth_succ]
    refine congrArg (fun y => y / (1 + P.interest)) ?_
    have hC : ∀ v : Z, P.income v + P.stageHumanWealth k v
        = P.income z + P.stageHumanWealth k z := fun v => by rw [hconst v z, ih v z]
    calc ∑ v, P.transitionMatrix z v * (P.income v + P.stageHumanWealth k v)
        = ∑ v, P.transitionMatrix z v * (P.income z + P.stageHumanWealth k z) :=
          Finset.sum_congr rfl fun v _ => by rw [hC v]
      _ = P.income z + P.stageHumanWealth k z := by
          rw [← Finset.sum_mul, P.transitionMatrix_sum z, one_mul]
      _ = ∑ v, P.transitionMatrix w v * (P.income v + P.stageHumanWealth k v) := by
          rw [Finset.sum_congr rfl fun v _ => by rw [hC v], ← Finset.sum_mul,
            P.transitionMatrix_sum w, one_mul]

/-- **The sandwich closes**: with income the same in every state and the household interior at
every age, consumption is exactly the permanent-income rule. -/
theorem stageConsumption_eq_of_interior {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) (hconst : P.ConstantIncome)
    (hslack : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      P.stagePolicy j (b, w) < P.maxSaving (b, w))
    (hpos : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z, 0 < P.stagePolicy (j + 1) (b, w))
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.stageConsumption k z a = P.stageMPC γ k * (P.resources (a, z) + P.stageHumanWealth k z) := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hT0 : 0 < P.patience γ := P.patience_pos' hγ0 hβ
  have hTneg : P.patience γ ^ (-γ) = ((P.discount : ℝ) * (1 + P.interest))⁻¹ := by
    rw [patience, ← Real.rpow_mul (by positivity),
      show (1 / γ) * (-γ) = -1 from by field_simp, Real.rpow_neg_one]
  induction k generalizing a z with
  | zero =>
    rw [P.stageConsumption_zero ha z]
    simp [stageMPC, stageHumanWealth]
  | succ k ih =>
    have hκ := P.stageMPC_pos hγ0 hβ k
    set A : ℝ := P.stagePolicy (k + 1) (a, z) with hA
    have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
    have hc0 : 0 < P.stageConsumption (k + 1) z a := P.stageConsumption_pos hd _ z ha
    -- the Euler equation holds with equality
    have hle := P.stage_euler_le hu hd k z ha (hslack (k + 1) a ha z)
    have hge := P.stage_euler_ge hu hd k z ha (hpos k a ha z)
      (fun z' => hslack k A hAmem z')
    have heq : (P.stageConsumption (k + 1) z a) ^ (-γ)
        = (P.discount : ℝ) * ((1 + P.interest) * ∑ z', P.transitionMatrix z z'
          * (P.stageConsumption k z' A) ^ (-γ)) := le_antisymm hge hle
    -- the induction hypothesis makes tomorrow's consumption the same in every state
    set X : ℝ := P.stageMPC γ k * (P.income z + (1 + P.interest) * A
      + P.stageHumanWealth k z) with hX
    have hXval : ∀ z', P.stageConsumption k z' A = X := by
      intro z'
      rw [ih z' hAmem, P.resources_eq_of_mem hAmem z', hconst z' z,
        P.stageHumanWealth_const hconst k z' z, hX]
    have hX0 : 0 < X := by
      have hp := P.stageConsumption_pos hd k (Classical.arbitrary Z) hAmem
      rwa [hXval (Classical.arbitrary Z)] at hp
    have hsum : ∑ z', P.transitionMatrix z z' * (P.stageConsumption k z' A) ^ (-γ)
        = X ^ (-γ) := by
      rw [Finset.sum_congr rfl fun z' _ => by rw [hXval z'], ← Finset.sum_mul,
        P.transitionMatrix_sum z, one_mul]
    rw [hsum] at heq
    -- invert the power: `Þ c = X`
    have hTc : P.patience γ * P.stageConsumption (k + 1) z a = X := by
      have hpow : (P.patience γ * P.stageConsumption (k + 1) z a) ^ (-γ) = X ^ (-γ) := by
        rw [Real.mul_rpow hT0.le hc0.le, hTneg, heq]
        field_simp
      have h1 : (0 : ℝ) < P.patience γ * P.stageConsumption (k + 1) z a := by positivity
      exact le_antisymm (le_of_rpow_neg_le hX0 h1 hγ0 (le_of_eq hpow.symm))
        (le_of_rpow_neg_le h1 hX0 hγ0 (le_of_eq hpow))
    -- and the budget identity closes it
    have hbud : P.stageConsumption (k + 1) z a = P.resources (a, z) - A := rfl
    have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a :=
      P.resources_eq_of_mem ha z
    have hH : P.stageHumanWealth (k + 1) z
        = (P.income z + P.stageHumanWealth k z) / (1 + P.interest) := by
      rw [stageHumanWealth_succ]
      refine congrArg (fun y => y / (1 + P.interest)) ?_
      rw [Finset.sum_congr rfl fun z' _ => by
        rw [hconst z' z, P.stageHumanWealth_const hconst k z' z], ← Finset.sum_mul,
        P.transitionMatrix_sum z, one_mul]
    have hAval : A = (P.income z + (1 + P.interest) * a) - P.stageConsumption (k + 1) z a := by
      rw [← hres, hbud]; ring
    rw [hX, hAval] at hTc
    rw [stageMPC_succ, hH, hres]
    have hden : 0 < P.patience γ + P.stageMPC γ k * (1 + P.interest) := by positivity
    field_simp
    nlinarith [hTc, hR, hT0, hκ]

/-- With income the same in every state, human wealth obeys the scalar recursion
`R H_{k+1} = y + H_k`. -/
theorem stageHumanWealth_succ_const (hconst : P.ConstantIncome) (k : ℕ) (z : Z) :
    P.stageHumanWealth (k + 1) z
      = (P.income z + P.stageHumanWealth k z) / (1 + P.interest) := by
  rw [stageHumanWealth_succ]
  refine congrArg (fun y => y / (1 + P.interest)) ?_
  rw [Finset.sum_congr rfl fun v _ => by
      rw [hconst v z, P.stageHumanWealth_const hconst k v z], ← Finset.sum_mul,
    P.transitionMatrix_sum z, one_mul]

/-! ### The comparative static -/

variable {r₁ r₂ : ℝ}

/-- **Human wealth falls as the rate rises.** -/
theorem stageHumanWealth_antitone_rate (hconst : P.ConstantIncome) (h₁ : P.RateOK r₁)
    (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂) (k : ℕ) (z : Z) :
    (P.withRate r₂ h₂).stageHumanWealth k z ≤ (P.withRate r₁ h₁).stageHumanWealth k z := by
  have hc₁ : (P.withRate r₁ h₁).ConstantIncome := hconst
  have hc₂ : (P.withRate r₂ h₂).ConstantIncome := hconst
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hy : 0 < P.income z := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z)
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have e₁ := (P.withRate r₁ h₁).stageHumanWealth_succ_const hc₁ k z
    have e₂ := (P.withRate r₂ h₂).stageHumanWealth_succ_const hc₂ k z
    have hn₁ : 0 ≤ (P.withRate r₁ h₁).stageHumanWealth k z :=
      (P.withRate r₁ h₁).stageHumanWealth_nonneg k z
    have hn₂ : 0 ≤ (P.withRate r₂ h₂).stageHumanWealth k z :=
      (P.withRate r₂ h₂).stageHumanWealth_nonneg k z
    rw [e₁, e₂]
    have hi₁ : (P.withRate r₁ h₁).income z = P.income z := rfl
    have hi₂ : (P.withRate r₂ h₂).income z = P.income z := rfl
    have hint₁ : (P.withRate r₁ h₁).interest = r₁ := rfl
    have hint₂ : (P.withRate r₂ h₂).interest = r₂ := rfl
    rw [hi₁, hi₂, hint₁, hint₂]
    rw [div_le_div_iff₀ hR₂ hR₁]
    nlinarith [ih, hn₁, hn₂, hy, hr]

/-- **At logarithmic utility the propensity does not depend on the rate.** With `γ = 1` the
patience factor is `βR`, and the `R` cancels out of the recursion. -/
theorem stageMPC_one_eq_of_rate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (k : ℕ) :
    (P.withRate r₁ h₁).stageMPC 1 k = (P.withRate r₂ h₂).stageMPC 1 k := by
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hp : ∀ (r : ℝ) (h : P.RateOK r),
      (P.withRate r h).patience 1 = (P.discount : ℝ) * (1 + r) := by
    intro r h
    rw [patience]
    norm_num
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [stageMPC_succ, stageMPC_succ, hp r₁ h₁, hp r₂ h₂, ih]
    have hint₁ : (P.withRate r₁ h₁).interest = r₁ := rfl
    have hint₂ : (P.withRate r₂ h₂).interest = r₂ := rfl
    rw [hint₁, hint₂]
    set κ : ℝ := (P.withRate r₂ h₂).stageMPC 1 k with hκ
    rw [show (P.discount : ℝ) * (1 + r₁) + κ * (1 + r₁)
        = ((P.discount : ℝ) + κ) * (1 + r₁) from by ring,
      show (P.discount : ℝ) * (1 + r₂) + κ * (1 + r₂)
        = ((P.discount : ℝ) + κ) * (1 + r₂) from by ring]
    rw [mul_div_mul_right _ _ hR₁.ne', mul_div_mul_right _ _ hR₂.ne']

/-- **Light's Theorem 1 in the deterministic life cycle at logarithmic utility.** Saving rises with
the interest rate at every age and every asset level, with no condition: the propensity is
rate-free and human wealth falls. -/
theorem stagePolicy_mono_det_log (hu : P.u = crraUtility 1) (hβ : 0 < (P.discount : ℝ))
    (hd : P.Unbounded) (hconst : P.ConstantIncome) (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    (hr : r₁ ≤ r₂)
    (hs₁ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate r₁ h₁).stagePolicy j (b, w) < (P.withRate r₁ h₁).maxSaving (b, w))
    (hp₁ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      0 < (P.withRate r₁ h₁).stagePolicy (j + 1) (b, w))
    (hs₂ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate r₂ h₂).stagePolicy j (b, w) < (P.withRate r₂ h₂).maxSaving (b, w))
    (hp₂ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      0 < (P.withRate r₂ h₂).stagePolicy (j + 1) (b, w))
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).stagePolicy k (a, z) ≤ (P.withRate r₂ h₂).stagePolicy k (a, z) := by
  have hc₁ := (P.withRate r₁ h₁).stageConsumption_eq_of_interior one_pos hu hβ hd hconst
    hs₁ hp₁ k z ha
  have hc₂ := (P.withRate r₂ h₂).stageConsumption_eq_of_interior one_pos hu hβ hd hconst
    hs₂ hp₂ k z ha
  have hres₁ := (P.withRate r₁ h₁).resources_eq_of_mem ha z
  have hres₂ := (P.withRate r₂ h₂).resources_eq_of_mem ha z
  have hb₁ : (P.withRate r₁ h₁).stageConsumption k z a
      = (P.withRate r₁ h₁).resources (a, z) - (P.withRate r₁ h₁).stagePolicy k (a, z) := rfl
  have hb₂ : (P.withRate r₂ h₂).stageConsumption k z a
      = (P.withRate r₂ h₂).resources (a, z) - (P.withRate r₂ h₂).stagePolicy k (a, z) := rfl
  have hκ := P.stageMPC_one_eq_of_rate h₁ h₂ k
  have hH := P.stageHumanWealth_antitone_rate hconst h₁ h₂ hr k z
  have hκ1 : (P.withRate r₂ h₂).stageMPC 1 k ≤ 1 :=
    (P.withRate r₂ h₂).stageMPC_le_one one_pos hβ k
  have hκ0 : 0 < (P.withRate r₂ h₂).stageMPC 1 k :=
    (P.withRate r₂ h₂).stageMPC_pos one_pos hβ k
  rw [hres₁] at hc₁ hb₁
  rw [hres₂] at hc₂ hb₂
  have hi₁ : (P.withRate r₁ h₁).income z = P.income z := rfl
  have hi₂ : (P.withRate r₂ h₂).income z = P.income z := rfl
  have hint₁ : (P.withRate r₁ h₁).interest = r₁ := rfl
  have hint₂ : (P.withRate r₂ h₂).interest = r₂ := rfl
  rw [hi₁, hint₁] at hc₁ hb₁
  rw [hi₂, hint₂] at hc₂ hb₂
  rw [hκ] at hc₁
  set κ : ℝ := (P.withRate r₂ h₂).stageMPC 1 k with hκdef
  set H₁ : ℝ := (P.withRate r₁ h₁).stageHumanWealth k z with hH₁
  set H₂ : ℝ := (P.withRate r₂ h₂).stageHumanWealth k z with hH₂
  have e₁ : (P.withRate r₁ h₁).stagePolicy k (a, z)
      = (P.income z + (1 + r₁) * a) - κ * (P.income z + (1 + r₁) * a + H₁) := by
    linarith [hb₁, hc₁]
  have e₂ : (P.withRate r₂ h₂).stagePolicy k (a, z)
      = (P.income z + (1 + r₂) * a) - κ * (P.income z + (1 + r₂) * a + H₂) := by
    linarith [hb₂, hc₂]
  have hd1 : (0 : ℝ) ≤ (1 - κ) * ((r₂ - r₁) * a) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) ha.1)
  have hd2 : (0 : ℝ) ≤ κ * (H₁ - H₂) := mul_nonneg hκ0.le (by linarith)
  have hgap : (P.withRate r₂ h₂).stagePolicy k (a, z)
      - (P.withRate r₁ h₁).stagePolicy k (a, z)
      = (1 - κ) * ((r₂ - r₁) * a) + κ * (H₁ - H₂) := by
    rw [e₁, e₂]; ring
  linarith [hgap, hd1, hd2]

/-- **Aggregate capital rises with the rate**, and hence the stationary equilibrium rate of the
deterministic life-cycle economy at logarithmic utility is unique. -/
theorem olgCapital_mono_det_log (hu : P.u = crraUtility 1) (hβ : 0 < (P.discount : ℝ))
    (hd : P.Unbounded) (hconst : P.ConstantIncome) (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    (hr : r₁ ≤ r₂)
    (hs₁ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate r₁ h₁).stagePolicy j (b, w) < (P.withRate r₁ h₁).maxSaving (b, w))
    (hp₁ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      0 < (P.withRate r₁ h₁).stagePolicy (j + 1) (b, w))
    (hs₂ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      (P.withRate r₂ h₂).stagePolicy j (b, w) < (P.withRate r₂ h₂).maxSaving (b, w))
    (hp₂ : ∀ j : ℕ, ∀ b ∈ Icc (0 : ℝ) assetCap, ∀ w : Z,
      0 < (P.withRate r₂ h₂).stagePolicy (j + 1) (b, w))
    (K : ℕ) {ν : Z → ℝ} (hν : ∀ z, 0 ≤ ν z) :
    (P.withRate r₁ h₁).olgCapital K ν ≤ (P.withRate r₂ h₂).olgCapital K ν :=
  (P.withRate r₁ h₁).olgCapital_le_of_stagePolicy_le (Q := P.withRate r₂ h₂) rfl
    (fun j t ht => P.stagePolicy_mono_det_log hu hβ hd hconst h₁ h₂ hr hs₁ hp₁ hs₂ hp₂ j t.2 ht)
    K hν

end IncomeFluctuation

end LeanEconomics
