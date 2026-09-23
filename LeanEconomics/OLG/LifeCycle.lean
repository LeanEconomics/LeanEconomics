/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.MinimalMPC
import LeanEconomics.Models.ConsumptionSandwich
import LeanEconomics.Models.IncomeFluctuationIterate
import LeanEconomics.Models.LargeBetaLight
import LeanEconomics.Analysis.PowerMean

/-!
# The life-cycle household

A household that lives `J` periods, faces the income-fluctuation problem of `IncomeFluctuation`
in each of them, and leaves nothing behind. With `k` periods still to come after today its
continuation value is the `k`-th Bellman iterate from zero,

  `stageValue k = bellman^[k] 0`,

so the household with `k` periods left chooses `stagePolicy k = policyOf (stageValue k)` and
consumes `stageConsumption k`. Age `j` of a `J`-period life is stage `k = J - 1 - j`. In the
last period (`k = 0`) the household consumes its whole cash on hand.

This is the finite-horizon problem with a FLAT age profile of earnings: the same income process
at every age. Everything the repository proves for `bellman v` with an arbitrary continuation
`v` applies stage by stage with no fixed point: the two Euler inequalities, uniqueness of the
action, Carroll–Kimball concavity, monotonicity in wealth. An age profile of earnings needs
income as a parameter of the Bellman step rather than a field, and is deferred.

## The finite-horizon sandwich

New here is the stage-dependent sandwich. Let `Þ = (βR)^{1/γ}` and define the finite-horizon
minimal propensities to consume by `κ₀ = 1`, `κ_{k+1} = κ_k R / (Þ + κ_k R)`, so that
`1/κ_k = ∑_{i ≤ k} (Þ/R)^i` — the consumption share of a household with `k` periods left and no
future income. Then at every stage

  `κ_k · m ≤ c_k(a, z) ≤ κ_k · (m + H_k(z))`   (`stageMPC_mul_le_stageConsumption`,
                                                `stageConsumption_le_stageHumanWealth`),

where `H_0 = 0` and `R H_{k+1}(z) = ∑_{z'} π(z,z') (y_{z'} + H_k(z'))` is the expected present
value of the next `k` incomes. Both bounds are proved by one Euler step each
(`crra_stageMPC_step`, `crra_stageUpper_step`), the lower from the Euler inequality above the
floor and the upper from the Euler inequality under the cap with Jensen for the negative power.
The finite-horizon propensities decrease in `k` towards the infinite-horizon `κ = 1 - Þ/R`
(`minMPC_le_stageMPC`): a household with less life left consumes a larger share of its cash.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### Stages -/

/-- The continuation value with `k` periods still to come: the `k`-th Bellman iterate from zero. -/
noncomputable def stageValue (k : ℕ) : (ℝ × Z) →ᵇ ℝ :=
  (P.toExtended.bellman)^[k] (0 : (ℝ × Z) →ᵇ ℝ)

/-- The saving of a household with `k` periods still to come. -/
noncomputable def stagePolicy (k : ℕ) (s : ℝ × Z) : ℝ := P.policyOf (P.stageValue k) s

/-- The consumption of a household with `k` periods still to come. -/
noncomputable def stageConsumption (k : ℕ) (z : Z) (a : ℝ) : ℝ :=
  P.consumptionFnOf (P.stageValue k) z a

theorem stageValue_zero : P.stageValue 0 = 0 := rfl

theorem stageValue_succ (k : ℕ) :
    P.stageValue (k + 1) = P.toExtended.bellman (P.stageValue k) :=
  Function.iterate_succ_apply' _ _ _

theorem stageConsumption_eq (k : ℕ) (z : Z) (a : ℝ) :
    P.stageConsumption k z a = P.resources (a, z) - P.stagePolicy k (a, z) := rfl

theorem stagePolicy_mem_region (k : ℕ) (s : ℝ × Z) : P.stagePolicy k s ∈ Icc (0 : ℝ) assetCap :=
  P.feasible_subset_region (P.policyOf_mem _ s)

/-- **In the last period the household saves nothing.** -/
theorem stagePolicy_zero {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.stagePolicy 0 (a, z) = 0 :=
  P.policyOf_zero (s := (a, z)) ha

/-- **In the last period the household consumes its cash on hand.** -/
theorem stageConsumption_zero {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.stageConsumption 0 z a = P.resources (a, z) := by
  rw [stageConsumption_eq, P.stagePolicy_zero ha z, sub_zero]

/-- Consumption is positive at every stage when marginal utility is unbounded at zero. -/
theorem stageConsumption_pos (hd : P.Unbounded) (k : ℕ) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) : 0 < P.stageConsumption k z a :=
  P.consumptionFnOf_pos hd _ ha

/-- The stage value has concave slices, so the stage policy is well behaved. -/
theorem concaveSlices_stageValue (k : ℕ) : ConcaveSlices 0 assetCap (P.stageValue k) :=
  P.concaveSlices_iterate_zero k

/-- Saving rises with wealth at every stage. -/
theorem stagePolicy_mono (k : ℕ) {a a' : ℝ} {z : Z} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (ha' : a' ∈ Icc (0 : ℝ) assetCap) (hle : a ≤ a') :
    P.stagePolicy k (a, z) ≤ P.stagePolicy k (a', z) :=
  P.policyOf_mono (P.concaveSlices_stageValue k) ha ha' hle

/-- Consumption rises with wealth at every stage. -/
theorem stageConsumption_mono (k : ℕ) {a a' : ℝ} {z : Z} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (ha' : a' ∈ Icc (0 : ℝ) assetCap) (hle : a ≤ a') :
    P.stageConsumption k z a ≤ P.stageConsumption k z a' :=
  P.consumptionFnOf_mono (P.concaveSlices_stageValue k) ha ha' hle

/-- **Carroll–Kimball at every stage**: consumption is concave in wealth. -/
theorem concaveOn_stageConsumption {γ : ℝ} (hpc : P.PositiveConsumptionAll) (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ)
    (hslack : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, P.stagePolicy k (a, z) < assetCap)
    (k : ℕ) (z : Z) : ConcaveOn ℝ (Icc (0 : ℝ) assetCap) (P.stageConsumption k z) :=
  P.concaveOn_consumptionFnOf_iterates_of_crra hpc hγ0 hβ hu hslack k z

/-! ### The Euler inequalities, stage by stage -/

/-- **Euler under the cap** at stage `k + 1`: `βR E[u'(c_k(a', z'))] ≤ u'(c_{k+1}(a, z))`. -/
theorem stage_euler_le {γ : ℝ} (hu : P.u = crraUtility γ) (hd : P.Unbounded) (k : ℕ) (z : Z)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hroom : P.stagePolicy (k + 1) (a, z) < P.maxSaving (a, z)) :
    (P.discount : ℝ) * ((1 + P.interest) * ∑ z', P.transitionMatrix z z'
        * (P.stageConsumption k z' (P.stagePolicy (k + 1) (a, z))) ^ (-γ))
      ≤ (P.stageConsumption (k + 1) z a) ^ (-γ) := by
  have hV : P.toExtended.bellman (P.stageValue k) = P.stageValue (k + 1) :=
    (P.stageValue_succ k).symm
  have hA : P.stagePolicy (k + 1) (a, z) ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
  have hc : 0 < P.stageConsumption (k + 1) z a := P.stageConsumption_pos hd _ z ha
  have hc' : ∀ z', 0 < P.stageConsumption k z' (P.stagePolicy (k + 1) (a, z)) :=
    fun z' => P.stageConsumption_pos hd _ z' hA
  refine P.euler_le (v := P.stageValue k) (z := z) (a := a) (A := P.stagePolicy (k + 1) (a, z))
    (du := (P.stageConsumption (k + 1) z a) ^ (-γ))
    (du' := fun z' => (P.stageConsumption k z' (P.stagePolicy (k + 1) (a, z))) ^ (-γ))
    ha (by rw [hV]; rfl) hroom (by rw [hV]; exact hc) ?_ hc' ?_
  · rw [hV, hu]; exact hasDerivAt_crraUtility γ hc
  · intro z'; rw [hu]; exact hasDerivAt_crraUtility γ (hc' z')

/-- **Euler above the floor** at stage `k + 1`, at a state where the household saves:
`u'(c_{k+1}(a, z)) ≤ βR E[u'(c_k(a', z'))]`. -/
theorem stage_euler_ge {γ : ℝ} (hu : P.u = crraUtility γ) (hd : P.Unbounded) (k : ℕ) (z : Z)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (hint : 0 < P.stagePolicy (k + 1) (a, z))
    (hslack : ∀ z', P.stagePolicy k (P.stagePolicy (k + 1) (a, z), z')
      < P.maxSaving (P.stagePolicy (k + 1) (a, z), z')) :
    (P.stageConsumption (k + 1) z a) ^ (-γ)
      ≤ (P.discount : ℝ) * ((1 + P.interest) * ∑ z', P.transitionMatrix z z'
        * (P.stageConsumption k z' (P.stagePolicy (k + 1) (a, z))) ^ (-γ)) := by
  have hV : P.toExtended.bellman (P.stageValue k) = P.stageValue (k + 1) :=
    (P.stageValue_succ k).symm
  have hA : P.stagePolicy (k + 1) (a, z) ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
  have hc : 0 < P.stageConsumption (k + 1) z a := P.stageConsumption_pos hd _ z ha
  have hc' : ∀ z', 0 < P.stageConsumption k z' (P.stagePolicy (k + 1) (a, z)) :=
    fun z' => P.stageConsumption_pos hd _ z' hA
  refine P.euler_ge (v := P.stageValue k) (z := z) (a := a) (A := P.stagePolicy (k + 1) (a, z))
    (du := (P.stageConsumption (k + 1) z a) ^ (-γ))
    (du' := fun z' => (P.stageConsumption k z' (P.stagePolicy (k + 1) (a, z))) ^ (-γ))
    ha (by rw [hV]; rfl) hint hslack (by rw [hV]; exact hc) ?_ hc' ?_
  · rw [hV, hu]; exact hasDerivAt_crraUtility γ hc
  · intro z'; rw [hu]; exact hasDerivAt_crraUtility γ (hc' z')

/-! ### The finite-horizon propensities to consume -/

/-- The patience factor `Þ = (βR)^{1/γ}`. -/
noncomputable def patience (γ : ℝ) : ℝ := ((P.discount : ℝ) * (1 + P.interest)) ^ (1 / γ)

/-- **The finite-horizon minimal propensity to consume**: `κ₀ = 1`,
`κ_{k+1} = κ_k R / (Þ + κ_k R)`, so that `1/κ_k = ∑_{i ≤ k} (Þ/R)^i`. -/
noncomputable def stageMPC (γ : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => stageMPC γ k * (1 + P.interest) / (P.patience γ + stageMPC γ k * (1 + P.interest))

theorem stageMPC_succ (γ : ℝ) (k : ℕ) : P.stageMPC γ (k + 1)
    = P.stageMPC γ k * (1 + P.interest) / (P.patience γ + P.stageMPC γ k * (1 + P.interest)) :=
  rfl

/-- **Finite-horizon human wealth**: `H₀ = 0`, `R H_{k+1}(z) = ∑ π(z,z') (y_{z'} + H_k(z'))`. -/
noncomputable def stageHumanWealth : ℕ → Z → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun z =>
      (∑ z', P.transitionMatrix z z' * (P.income z' + stageHumanWealth k z')) / (1 + P.interest)

theorem stageHumanWealth_succ (k : ℕ) (z : Z) : P.stageHumanWealth (k + 1) z
    = (∑ z', P.transitionMatrix z z' * (P.income z' + P.stageHumanWealth k z'))
      / (1 + P.interest) :=
  rfl

theorem patience_pos' {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) : 0 < P.patience γ :=
  patience_pos (P := P) hγ0 hβ

theorem stageMPC_pos {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    0 < P.stageMPC γ k := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hT := P.patience_pos' hγ0 hβ
  induction k with
  | zero => exact one_pos
  | succ k ih => rw [stageMPC_succ]; exact div_pos (mul_pos ih hR) (add_pos hT (mul_pos ih hR))

theorem stageMPC_le_one {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    P.stageMPC γ k ≤ 1 := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hT := P.patience_pos' hγ0 hβ
  cases k with
  | zero => exact le_rfl
  | succ k =>
    have hκ := P.stageMPC_pos hγ0 hβ k
    rw [stageMPC_succ, div_le_one (add_pos hT (mul_pos hκ hR))]
    linarith

/-- **Less life, larger share**: the finite-horizon propensity is at least the infinite-horizon
`κ = 1 - Þ/R`. -/
theorem minMPC_le_stageMPC {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    P.minMPC γ ≤ P.stageMPC γ k := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hT := P.patience_pos' hγ0 hβ
  have hkey : (1 - P.minMPC γ) * (1 + P.interest) = P.patience γ := one_sub_minMPC_mul (P := P)
  induction k with
  | zero => exact minMPC_le_one (P := P) hγ0 hβ
  | succ k ih =>
    have hκ := P.stageMPC_pos hγ0 hβ k
    have hκ1 : P.minMPC γ ≤ 1 := minMPC_le_one (P := P) hγ0 hβ
    rw [stageMPC_succ, le_div_iff₀ (add_pos hT (mul_pos hκ hR))]
    -- `κ (Þ + κ_k R) ≤ κ_k R` because `κ_k R - κ Þ - κ κ_k R = R (1 - κ)(κ_k - κ) ≥ 0`
    have h2 : P.minMPC γ * P.patience γ
        = P.minMPC γ * ((1 - P.minMPC γ) * (1 + P.interest)) := by rw [hkey]
    nlinarith [h2, mul_nonneg (mul_nonneg (sub_nonneg.2 ih) (sub_nonneg.2 hκ1)) hR.le]

theorem stageHumanWealth_nonneg (k : ℕ) (z : Z) : 0 ≤ P.stageHumanWealth k z := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  induction k generalizing z with
  | zero => exact le_rfl
  | succ k ih =>
    rw [stageHumanWealth_succ]
    refine div_nonneg (Finset.sum_nonneg fun z' _ => mul_nonneg (P.transitionMatrix_nonneg z z')
      (add_nonneg ?_ (ih z'))) hR.le
    exact (lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z')).le

/-! ### One Euler step of each bound -/

/-- **The lower step.** If consumption against `v` is at least `κ m`, then consumption against
`bellman v` is at least `κ R / (Þ + κ R) · m`. -/
theorem crra_stageMPC_step {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) {v : (ℝ × Z) →ᵇ ℝ} {T : Set ℝ}
    (hposv : ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap, 0 < P.consumptionFnOf v z a)
    (hcapv : ∀ a ∈ T, ∀ z : Z, P.policyOf v (a, z) < assetCap)
    (hposW : ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    {κ : ℝ} (hκ : 0 < κ)
    (ih : ∀ z : Z, ∀ a ∈ T, κ * P.resources (a, z) ≤ P.consumptionFnOf v z a)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hmaps : P.policyOf (P.toExtended.bellman v) (a, z) ∈ T) :
    κ * (1 + P.interest) / (P.patience γ + κ * (1 + P.interest)) * P.resources (a, z)
      ≤ P.consumptionFnOf (P.toExtended.bellman v) z a := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  set T : ℝ := P.patience γ with hTdef
  have hT0 : 0 < T := P.patience_pos' hγ0 hβ
  have hTneg : T ^ (-γ) = ((P.discount : ℝ) * (1 + P.interest))⁻¹ := by
    rw [hTdef, patience, ← Real.rpow_mul hβR0.le,
      show (1 / γ) * (-γ) = -1 from by field_simp, Real.rpow_neg_one]
  have hden : 0 < T + κ * (1 + P.interest) := by positivity
  set W : (ℝ × Z) →ᵇ ℝ := P.toExtended.bellman v with hWdef
  set A : ℝ := P.policyOf W (a, z) with hAdef
  have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.feasible_subset_region (P.policyOf_mem W (a, z))
  set c : ℝ := P.consumptionFnOf W z a with hcdef
  have hcA : c = P.resources (a, z) - A := rfl
  have hc0 : 0 < c := hposW z a ha
  have hm0 : 0 ≤ P.resources (a, z) := (P.assetFloor_lt_resources (a, z)).le
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  rcases eq_or_lt_of_le hAmem.1 with hA0 | hA0
  · have hcm : c = P.resources (a, z) := by rw [hcA, ← hA0, sub_zero]
    rw [hcm]
    nlinarith [mul_nonneg hT0.le hm0]
  · have hslack : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z') := fun z' =>
      P.policyOf_lt_maxSaving_of_pos (hposv z' A hAmem) (hcapv A hmaps z')
    have hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A := fun z' => hposv z' A hAmem
    have hder : ∀ z' : Z, HasDerivAt P.u ((P.consumptionFnOf v z' A) ^ (-γ))
        (P.consumptionFnOf v z' A) := by
      intro z'; rw [hu]; exact hasDerivAt_crraUtility γ (hc' z')
    have heuler := P.euler_ge (v := v) (z := z) (a := a) (A := A) ha rfl hA0 hslack hc0
      (by rw [hu]; exact hasDerivAt_crraUtility γ hc0) hc' hder
    set X : ℝ := κ * ((1 + P.interest) * A) with hXdef
    have hX0 : 0 < X := by rw [hXdef]; positivity
    have hstep : ∀ z' : Z, X ≤ P.consumptionFnOf v z' A := by
      intro z'
      refine le_trans ?_ (ih z' A hmaps)
      have hres : P.resources (A, z') = P.income z' + (1 + P.interest) * A :=
        P.resources_eq_of_mem hAmem z'
      have hinc : 0 < P.income z' := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z')
      rw [hres, hXdef]
      nlinarith [hκ]
    have hsum : ∑ z' : Z, P.transitionMatrix z z' * (P.consumptionFnOf v z' A) ^ (-γ)
        ≤ X ^ (-γ) := by
      calc ∑ z' : Z, P.transitionMatrix z z' * (P.consumptionFnOf v z' A) ^ (-γ)
          ≤ ∑ z' : Z, P.transitionMatrix z z' * X ^ (-γ) :=
            Finset.sum_le_sum fun z' _ =>
              mul_le_mul_of_nonneg_left (rpow_neg_antitone hγ0 hX0 (hstep z'))
                (P.transitionMatrix_nonneg z z')
        _ = X ^ (-γ) := by rw [← Finset.sum_mul, P.transitionMatrix_sum z, one_mul]
    have hchain : c ^ (-γ) ≤ (P.discount : ℝ) * (1 + P.interest) * X ^ (-γ) := by
      have := le_trans heuler
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hR.le) hβ.le)
      linarith [this]
    have hTc : (T * c) ^ (-γ) ≤ X ^ (-γ) := by
      rw [Real.mul_rpow hT0.le hc0.le, hTneg, inv_mul_le_iff₀ hβR0]
      linarith [hchain]
    have hXTc : X ≤ T * c := le_of_rpow_neg_le (by positivity) hX0 hγ0 hTc
    rw [hXdef, hcA] at hXTc
    rw [hcA]
    nlinarith [hXTc, hR]

/-- **The upper step.** If consumption against `v` is at most `κ (m + H(z))`, then consumption
against `bellman v` is at most `κ R / (Þ + κ R) · (m + H'(z))` with
`R H'(z) = ∑ π(z,z') (y_{z'} + H(z'))`. -/
theorem crra_stageUpper_step {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) {v : (ℝ × Z) →ᵇ ℝ} {S T : Set ℝ}
    (hposv : ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap, 0 < P.consumptionFnOf v z a)
    (hposW : ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hcapW : ∀ a ∈ S, ∀ z : Z, P.policyOf (P.toExtended.bellman v) (a, z) < assetCap)
    {κ : ℝ} (hκ : 0 < κ) {H : Z → ℝ} (hH0 : ∀ z, 0 ≤ H z)
    (ih : ∀ z : Z, ∀ a ∈ T, P.consumptionFnOf v z a ≤ κ * (P.resources (a, z) + H z))
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (haS : a ∈ S)
    (hmaps : P.policyOf (P.toExtended.bellman v) (a, z) ∈ T) :
    P.consumptionFnOf (P.toExtended.bellman v) z a
      ≤ κ * (1 + P.interest) / (P.patience γ + κ * (1 + P.interest))
        * (P.resources (a, z)
          + (∑ z', P.transitionMatrix z z' * (P.income z' + H z')) / (1 + P.interest)) := by
  classical
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  set T : ℝ := P.patience γ with hTdef
  have hT0 : 0 < T := P.patience_pos' hγ0 hβ
  have hTneg : T ^ (-γ) = ((P.discount : ℝ) * (1 + P.interest))⁻¹ := by
    rw [hTdef, patience, ← Real.rpow_mul hβR0.le,
      show (1 / γ) * (-γ) = -1 from by field_simp, Real.rpow_neg_one]
  have hden : 0 < T + κ * (1 + P.interest) := by positivity
  set W : (ℝ × Z) →ᵇ ℝ := P.toExtended.bellman v with hWdef
  set A : ℝ := P.policyOf W (a, z) with hAdef
  have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.feasible_subset_region (P.policyOf_mem W (a, z))
  set c : ℝ := P.consumptionFnOf W z a with hcdef
  have hcA : c = P.resources (a, z) - A := rfl
  have hc0 : 0 < c := hposW z a ha
  have hroom : A < P.maxSaving (a, z) := P.policyOf_lt_maxSaving_of_pos hc0 (hcapW a haS z)
  have hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A := fun z' => hposv z' A hAmem
  have hder : ∀ z' : Z, HasDerivAt P.u ((P.consumptionFnOf v z' A) ^ (-γ))
      (P.consumptionFnOf v z' A) := by
    intro z'; rw [hu]; exact hasDerivAt_crraUtility γ (hc' z')
  have hE := P.euler_le (v := v) (z := z) (a := a) (A := A) ha rfl hroom hc0
    (by rw [hu]; exact hasDerivAt_crraUtility γ hc0) hc' hder
  -- expected consumption tomorrow, and its bound
  set Ec : ℝ := ∑ z', P.transitionMatrix z z' * P.consumptionFnOf v z' A with hEcdef
  set S : ℝ := ∑ z', P.transitionMatrix z z' * (P.income z' + H z') with hSdef
  set Y : ℝ := κ * ((1 + P.interest) * A + S) with hYdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun z' _ => mul_nonneg (P.transitionMatrix_nonneg z z')
    (add_nonneg (lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z')).le (hH0 z'))
  have hEc0 : 0 < Ec := by
    have := (convex_Ioi (0 : ℝ)).sum_mem (t := Finset.univ) (w := P.transitionMatrix z)
      (z := fun z' => P.consumptionFnOf v z' A) (fun z' _ => P.transitionMatrix_nonneg z z')
      (P.transitionMatrix_sum z) (fun z' _ => hc' z')
    simpa [smul_eq_mul, hEcdef] using this
  have hEcY : Ec ≤ Y := by
    have h1 : ∀ z', P.consumptionFnOf v z' A
        ≤ κ * (P.income z' + (1 + P.interest) * A + H z') := by
      intro z'
      have := ih z' A hmaps
      rwa [P.resources_eq_of_mem hAmem z'] at this
    have h2 : ∑ z', P.transitionMatrix z z' * P.consumptionFnOf v z' A
        ≤ ∑ z', P.transitionMatrix z z' * (κ * (P.income z' + (1 + P.interest) * A + H z')) :=
      Finset.sum_le_sum fun z' _ =>
        mul_le_mul_of_nonneg_left (h1 z') (P.transitionMatrix_nonneg z z')
    have h3 : ∑ z', P.transitionMatrix z z' * (κ * (P.income z' + (1 + P.interest) * A + H z'))
        = κ * ((1 + P.interest) * A) + κ * S := by
      rw [hSdef, Finset.mul_sum]
      have : ∑ z', P.transitionMatrix z z' * (κ * (P.income z' + (1 + P.interest) * A + H z'))
          = ∑ z', (P.transitionMatrix z z' * (κ * ((1 + P.interest) * A))
            + κ * (P.transitionMatrix z z' * (P.income z' + H z'))) :=
        Finset.sum_congr rfl fun z' _ => by ring
      rw [this, Finset.sum_add_distrib, ← Finset.sum_mul, P.transitionMatrix_sum z, one_mul]
    rw [hYdef]
    linarith [h2, h3]
  have hY0 : 0 < Y := hEc0.trans_le hEcY
  have hJ : Ec ^ (-γ) ≤ ∑ z', P.transitionMatrix z z' * (P.consumptionFnOf v z' A) ^ (-γ) := by
    have := (convexOn_rpow_of_neg (by linarith : -γ < 0)).map_sum_le (t := Finset.univ)
      (w := P.transitionMatrix z) (p := fun z' => P.consumptionFnOf v z' A)
      (fun z' _ => P.transitionMatrix_nonneg z z') (P.transitionMatrix_sum z)
      (fun z' _ => hc' z')
    simpa [smul_eq_mul, hEcdef] using this
  have hYE : Y ^ (-γ) ≤ Ec ^ (-γ) := rpow_neg_antitone hγ0 hEc0 hEcY
  have hchain : (P.discount : ℝ) * (1 + P.interest) * Y ^ (-γ) ≤ c ^ (-γ) := by
    have := le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hYE.trans hJ) hR.le) hβ.le) hE
    linarith [this]
  have hYT : (Y / T) ^ (-γ) ≤ c ^ (-γ) := by
    rw [Real.div_rpow hY0.le hT0.le, hTneg, div_inv_eq_mul]
    nlinarith [hchain]
  have hcle : c ≤ Y / T := le_of_rpow_neg_le (div_pos hY0 hT0) hc0 hγ0 hYT
  have hTc : c * T ≤ Y := (le_div_iff₀ hT0).1 hcle
  -- `T c ≤ κ R (m - c) + κ S`, so `c (T + κ R) ≤ κ R m + κ S = κ R (m + S/R)`
  rw [hYdef, hcA] at hTc
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  have hSR : (1 + P.interest) * (S / (1 + P.interest)) = S := by field_simp
  rw [hcA]
  nlinarith [hTc, hSR, hR]

/-! ### The finite-horizon propensity in closed form

`κ_k` is not merely above its infinite-horizon limit; it is a geometric sum away from it, and the
gap closes at rate `Þ/R`. Writing `q = Þ/R` and `S_k = ∑_{i ≤ k} q^i`, the defining recursion
`κ_{k+1} = κ_k R/(Þ + κ_k R)` is exactly `1/κ_{k+1} = 1 + q/κ_k`, so `κ_k S_k = 1`. Everything
else follows: `κ_k (1 - q^{k+1}) = 1 - q`, so `κ_k` exceeds `1 - q` by exactly `κ_k q^{k+1}`.

The rate matters quantitatively. Bounds that use only `κ_k ≥ 1 - q` throw away how quickly the
propensity settles, and in the equilibrium floor of `OLG.Existence` that loss is the difference
between an interest rate of ten per cent and one of six hundred.
-/

/-- The geometric sum whose reciprocal is the finite-horizon propensity, `∑_{i ≤ k} (Þ/R)^i`. -/
noncomputable def mpcSum (γ : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (P.patience γ / (1 + P.interest)) ^ i

theorem mpcSum_succ (γ : ℝ) (k : ℕ) :
    P.mpcSum γ (k + 1)
      = P.patience γ / (1 + P.interest) * P.mpcSum γ k + 1 := by
  simp only [mpcSum]
  exact geom_sum_succ

theorem one_le_mpcSum {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    1 ≤ P.mpcSum γ k := by
  have hq : 0 ≤ P.patience γ / (1 + P.interest) :=
    div_nonneg (P.patience_pos' hγ0 hβ).le P.interest_gt_neg_one.le
  induction k with
  | zero => simp [mpcSum]
  | succ k ih => rw [P.mpcSum_succ]; nlinarith

/-- **The finite-horizon propensity in closed form**: `κ_k` is the reciprocal of
`∑_{i ≤ k} (Þ/R)^i`. Everything about how fast it settles is read off this. -/
theorem stageMPC_mul_mpcSum {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    P.stageMPC γ k * P.mpcSum γ k = 1 := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hT := P.patience_pos' hγ0 hβ
  induction k with
  | zero => simp [mpcSum, stageMPC]
  | succ k ih =>
    have hκ := P.stageMPC_pos hγ0 hβ k
    have hden : 0 < P.patience γ + P.stageMPC γ k * (1 + P.interest) := by positivity
    rw [stageMPC_succ, P.mpcSum_succ]
    field_simp
    nlinarith [ih, hR, hT, hκ]

/-- The gap to the infinite-horizon propensity closes geometrically:
`κ_k (1 - (Þ/R)^{k+1}) = 1 - Þ/R`. -/
theorem stageMPC_mul_one_sub_pow {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    P.stageMPC γ k * (1 - (P.patience γ / (1 + P.interest)) ^ (k + 1))
      = 1 - P.patience γ / (1 + P.interest) := by
  have h := P.stageMPC_mul_mpcSum hγ0 hβ k
  have hg : (1 - P.patience γ / (1 + P.interest)) * P.mpcSum γ k
      = 1 - (P.patience γ / (1 + P.interest)) ^ (k + 1) := by
    simpa [mpcSum] using
      (mul_neg_geom_sum (P.patience γ / (1 + P.interest)) (k + 1))
  calc P.stageMPC γ k * (1 - (P.patience γ / (1 + P.interest)) ^ (k + 1))
      = P.stageMPC γ k
          * ((1 - P.patience γ / (1 + P.interest)) * P.mpcSum γ k) := by rw [hg]
    _ = (P.stageMPC γ k * P.mpcSum γ k) * (1 - P.patience γ / (1 + P.interest)) := by ring
    _ = 1 - P.patience γ / (1 + P.interest) := by rw [h, one_mul]

/-- **The geometric sum is bounded when the household is impatient enough to settle**, which is
`Þ < R`. This is what turns the closed form into a usable lower bound on `κ_k`. -/
theorem sub_mul_mpcSum_le_one {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    (1 - P.patience γ / (1 + P.interest)) * P.mpcSum γ k ≤ 1 := by
  have hq : 0 ≤ P.patience γ / (1 + P.interest) :=
    div_nonneg (P.patience_pos' hγ0 hβ).le P.interest_gt_neg_one.le
  have hg : (1 - P.patience γ / (1 + P.interest)) * P.mpcSum γ k
      = 1 - (P.patience γ / (1 + P.interest)) ^ (k + 1) := by
    simpa [mpcSum] using
      (mul_neg_geom_sum (P.patience γ / (1 + P.interest)) (k + 1))
  rw [hg]
  have : 0 ≤ (P.patience γ / (1 + P.interest)) ^ (k + 1) := pow_nonneg hq _
  linarith

/-! ### Reachable families

The sandwich below needs the artefactual asset cap to be slack where the household actually is,
and the obvious way to say that is to ask for slack everywhere in `Icc 0 assetCap`. That is too
much to ask. The one-step bound `stagePolicy_le` gives `a' ≤ (1 - κ_k)(R a + y_max)`, so the
capped interval is carried into itself only when `(1 - κ_k) R < 1`, which is to say only below the
rate of time preference `1/β - 1`. Above that rate no cap is forward invariant at all: a patient
household sitting at the cap wants to save past it, so the cap binds and the Euler inequality
under it is unavailable. Since a stationary overlapping-generations equilibrium in a life-cycle
economy typically sits *above* the rate of time preference, assuming slack everywhere would make
the equilibrium theorems vacuous exactly where they are wanted.

A cohort that starts life with nothing never visits the top of the capped interval. What follows
therefore carries a family of regions, one per stage, that the stage policies map down through,
and asks for slack only on those.
-/

/-- **A reachable family**: one region of asset levels per stage, carried into one another by the
stage policies, with the artefactual cap slack on each. A household with `k + 1` periods left and
assets in `region (k + 1)` saves into `region k`, and nowhere on any region does the cap bind. -/
structure StageRegions (Q : IncomeFluctuation Z 0 assetCap) where
  /-- The asset levels a household with `k` periods still to come can be at. -/
  region : ℕ → Set ℝ
  /-- Every region sits inside the capped state space. -/
  subset : ∀ k, region k ⊆ Icc (0 : ℝ) assetCap
  /-- The stage-`k + 1` policy carries `region (k + 1)` into `region k`. -/
  maps : ∀ k, ∀ a ∈ region (k + 1), ∀ z : Z, Q.stagePolicy (k + 1) (a, z) ∈ region k
  /-- The artefactual asset cap is slack on every region. -/
  slack : ∀ k, ∀ a ∈ region k, ∀ z : Z, Q.stagePolicy k (a, z) < assetCap

/-- The whole capped state space is a reachable family exactly when the cap is slack on it, which
is the hypothesis the sandwich used to carry. Impatience buys it; nothing else does. -/
def allRegions (hslack : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
    P.stagePolicy k (a, z) < assetCap) : P.StageRegions where
  region := fun _ => Icc (0 : ℝ) assetCap
  subset := fun _ => subset_rfl
  maps := fun k a _ z => P.stagePolicy_mem_region (k + 1) (a, z)
  slack := hslack

@[simp] theorem allRegions_region (hslack : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
    P.stagePolicy k (a, z) < assetCap) (k : ℕ) :
    (P.allRegions hslack).region k = Icc (0 : ℝ) assetCap := rfl

/-! ### The finite-horizon sandwich -/

/-- **The finite-horizon minimal-MPC bound on a reachable family**: `κ_k · m ≤ c_k(a, z)` at every
stage, at every asset level the family admits. -/
theorem stageMPC_mul_le_stageConsumption_on {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) (G : P.StageRegions)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ G.region k) :
    P.stageMPC γ k * P.resources (a, z) ≤ P.stageConsumption k z a := by
  induction k generalizing z a with
  | zero => rw [P.stageConsumption_zero (G.subset 0 ha) z]; simp [stageMPC]
  | succ k ih =>
    have h := P.crra_stageMPC_step hγ0 hu hβ (v := P.stageValue k) (T := G.region k)
      (fun z a ha => P.stageConsumption_pos hd k z ha)
      (fun b hb z => G.slack k b hb z)
      (fun z a ha => by rw [← stageValue_succ]; exact P.stageConsumption_pos hd (k + 1) z ha)
      (P.stageMPC_pos hγ0 hβ k) (fun z b hb => ih z hb) z (G.subset (k + 1) ha)
      (by rw [← stageValue_succ]; exact G.maps k a ha z)
    rw [← stageValue_succ] at h
    rw [stageMPC_succ]
    exact h

/-- **The finite-horizon upper sandwich on a reachable family**: `c_k(a, z) ≤ κ_k · (m + H_k(z))`
at every stage, at every asset level the family admits. -/
theorem stageConsumption_le_stageHumanWealth_on {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) (G : P.StageRegions)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ G.region k) :
    P.stageConsumption k z a
      ≤ P.stageMPC γ k * (P.resources (a, z) + P.stageHumanWealth k z) := by
  induction k generalizing z a with
  | zero =>
    rw [P.stageConsumption_zero (G.subset 0 ha) z]; simp [stageMPC, stageHumanWealth]
  | succ k ih =>
    have h := P.crra_stageUpper_step hγ0 hu hβ (v := P.stageValue k)
      (S := G.region (k + 1)) (T := G.region k)
      (fun z a ha => P.stageConsumption_pos hd k z ha)
      (fun z a ha => by rw [← stageValue_succ]; exact P.stageConsumption_pos hd (k + 1) z ha)
      (fun b hb z => by rw [← stageValue_succ]; exact G.slack (k + 1) b hb z)
      (P.stageMPC_pos hγ0 hβ k) (P.stageHumanWealth_nonneg k) (fun z b hb => ih z hb) z
      (G.subset (k + 1) ha) ha (by rw [← stageValue_succ]; exact G.maps k a ha z)
    rw [← stageValue_succ] at h
    rw [stageMPC_succ, stageHumanWealth_succ]
    exact h

/-- **A one-step saving bound on a reachable family**: `a' ≤ (1 - κ_k)(R a + y_max)`. -/
theorem stagePolicy_le_on {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) (G : P.StageRegions)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ G.region k) :
    P.stagePolicy k (a, z) ≤ (1 - P.stageMPC γ k) * ((1 + P.interest) * a + P.maxIncome) := by
  have h := P.stageMPC_mul_le_stageConsumption_on hγ0 hu hβ hd G k z ha
  rw [stageConsumption_eq, P.resources_eq_of_mem (G.subset k ha) z] at h
  have hκ1 := P.stageMPC_le_one hγ0 hβ k
  have hy := P.le_maxIncome z
  have h1 : P.stagePolicy k (a, z)
      ≤ (1 - P.stageMPC γ k) * (P.income z + (1 + P.interest) * a) := by linarith
  have h2 : (1 - P.stageMPC γ k) * (P.income z + (1 + P.interest) * a)
      ≤ (1 - P.stageMPC γ k) * ((1 + P.interest) * a + P.maxIncome) :=
    mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.2 hκ1)
  linarith

/-! ### The sandwich when the cap is slack everywhere

The original statements, recovered by taking the constant family. They are what an impatient
household satisfies, and they remain the right form whenever the cap can be shown slack on the
whole capped interval.
-/

/-- **The finite-horizon minimal-MPC bound**: `κ_k · m ≤ c_k(a, z)` at every stage. -/
theorem stageMPC_mul_le_stageConsumption {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, P.stagePolicy k (a, z) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.stageMPC γ k * P.resources (a, z) ≤ P.stageConsumption k z a :=
  P.stageMPC_mul_le_stageConsumption_on hγ0 hu hβ hd (P.allRegions hslack) k z ha

/-- **The finite-horizon upper sandwich**: `c_k(a, z) ≤ κ_k · (m + H_k(z))` at every stage. -/
theorem stageConsumption_le_stageHumanWealth {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, P.stagePolicy k (a, z) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.stageConsumption k z a
      ≤ P.stageMPC γ k * (P.resources (a, z) + P.stageHumanWealth k z) :=
  P.stageConsumption_le_stageHumanWealth_on hγ0 hu hβ hd (P.allRegions hslack) k z ha

/-- **A one-step saving bound**: `a' ≤ (1 - κ_k)(R a + y_max)` at stage `k`. -/
theorem stagePolicy_le {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded)
    (hslack : ∀ k : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, P.stagePolicy k (a, z) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.stagePolicy k (a, z) ≤ (1 - P.stageMPC γ k) * ((1 + P.interest) * a + P.maxIncome) :=
  P.stagePolicy_le_on hγ0 hu hβ hd (P.allRegions hslack) k z ha

end IncomeFluctuation

end LeanEconomics
