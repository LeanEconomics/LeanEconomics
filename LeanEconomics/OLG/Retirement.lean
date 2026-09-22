/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.LifeCycle

/-!
# Retirement and a lump-sum pension

A household works until age `Jr` and is retired after it. During retirement it receives a pension
instead of its labour earnings. With a **lump-sum** pension the retired household faces the same
problem as the working one with income replaced by the constant `p`, so the retired phase is an
`IncomeFluctuation` in its own right (`withPension`) and everything proved in `LifeCycle` applies
to it unchanged.

The life-cycle value is then assembled by iterating the working Bellman operator on the retired
value: `lifeValue nr nw` is the value of a household with `nw` working periods and `nr` retired
periods still to come, so a household of age `j < Jr` in a life of `J` periods sits at
`nw = Jr - j`, `nr = J - Jr`.

Two facts are worth stating for the pension itself. A retiree's human wealth never exceeds the
perpetuity value of the pension, `H_k ≤ p / r` (`stageHumanWealth_withPension_le`), so the
finite-horizon sandwich of `LifeCycle` reads

  `κ_k · m ≤ c_k(a) ≤ κ_k · (m + p/r)`

at every retired age. And cash on hand is strictly increasing in assets, which with the
monotonicity of `LifeCycle` makes saving and consumption rise with wealth at every age. Both fail
once the pension is means-tested, which is the subject of `OLG/MeansTest.lean`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### The retired household -/

/-- **The retired household**: the same primitives with labour income replaced by a constant
lump-sum pension `p`. -/
def withPension {p : ℝ} (hp : 0 < p) : IncomeFluctuation Z 0 assetCap :=
  { P with
    income := fun _ => p
    minIncome := p
    maxIncome := p
    minIncome_pos := hp
    minIncome_le := fun _ => le_rfl
    le_maxIncome := fun _ => le_rfl
    minConsumption := p
    minConsumption_pos := hp
    minConsumption_le_floor := by simp }

@[simp] theorem withPension_income {p : ℝ} (hp : 0 < p) (z : Z) :
    (P.withPension hp).income z = p := rfl
@[simp] theorem withPension_minIncome {p : ℝ} (hp : 0 < p) :
    (P.withPension hp).minIncome = p := rfl
@[simp] theorem withPension_maxIncome {p : ℝ} (hp : 0 < p) :
    (P.withPension hp).maxIncome = p := rfl
@[simp] theorem withPension_interest {p : ℝ} (hp : 0 < p) :
    (P.withPension hp).interest = P.interest := rfl
@[simp] theorem withPension_discount {p : ℝ} (hp : 0 < p) :
    (P.withPension hp).discount = P.discount := rfl
@[simp] theorem withPension_u {p : ℝ} (hp : 0 < p) : (P.withPension hp).u = P.u := rfl
@[simp] theorem withPension_transitionMatrix {p : ℝ} (hp : 0 < p) :
    (P.withPension hp).transitionMatrix = P.transitionMatrix := rfl
@[simp] theorem withPension_dom {p : ℝ} (hp : 0 < p) : (P.withPension hp).dom = P.dom := rfl

theorem withPension_unbounded {p : ℝ} (hp : 0 < p) (hd : P.Unbounded) :
    (P.withPension hp).Unbounded := hd

theorem withPension_resources {p : ℝ} (hp : 0 < p) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (z : Z) : (P.withPension hp).resources (a, z) = p + (1 + P.interest) * a :=
  (P.withPension hp).resources_eq_of_mem ha z

/-- **Cash on hand rises with wealth under a lump-sum pension.** The contrast with a means-tested
pension is the whole content of `OLG/MeansTest.lean`. -/
theorem withPension_resources_strictMono {p : ℝ} (hp : 0 < p) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) (hb : b ∈ Icc (0 : ℝ) assetCap) (hab : a < b) (z : Z) :
    (P.withPension hp).resources (a, z) < (P.withPension hp).resources (b, z) := by
  rw [P.withPension_resources hp ha z, P.withPension_resources hp hb z]
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have := mul_lt_mul_of_pos_left hab hR
  linarith

/-- **A retiree's human wealth is the same in every income state**: the pension does not depend
on the earnings shock, so neither does the present value of the pensions still to come. -/
theorem stageHumanWealth_withPension_const {p : ℝ} (hp : 0 < p) (k : ℕ) (z z' : Z) :
    (P.withPension hp).stageHumanWealth k z = (P.withPension hp).stageHumanWealth k z' := by
  classical
  induction k generalizing z z' with
  | zero => rfl
  | succ k ih =>
    set w₀ : Z := Classical.arbitrary Z with hw₀
    have hconst : ∀ y : Z, ∀ w : Z, ∑ v, (P.withPension hp).transitionMatrix y v
          * ((P.withPension hp).income v + (P.withPension hp).stageHumanWealth k v)
        = p + (P.withPension hp).stageHumanWealth k w := by
      intro y w
      have : ∀ v : Z, (P.withPension hp).transitionMatrix y v
            * ((P.withPension hp).income v + (P.withPension hp).stageHumanWealth k v)
          = (P.withPension hp).transitionMatrix y v
            * (p + (P.withPension hp).stageHumanWealth k w) := by
        intro v
        rw [withPension_income, ih v w]
      rw [Finset.sum_congr rfl fun v _ => this v, ← Finset.sum_mul,
        (P.withPension hp).transitionMatrix_sum y, one_mul]
    rw [stageHumanWealth_succ, stageHumanWealth_succ, hconst z w₀, hconst z' w₀]

/-- **The perpetuity bound**: a retiree's human wealth never exceeds `p / r`. -/
theorem stageHumanWealth_withPension_le {p : ℝ} (hp : 0 < p) (hint : 0 < P.interest) (k : ℕ)
    (z : Z) : (P.withPension hp).stageHumanWealth k z ≤ p / P.interest := by
  classical
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  induction k generalizing z with
  | zero => exact div_nonneg hp.le hint.le
  | succ k ih =>
    rw [stageHumanWealth_succ]
    simp only [withPension_interest, withPension_income, withPension_transitionMatrix]
    rw [div_le_div_iff₀ hR hint]
    have hsum : ∑ z', P.transitionMatrix z z'
          * (p + (P.withPension hp).stageHumanWealth k z')
        ≤ ∑ z', P.transitionMatrix z z' * (p + p / P.interest) := by
      refine Finset.sum_le_sum fun z' _ => ?_
      exact mul_le_mul_of_nonneg_left (by linarith [ih z']) (P.transitionMatrix_nonneg z z')
    rw [← Finset.sum_mul, P.transitionMatrix_sum z, one_mul] at hsum
    have hkey : (p + p / P.interest) * P.interest = p * (1 + P.interest) := by
      field_simp; ring
    calc (∑ z', P.transitionMatrix z z' * (p + (P.withPension hp).stageHumanWealth k z'))
          * P.interest
        ≤ (p + p / P.interest) * P.interest := mul_le_mul_of_nonneg_right hsum hint.le
      _ = p * (1 + P.interest) := hkey

/-! ### The life cycle with retirement -/

variable (Q : IncomeFluctuation Z 0 assetCap)

/-- **The value with `nw` working periods and `nr` retired periods still to come.** The retired
phase is run first, from the terminal condition, and the working Bellman operator of `P` is then
applied `nw` times. -/
noncomputable def lifeValue (nr nw : ℕ) : (ℝ × Z) →ᵇ ℝ :=
  (P.toExtended.bellman)^[nw] (Q.stageValue nr)

theorem lifeValue_zero (nr : ℕ) : P.lifeValue Q nr 0 = Q.stageValue nr := rfl

theorem lifeValue_succ (nr nw : ℕ) :
    P.lifeValue Q nr (nw + 1) = P.toExtended.bellman (P.lifeValue Q nr nw) :=
  Function.iterate_succ_apply' _ _ _

/-- Saving at a working age with `nw` periods of work and `nr` of retirement still to come. -/
noncomputable def lifePolicy (nr nw : ℕ) (s : ℝ × Z) : ℝ := P.policyOf (P.lifeValue Q nr nw) s

/-- Consumption at a working age. -/
noncomputable def lifeConsumption (nr nw : ℕ) (z : Z) (a : ℝ) : ℝ :=
  P.consumptionFnOf (P.lifeValue Q nr nw) z a

/-- The life-cycle value has concave slices at every age, so the optimal action is unique and
the policy is well behaved. -/
theorem concaveSlices_lifeValue (nr nw : ℕ) : ConcaveSlices 0 assetCap (P.lifeValue Q nr nw) := by
  induction nw with
  | zero => exact Q.concaveSlices_stageValue nr
  | succ k ih => rw [lifeValue_succ]; exact P.concaveSlices_bellman ih

/-- **Saving rises with wealth at every working age.** -/
theorem lifePolicy_mono (nr nw : ℕ) {a a' : ℝ} {z : Z} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (ha' : a' ∈ Icc (0 : ℝ) assetCap) (hle : a ≤ a') :
    P.lifePolicy Q nr nw (a, z) ≤ P.lifePolicy Q nr nw (a', z) :=
  P.policyOf_mono (P.concaveSlices_lifeValue Q nr nw) ha ha' hle

/-- **Consumption rises with wealth at every working age.** -/
theorem lifeConsumption_mono (nr nw : ℕ) {a a' : ℝ} {z : Z} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (ha' : a' ∈ Icc (0 : ℝ) assetCap) (hle : a ≤ a') :
    P.lifeConsumption Q nr nw z a ≤ P.lifeConsumption Q nr nw z a' :=
  P.consumptionFnOf_mono (P.concaveSlices_lifeValue Q nr nw) ha ha' hle

/-- Consumption is positive at every working age. -/
theorem lifeConsumption_pos (hd : P.Unbounded) (nr nw : ℕ) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) : 0 < P.lifeConsumption Q nr nw z a :=
  P.consumptionFnOf_pos hd _ ha

end IncomeFluctuation

end LeanEconomics
