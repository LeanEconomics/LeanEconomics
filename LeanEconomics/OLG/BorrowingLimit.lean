/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.LifeCycle

/-!
# What the borrowing limit does

The numerical sections show that the whole of the risk correction to Theorem 1 is the borrowing
constraint: loosening the limit to the natural one moves the threshold in risk aversion from
`3.42` to `4.38`, which is the certainty-equivalent household's `4.33`, while precaution moves the
level of saving and not the threshold. This file proves the comparative static in the limit
itself, which is the one-sided half of that statement and needs no condition at all.

## The statement

Two households share every primitive and differ only in the borrowing limit, `f₂ ≤ f₁`
(`withFloor`). Then at every age and every state the household with the tighter limit consumes
less and saves more (`finiteConsumption_le_of_floor_le`, `le_finitePolicy_of_floor_le`).

## Why it needs no condition

The induction is the one of `RateMonotone` with the interest rate held fixed, and that is exactly
what removes the difficulty. Suppose the claim holds with `k` periods to come and fails at `k+1`,
so the tighter household consumes strictly more and therefore saves strictly less. Its Euler
inequality under the cap, the looser household's Euler inequality above its floor --- available
because the looser household saves strictly more than the tighter one, hence strictly more than
either floor --- the induction hypothesis, and monotonicity of consumption in wealth chain into
`u'(c₁) ≥ u'(c₂)`, which contradicts `c₁ > c₂`. The gross return appears on both sides and
cancels, so there is no substitution term to control, and no analogue of the slack condition
`StageSlack` is needed. Tightening the limit raises the marginal value of saving unambiguously.

That is the sense in which the constraint channel is easier than the rate channel, and it is why
the remaining work on Theorem 1 for `μ = 3` should be aimed here.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]

/-! ### The same household at a different borrowing limit -/

variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- The same primitives at a different borrowing limit. The hypothesis is the natural-limit
condition at the new floor: a household pinned there must still be able to eat. -/
def withFloor (f : ℝ) (hcap : f ≤ assetCap)
    (hmc : P.minConsumption ≤ P.minIncome + P.interest * f) : IncomeFluctuation Z f assetCap :=
  { P with
    assetFloor_le_assetCap := hcap
    minConsumption_le_floor := hmc }

@[simp] theorem withFloor_income (f : ℝ) (hcap : f ≤ assetCap)
    (hmc : P.minConsumption ≤ P.minIncome + P.interest * f) :
    (P.withFloor f hcap hmc).income = P.income := rfl
@[simp] theorem withFloor_interest (f : ℝ) (hcap : f ≤ assetCap)
    (hmc : P.minConsumption ≤ P.minIncome + P.interest * f) :
    (P.withFloor f hcap hmc).interest = P.interest := rfl
@[simp] theorem withFloor_discount (f : ℝ) (hcap : f ≤ assetCap)
    (hmc : P.minConsumption ≤ P.minIncome + P.interest * f) :
    (P.withFloor f hcap hmc).discount = P.discount := rfl
@[simp] theorem withFloor_u (f : ℝ) (hcap : f ≤ assetCap)
    (hmc : P.minConsumption ≤ P.minIncome + P.interest * f) :
    (P.withFloor f hcap hmc).u = P.u := rfl
@[simp] theorem withFloor_transitionMatrix (f : ℝ) (hcap : f ≤ assetCap)
    (hmc : P.minConsumption ≤ P.minIncome + P.interest * f) :
    (P.withFloor f hcap hmc).transitionMatrix = P.transitionMatrix := rfl
@[simp] theorem withFloor_dom (f : ℝ) (hcap : f ≤ assetCap)
    (hmc : P.minConsumption ≤ P.minIncome + P.interest * f) :
    (P.withFloor f hcap hmc).dom = P.dom := rfl

/-! ### Stages at a general borrowing limit

`LifeCycle` builds the stages at a zero limit, because that is where the sandwich lives. The
definitions themselves need no such restriction, and here they are read at an arbitrary floor. -/

/-- The continuation value with `k` periods still to come. -/
noncomputable def finiteValue (k : ℕ) : (ℝ × Z) →ᵇ ℝ :=
  (P.toExtended.bellman)^[k] (0 : (ℝ × Z) →ᵇ ℝ)

/-- The saving of a household with `k` periods still to come. -/
noncomputable def finitePolicy (k : ℕ) (s : ℝ × Z) : ℝ := P.policyOf (P.finiteValue k) s

/-- The consumption of a household with `k` periods still to come. -/
noncomputable def finiteConsumption (k : ℕ) (z : Z) (a : ℝ) : ℝ :=
  P.consumptionFnOf (P.finiteValue k) z a

theorem finiteValue_succ (k : ℕ) :
    P.finiteValue (k + 1) = P.toExtended.bellman (P.finiteValue k) :=
  Function.iterate_succ_apply' _ _ _

theorem finiteConsumption_eq (k : ℕ) (z : Z) (a : ℝ) :
    P.finiteConsumption k z a = P.resources (a, z) - P.finitePolicy k (a, z) := rfl

theorem finitePolicy_mem_region (k : ℕ) (s : ℝ × Z) :
    P.finitePolicy k s ∈ Icc assetFloor assetCap :=
  P.feasible_subset_region (P.policyOf_mem _ s)

/-- In the last period the household runs down to its borrowing limit. -/
theorem finiteConsumption_zero {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    P.finiteConsumption 0 z a = P.income z + (1 + P.interest) * a - assetFloor :=
  P.consumptionFnOf_zero ha

theorem finiteConsumption_pos (hd : P.Unbounded) (k : ℕ) (z : Z) {a : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) : 0 < P.finiteConsumption k z a :=
  P.consumptionFnOf_pos hd _ ha

theorem concaveSlices_finiteValue (k : ℕ) : ConcaveSlices assetFloor assetCap (P.finiteValue k) :=
  P.concaveSlices_iterate_zero k

theorem finiteConsumption_mono (k : ℕ) {a a' : ℝ} {z : Z} (ha : a ∈ Icc assetFloor assetCap)
    (ha' : a' ∈ Icc assetFloor assetCap) (hle : a ≤ a') :
    P.finiteConsumption k z a ≤ P.finiteConsumption k z a' :=
  P.consumptionFnOf_mono (P.concaveSlices_finiteValue k) ha ha' hle

end IncomeFluctuation

/-! ### The comparison -/

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {f₁ f₂ assetCap : ℝ} (P : IncomeFluctuation Z f₁ assetCap)
  (Q : IncomeFluctuation Z f₂ assetCap)

/-- **A tighter borrowing limit means less consumption, at every age and every state.** The two
households share every primitive; `P` may not borrow below `f₁` and `Q` may go to `f₂ ≤ f₁`. No
condition beyond the standing ones is needed: the gross return is the same in both, so it cancels,
and tightening the limit raises the marginal value of saving unambiguously. -/
theorem finiteConsumption_le_of_floor_le {γ : ℝ} (hγ0 : 0 < γ)
    (hu : P.u = crraUtility γ) (huQ : Q.u = crraUtility γ)
    (hdP : P.Unbounded) (hdQ : Q.Unbounded)
    (hinc : Q.income = P.income) (hpi : Q.transitionMatrix = P.transitionMatrix)
    (hr : Q.interest = P.interest) (hβ : Q.discount = P.discount)
    (hf : f₂ ≤ f₁)
    (hcapP : ∀ j : ℕ, ∀ b ∈ Icc f₁ assetCap, ∀ w : Z, P.finitePolicy j (b, w) < assetCap)
    (hcapQ : ∀ j : ℕ, ∀ b ∈ Icc f₂ assetCap, ∀ w : Z, Q.finitePolicy j (b, w) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc f₁ assetCap) :
    P.finiteConsumption k z a ≤ Q.finiteConsumption k z a := by
  classical
  have hres : ∀ x ∈ Icc f₁ assetCap, ∀ w : Z, Q.resources (x, w) = P.resources (x, w) := by
    intro x hx w
    simp only [resources, hinc, hr, max_eq_right hx.1, max_eq_right (le_trans hf hx.1)]
  induction k generalizing a z with
  | zero =>
    have haQ : a ∈ Icc f₂ assetCap := ⟨le_trans hf ha.1, ha.2⟩
    rw [P.finiteConsumption_zero ha z, Q.finiteConsumption_zero haQ z]
    simp only [hinc, hr]
    linarith
  | succ k ih =>
    have haQ : a ∈ Icc f₂ assetCap := ⟨le_trans hf ha.1, ha.2⟩
    by_contra hcon
    rw [not_le] at hcon
    set b : ℝ := P.finitePolicy (k + 1) (a, z) with hb
    set d : ℝ := Q.finitePolicy (k + 1) (a, z) with hd
    have hbmem : b ∈ Icc f₁ assetCap := P.finitePolicy_mem_region _ _
    have hdmem : d ∈ Icc f₂ assetCap := Q.finitePolicy_mem_region _ _
    -- the tighter household consumes more, so it saves less
    have hlt : b < d := by
      have hcP : P.finiteConsumption (k + 1) z a = P.resources (a, z) - b := rfl
      have hcQ : Q.finiteConsumption (k + 1) z a = Q.resources (a, z) - d := rfl
      rw [hres a ha z] at hcQ
      linarith [hcon, hcP, hcQ]
    have hdf₁ : f₂ ≤ d := hdmem.1
    have hd0 : f₂ < d := lt_of_le_of_lt (le_trans hf hbmem.1) hlt
    have hcP0 : 0 < P.finiteConsumption (k + 1) z a := P.finiteConsumption_pos hdP _ z ha
    have hcQ0 : 0 < Q.finiteConsumption (k + 1) z a := Q.finiteConsumption_pos hdQ _ z haQ
    have hcP' : ∀ w : Z, 0 < P.finiteConsumption k w b := fun w =>
      P.finiteConsumption_pos hdP k w hbmem
    have hcQ' : ∀ w : Z, 0 < Q.finiteConsumption k w d := fun w =>
      Q.finiteConsumption_pos hdQ k w hdmem
    have hderP : ∀ c : ℝ, 0 < c → HasDerivAt P.u (c ^ (-γ)) c := fun c hc => by
      rw [hu]; exact hasDerivAt_crraUtility γ hc
    have hderQ : ∀ c : ℝ, 0 < c → HasDerivAt Q.u (c ^ (-γ)) c := fun c hc => by
      rw [huQ]; exact hasDerivAt_crraUtility γ hc
    -- Euler under the cap for the tighter household
    have hroomP : b < P.maxSaving (a, z) := by
      rw [maxSaving_eq]
      refine lt_min (hcapP (k + 1) a ha z) ?_
      have := hcP0
      change 0 < P.resources (a, z) - b at this
      linarith
    have hEP := P.euler_le (v := P.finiteValue k) (z := z) (a := a) (A := b)
      (du := (P.finiteConsumption (k + 1) z a) ^ (-γ))
      (du' := fun w => (P.finiteConsumption k w b) ^ (-γ))
      ha (by rw [← P.finiteValue_succ]; rfl) hroomP
      (by rw [← P.finiteValue_succ]; exact hcP0)
      (by rw [← P.finiteValue_succ]; exact hderP _ hcP0)
      (fun w => hcP' w) (fun w => hderP _ (hcP' w))
    -- Euler above the floor for the looser household
    have hslackQ : ∀ w : Z, Q.policyOf (Q.finiteValue k) (d, w) < Q.maxSaving (d, w) := by
      intro w
      rw [maxSaving_eq]
      refine lt_min (hcapQ k d hdmem w) ?_
      have h0 : 0 < Q.consumptionFnOf (Q.finiteValue k) w d :=
        Q.finiteConsumption_pos hdQ k w hdmem
      change 0 < Q.resources (d, w) - Q.policyOf (Q.finiteValue k) (d, w) at h0
      linarith
    have hEQ := Q.euler_ge (v := Q.finiteValue k) (z := z) (a := a) (A := d)
      (du := (Q.finiteConsumption (k + 1) z a) ^ (-γ))
      (du' := fun w => (Q.finiteConsumption k w d) ^ (-γ))
      haQ (by rw [← Q.finiteValue_succ]; rfl) hd0 hslackQ
      (by rw [← Q.finiteValue_succ]; exact hcQ0)
      (by rw [← Q.finiteValue_succ]; exact hderQ _ hcQ0)
      (fun w => hcQ' w) (fun w => hderQ _ (hcQ' w))
    -- the induction hypothesis and monotonicity, at tomorrow's states
    have hstep : ∀ w : Z, (Q.finiteConsumption k w d) ^ (-γ)
        ≤ (P.finiteConsumption k w b) ^ (-γ) := by
      intro w
      refine rpow_neg_antitone hγ0 (hcP' w) ?_
      calc P.finiteConsumption k w b ≤ Q.finiteConsumption k w b := ih w hbmem
        _ ≤ Q.finiteConsumption k w d :=
            Q.finiteConsumption_mono k ⟨le_trans hf hbmem.1, hbmem.2⟩ hdmem hlt.le
    have hsum : ∑ w, P.transitionMatrix z w * (Q.finiteConsumption k w d) ^ (-γ)
        ≤ ∑ w, P.transitionMatrix z w * (P.finiteConsumption k w b) ^ (-γ) :=
      Finset.sum_le_sum fun w _ =>
        mul_le_mul_of_nonneg_left (hstep w) (P.transitionMatrix_nonneg z w)
    -- chain: the tighter household's marginal utility is the larger
    rw [hpi, hr, hβ] at hEQ
    have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
    have hβ0 : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
    have hchain : (Q.finiteConsumption (k + 1) z a) ^ (-γ)
        ≤ (P.finiteConsumption (k + 1) z a) ^ (-γ) := by
      refine hEQ.trans (le_trans ?_ hEP)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hR.le) hβ0
    have := le_of_rpow_neg_le hcQ0 hcP0 hγ0 hchain
    linarith

/-- **The modulus: relaxing the limit by `Δ` is worth at most `Δ` of extra wealth.** The
household that may borrow down to `f₂`, holding `x`, consumes no more than the household that may
only borrow down to `f₁` would holding `x + (f₁ - f₂)`. With
`finiteConsumption_le_of_floor_le` this sandwiches the looser household's consumption between the
tighter one's at `x` and at `x + Δ`, so the whole effect of the limit on consumption is worth less
than the relaxation itself. -/
theorem finiteConsumption_le_shift {γ : ℝ} (hγ0 : 0 < γ)
    (hu : P.u = crraUtility γ) (huQ : Q.u = crraUtility γ)
    (hdP : P.Unbounded) (hdQ : Q.Unbounded)
    (hinc : Q.income = P.income) (hpi : Q.transitionMatrix = P.transitionMatrix)
    (hr : Q.interest = P.interest) (hβ : Q.discount = P.discount)
    (hint : 0 ≤ P.interest) (hf : f₂ ≤ f₁)
    (hcapP : ∀ j : ℕ, ∀ b ∈ Icc f₁ assetCap, ∀ w : Z, P.finitePolicy j (b, w) < assetCap)
    (hcapQ : ∀ j : ℕ, ∀ b ∈ Icc f₂ assetCap, ∀ w : Z, Q.finitePolicy j (b, w) < assetCap)
    (k : ℕ) (z : Z) {x : ℝ} (hx : x ∈ Icc f₂ (assetCap - (f₁ - f₂))) :
    Q.finiteConsumption k z x ≤ P.finiteConsumption k z (x + (f₁ - f₂)) := by
  classical
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hΔ : (0 : ℝ) ≤ f₁ - f₂ := by linarith
  induction k generalizing x z with
  | zero =>
    have hxQ : x ∈ Icc f₂ assetCap := ⟨hx.1, by linarith [hx.2]⟩
    have hxP : x + (f₁ - f₂) ∈ Icc f₁ assetCap := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [Q.finiteConsumption_zero hxQ z, P.finiteConsumption_zero hxP z]
    simp only [hinc, hr]
    nlinarith [mul_nonneg hR.le hΔ]
  | succ k ih =>
    have hxQ : x ∈ Icc f₂ assetCap := ⟨hx.1, by linarith [hx.2]⟩
    have hxP : x + (f₁ - f₂) ∈ Icc f₁ assetCap := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    by_contra hcon
    rw [not_le] at hcon
    set aQ : ℝ := Q.finitePolicy (k + 1) (x, z) with haQ
    set aP : ℝ := P.finitePolicy (k + 1) (x + (f₁ - f₂), z) with haP
    have haQmem : aQ ∈ Icc f₂ assetCap := Q.finitePolicy_mem_region _ _
    have haPmem : aP ∈ Icc f₁ assetCap := P.finitePolicy_mem_region _ _
    have hcQ0 : 0 < Q.finiteConsumption (k + 1) z x := Q.finiteConsumption_pos hdQ _ z hxQ
    have hcP0 : 0 < P.finiteConsumption (k + 1) z (x + (f₁ - f₂)) :=
      P.finiteConsumption_pos hdP _ z hxP
    -- the failure says the tighter household saves much more
    have hresQ : Q.resources (x, z) = P.income z + (1 + P.interest) * x := by
      simp only [resources, hinc, hr, max_eq_right hx.1]
    have hresP : P.resources (x + (f₁ - f₂), z)
        = P.income z + (1 + P.interest) * (x + (f₁ - f₂)) := by
      simp only [resources, max_eq_right hxP.1]
    have hgap : aQ + (1 + P.interest) * (f₁ - f₂) < aP := by
      have e₁ : Q.finiteConsumption (k + 1) z x = Q.resources (x, z) - aQ := rfl
      have e₂ : P.finiteConsumption (k + 1) z (x + (f₁ - f₂))
          = P.resources (x + (f₁ - f₂), z) - aP := rfl
      rw [hresQ] at e₁
      rw [hresP] at e₂
      nlinarith [hcon, e₁, e₂]
    have hgapΔ : aQ + (f₁ - f₂) < aP := by nlinarith [hgap, mul_nonneg hint hΔ]
    have haPf : f₁ < aP := by linarith [haQmem.1]
    -- the induction hypothesis at tomorrow's assets, then monotonicity
    have haQrange : aQ ∈ Icc f₂ (assetCap - (f₁ - f₂)) :=
      ⟨haQmem.1, by linarith [haPmem.2]⟩
    have hstep : ∀ w : Z, Q.finiteConsumption k w aQ ≤ P.finiteConsumption k w aP := by
      intro w
      calc Q.finiteConsumption k w aQ ≤ P.finiteConsumption k w (aQ + (f₁ - f₂)) := ih w haQrange
        _ ≤ P.finiteConsumption k w aP :=
            P.finiteConsumption_mono k ⟨by linarith [haQmem.1], by linarith [haPmem.2]⟩
              haPmem hgapΔ.le
    -- the two Euler inequalities
    have hcQ' : ∀ w : Z, 0 < Q.finiteConsumption k w aQ := fun w =>
      Q.finiteConsumption_pos hdQ k w haQmem
    have hcP' : ∀ w : Z, 0 < P.finiteConsumption k w aP := fun w =>
      P.finiteConsumption_pos hdP k w haPmem
    have hderP : ∀ c : ℝ, 0 < c → HasDerivAt P.u (c ^ (-γ)) c := fun c hc => by
      rw [hu]; exact hasDerivAt_crraUtility γ hc
    have hderQ : ∀ c : ℝ, 0 < c → HasDerivAt Q.u (c ^ (-γ)) c := fun c hc => by
      rw [huQ]; exact hasDerivAt_crraUtility γ hc
    have hroomQ : aQ < Q.maxSaving (x, z) := by
      rw [maxSaving_eq]
      refine lt_min (hcapQ (k + 1) x hxQ z) ?_
      have h0 : 0 < Q.resources (x, z) - aQ := hcQ0
      linarith
    have hEQ := Q.euler_le (v := Q.finiteValue k) (z := z) (a := x) (A := aQ)
      (du := (Q.finiteConsumption (k + 1) z x) ^ (-γ))
      (du' := fun w => (Q.finiteConsumption k w aQ) ^ (-γ))
      hxQ (by rw [← Q.finiteValue_succ]; rfl) hroomQ
      (by rw [← Q.finiteValue_succ]; exact hcQ0)
      (by rw [← Q.finiteValue_succ]; exact hderQ _ hcQ0)
      (fun w => hcQ' w) (fun w => hderQ _ (hcQ' w))
    have hslackP : ∀ w : Z, P.policyOf (P.finiteValue k) (aP, w) < P.maxSaving (aP, w) := by
      intro w
      rw [maxSaving_eq]
      refine lt_min (hcapP k aP haPmem w) ?_
      have h0 : 0 < P.consumptionFnOf (P.finiteValue k) w aP := hcP' w
      change 0 < P.resources (aP, w) - P.policyOf (P.finiteValue k) (aP, w) at h0
      linarith
    have hEP := P.euler_ge (v := P.finiteValue k) (z := z) (a := x + (f₁ - f₂)) (A := aP)
      (du := (P.finiteConsumption (k + 1) z (x + (f₁ - f₂))) ^ (-γ))
      (du' := fun w => (P.finiteConsumption k w aP) ^ (-γ))
      hxP (by rw [← P.finiteValue_succ]; rfl) haPf hslackP
      (by rw [← P.finiteValue_succ]; exact hcP0)
      (by rw [← P.finiteValue_succ]; exact hderP _ hcP0)
      (fun w => hcP' w) (fun w => hderP _ (hcP' w))
    -- chain them
    have hsum : ∑ w, P.transitionMatrix z w * (P.finiteConsumption k w aP) ^ (-γ)
        ≤ ∑ w, P.transitionMatrix z w * (Q.finiteConsumption k w aQ) ^ (-γ) :=
      Finset.sum_le_sum fun w _ =>
        mul_le_mul_of_nonneg_left (rpow_neg_antitone hγ0 (hcQ' w) (hstep w))
          (P.transitionMatrix_nonneg z w)
    rw [hpi, hr, hβ] at hEQ
    have hβ0 : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
    have hchain : (P.finiteConsumption (k + 1) z (x + (f₁ - f₂))) ^ (-γ)
        ≤ (Q.finiteConsumption (k + 1) z x) ^ (-γ) := by
      refine hEP.trans (le_trans ?_ hEQ)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hR.le) hβ0
    have := le_of_rpow_neg_le hcP0 hcQ0 hγ0 hchain
    linarith

/-- **A tighter borrowing limit means more saving.** -/
theorem le_finitePolicy_of_floor_le {γ : ℝ} (hγ0 : 0 < γ)
    (hu : P.u = crraUtility γ) (huQ : Q.u = crraUtility γ)
    (hdP : P.Unbounded) (hdQ : Q.Unbounded)
    (hinc : Q.income = P.income) (hpi : Q.transitionMatrix = P.transitionMatrix)
    (hr : Q.interest = P.interest) (hβ : Q.discount = P.discount)
    (hf : f₂ ≤ f₁)
    (hcapP : ∀ j : ℕ, ∀ b ∈ Icc f₁ assetCap, ∀ w : Z, P.finitePolicy j (b, w) < assetCap)
    (hcapQ : ∀ j : ℕ, ∀ b ∈ Icc f₂ assetCap, ∀ w : Z, Q.finitePolicy j (b, w) < assetCap)
    (k : ℕ) (z : Z) {a : ℝ} (ha : a ∈ Icc f₁ assetCap) :
    Q.finitePolicy k (a, z) ≤ P.finitePolicy k (a, z) := by
  have hc := P.finiteConsumption_le_of_floor_le Q hγ0 hu huQ hdP hdQ hinc hpi hr hβ hf hcapP
    hcapQ k z ha
  have hres : Q.resources (a, z) = P.resources (a, z) := by
    simp only [resources, hinc, hr, max_eq_right ha.1, max_eq_right (le_trans hf ha.1)]
  rw [P.finiteConsumption_eq, Q.finiteConsumption_eq, hres] at hc
  linarith

end IncomeFluctuation

end LeanEconomics
