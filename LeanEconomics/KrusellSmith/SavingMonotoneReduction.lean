/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.GreatestEquilibrium

/-!
# What "savings rise with capital" requires of the household problem

Milestone MR4a of `MINIMAL_STATE_PLAN.md`. The hypothesis `SavingMonotone` of
`GreatestEquilibrium.lean` (along a higher capital path every household saves more) is reduced
to a property of value functions alone, plus two properties of prices.

At a state, the household's problem depends on the path only through cash on hand and through the
continuation value of saving (`cont`). So:

* `policy_le_policy` (Topkis): **more cash and a continuation with increasing differences give
  more saving.** The swap argument of `policy_mono`: if the household with more cash and the
  steeper continuation saved strictly less, each could take the other's saving; concavity of
  utility and increasing differences of the continuation make the poorer one indifferent, and
  uniqueness of the optimal saving (`eq_policy_of_objective`) gives a contradiction.
* `cont_increasingDifferences`: increasing differences of the value function at every child
  give increasing differences of the continuation (the shock probabilities do not depend on
  saving).
* **`savingMonotone_of`**: if the **wage does not depend on capital**, the **return is
  nondecreasing in capital**, and value functions have **increasing differences across higher
  capital paths** (`ValueIncreasingDifferences`), then `SavingMonotone` holds, hence (MR3) a
  recursive equilibrium on the minimal state exists without uniqueness.

`ValueIncreasingDifferences` is what remains to prove (MR4b–c, Light's step on the tree: relative
risk aversion at most one, Carroll–Kimball concavity, the asset cap slack). It fails with an
asset cap that binds next period (see the plan), and the price conditions fail with
Cobb–Douglas.
-/

open Set

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z)

/-- **More cash and a steeper continuation give more saving** (Topkis). -/
theorem policy_le_policy {P P' : List Z → ℝ × ℝ} (s : M.State)
    (hcash : M.cash z₀ P s ≤ M.cash z₀ P' s)
    (hid : ∀ x y, x ∈ Icc 0 M.assetCap → y ∈ Icc 0 M.assetCap → x ≤ y →
      M.cont z₀ P s y - M.cont z₀ P s x ≤ M.cont z₀ P' s y - M.cont z₀ P' s x) :
    M.policy z₀ P s ≤ M.policy z₀ P' s := by
  set p := M.policy z₀ P s
  set p' := M.policy z₀ P' s
  set x := M.cash z₀ P s
  set x' := M.cash z₀ P' s
  by_contra hlt
  rw [not_le] at hlt
  have hp := M.policy_mem z₀ P s
  have hp' := M.policy_mem z₀ P' s
  have hpx : p ≤ x - M.consFloor := hp.2.trans (min_le_right _ _)
  -- each could take the other's saving
  have hf' : p' ∈ (M.household z₀ P).feasible s := ⟨hp'.1, hlt.le.trans hp.2⟩
  have hf : p ∈ (M.household z₀ P').feasible s :=
    ⟨hp.1, le_min (hp.2.trans (min_le_left _ _)) (by
      change p ≤ x' - M.consFloor
      linarith)⟩
  have h2 := M.le_valueFunction z₀ P' hf
  have v1 : (M.household z₀ P).valueFunction s = M.utility (x - p) + M.discount * M.cont z₀ P s p :=
    M.valueFunction_eq_cont z₀ P s
  have v2 : (M.household z₀ P').valueFunction s
      = M.utility (x' - p') + M.discount * M.cont z₀ P' s p' :=
    M.valueFunction_eq_cont z₀ P' s
  have hid' := hid p' p (M.mem_Icc_of_mem_feasible z₀ P' (M.policy_mem z₀ P' s))
    (M.mem_Icc_of_mem_feasible z₀ P (M.policy_mem z₀ P s)) hlt.le
  have hβ := mul_le_mul_of_nonneg_left hid' M.discount_pos.le
  rw [mul_sub, mul_sub] at hβ
  -- increasing differences of utility, from concavity
  have hcf : M.consFloor ≤ x - p := by linarith
  have hu := concave_increment_le M.strictConcaveOn_utility.concaveOn
    (x := x - p) (y := x' - p) (d := p - p') (by linarith) (by linarith) (mem_Ici.2 hcf)
    (mem_Ici.2 (by linarith))
  have e1 : x' - p + (p - p') = x' - p' := by ring
  have e2 : x - p + (p - p') = x - p' := by ring
  rw [e1, e2] at hu
  -- the household with less cash is indifferent to the other's saving
  have htie : M.utility (x - p') + M.discount * M.cont z₀ P s p'
      = (M.household z₀ P).valueFunction s := by
    have h1 := M.le_valueFunction z₀ P hf'
    linarith
  exact absurd (M.eq_policy_of_objective z₀ P hf' htie) hlt.ne

/-- Increasing differences of the value at every child give increasing differences of the
continuation. -/
theorem cont_increasingDifferences {P P' : List Z → ℝ × ℝ} (s : M.State)
    (hV : ∀ (l : Label Z E) (x y : ℝ), x ∈ Icc 0 M.assetCap → y ∈ Icc 0 M.assetCap → x ≤ y →
      (M.household z₀ P).valueFunction (M.stateAt y l)
          - (M.household z₀ P).valueFunction (M.stateAt x l)
        ≤ (M.household z₀ P').valueFunction (M.stateAt y l)
          - (M.household z₀ P').valueFunction (M.stateAt x l))
    (x y : ℝ) (hx : x ∈ Icc 0 M.assetCap) (hy : y ∈ Icc 0 M.assetCap) (hxy : x ≤ y) :
    M.cont z₀ P s y - M.cont z₀ P s x ≤ M.cont z₀ P' s y - M.cont z₀ P' s x := by
  simp only [cont]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun ze _ => ?_
  have hp := M.shockProb_nonneg' z₀ ze (s, x)
  change M.shockProb z₀ ze (s, x) * _ - M.shockProb z₀ ze (s, x) * _
    ≤ M.shockProb z₀ ze (s, x) * _ - M.shockProb z₀ ze (s, x) * _
  rw [← mul_sub, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (hV _ x y hx hy hxy) hp

/-- **The wage does not depend on capital.** -/
def WageIndependent : Prop := ∀ (z : Z) (K K' L : ℝ), M.wage z K L = M.wage z K' L

/-- **The return is nondecreasing in capital** (complementarity). -/
def ReturnMonotone : Prop :=
  ∀ (z : Z) (K K' L : ℝ), K ≤ K' → M.grossReturn z K L ≤ M.grossReturn z K' L

/-- **Value functions have increasing differences across higher capital paths**: along a
pointwise higher path of capital, with the same labour, the value gains more from extra assets,
at every label. -/
def ValueIncreasingDifferences : Prop :=
  ∀ (z : Z) (m₀ : E → ℝ) (K K' : List Z → ℝ), (∀ h, K h ≤ K' h) →
    ∀ (l : Label Z E) (x y : ℝ), x ∈ Icc 0 M.assetCap → y ∈ Icc 0 M.assetCap → x ≤ y →
      (M.household z (M.pricePath z m₀ K)).valueFunction (M.stateAt y l)
          - (M.household z (M.pricePath z m₀ K)).valueFunction (M.stateAt x l)
        ≤ (M.household z (M.pricePath z m₀ K')).valueFunction (M.stateAt y l)
          - (M.household z (M.pricePath z m₀ K')).valueFunction (M.stateAt x l)

variable {M}

/-- **Reduction of `SavingMonotone`**: a wage independent of capital, a return nondecreasing in
capital, no borrowing (a higher return hurts debtors), and value functions with increasing
differences across higher capital paths give
"savings rise with capital", hence (`SavingMonotone.isRecursive`) a recursive equilibrium on the
minimal state without uniqueness. -/
theorem savingMonotone_of (hw : M.WageIndependent) (hR : M.ReturnMonotone)
    (hb : M.borrowLimit = 0) (hV : M.ValueIncreasingDifferences) : M.SavingMonotone := by
  intro z m₀ K K' hKK' s
  refine M.policy_le_policy z s ?_ (M.cont_increasingDifferences z s (hV z m₀ K K' hKK'))
  simp only [cash, returnAt, wageAt, pricePath, hb, mul_zero, sub_zero]
  rw [hw (shockAt z s.2.node) (K s.2.node) (K' s.2.node)]
  have := hR (shockAt z s.2.node) _ _ (M.labour z m₀ s.2.node) (hKK' s.2.node)
  have ha : (0 : ℝ) ≤ s.1 := s.1.2.1
  nlinarith

end KSModel

end KrusellSmith

end LeanEconomics
