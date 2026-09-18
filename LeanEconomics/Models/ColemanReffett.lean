/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Models.IncomeFluctuationEuler
import LeanEconomics.Models.IncomeFluctuationConsumption

/-!
# The functional Euler equation, with kinks

Sargent and Stachurski (Vol. 2, §8.3.3–8.3.4) solve the growth model in policy space: the
Coleman–Reffett operator `K` maps a consumption function `σ` to the consumption function that
solves the Euler equation against `σ` tomorrow, `K` is order preserving, and `K` is conjugate to
the Bellman operator through `v ↦ (u')⁻¹ ∘ v'`, so a policy is optimal if and only if it solves
the functional Euler equation. Their setting has interior policies; the income fluctuation
problem does not, so the equation carries the borrowing constraint as an inequality.

This file records the two halves of that programme that the development already pays for.
`IsEulerSolution` is the functional Euler equation with the kink: equality where saving is
interior, the inequality `βR E u'(c') ≤ u'(c)` at the borrowing limit. The optimal consumption
function satisfies it (`isEulerSolution_consumptionFn`) — the necessary direction, from
`euler_eq` and `euler_le` — and the Euler root is monotone in the continuation consumption
function (`euler_root_le`, `eulerRhs_mono`, `eulerRhs_anti_of_le`), which is what makes `K`
order preserving. The sufficient direction — a solution of the functional Euler equation is
optimal — is the conjugacy argument and is not formalised here; the reduction of Theorem 1 to
Euler inequalities in `Equilibrium/ElasticityReduction` uses only the necessary direction.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **Tomorrow's expected discounted marginal utility** when consumption tomorrow follows `σ`
and saving today is `A`: the right-hand side of the Euler equation. -/
noncomputable def eulerRhs (du : ℝ → ℝ) (σ : Z → ℝ → ℝ) (z : Z) (A : ℝ) : ℝ :=
  (P.discount : ℝ) * ((1 + P.interest) * ∑ z' : Z, P.transitionMatrix z z' * du (σ z' A))

/-- **The functional Euler equation with the borrowing kink.** Equality where saving is
strictly between the floor and the feasible maximum; the deviation inequality at the floor. -/
structure IsEulerSolution (du : ℝ → ℝ) (σ : Z → ℝ → ℝ) : Prop where
  interior : ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap,
    assetFloor < P.resources (a, z) - σ z a →
      P.resources (a, z) - σ z a < P.maxSaving (a, z) →
        du (σ z a) = P.eulerRhs du σ z (P.resources (a, z) - σ z a)
  corner : ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap,
    P.resources (a, z) - σ z a = assetFloor → P.eulerRhs du σ z assetFloor ≤ du (σ z a)

theorem resources_sub_consumptionFn (z : Z) (a : ℝ) :
    P.resources (a, z) - P.consumptionFn z a = P.policy (a, z) := by
  simp only [consumptionFn, consumption]; ring

/-- **The optimal consumption function solves the functional Euler equation**, given positive
consumption and a slack cap. The necessary direction of Sargent–Stachurski's Prop. 8.3.13. -/
theorem isEulerSolution_consumptionFn {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c) (hpc : P.PositiveConsumption)
    (hfc : assetFloor < assetCap)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s < assetCap) :
    P.IsEulerSolution du P.consumptionFn := by
  have hbv := P.toExtended.bellman_valueFunction
  have hpol : ∀ s : ℝ × Z, P.policyOf P.toExtended.valueFunction s = P.policy s :=
    fun s => congrFun P.policyOf_valueFunction s
  -- next period: positivity and slack at the chosen saving
  have hnext : ∀ (A : ℝ), A ∈ Icc assetFloor assetCap →
      (∀ z' : Z, 0 < P.consumptionFn z' A) ∧
      (∀ z' : Z, P.policyOf P.toExtended.valueFunction (A, z') < P.maxSaving (A, z')) := by
    intro A hA
    refine ⟨fun z' => P.consumptionFn_pos hpc hA z', fun z' => ?_⟩
    rw [hpol, maxSaving_eq]
    refine lt_min (hslack _ hA) ?_
    have := P.consumptionFn_pos hpc hA z'
    simp only [consumptionFn, consumption] at this
    linarith
  constructor
  · intro z a ha hA0 hAmax
    rw [P.resources_sub_consumptionFn] at hA0 hAmax ⊢
    have hAmem : P.policy (a, z) ∈ Icc assetFloor assetCap := P.policy_mem_region _
    obtain ⟨hc', hsl⟩ := hnext _ hAmem
    have hc : 0 < P.consumptionFn z a := P.consumptionFn_pos hpc ha z
    have := P.euler_eq (v := P.toExtended.valueFunction) (z := z) (a := a)
      (A := P.policy (a, z)) (du := du (P.consumptionFn z a))
      (du' := fun z' => du (P.consumptionFn z' (P.policy (a, z))))
      ha (by rw [hbv]; exact hpol _) hA0 hAmax hsl (by rw [hbv]; exact hc)
      (by rw [hbv]; exact hderiv _ hc) (fun z' => hc' z') (fun z' => hderiv _ (hc' z'))
    exact this
  · intro z a ha hA
    rw [P.resources_sub_consumptionFn] at hA
    have hAmem : P.policy (a, z) ∈ Icc assetFloor assetCap := P.policy_mem_region _
    obtain ⟨hc', -⟩ := hnext _ hAmem
    have hc : 0 < P.consumptionFn z a := P.consumptionFn_pos hpc ha z
    have hroom : P.policy (a, z) < P.maxSaving (a, z) := by
      rw [maxSaving_eq, hA]
      refine lt_min hfc ?_
      have := hc
      simp only [consumptionFn, consumption] at this
      linarith
    have := P.euler_le (v := P.toExtended.valueFunction) (z := z) (a := a)
      (A := P.policy (a, z)) (du := du (P.consumptionFn z a))
      (du' := fun z' => du (P.consumptionFn z' (P.policy (a, z))))
      ha (by rw [hbv]; exact hpol _) hroom (by rw [hbv]; exact hc)
      (by rw [hbv]; exact hderiv _ hc) (fun z' => hc' z') (fun z' => hderiv _ (hc' z'))
    rw [hA] at this
    exact this

/-! ### Order preservation of the Euler root -/

omit [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z] in
/-- **The Euler root is monotone in the right-hand side.** If `du` is strictly decreasing, `F`
is nondecreasing and `F' ≤ F`, then the roots of `du c = F c` and `du c' = F' c'` satisfy
`c ≤ c'`. -/
theorem euler_root_le {du F F' : ℝ → ℝ} {c c' : ℝ} (hdu : StrictAntiOn du (Ioi (0 : ℝ)))
    (hc : 0 < c) (hc' : 0 < c') (hF : MonotoneOn F (Ioi (0 : ℝ)))
    (hFF' : ∀ x ∈ Ioi (0 : ℝ), F' x ≤ F x) (hroot : du c = F c) (hroot' : du c' = F' c') :
    c ≤ c' := by
  by_contra h
  push Not at h
  have h1 : du c < du c' := hdu (mem_Ioi.mpr hc') (mem_Ioi.mpr hc) h
  have h2 : F c' ≤ F c := hF (mem_Ioi.mpr hc') (mem_Ioi.mpr hc) h.le
  have h3 : F' c' ≤ F c' := hFF' c' (mem_Ioi.mpr hc')
  linarith

/-- The right-hand side rises with consumption today (less is saved, so tomorrow's marginal
utility is higher) when tomorrow's consumption rises with assets. -/
theorem eulerRhs_mono {du : ℝ → ℝ} (hdu : AntitoneOn du (Ioi (0 : ℝ))) {σ : Z → ℝ → ℝ}
    (hσpos : ∀ z, ∀ A ∈ Icc assetFloor assetCap, 0 < σ z A)
    (hσ : ∀ z, MonotoneOn (σ z) (Icc assetFloor assetCap)) (z : Z) {A A' : ℝ}
    (hA : A ∈ Icc assetFloor assetCap) (hA' : A' ∈ Icc assetFloor assetCap) (hle : A' ≤ A) :
    P.eulerRhs du σ z A ≤ P.eulerRhs du σ z A' := by
  unfold eulerRhs
  have hR : (0 : ℝ) ≤ 1 + P.interest := P.interest_gt_neg_one.le
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hR) P.discount.coe_nonneg
  refine Finset.sum_le_sum fun z' _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (P.transitionMatrix_nonneg z z')
  exact hdu (mem_Ioi.mpr (hσpos z' A' hA')) (mem_Ioi.mpr (hσpos z' A hA)) (hσ z' hA' hA hle)

/-- A larger continuation consumption function gives a smaller right-hand side. -/
theorem eulerRhs_anti_of_le {du : ℝ → ℝ} (hdu : AntitoneOn du (Ioi (0 : ℝ)))
    {σ σ' : Z → ℝ → ℝ} (hσpos : ∀ z, ∀ A ∈ Icc assetFloor assetCap, 0 < σ z A)
    (hle : ∀ z, ∀ A ∈ Icc assetFloor assetCap, σ z A ≤ σ' z A) (z : Z) {A : ℝ}
    (hA : A ∈ Icc assetFloor assetCap) :
    P.eulerRhs du σ' z A ≤ P.eulerRhs du σ z A := by
  unfold eulerRhs
  have hR : (0 : ℝ) ≤ 1 + P.interest := P.interest_gt_neg_one.le
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hR) P.discount.coe_nonneg
  refine Finset.sum_le_sum fun z' _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (P.transitionMatrix_nonneg z z')
  have hpos := hσpos z' A hA
  exact hdu (mem_Ioi.mpr hpos) (mem_Ioi.mpr (lt_of_lt_of_le hpos (hle z' A hA))) (hle z' A hA)

end IncomeFluctuation

end LeanEconomics
