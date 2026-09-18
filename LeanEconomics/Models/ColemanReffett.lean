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

/-! ### Sufficiency: the kinked Euler equation has one solution

Li and Stachurski (2014) show the time-iteration operator is a contraction of modulus `βR` in
the marginal-utility sup-metric `ρ(σ, τ) = sup |u'(σ) - u'(τ)|`. The estimate needs no
operator: at a state where `σ` consumes strictly less than `τ`, `σ` saves strictly more, so
its saving is interior and its Euler equation holds with equality, while `τ`'s holds at least
as an inequality; subtracting, and using that `τ` rises with assets, the gap in marginal utility
today is at most `βR` times the gap tomorrow. Two solutions are therefore at distance
`ρ ≤ βR·ρ`, hence equal (`eq_of_isEulerSolution`). Since the optimal consumption function is
a solution (`isEulerSolution_consumptionFn`), every solution in the class — increasing in
assets, feasible, cap-slack, bounded away from zero — IS the optimal consumption function
(`eq_consumptionFn_of_isEulerSolution`): the sufficient direction of Sargent–Stachurski's
Prop. 8.3.13, with the borrowing kink and without the conjugacy. -/

/-- The class in which the functional Euler equation is solved. -/
structure EulerClass (σ : Z → ℝ → ℝ) (m₀ : ℝ) : Prop where
  mono : ∀ z : Z, MonotoneOn (σ z) (Icc assetFloor assetCap)
  floor_le : ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap, assetFloor ≤ P.resources (a, z) - σ z a
  slack : ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap, P.resources (a, z) - σ z a < P.maxSaving (a, z)
  pos : ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap, m₀ ≤ σ z a

/-- **The one-sided contraction estimate.** At a state where `σ` consumes strictly less than
`τ`, the marginal-utility gap today is at most `βR` times the largest gap tomorrow. -/
theorem euler_gap_le {du : ℝ → ℝ} (hanti : AntitoneOn du (Ioi (0 : ℝ))) {σ τ : Z → ℝ → ℝ}
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hσ : P.IsEulerSolution du σ) (hτ : P.IsEulerSolution du τ)
    (hσc : P.EulerClass σ m₀) (hτc : P.EulerClass τ m₀) {M : ℝ}
    (hM : ∀ z : Z, ∀ b ∈ Icc assetFloor assetCap, du (σ z b) - du (τ z b) ≤ M)
    {z : Z} {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (hlt : σ z a < τ z a) :
    du (σ z a) - du (τ z a) ≤ (P.discount : ℝ) * (1 + P.interest) * M := by
  classical
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hR : (0 : ℝ) ≤ 1 + P.interest := P.interest_gt_neg_one.le
  set A := P.resources (a, z) - σ z a with hAdef
  set B := P.resources (a, z) - τ z a with hBdef
  have hAB : B < A := by rw [hAdef, hBdef]; linarith
  have hBfl : assetFloor ≤ B := hτc.floor_le z a ha
  have hAmem : A ∈ Icc assetFloor assetCap :=
    ⟨le_trans hBfl hAB.le, le_trans (hσc.slack z a ha).le (P.maxSaving_le_assetCap _)⟩
  have hBmem : B ∈ Icc assetFloor assetCap :=
    ⟨hBfl, le_trans (hτc.slack z a ha).le (P.maxSaving_le_assetCap _)⟩
  -- `σ` is interior, so its Euler equation holds with equality
  have hσeq : du (σ z a) = P.eulerRhs du σ z A :=
    hσ.interior z a ha (lt_of_le_of_lt hBfl hAB) (hσc.slack z a ha)
  -- `τ`'s holds at least as an inequality
  have hτle : P.eulerRhs du τ z B ≤ du (τ z a) := by
    rcases eq_or_lt_of_le hBfl with h | h
    · rw [← h]; exact hτ.corner z a ha h.symm
    · exact le_of_eq (hτ.interior z a ha h (hτc.slack z a ha)).symm
  -- tomorrow: `τ` at `B` consumes at most `τ` at `A`
  have hterm : ∀ z' : Z, du (σ z' A) - du (τ z' B) ≤ M := by
    intro z'
    have h1 : τ z' B ≤ τ z' A := hτc.mono z' hBmem hAmem hAB.le
    have hpos : 0 < τ z' B := lt_of_lt_of_le hm₀ (hτc.pos z' B hBmem)
    have h2 : du (τ z' A) ≤ du (τ z' B) :=
      hanti (mem_Ioi.mpr hpos) (mem_Ioi.mpr (lt_of_lt_of_le hpos h1)) h1
    linarith [hM z' A hAmem]
  have hsum : ∑ z' : Z, P.transitionMatrix z z' * du (σ z' A)
      - ∑ z' : Z, P.transitionMatrix z z' * du (τ z' B) ≤ M := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ z' : Z, (P.transitionMatrix z z' * du (σ z' A) - P.transitionMatrix z z' * du (τ z' B))
        = ∑ z' : Z, P.transitionMatrix z z' * (du (σ z' A) - du (τ z' B)) := by
          refine Finset.sum_congr rfl fun z' _ => ?_; ring
      _ ≤ ∑ z' : Z, P.transitionMatrix z z' * M :=
          Finset.sum_le_sum fun z' _ =>
            mul_le_mul_of_nonneg_left (hterm z') (P.transitionMatrix_nonneg z z')
      _ = M := by rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]
  have := mul_le_mul_of_nonneg_left hsum (mul_nonneg hβ hR)
  unfold eulerRhs at hσeq hτle
  nlinarith

/-- **Two solutions of the kinked Euler equation in the class coincide** when `βR < 1`. -/
theorem eq_of_isEulerSolution {du : ℝ → ℝ} (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hdunn : ∀ c : ℝ, 0 < c → 0 ≤ du c)
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) {σ τ : Z → ℝ → ℝ} {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hσ : P.IsEulerSolution du σ) (hτ : P.IsEulerSolution du τ)
    (hσc : P.EulerClass σ m₀) (hτc : P.EulerClass τ m₀) :
    ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap, σ z a = τ z a := by
  classical
  have hβR0 : (0 : ℝ) ≤ (P.discount : ℝ) * (1 + P.interest) :=
    mul_nonneg P.discount.coe_nonneg P.interest_gt_neg_one.le
  have hfc : assetFloor ≤ assetCap := P.assetFloor_le_assetCap
  -- the gaps in marginal utility, and their supremum
  set S : Set ℝ :=
    {d | ∃ z : Z, ∃ a ∈ Icc assetFloor assetCap, d = |du (σ z a) - du (τ z a)|} with hSdef
  have hgap : ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap, |du (σ z a) - du (τ z a)| ≤ du m₀ := by
    intro z a ha
    have h1 := hσc.pos z a ha
    have h2 := hτc.pos z a ha
    have hp1 : 0 < σ z a := lt_of_lt_of_le hm₀ h1
    have hp2 : 0 < τ z a := lt_of_lt_of_le hm₀ h2
    have hd1 : du (σ z a) ≤ du m₀ := hanti.antitoneOn (mem_Ioi.mpr hm₀) (mem_Ioi.mpr hp1) h1
    have hd2 : du (τ z a) ≤ du m₀ := hanti.antitoneOn (mem_Ioi.mpr hm₀) (mem_Ioi.mpr hp2) h2
    have hn1 := hdunn _ hp1
    have hn2 := hdunn _ hp2
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hSne : S.Nonempty := by
    obtain ⟨z⟩ := (inferInstance : Nonempty Z)
    exact ⟨_, z, assetFloor, ⟨le_rfl, hfc⟩, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨du m₀, ?_⟩
    rintro d ⟨z, a, ha, rfl⟩
    exact hgap z a ha
  set M : ℝ := sSup S with hMdef
  have hMle : ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap, |du (σ z a) - du (τ z a)| ≤ M :=
    fun z a ha => le_csSup hSbdd ⟨z, a, ha, rfl⟩
  have hM0 : 0 ≤ M := by
    obtain ⟨z⟩ := (inferInstance : Nonempty Z)
    exact le_trans (abs_nonneg _) (hMle z assetFloor ⟨le_rfl, hfc⟩)
  -- the contraction estimate, pointwise
  have hpt : ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap,
      |du (σ z a) - du (τ z a)| ≤ (P.discount : ℝ) * (1 + P.interest) * M := by
    intro z a ha
    rcases lt_trichotomy (σ z a) (τ z a) with hlt | heq | hgt
    · have hM' : ∀ z' : Z, ∀ b ∈ Icc assetFloor assetCap, du (σ z' b) - du (τ z' b) ≤ M :=
        fun z' b hb => le_trans (le_abs_self _) (hMle z' b hb)
      have h := P.euler_gap_le hanti.antitoneOn hm₀ hσ hτ hσc hτc hM' ha hlt
      have hp1 : 0 < σ z a := lt_of_lt_of_le hm₀ (hσc.pos z a ha)
      have hp2 : 0 < τ z a := lt_of_lt_of_le hm₀ (hτc.pos z a ha)
      have hpos : 0 < du (σ z a) - du (τ z a) :=
        sub_pos.mpr (hanti (mem_Ioi.mpr hp1) (mem_Ioi.mpr hp2) hlt)
      rw [abs_of_pos hpos]; exact h
    · rw [heq, sub_self, abs_zero]; exact mul_nonneg hβR0 hM0
    · have hM' : ∀ z' : Z, ∀ b ∈ Icc assetFloor assetCap, du (τ z' b) - du (σ z' b) ≤ M :=
        fun z' b hb => le_trans (neg_le_abs _ |>.trans_eq' (by ring)) (hMle z' b hb)
      have h := P.euler_gap_le hanti.antitoneOn hm₀ hτ hσ hτc hσc hM' ha hgt
      have hp1 : 0 < σ z a := lt_of_lt_of_le hm₀ (hσc.pos z a ha)
      have hp2 : 0 < τ z a := lt_of_lt_of_le hm₀ (hτc.pos z a ha)
      have hpos : 0 < du (τ z a) - du (σ z a) :=
        sub_pos.mpr (hanti (mem_Ioi.mpr hp2) (mem_Ioi.mpr hp1) hgt)
      rw [abs_sub_comm, abs_of_pos hpos]; exact h
  have hMM : M ≤ (P.discount : ℝ) * (1 + P.interest) * M := by
    refine csSup_le hSne ?_
    rintro d ⟨z, a, ha, rfl⟩
    exact hpt z a ha
  have hMzero : M = 0 := by nlinarith
  intro z a ha
  have h0 : |du (σ z a) - du (τ z a)| = 0 :=
    le_antisymm (hMzero ▸ hMle z a ha) (abs_nonneg _)
  have hp1 : 0 < σ z a := lt_of_lt_of_le hm₀ (hσc.pos z a ha)
  have hp2 : 0 < τ z a := lt_of_lt_of_le hm₀ (hτc.pos z a ha)
  exact hanti.injOn (mem_Ioi.mpr hp1) (mem_Ioi.mpr hp2) (sub_eq_zero.mp (abs_eq_zero.mp h0))

/-- **The optimal consumption function is in the class**, given cap slack and a positive
floor on consumption. -/
theorem eulerClass_consumptionFn (hpc : P.PositiveConsumption)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s < assetCap)
    {m₀ : ℝ} (hpos : ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap, m₀ ≤ P.consumptionFn z a) :
    P.EulerClass P.consumptionFn m₀ where
  mono := fun z a ha a' ha' hle => P.consumptionFn_mono ha ha' hle
  floor_le := fun z a _ => by rw [P.resources_sub_consumptionFn]; exact (P.policy_mem_region _).1
  slack := fun z a ha => by
    rw [P.resources_sub_consumptionFn, maxSaving_eq]
    refine lt_min (hslack _ ha) ?_
    have := P.consumptionFn_pos hpc ha z
    simp only [consumptionFn, consumption] at this
    linarith
  pos := hpos

/-- **A solution of the kinked functional Euler equation is the optimal consumption
function** — the sufficient direction, without conjugacy. -/
theorem eq_consumptionFn_of_isEulerSolution {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ))) (hdunn : ∀ c : ℝ, 0 < c → 0 ≤ du c)
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hpc : P.PositiveConsumption)
    (hfc : assetFloor < assetCap)
    (hslack : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s < assetCap)
    {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hpos : ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap, m₀ ≤ P.consumptionFn z a)
    {σ : Z → ℝ → ℝ} (hσ : P.IsEulerSolution du σ) (hσc : P.EulerClass σ m₀) :
    ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap, σ z a = P.consumptionFn z a :=
  P.eq_of_isEulerSolution hanti hdunn hβR hm₀ hσ
    (P.isEulerSolution_consumptionFn hderiv hpc hfc hslack) hσc
    (P.eulerClass_consumptionFn hpc hslack hpos)

end IncomeFluctuation

end LeanEconomics
