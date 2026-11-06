/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.MinMPCSmallShare

/-!
# Exactly one equilibrium without the Krusell–Smith employment design

The uniqueness theorems of `EmploymentMarginals.lean` and `MinMPCSmallShare.lean` use the
Krusell–Smith design only to give two equilibria the same employment marginal at every history.
That needs much less: the marginals of every sequence-state equilibrium move by the same exogenous
chain (`IsSeqStateEquilibrium.initMass_cons`), so if every transition probability is at least
`ε > 0` the gap between two equilibria's marginals shrinks by `1 − |E| ε` each period back, and
over an infinite past it is zero (`IsSeqStateEquilibrium.initMass_eq_of_minor`). The marginals may
depend on the whole history.

* **`minor_smallShare_existsUnique_seqStateEquilibrium`**: CRRA, clamped Cobb–Douglas, `δ > 0`,
  transitions bounded below: exactly one sequence-state equilibrium for small shares;
* **`minor_minMPC_smallShare_existsUnique_seqStateEquilibrium`**: the same for `0 ≤ δ < 1` with
  `(β (1 − δ))^{1/γ} < 1 − δ`, and **`minor_zeroDepreciation_…`** at `δ = 0`.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} {μ μ' : History Z → ProbabilityMeasure M.AState}

/-- **Two sequence-state equilibria have the same employment marginals at every history**, when
every transition probability is at least `ε > 0`. -/
theorem IsSeqStateEquilibrium.initMass_eq_of_minor (hμ : M.IsSeqStateEquilibrium μ)
    (hμ' : M.IsSeqStateEquilibrium μ') {ε : ℝ} (hε : 0 < ε)
    (hminor : ∀ z z' e e', ε ≤ M.idioProb z z' e e') (ω : History Z) :
    M.initMass (μ ω : Measure M.AState) = M.initMass (μ' ω : Measure M.AState) := by
  funext e₀
  have hE : 0 < (Fintype.card E : ℝ) := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨e₀⟩)
  set c := 1 - Fintype.card E * ε
  have hc0 : 0 ≤ c := by
    have h1 := M.idioProb_sum (ω 0) (ω 0) e₀
    have h2 : ∑ e' : E, ε ≤ ∑ e', M.idioProb (ω 0) (ω 0) e₀ e' :=
      Finset.sum_le_sum fun e' _ => hminor _ _ _ _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h1] at h2
    simp only [c]
    linarith
  have hc1 : c < 1 := by
    have := mul_pos hE hε
    simp only [c]
    linarith
  have hiter : ∀ (T : ℕ) (ω : History Z),
      ∑ e, |M.initMass (μ ω : Measure M.AState) e - M.initMass (μ' ω : Measure M.AState) e|
        ≤ c ^ T * 2 := by
    intro T
    induction T with
    | zero =>
      intro ω
      rw [pow_zero, one_mul]
      calc _ ≤ ∑ e, (M.initMass (μ ω : Measure M.AState) e
            + M.initMass (μ' ω : Measure M.AState) e) := by
            refine Finset.sum_le_sum fun e _ => ?_
            have h1 := M.initMass_nonneg (μ ω : Measure M.AState) e
            have h2 := M.initMass_nonneg (μ' ω : Measure M.AState) e
            rw [abs_le]
            constructor <;> linarith
        _ = 2 := by
            rw [Finset.sum_add_distrib, M.sum_initMass, M.sum_initMass]
            norm_num
    | succ T ih =>
      intro ω
      set d : E → ℝ := fun e =>
        M.initMass (μ (History.tail ω) : Measure M.AState) e
          - M.initMass (μ' (History.tail ω) : Measure M.AState) e
      have hd : ∑ e, d e = 0 := by
        simp only [d, Finset.sum_sub_distrib, M.sum_initMass, sub_self]
      have e1 : ∀ e', M.initMass (μ ω : Measure M.AState) e'
          - M.initMass (μ' ω : Measure M.AState) e'
          = ∑ e, d e * M.idioProb (ω 1) (ω 0) e e' := by
        intro e'
        have h1 := hμ.initMass_cons (History.tail ω) (ω 0) e'
        have h2 := hμ'.initMass_cons (History.tail ω) (ω 0) e'
        rw [History.cons_head_tail] at h1 h2
        rw [h1, h2, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [d, sub_mul]
        rfl
      have hk := sum_abs_mul_le (fun e e' => hminor (ω 1) (ω 0) e e')
        (M.idioProb_sum (ω 1) (ω 0)) hd
      simp_rw [e1]
      calc _ ≤ c * ∑ e, |d e| := hk
        _ ≤ c * (c ^ T * 2) := mul_le_mul_of_nonneg_left (ih (History.tail ω)) hc0
        _ = c ^ (T + 1) * 2 := by ring
  have hlim : Tendsto (fun T : ℕ => c ^ T * 2) atTop (𝓝 (0 * 2)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul tendsto_const_nhds
  rw [zero_mul] at hlim
  have h0 := ge_of_tendsto' hlim fun T => hiter T ω
  have hterm : |M.initMass (μ ω : Measure M.AState) e₀ - M.initMass (μ' ω : Measure M.AState) e₀|
      ≤ 0 :=
    (Finset.single_le_sum (fun e _ => abs_nonneg
      (M.initMass (μ ω : Measure M.AState) e - M.initMass (μ' ω : Measure M.AState) e))
      (Finset.mem_univ e₀)).trans h0
  exact sub_eq_zero.1 (abs_nonpos_iff.1 hterm)

end KSModel

variable [Nonempty Z] [Nonempty E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ}
  (hγ : 0 < γ) {ε : ℝ} (hε : 0 < ε) (hminor : ∀ z z' e e', ε ≤ V.idioProb z z' e e')
include hε hminor

/-- **Exactly one sequence-state equilibrium for small capital shares** (`δ > 0`), with
transitions bounded below and marginals free to depend on the history. -/
theorem minor_smallShare_existsUnique_seqStateEquilibrium (hδ : 0 < T.depreciation) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃! μ : History Z → ProbabilityMeasure (crraModel V (T.withShare α h0 hα) hγ).AState,
        (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ := by
  obtain ⟨α₀, hα₀, h⟩ := smallShare_contraction V T hγ hδ
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, -, H, hκ, hr⟩ := h α h0 hα
  refine ⟨h1, ?_⟩
  obtain ⟨μ, hμ⟩ := (crraModel V (T.withShare α h0 h1) hγ).exists_seqStateEquilibrium
  refine ⟨μ, hμ, fun μ' hμ' => ?_⟩
  exact (hμ.eq_of_lawRate_lt_one H hκ hr hμ'
    (hμ.initMass_eq_of_minor hμ' hε hminor)).symm

/-- **Exactly one sequence-state equilibrium for small capital shares**, minimal-MPC version:
`0 ≤ δ < 1` with `(β (1 − δ))^{1/γ} < 1 − δ`, transitions bounded below. -/
theorem minor_minMPC_smallShare_existsUnique_seqStateEquilibrium (hδ1 : T.depreciation < 1)
    (hgap : (V.discount * (1 - T.depreciation)) ^ (1 / γ) < 1 - T.depreciation) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃! μ : History Z → ProbabilityMeasure (crraModel V (T.withShare α h0 hα) hγ).AState,
        (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ := by
  obtain ⟨α₀, hα₀, h⟩ := minMPC_smallShare V T hγ hδ1 hgap
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, S, hκ, hr⟩ := h α h0 hα
  refine ⟨h1, ?_⟩
  obtain ⟨μ, hμ⟩ := (crraModel V (T.withShare α h0 h1) hγ).exists_seqStateEquilibrium
  refine ⟨μ, hμ, fun μ' hμ' => ?_⟩
  exact (S.eq_of_rate_lt_one hκ hμ hr hμ' (hμ.initMass_eq_of_minor hμ' hε hminor)).symm

/-- **Zero depreciation**, transitions bounded below: exactly one sequence-state equilibrium for
small capital shares. -/
theorem minor_zeroDepreciation_smallShare_existsUnique_seqStateEquilibrium
    (hδ : T.depreciation = 0) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃! μ : History Z → ProbabilityMeasure (crraModel V (T.withShare α h0 hα) hγ).AState,
        (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ := by
  refine minor_minMPC_smallShare_existsUnique_seqStateEquilibrium V T hγ hε hminor
    (by rw [hδ]; norm_num) ?_
  rw [hδ, sub_zero, mul_one]
  exact Real.rpow_lt_one V.discount_pos.le V.discount_lt_one (by positivity)

end KrusellSmith

end LeanEconomics
