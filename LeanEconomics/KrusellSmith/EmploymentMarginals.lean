/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.SmallShare

/-!
# Employment marginals are pinned down by today's shock; exactly one equilibrium

Krusell and Smith design the employment process so that the unemployment rate is a function of
the aggregate shock alone: a family `m z` of employment marginals that the transitions carry into
each other, `∑ e, m z e · π(e' | e, z, z') = m z' e'` (`EmploymentDesign`). With every transition
probability at least `ε > 0` (a Doeblin minorisation), the employment chain forgets its start at
rate `c = 1 − |E| ε` in `ℓ¹` (`sum_abs_mul_le`).

* `IsSeqStateEquilibrium.initMass_eq_design`: in **every** sequence-state equilibrium, the
  employment marginal at the history `ω` is `m (ω 0)`. The marginals move exogenously, so their
  gap to the design shrinks by `c` each period back; over an infinite past it is zero.

This discharges the marginal hypothesis of `LawContraction.lean`, so for small capital shares
(`SmallShare.lean`):

* `smallShare_existsUnique_seqStateEquilibrium`: for CRRA utility and clamped Cobb–Douglas
  prices with depreciation `δ > 0`, under the Krusell–Smith employment design, there is a share
  `α₀ > 0` below which **there is exactly one sequence-state equilibrium**. It is the Markov
  equilibrium on `(z, μ)`, forgets old shocks at a geometric rate, and matched expectations are
  within an explicit bound of it (`LawContraction.lean`).
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

/-- **The Krusell–Smith employment design**: a family of employment marginals, one per aggregate
shock, carried into each other by the transitions, with every transition probability at least
`ε > 0`. -/
structure EmploymentDesign (P : Z → Z → E → E → ℝ) where
  m : Z → E → ℝ
  m_nonneg : ∀ z e, 0 ≤ m z e
  sum_m : ∀ z, ∑ e, m z e = 1
  consistent : ∀ z z' e', ∑ e, m z e * P z z' e e' = m z' e'
  ε : ℝ
  ε_pos : 0 < ε
  minor : ∀ z z' e e', ε ≤ P z z' e e'

/-- **Doeblin contraction in `ℓ¹`**: a zero-sum vector shrinks by `1 − |E| ε` under a stochastic
matrix with entries at least `ε`. -/
theorem sum_abs_mul_le {P : E → E → ℝ} {ε : ℝ} (hP : ∀ e e', ε ≤ P e e')
    (hsum : ∀ e, ∑ e', P e e' = 1) {d : E → ℝ} (hd : ∑ e, d e = 0) :
    ∑ e', |∑ e, d e * P e e'| ≤ (1 - Fintype.card E * ε) * ∑ e, |d e| := by
  have h1 : ∀ e', ∑ e, d e * P e e' = ∑ e, d e * (P e e' - ε) := by
    intro e'
    have : ∑ e, d e * ε = 0 := by rw [← Finset.sum_mul, hd, zero_mul]
    simp only [mul_sub, Finset.sum_sub_distrib, this, sub_zero]
  have h2 : ∀ e', |∑ e, d e * P e e'| ≤ ∑ e, |d e| * (P e e' - ε) := by
    intro e'
    rw [h1 e']
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hP e e'))]
  calc _ ≤ ∑ e', ∑ e, |d e| * (P e e' - ε) := Finset.sum_le_sum fun e' _ => h2 e'
    _ = ∑ e, |d e| * ∑ e', (P e e' - ε) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
    _ = ∑ e, |d e| * (1 - Fintype.card E * ε) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_sub_distrib, hsum e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (1 - Fintype.card E * ε) * ∑ e, |d e| := by rw [← Finset.sum_mul, mul_comm]

namespace KSModel

variable {M : KSModel Z E} {μ : History Z → ProbabilityMeasure M.AState}

/-- **The employment marginals move exogenously**: tomorrow's is today's, carried by the
transition. -/
theorem IsSeqStateEquilibrium.initMass_cons (hμ : M.IsSeqStateEquilibrium μ) (ω : History Z)
    (z' : Z) (e' : E) :
    M.initMass (μ (History.cons z' ω) : Measure M.AState) e'
      = ∑ e, M.initMass (μ ω : Measure M.AState) e * M.idioProb (ω 0) z' e e' := by
  have h := hμ.nodeDist_eq ω [z']
  rw [History.prepend_singleton] at h
  rw [← h, M.initMass_nodeDist (ω 0) (μ ω : Measure M.AState) _ [z']]
  rfl

/-- **In every sequence-state equilibrium, the employment marginal is the design's**, `m (ω 0)`. -/
theorem IsSeqStateEquilibrium.initMass_eq_design (hμ : M.IsSeqStateEquilibrium μ)
    (D : EmploymentDesign M.idioProb) (ω : History Z) :
    M.initMass (μ ω : Measure M.AState) = D.m (ω 0) := by
  funext e₀
  have hE : 0 < (Fintype.card E : ℝ) := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨e₀⟩)
  set c := 1 - Fintype.card E * D.ε
  have hc0 : 0 ≤ c := by
    have h1 := M.idioProb_sum (ω 0) (ω 0) e₀
    have h2 : ∑ e' : E, D.ε ≤ ∑ e', M.idioProb (ω 0) (ω 0) e₀ e' :=
      Finset.sum_le_sum fun e' _ => D.minor _ _ _ _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h1] at h2
    simp only [c]
    linarith
  have hc1 : c < 1 := by
    have := mul_pos hE D.ε_pos
    simp only [c]
    linarith
  have hiter : ∀ (T : ℕ) (ω : History Z),
      ∑ e, |M.initMass (μ ω : Measure M.AState) e - D.m (ω 0) e| ≤ c ^ T * 2 := by
    intro T
    induction T with
    | zero =>
      intro ω
      rw [pow_zero, one_mul]
      calc _ ≤ ∑ e, (M.initMass (μ ω : Measure M.AState) e + D.m (ω 0) e) := by
            refine Finset.sum_le_sum fun e _ => ?_
            have h1 := M.initMass_nonneg (μ ω : Measure M.AState) e
            have h2 := D.m_nonneg (ω 0) e
            rw [abs_le]
            constructor <;> linarith
        _ = 2 := by
            rw [Finset.sum_add_distrib, M.sum_initMass, D.sum_m]
            norm_num
    | succ T ih =>
      intro ω
      set d : E → ℝ := fun e =>
        M.initMass (μ (History.tail ω) : Measure M.AState) e - D.m (ω 1) e
      have hd : ∑ e, d e = 0 := by
        simp only [d, Finset.sum_sub_distrib, M.sum_initMass, D.sum_m, sub_self]
      have e1 : ∀ e', M.initMass (μ ω : Measure M.AState) e' - D.m (ω 0) e'
          = ∑ e, d e * M.idioProb (ω 1) (ω 0) e e' := by
        intro e'
        have h1 := hμ.initMass_cons (History.tail ω) (ω 0) e'
        rw [History.cons_head_tail] at h1
        rw [h1, ← D.consistent (ω 1) (ω 0) e', ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [d, sub_mul]
        rfl
      have hk := sum_abs_mul_le (fun e e' => D.minor (ω 1) (ω 0) e e')
        (M.idioProb_sum (ω 1) (ω 0)) hd
      simp_rw [e1]
      calc _ ≤ c * ∑ e, |d e| := hk
        _ ≤ c * (c ^ T * 2) := mul_le_mul_of_nonneg_left (ih (History.tail ω)) hc0
        _ = c ^ (T + 1) * 2 := by ring
  have hlim : Tendsto (fun T : ℕ => c ^ T * 2) atTop (𝓝 (0 * 2)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul tendsto_const_nhds
  rw [zero_mul] at hlim
  have h0 := ge_of_tendsto' hlim fun T => hiter T ω
  have hterm : |M.initMass (μ ω : Measure M.AState) e₀ - D.m (ω 0) e₀| ≤ 0 :=
    (Finset.single_le_sum (fun e _ => abs_nonneg
      (M.initMass (μ ω : Measure M.AState) e - D.m (ω 0) e)) (Finset.mem_univ e₀)).trans h0
  exact sub_eq_zero.1 (abs_nonpos_iff.1 hterm)

/-- **The employment marginal depends only on today's shock.** -/
theorem IsSeqStateEquilibrium.initMass_eq_of_shock (hμ : M.IsSeqStateEquilibrium μ)
    (D : EmploymentDesign M.idioProb) {ω ω' : History Z} (h : ω 0 = ω' 0) :
    M.initMass (μ ω : Measure M.AState) = M.initMass (μ ω' : Measure M.AState) := by
  rw [hμ.initMass_eq_design D, hμ.initMass_eq_design D, h]

end KSModel

/-! ### Exactly one sequence-state equilibrium for small capital shares -/

variable [Nonempty Z] [Nonempty E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ}
  (hγ : 0 < γ) (hδ : 0 < T.depreciation) (D : EmploymentDesign V.idioProb)
include hγ hδ D

/-- **Exactly one sequence-state equilibrium.** For CRRA utility and clamped Cobb–Douglas prices
with depreciation `δ > 0`, under the Krusell–Smith employment design, there is a capital share
`α₀ > 0` below which the economy has exactly one sequence-state equilibrium. -/
theorem smallShare_existsUnique_seqStateEquilibrium :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃! μ : History Z → ProbabilityMeasure (crraModel V (T.withShare α h0 hα) hγ).AState,
        (crraModel V (T.withShare α h0 hα) hγ).IsSeqStateEquilibrium μ := by
  obtain ⟨α₀, hα₀, h⟩ := smallShare_contraction V T hγ hδ
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, -, H, hκ, hr⟩ := h α h0 hα
  refine ⟨h1, ?_⟩
  obtain ⟨μ, hμ⟩ := (crraModel V (T.withShare α h0 h1) hγ).exists_seqStateEquilibrium
  refine ⟨μ, hμ, fun μ' hμ' => ?_⟩
  have D' : EmploymentDesign (crraModel V (T.withShare α h0 h1) hγ).idioProb := D
  exact (hμ.eq_of_lawRate_lt_one H hκ hr hμ' fun ω => by
    rw [hμ.initMass_eq_design D' ω, hμ'.initMass_eq_design D' ω]).symm

end KrusellSmith

end LeanEconomics
