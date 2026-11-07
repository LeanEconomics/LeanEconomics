/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.AggregateStateIff
import LeanEconomics.KrusellSmith.StochasticOrder

/-!
# A chain of cross-sections: capital determines the cross-section

Milestones OS0–OS1 of `ORDER_STRUCTURE_PLAN.md`.

* **OS0** (`AssetDominates`, stochastic dominance in assets for each employment state):
  * `AssetDominates.initMass_eq`: dominance forces **equal employment marginals** (functions of
    `e` alone are asset-monotone both ways);
  * **`eq_of_dominates_of_mean_eq`**: if `ν ≼ ν'` and mean assets are equal, then `ν = ν'`. For
    an asset-Lipschitz test function `f` with constant `L`, both `f + L a` and `L a − f` are
    asset-monotone, so dominance and equal means give equal integrals of `f`; asset-Lipschitz
    functions determine measures (`eq_of_forall_assetLip`).
* **OS1** (chain theorem; `Z` linearly ordered): with
  * **(Mon)** `MonOnHistories μ`: comparable cross-sections at histories with the same shock stay
    comparable after a common new shock, and
  * **(Sep)** `SepOnHistories μ`: after histories whose newest shocks are ordered, the next
    cross-sections are ordered the same way, whatever their pasts,

  **any two cross-sections at the same shock are comparable** (`comparable_of_sameShock`, by
  induction on the lag of the most recent differing shock), so **capital determines the
  cross-section** (`kInjective_of_chain`) and `(z, K)` is a sufficient state
  (`kSufficient_of_chain`), with all of `AggregateStateIff.lean` available.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

/-! ### OS0: dominance with equal means is equality -/

/-- **Dominance forces equal employment marginals.** -/
theorem AssetDominates.initMass_eq {ν ν' : Measure M.AState} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (h : M.AssetDominates ν ν') : M.initMass ν = M.initMass ν' := by
  funext e
  have hmono : M.AssetMono (M.idioInd e) := by
    intro x y hxy _
    by_cases hx : x.2.idio = e
    · rw [M.idioInd_of_eq hx, M.idioInd_of_eq (by rw [← hxy]; exact hx)]
    · rw [M.idioInd_of_ne hx, M.idioInd_of_ne (by rw [← hxy]; exact hx)]
  have hmono' : M.AssetMono ((-M.idioInd e : M.AState →ᵇ ℝ)) := by
    intro x y hxy _
    by_cases hx : x.2.idio = e
    · change -(M.idioInd e x) ≤ -(M.idioInd e y)
      rw [M.idioInd_of_eq hx, M.idioInd_of_eq (show y.2.idio = e by rw [← hxy]; exact hx)]
    · change -(M.idioInd e x) ≤ -(M.idioInd e y)
      rw [M.idioInd_of_ne hx, M.idioInd_of_ne (show ¬ y.2.idio = e by rw [← hxy]; exact hx)]
  have h1 := h _ hmono
  have h2 := h _ hmono'
  simp only [coe_neg, Pi.neg_apply, integral_neg, neg_le_neg_iff] at h2
  rw [show M.initMass ν e = ∫ x, M.idioInd e x ∂ν from (M.integral_idioInd ν e).symm,
    show M.initMass ν' e = ∫ x, M.idioInd e x ∂ν' from (M.integral_idioInd ν' e).symm]
  exact le_antisymm h1 h2

/-- **Dominance with equal mean assets is equality.** -/
theorem eq_of_dominates_of_mean_eq {ν ν' : Measure M.AState} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (h : M.AssetDominates ν ν')
    (hmean : ∫ x, M.assets x ∂ν = ∫ x, M.assets x ∂ν') : ν = ν' := by
  refine eq_of_forall_assetLip fun L _ f hf => ?_
  -- `f + L a` and `L a − f` are asset-monotone
  have hup : M.AssetMono ((f + L • M.assets : M.AState →ᵇ ℝ)) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ hij hab
    change i = j at hij
    subst hij
    change (a : ℝ) ≤ b at hab
    have := hf a b i
    rw [abs_sub_comm (a : ℝ) b, abs_of_nonneg (sub_nonneg.2 hab)] at this
    change f (a, i) + L * (a : ℝ) ≤ f (b, i) + L * (b : ℝ)
    have h' := (abs_le.1 this).2
    linarith
  have hdown : M.AssetMono ((L • M.assets - f : M.AState →ᵇ ℝ)) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ hij hab
    change i = j at hij
    subst hij
    change (a : ℝ) ≤ b at hab
    have := hf a b i
    rw [abs_sub_comm (a : ℝ) b, abs_of_nonneg (sub_nonneg.2 hab)] at this
    change L * (a : ℝ) - f (a, i) ≤ L * (b : ℝ) - f (b, i)
    have h' := (abs_le.1 this).1
    linarith
  have h1 := h _ hup
  have h2 := h _ hdown
  have hint : ∀ μ' : Measure M.AState, IsProbabilityMeasure μ' →
      Integrable (fun x => L * M.assets x) μ' := fun μ' _ => (M.assets.integrable μ').const_mul L
  simp only [coe_add, coe_sub, coe_smul, Pi.add_apply, Pi.sub_apply, smul_eq_mul] at h1 h2
  rw [integral_add (f.integrable _) (hint ν inferInstance),
    integral_add (f.integrable _) (hint ν' inferInstance), integral_const_mul,
    integral_const_mul, hmean] at h1
  rw [integral_sub (hint ν inferInstance) (f.integrable _),
    integral_sub (hint ν' inferInstance) (f.integrable _), integral_const_mul,
    integral_const_mul, hmean] at h2
  linarith

/-! ### OS1: the chain theorem -/

variable {μ : History Z → ProbabilityMeasure M.AState}

/-- Two cross-sections are **comparable** for dominance. -/
def Comparable (M : KSModel Z E) (ν ν' : Measure M.AState) : Prop :=
  M.AssetDominates ν ν' ∨ M.AssetDominates ν' ν

variable [LinearOrder Z]

/-- **(Mon)**: comparable cross-sections at histories with the same shock stay comparable, in the
same direction, after a common new shock. -/
def MonOnHistories (μ : History Z → ProbabilityMeasure M.AState) : Prop :=
  ∀ ω ω' : History Z, ω 0 = ω' 0 → M.AssetDominates (μ ω) (μ ω') →
    ∀ z', M.AssetDominates (μ (History.cons z' ω)) (μ (History.cons z' ω'))

/-- **(Sep)**: after histories whose newest shocks are ordered, the next cross-sections are
ordered the same way, whatever the pasts. -/
def SepOnHistories (μ : History Z → ProbabilityMeasure M.AState) : Prop :=
  ∀ ω ω' : History Z, ω 0 < ω' 0 →
    ∀ z', M.AssetDominates (μ (History.cons z' ω)) (μ (History.cons z' ω'))

omit [LinearOrder Z] in
theorem eq_cons_tail {ω ω' : History Z} (h0 : ω 0 = ω' 0)
    (ν : History Z → ProbabilityMeasure M.AState) :
    ν ω' = ν (History.cons (ω 0) (History.tail ω')) := by
  rw [h0, History.cons_head_tail]

/-- **Comparability by the most recent differing shock.** -/
theorem comparable_of_firstDiff (hMon : MonOnHistories μ) (hSep : SepOnHistories μ) :
    ∀ (T : ℕ) (ω ω' : History Z), (∀ k ≤ T, ω k = ω' k) → ω (T + 1) ≠ ω' (T + 1) →
      M.Comparable (μ ω) (μ ω')
  | 0, ω, ω', hag, hne => by
    have h0 := hag 0 le_rfl
    have hω : μ ω = μ (History.cons (ω 0) (History.tail ω)) := by rw [History.cons_head_tail]
    rw [hω, eq_cons_tail h0 μ]
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (hSep _ _ h (ω 0))
    · exact Or.inr (hSep _ _ h (ω 0))
  | T + 1, ω, ω', hag, hne => by
    have h0 := hag 0 (Nat.zero_le _)
    have ih := comparable_of_firstDiff hMon hSep T (History.tail ω) (History.tail ω')
      (fun k hk => hag (k + 1) (by omega)) hne
    have ht0 : History.tail ω 0 = History.tail ω' 0 := hag 1 (by omega)
    have hω : μ ω = μ (History.cons (ω 0) (History.tail ω)) := by rw [History.cons_head_tail]
    rw [hω, eq_cons_tail h0 μ]
    rcases ih with h | h
    · exact Or.inl (hMon _ _ ht0 h (ω 0))
    · exact Or.inr (hMon _ _ ht0.symm h (ω 0))

/-- **Any two cross-sections at the same shock are comparable.** -/
theorem comparable_of_sameShock (hMon : MonOnHistories μ) (hSep : SepOnHistories μ)
    {ω ω' : History Z} (h0 : ω 0 = ω' 0) : M.Comparable (μ ω) (μ ω') := by
  classical
  by_cases h : ω = ω'
  · subst h
    exact Or.inl (AssetDominates.refl _)
  · have hex : ∃ n, ω (n + 1) ≠ ω' (n + 1) := by
      by_contra hc
      apply h
      funext n
      cases n with
      | zero => exact h0
      | succ n => exact by_contra fun hne => hc ⟨n, hne⟩
    refine comparable_of_firstDiff hMon hSep (Nat.find hex) ω ω' (fun k hk => ?_)
      (Nat.find_spec hex)
    cases k with
    | zero => exact h0
    | succ k => exact by_contra fun hne => Nat.find_min hex (by omega : k < Nat.find hex) hne

/-- **Capital determines the cross-section** when the cross-sections form a chain. -/
theorem kInjective_of_chain (hMon : MonOnHistories μ) (hSep : SepOnHistories μ) :
    KInjective μ := by
  intro ω ω' h0 hk
  have hmean : ∫ x, M.assets x ∂(μ ω : Measure M.AState)
      = ∫ x, M.assets x ∂(μ ω' : Measure M.AState) := hk
  apply ProbabilityMeasure.toMeasure_injective
  rcases comparable_of_sameShock hMon hSep h0 with h | h
  · exact eq_of_dominates_of_mean_eq h hmean
  · exact (eq_of_dominates_of_mean_eq h hmean.symm).symm

/-- **`(z, K)` is a sufficient state** when the cross-sections form a chain (under uniqueness). -/
theorem kSufficient_of_chain (hμ : M.IsSeqStateEquilibrium μ)
    (hU : M.UniqueSequentialEquilibrium) (hMon : MonOnHistories μ) (hSep : SepOnHistories μ) :
    KSufficient μ :=
  KInjective.kSufficient hμ hU (kInjective_of_chain hMon hSep)

end KSModel

end KrusellSmith

end LeanEconomics
