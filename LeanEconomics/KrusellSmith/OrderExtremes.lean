/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.OrderMonotone

/-!
# Separation reduces to extreme histories

Milestone OS3 of `ORDER_STRUCTURE_PLAN.md`. `Z` is finite and linearly ordered, with best shock
`zMax` and worst `zMin`.

**(ShockMon)** `ShockMonOnHistories μ`: a better newest shock, with the same past, gives a
dominating cross-section after any common next shock.

* `dominates_of_singleDiff`: histories with the same shock that differ at one older lag, the second
  better there, have dominating cross-sections ((ShockMon) at that lag, (Mon) carries it forward);
* **`dominates_of_le`** (Lemma A): if `ω 0 = ω' 0` and `ω ≤ ω'` at every lag, then `μ ω ≼ μ ω'`
  — change one lag at a time, then pass to the limit (`μ` continuous in the history, dominance
  closed under weak limits);
* hence the cross-section after `(y, zMax, zMax, …)` dominates every cross-section at `y`, and the
  one after `(y, zMin, zMin, …)` is dominated by every one;
* **(ExtremeSep)** `ExtremeSep μ`: for `y < y'`, one step after `(y, zMax, zMax, …)` is dominated
  by one step after `(y', zMin, zMin, …)` — finitely many comparisons;
* **`sepOnHistories_of_extremes`**: (Mon) + (ShockMon) + (ExtremeSep) ⇒ (Sep);
  **`kSufficient_of_extremes`**: with `SavingMonotone` and uniqueness, `(z, K)` is a sufficient
  state.
-/

open MeasureTheory Topology Filter Set

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} {μ : History Z → ProbabilityMeasure M.AState}

theorem AssetDominates.trans {ν₁ ν₂ ν₃ : Measure M.AState} (h₁ : M.AssetDominates ν₁ ν₂)
    (h₂ : M.AssetDominates ν₂ ν₃) : M.AssetDominates ν₁ ν₃ :=
  fun f hf => (h₁ f hf).trans (h₂ f hf)

variable [LinearOrder Z]

/-- **(ShockMon)**: a better newest shock, with the same past, gives a dominating cross-section
after any common next shock. -/
def ShockMonOnHistories (μ : History Z → ProbabilityMeasure M.AState) : Prop :=
  ∀ ω ω' : History Z, History.tail ω = History.tail ω' → ω 0 < ω' 0 →
    ∀ z', M.AssetDominates (μ (History.cons z' ω)) (μ (History.cons z' ω'))

/-- **One older shock better**: histories with the same shock, differing only at lag `n + 1`, the
second better there, have dominating cross-sections. -/
theorem dominates_of_singleDiff (hMon : MonOnHistories μ) (hShock : ShockMonOnHistories μ) :
    ∀ (n : ℕ) (ω ω' : History Z), (∀ k, k ≠ n + 1 → ω k = ω' k) → ω (n + 1) ≤ ω' (n + 1) →
      M.AssetDominates (μ ω) (μ ω')
  | 0, ω, ω', hag, hle => by
    have h0 : ω 0 = ω' 0 := hag 0 (by omega)
    rcases hle.lt_or_eq with hlt | heq
    · have htail : History.tail (History.tail ω) = History.tail (History.tail ω') :=
        funext fun k => hag (k + 2) (by omega)
      have hω : μ ω = μ (History.cons (ω 0) (History.tail ω)) := by rw [History.cons_head_tail]
      rw [hω, eq_cons_tail h0 μ]
      exact hShock _ _ htail hlt (ω 0)
    · have : ω = ω' := funext fun k => by
        by_cases hk : k = 1
        · subst hk; exact heq
        · exact hag k hk
      rw [this]
      exact AssetDominates.refl _
  | n + 1, ω, ω', hag, hle => by
    have h0 : ω 0 = ω' 0 := hag 0 (by omega)
    have ih := dominates_of_singleDiff hMon hShock n (History.tail ω) (History.tail ω')
      (fun k hk => hag (k + 1) (by omega)) hle
    have ht0 : History.tail ω 0 = History.tail ω' 0 := hag 1 (by omega)
    have hω : μ ω = μ (History.cons (ω 0) (History.tail ω)) := by rw [History.cons_head_tail]
    rw [hω, eq_cons_tail h0 μ]
    exact hMon _ _ ht0 ih (ω 0)

/-- The history agreeing with `ω'` at lags below `n` and with `ω` from lag `n` on. -/
def interp (ω ω' : History Z) (n : ℕ) : History Z := fun k => if k < n then ω' k else ω k

omit [Fintype Z] [Fintype E] [LinearOrder Z] in
theorem interp_zero (ω ω' : History Z) : interp ω ω' 0 = ω := funext fun k => by
  simp [interp]

/-- **Lemma A: a pointwise better history with the same shock has a dominating cross-section.** -/
theorem dominates_of_le (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory)
    (hMon : MonOnHistories μ) (hShock : ShockMonOnHistories μ) {ω ω' : History Z}
    (h0 : ω 0 = ω' 0) (hle : ∀ k, ω k ≤ ω' k) : M.AssetDominates (μ ω) (μ ω') := by
  -- one lag at a time
  have hstep : ∀ n, M.AssetDominates (μ (interp ω ω' n)) (μ (interp ω ω' (n + 1))) := by
    intro n
    cases n with
    | zero =>
      have : interp ω ω' 1 = interp ω ω' 0 := funext fun k => by
        by_cases hk : k = 0
        · subst hk; simp [interp, h0]
        · simp [interp, show ¬ k < 1 by omega]
      rw [this]
      exact AssetDominates.refl _
    | succ m =>
      refine dominates_of_singleDiff hMon hShock m _ _ (fun k hk => ?_) ?_
      · by_cases h1 : k < m + 1
        · have h2 : k < m + 1 + 1 := by omega
          simp [interp, h1, h2]
        · have h2 : ¬ k < m + 1 + 1 := by omega
          simp [interp, h1, h2]
      · have := hle (m + 1)
        simpa [interp] using this
  have hall : ∀ n, M.AssetDominates (μ ω) (μ (interp ω ω' n)) := by
    intro n
    induction n with
    | zero => rw [interp_zero]; exact AssetDominates.refl _
    | succ n ih => exact ih.trans (hstep n)
  -- the limit
  have hlim : Tendsto (fun n => μ (interp ω ω' n)) atTop (𝓝 (μ ω')) := by
    have hpath : Tendsto (fun n => ShockPath.ofHistory (interp ω ω' n)) atTop
        (𝓝 (ShockPath.ofHistory ω')) := by
      refine tendsto_pi_nhds.2 fun k => tendsto_atTop_of_eventually_const (i₀ := k + 1)
        fun n hn => ?_
      simp [ShockPath.ofHistory, interp, show k < n by omega]
    exact (hc.tendsto _).comp hpath
  intro f hf
  have hint := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) f
  exact ge_of_tendsto' hint fun n => hall n f hf

variable [Nonempty Z]

/-- The best shock. -/
noncomputable def zMax (Z : Type*) [Fintype Z] [LinearOrder Z] [Nonempty Z] : Z :=
  Finset.univ.max' Finset.univ_nonempty

/-- The worst shock. -/
noncomputable def zMin (Z : Type*) [Fintype Z] [LinearOrder Z] [Nonempty Z] : Z :=
  Finset.univ.min' Finset.univ_nonempty

omit [Fintype E] in
theorem le_zMax (z : Z) : z ≤ zMax Z := Finset.le_max' _ _ (Finset.mem_univ z)

omit [Fintype E] in
theorem zMin_le (z : Z) : zMin Z ≤ z := Finset.min'_le _ _ (Finset.mem_univ z)

/-- **(ExtremeSep)**: for `y < y'`, one step after `(y, zMax, zMax, …)` is dominated by one step
after `(y', zMin, zMin, …)`. -/
def ExtremeSep (μ : History Z → ProbabilityMeasure M.AState) : Prop :=
  ∀ y y' : Z, y < y' → ∀ z', M.AssetDominates
    (μ (History.cons z' (History.cons y fun _ => zMax Z)))
    (μ (History.cons z' (History.cons y' fun _ => zMin Z)))

/-- **(Sep) from the extreme comparisons.** -/
theorem sepOnHistories_of_extremes (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory)
    (hMon : MonOnHistories μ) (hShock : ShockMonOnHistories μ) (hExt : ExtremeSep μ) :
    SepOnHistories μ := by
  intro ω ω' hlt z'
  -- `ω` lies below `(ω 0, zMax, …)`; `ω'` above `(ω' 0, zMin, …)`
  have hup : M.AssetDominates (μ ω) (μ (History.cons (ω 0) fun _ => zMax Z)) :=
    dominates_of_le hc hMon hShock rfl fun k => by
      cases k with
      | zero => exact le_rfl
      | succ k => exact le_zMax _
  have hdown : M.AssetDominates (μ (History.cons (ω' 0) fun _ => zMin Z)) (μ ω') :=
    dominates_of_le hc hMon hShock rfl fun k => by
      cases k with
      | zero => exact le_rfl
      | succ k => exact zMin_le _
  have h1 := hMon ω (History.cons (ω 0) fun _ => zMax Z) rfl hup z'
  have h2 := hMon (History.cons (ω' 0) fun _ => zMin Z) ω' rfl hdown z'
  exact (h1.trans (hExt _ _ hlt z')).trans h2

/-- **`(z, K)` is a sufficient state** when savings rise with aggregate capital, sequential
equilibrium is unique, the equilibrium is continuous in the history, better shocks raise the
cross-section (ShockMon), and the extreme comparisons hold (ExtremeSep). -/
theorem kSufficient_of_extremes (hH : M.SavingMonotone) (hU : M.UniqueSequentialEquilibrium)
    (hμ : M.IsSeqStateEquilibrium μ) (hc : Continuous fun ξ : ShockPath Z => μ ξ.toHistory)
    (hShock : ShockMonOnHistories μ) (hExt : ExtremeSep μ) : KSufficient μ :=
  kSufficient_of_savingMonotone hH hU hμ (sepOnHistories_of_extremes hc
    (monOnHistories_of_savingMonotone hH hU hμ) hShock hExt)

end KSModel

end KrusellSmith

end LeanEconomics
