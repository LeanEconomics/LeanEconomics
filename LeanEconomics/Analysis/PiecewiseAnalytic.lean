/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Basic

/-!
# Zeros of a piecewise analytic function on a compact interval

Excess demand `E = S - D` for the life cycle is, under CRRA utility and a finite earnings chain,
piecewise real-analytic in the rate: the interior branch of every stage policy comes from the
Euler equality by the analytic implicit function theorem, the constrained branch is affine, and
aggregate supply is a finite composition of these along the cohort's paths. This file records the
consequence for the number of equilibria: on a compact bracket a function that agrees on each of
finitely many closed pieces with a function analytic on a neighbourhood of the piece has finitely
many zeros, unless it vanishes identically on some piece. Finiteness at the calibration is
therefore reduced to excluding a piece on which supply coincides with demand, i.e. to the
magnitude question of how fast supply can fall (`numerics/slopebnd.m`).
-/

open Set Filter Topology

namespace LeanEconomics

/-- **Zeros of an analytic function on a compact interval are finite** unless the function
vanishes identically on the connected open set containing the interval. -/
theorem finite_zeros_of_analyticOnNhd {f : ℝ → ℝ} {a b : ℝ} {U : Set ℝ} (hU : IsPreconnected U)
    (hsub : Icc a b ⊆ U) (hf : AnalyticOnNhd ℝ f U) (hne : ∃ x ∈ U, f x ≠ 0) :
    {x ∈ Icc a b | f x = 0}.Finite := by
  by_contra hinf
  have hinf' : {x ∈ Icc a b | f x = 0}.Infinite := hinf
  obtain ⟨x₀, hx₀, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact isCompact_Icc
    (fun x hx => hx.1)
  have hfreq : ∃ᶠ z in 𝓝[≠] x₀, f z = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hacc
    exact hacc.mono fun z hz => hz.2
  have h0 := hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU (hsub hx₀) hfreq
  obtain ⟨x, hxU, hx⟩ := hne
  exact hx (h0 hxU)

/-- A function on `[a, b]` is piecewise analytic with `n` pieces at the breakpoints `t 0 ≤ … ≤ t n`,
`t 0 = a`, `t n = b`, if on each closed piece `[t i, t (i+1)]` it agrees with a function that is
analytic on a preconnected open neighbourhood of the piece. -/
structure PiecewiseAnalyticOn (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (t : ℕ → ℝ) : Prop where
  first : t 0 = a
  last : t n = b
  mono : ∀ i < n, t i ≤ t (i + 1)
  piece : ∀ i < n, ∃ (U : Set ℝ) (g : ℝ → ℝ), IsOpen U ∧ IsPreconnected U ∧
    Icc (t i) (t (i + 1)) ⊆ U ∧ AnalyticOnNhd ℝ g U ∧ EqOn f g (Icc (t i) (t (i + 1)))

/-- The pieces cover the interval. -/
theorem PiecewiseAnalyticOn.mem_piece {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} {t : ℕ → ℝ}
    (h : PiecewiseAnalyticOn f a b n t) (hn : 0 < n) {x : ℝ} (hx : x ∈ Icc a b) :
    ∃ i < n, x ∈ Icc (t i) (t (i + 1)) := by
  classical
  -- take the largest `i < n` with `t i ≤ x`
  let s : Finset ℕ := (Finset.range n).filter fun i => t i ≤ x
  have hs : s.Nonempty := ⟨0, by simp [s, hn, h.first, hx.1]⟩
  let i := s.max' hs
  have hi : i ∈ s := Finset.max'_mem s hs
  have hin : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hti : t i ≤ x := (Finset.mem_filter.mp hi).2
  refine ⟨i, hin, hti, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  -- then `i + 1 < n` (else `t (i+1) = b ≥ x`), and `i + 1 ∈ s` contradicts maximality
  have hi1 : i + 1 < n := by
    by_contra hge
    have : i + 1 = n := by omega
    rw [this, h.last] at hlt
    exact absurd hx.2 (not_le.mpr hlt)
  have hmem : i + 1 ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi1, hlt.le⟩
  exact absurd (Finset.le_max' s (i + 1) hmem) (by omega)

/-- **Finiteness of equilibria on a bracket.** A piecewise analytic function with finitely many
pieces has finitely many zeros on `[a, b]`, provided it does not vanish identically on any piece
(each piece's analytic extension is nonzero somewhere on its neighbourhood). -/
theorem PiecewiseAnalyticOn.finite_zeros {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} {t : ℕ → ℝ}
    (h : PiecewiseAnalyticOn f a b n t)
    (hne : ∀ i < n, ∀ (U : Set ℝ) (g : ℝ → ℝ), IsOpen U → IsPreconnected U →
      Icc (t i) (t (i + 1)) ⊆ U → AnalyticOnNhd ℝ g U → EqOn f g (Icc (t i) (t (i + 1))) →
      ∃ x ∈ U, g x ≠ 0) :
    {x ∈ Icc a b | f x = 0}.Finite := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- no pieces: `a = b` and the interval is a point
    subst hn
    have hab : a = b := h.first.symm.trans h.last
    subst hab
    exact (Set.finite_singleton a).subset fun x hx => by rw [Set.Icc_self] at hx; exact hx.1
  -- the zero set is covered by the zero sets of the pieces' analytic extensions
  have hcover : {x ∈ Icc a b | f x = 0} ⊆
      ⋃ i ∈ Finset.range n, {x ∈ Icc (t i) (t (i + 1)) | f x = 0} := by
    intro x hx
    obtain ⟨i, hin, hxi⟩ := h.mem_piece hn hx.1
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hin, hxi, hx.2⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.range n).finite_toSet fun i hi => ?_) hcover
  have hin : i < n := Finset.mem_range.mp hi
  obtain ⟨U, g, hUo, hUc, hsub, hg, hfg⟩ := h.piece i hin
  have hgne := hne i hin U g hUo hUc hsub hg hfg
  have hfin := finite_zeros_of_analyticOnNhd hUc hsub hg hgne
  refine hfin.subset fun x hx => ⟨hx.1, ?_⟩
  rw [← hfg hx.1]
  exact hx.2

end LeanEconomics
