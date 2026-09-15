/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The Differentiable Sandwich Lemma

A function squeezed between two functions that are differentiable at a point, and agreeing
with both at that point, is itself differentiable there, with the same derivative.

This is Lemma 1 of Clausen and Strub (2020), "Reverse Calculus and Nested Optimization",
*Journal of Economic Theory* 187, 105019, and it is the foundation of their approach to
envelope theorems. Their point is that it needs neither concavity nor interiority, so it
applies where Benveniste–Scheinkman does not — in particular where a constraint binds, which
in a Bewley economy is exactly the states that matter, since the borrowing constraint is where
the whole ergodic argument lives.

The proof is two moves. The gap `U - L` is nonnegative near the point and vanishes at it, so
it has a local minimum there and its derivative is zero, which forces the two derivatives to
agree. Then the difference quotients of `F` are squeezed between those of `L` and `U`.

Mathlib has the local-minimum step (`IsLocalMin.hasDerivAt_eq_zero`) but not this lemma.
-/

open Filter Topology Asymptotics

/-- **Differentiable Sandwich Lemma** (Clausen–Strub 2020, Lemma 1). If `F` is squeezed
between `L` and `U` near `c`, all three agree at `c`, and `L` and `U` are differentiable at
`c`, then the two derivatives coincide and `F` is differentiable at `c` with that derivative. -/
theorem hasDerivAt_of_sandwich {F L U : ℝ → ℝ} {c l u : ℝ} {N : Set ℝ} (hN : N ∈ 𝓝 c)
    (hLF : ∀ x ∈ N, L x ≤ F x) (hFU : ∀ x ∈ N, F x ≤ U x)
    (hLc : L c = F c) (hUc : U c = F c)
    (hL : HasDerivAt L l c) (hU : HasDerivAt U u c) :
    l = u ∧ HasDerivAt F l c := by
  -- the gap has a local minimum at `c`, so the derivatives agree
  have hd : HasDerivAt (fun x => U x - L x) (u - l) c := hU.sub hL
  have hmin : IsLocalMin (fun x => U x - L x) c := by
    filter_upwards [hN] with x hx
    have h1 := hLF x hx
    have h2 := hFU x hx
    simp only [hLc, hUc]
    linarith
  have hul : u - l = 0 := hmin.hasDerivAt_eq_zero hd
  have hlu : l = u := by linarith
  refine ⟨hlu, ?_⟩
  -- and the difference quotients of `F` are squeezed
  have hU' : HasDerivAt U l c := by rwa [hlu]
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have hA := isLittleO_iff.mp (hasDerivAt_iff_isLittleO.mp hL) hε
  have hB := isLittleO_iff.mp (hasDerivAt_iff_isLittleO.mp hU') hε
  filter_upwards [hA, hB, hN] with y hya hyb hyn
  rw [Real.norm_eq_abs] at hya hyb ⊢
  have h1 := hLF y hyn
  have h2 := hFU y hyn
  rw [abs_le] at hya hyb ⊢
  simp only [smul_eq_mul] at hya hyb ⊢
  rw [hLc] at hya
  rw [hUc] at hyb
  constructor <;> linarith [hya.1, hya.2, hyb.1, hyb.2]
