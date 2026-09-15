# Candidates for upstreaming to Mathlib

Each entry below was checked against Mathlib before being listed, and two things I had
previously called gaps turned out not to be. The checks are recorded so they can be redone
when Mathlib moves.

## Genuine gaps

### 1. Berge's maximum theorem — `LeanEconomics/Topology/Berge.lean`

Both halves: continuity of the value of a parametrised maximisation, and upper
hemicontinuity of the argmax.

Mathlib **has** the hemicontinuity definitions and their characterisations
(`Mathlib/Topology/Semicontinuity/{Defs,Hemicontinuity}.lean`, added 2025) and Michael's
selection theorem. It does **not** have the maximum theorem. Checked by grepping Mathlib for
`Berge` and `maximum theorem`: the only hits are unrelated files.

This is the largest of the three and the best fit, because it is built directly on Mathlib's
own `UpperHemicontinuous` / `LowerHemicontinuous` rather than on a private notion, so it
extends that file rather than competing with it.

Before a PR: the supporting definitions `maxValue` and `argmax` would need a naming
discussion, and `eventually_forall_lt` — the generalised tube lemma that drives both halves —
deserves to be stated and named in its own right, since it is the reusable part.

An `EReal`-valued version exists in `Topology/BergeEReal.lean`. It is in places *simpler*
than the real one (a complete lattice removes the side conditions on `sSup`), and its argmax
half needs no nonemptiness hypothesis. Worth offering as a follow-up, not in the first PR.

### 2. Parametric continuity of a contraction's fixed point — `DynamicProgramming/Parametric.lean`

```
continuousAt_fixedPoint :
  (∀ r, LipschitzWith K (T r)) → K < 1 → (∀ r, T r (fix r) = fix r) →
  ContinuousAt (fun r => T r (fix r₀)) r₀ → ContinuousAt fix r₀
```

Mathlib has the Banach fixed point theorem and the `fixedPoint` / `efixedPoint` API, but no
statement about how the fixed point moves with a parameter. Checked by grepping every
occurrence of `fixedPoint` in Mathlib for `Continuous`, `Tendsto` or `param`: nothing.

Already standalone — the file imports only `Mathlib.Topology.MetricSpace.Contracting`.

The hypothesis is weaker than the obvious one in a way worth keeping in the statement:
continuity of the operator is needed at a **single** function, the fixed point at the
parameter of interest, not uniformly. The contraction absorbs everything else.

### 3. Decreasing increments of a concave function — `Analysis/DecreasingIncrements.lean`

```
ConcaveOn.sub_le_sub_of_shift :
  c₁ ≤ c₂ → 0 ≤ Δ → u (c₂ + Δ) - u (c₁ + Δ) ≤ u c₂ - u c₁
```

**Borderline, and weaker than the other two.** Mathlib has a developed slope API for convex
and concave functions (`Mathlib/Analysis/Convex/Slope.lean`: `slope_anti_adjacent`,
`secant_mono`, and their strict versions), and this statement is derivable from it. It is not
*stated* anywhere, and the derivation is not a one-liner because the two intervals may
overlap, which the adjacent-slope lemmas do not cover directly.

If offered, it belongs in `Slope.lean` and a reviewer may reasonably want it proved from the
existing slope lemmas rather than from scratch. The proof here is independent: `c₁ + Δ` and
`c₂` are complementary convex combinations of `c₁` and `c₂ + Δ`, so adding the two concavity
inequalities cancels the weights.

## Not gaps — corrected

### `min` is 1-Lipschitz

I previously listed `abs_min_sub_min_le` and `abs_min_sub_min_le_max` as contributions. They
are not. Mathlib has `lipschitzWith_min : LipschitzWith 1 fun p : ℝ × ℝ => min p.1 p.2`, along
with `LipschitzWith.const_min` and `LipschitzWith.min_const`, in
`Mathlib/Topology/MetricSpace/Lipschitz.lean`.

Both lemmas in this development have been rewritten to derive from it, which is what they
should have done from the start — the joint version is exactly `lipschitzWith_min` read
through the product's supremum metric.

## Not upstreamable

`norm_valueFunction_le`, the region bridge, the cutoff lemmas and the cross-rate estimates are
all stated in terms of this development's own structures. They are the right shape for
economics and the wrong shape for Mathlib.
