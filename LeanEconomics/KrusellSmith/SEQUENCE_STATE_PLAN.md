# Equilibrium on infinite shock histories (the sequence state)

Goal: a **time-homogeneous recursive equilibrium whose state is the entire infinite past of
aggregate shocks** `ω = (z_t, z_{t-1}, …)`, with **no initial distribution**, for every
`KSModel` — in particular Cobb–Douglas prices. Then: when does it depend on the history only
through the distribution `μ_t` (the minimal state)?

This is the object the matched-expectations-path (MEP) method computes: a long shock sequence,
with burn-in so the initial distribution is forgotten.

## What exists

`Equilibrium.lean`: sequential equilibrium from an initial `(z₀, μ₀)`, a capital path on finite
histories (`List Z → ℝ`), by Schauder–Tychonoff. That is a sequence-state equilibrium with state
`(μ₀, history since date 0)`. Minimal-state results need uniqueness (`Recursive.lean`) or
complementarity (`ComplementarityWitness.lean`); Cobb–Douglas breaks the latter
(`MINIMAL_STATE_PLAN.md`).

## The construction (direct fixed point, no truncation limits)

Infinite histories `H∞ := ℕ → Z`, newest first (`ω 0` is today's shock). A finite list of future
shocks `g` is prepended: `g ++ ω`; every history is `z' :: ω` for a unique `(z', ω)`.

An **assignment** `μ : H∞ → P(AState)` gives the distribution at every infinite history. From it:

* the price path seen at `ω`: `p_ω(g) = (mean assets of μ(g ++ ω), Σ_e initMass(μ(g ++ ω)) e · e)`;
* the household problem at `ω` along `p_ω` (`household (ω 0) p_ω`), its policy;
* **the update** `Γ μ (z' :: ω) = pushNode (ω 0) p_ω [] z' (μ ω)`: tomorrow's distribution after
  shock `z'`, from today's, under today's optimal saving.

A **two-sided (sequence-state) equilibrium** is a fixed point `μ = Γ μ`. Market clearing is
built in (capital is mean assets of `μ`), and labour is read off `μ`.

**Existence by Schauder–Tychonoff** (`FixedPoint.schauderTychonoff`, already used for sequential
equilibrium) on `P(AState)^{H∞}`, embedded coordinatewise by `MarkovEquilibrium.embed` into the
locally convex `H∞ → ((AState →ᵇ ℝ≥0) → ℝ)`:
* compact (Tychonoff, each `P(AState)` compact) and convex (coordinatewise mixtures);
* `Γ` continuous in the product topology: coordinate `z' :: ω` depends on `μ ω` and on the
  countably many `μ(g ++ ω)` through the price path, and `ClosedGraph.lean` already has the joint
  continuity of `pushNode`/`nodeDist` in the initial distribution and the price path
  (`continuousAt_integral_nodeDist_joint`), and `continuous_initMass` for labour.

No truncation argument is needed, and with it no forgetting/stability assumption: the anchor-shift
problem of truncating at a fixed depth (consistency `μ(z'::ω)` vs `μ(ω)` breaks at every finite
truncation, and only stability would repair it in the limit) disappears, because time-homogeneity
is imposed by the fixed-point equation itself.

## Milestones

* **TS1** (`KrusellSmith/InfiniteHistory.lean`): `H∞`, prepending finite lists, `z' :: ω`
  decomposition, shock at a finite extension (`shockAt (ω 0) g` is the newest shock of
  `g ++ ω`); the assignment space and its coordinatewise embedding (compact, convex, locally
  convex Hausdorff ambient space).
* **TS2** (`SequenceStateMap.lean`): the price path `p_ω` from an assignment, the update `Γ`, and
  **continuity of `Γ`** (the substantive step).
* **TS3** (`SequenceStateEquilibrium.lean`): **existence** of a fixed point; and that it is an
  equilibrium in the existing sense — for every `ω`, `g ↦ mean μ(g ++ ω)` is a sequential
  equilibrium from `(ω 0, μ ω)` (`IsSequentialEquilibrium`), with `μ(g ++ ω)` the node
  distribution (induction on `g`) and labour consistent (`real_nodeDist_idio`). For every
  `KSModel`, so for Cobb–Douglas.
* **TS4**: the **recursive structure on infinite histories**: law of motion `ω ↦ z' :: ω`;
  distribution, capital, prices and the saving policy are functions of `ω`; time-homogeneous.
* **TS5**: **when it depends on the history only through `(z_t, μ_t)`** (Markov in the minimal
  state), at least:
  * (a) under `UniqueSequentialEquilibrium` every two-sided equilibrium is Markov and agrees with
    `Recursive.lean`'s law of motion on the distributions it visits;
  * (b) a swap lemma: if two histories `ω, ω'` with the same shock and distribution have disjoint
    futures, exchanging the future subtrees gives another fixed point; so **uniqueness of the
    two-sided equilibrium** (weaker in principle than uniqueness from every `(z, μ)`) gives
    Markov-ness at such pairs (recurrent pairs, `ω = g₀ ++ ω'`, need separate treatment);
  * (c) research: fading memory — conditions (stability of the distribution dynamics, the
    Doeblin tools of the Aiyagari development or the `κ` contraction) under which `μ(ω)` depends
    on the recent shocks up to a geometrically small error, which is what the MEP burn-in uses.

## Risks

* Continuity of `Γ` (TS2): the household's policy at `ω` depends on infinitely many coordinates,
  but continuously in the product topology (as for the sequential equilibrium map); the joint
  continuity lemmas exist but are stated for `pricePath` built from a capital path and root
  masses, so they need restating for a price path read off an assignment.
* What TS3–TS4 give is not the minimal state; TS5(a) needs uniqueness, TS5(b) uniqueness of the
  two-sided fixed point (no tool yet), TS5(c) is open-ended.
* No measurability in `ω` is claimed (the equilibrium is a function of every infinite history);
  measurability would matter for probabilistic statements about simulated paths.

## Status

* Planned 2026-11-05; nothing coded.
