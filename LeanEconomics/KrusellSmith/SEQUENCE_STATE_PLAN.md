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

* Planned 2026-11-05.
* **TS1 DONE** 2026-11-05 (`InfiniteHistory.lean`): `History Z := ℕ → Z`, `History.cons`/`tail`,
  `cons_head_tail`, `cons_inj`, `prepend` (finite list onto a history; `g ++ ω` above is
  `prepend g ω`), `prepend_append`, `prepend_zero` (newest shock is `shockAt (ω 0) g`);
  `embedAssign`, `isEmbedding_embedAssign` (`IsEmbedding.piMap`), `isCompact_range_embedAssign`,
  `mixAssign`, `embedAssign_mix`, `convex_range_embedAssign`, ambient locally convex + T2.
  Standard axioms only.
* **TS2 DONE** 2026-11-05 (`SequenceStateMap.lean`): `seqPrices μ ω` (capital = mean assets,
  labour = Σ initMass·efficiency of `μ (prepend g ω)`), `seqPrices_prepend` (shift),
  `seqPrices_snd` (= `labour _ _ []`), `pushRoot` (one node as a `ProbabilityMeasure`),
  `seqStep` (Γ), `coe_seqStep_cons(_eq_nodeDist)`, `continuous_seqPrices`, `continuous_pushRoot`
  (via `tendsto_iff_forall_integral_tendsto` + `continuousAt_integral_nodeDist_joint`),
  **`continuous_seqStep`**. The feared restating was unnecessary: the joint lemma takes any price
  path. Standard axioms only.
* **TS3 DONE** 2026-11-05 (`SequenceStateEquilibrium.lean`): `IsSeqStateEquilibrium μ :=
  seqStep μ = μ`; **`exists_seqStateEquilibrium`** (every `KSModel`, `[Nonempty E]`; Schauder–
  Tychonoff via `IsEmbedding.toHomeomorph` onto the range of `embedAssign`);
  `IsSeqStateEquilibrium.nodeDist_eq` (tree from `μ ω` reproduces `μ (prepend g ω)`, by
  `pushNode_shift`), `seqCapital`, `pricePath_eq` (labour = exogenous recursion via
  `initMass_nodeDist`), **`isSequentialEquilibrium`** (in `capitalPaths`, sequential eqm from
  `(ω 0, μ ω)` at every `ω`), `labour_eq` (labour = mean efficiency);
  **`logEconomy_exists_seqStateEquilibrium`** (log utility + clamped Cobb–Douglas). Standard
  axioms only.
* **TS4 DONE** 2026-11-05 (`SequenceStateRecursive.lean`): household on histories for every
  assignment — `seqValue`, `seqPolicy`, `seqCash` (`seqCash_eq`: prices via `(ω 0, μ ω)`),
  `valueFunction_node`/`policy_node` (node `g` of tree at `ω` = root at `prepend g ω`),
  `seqValue_eq` (Bellman on histories), `objective_le_seqValue` (optimality), `seqPolicy_le`;
  `IsSeqStateEquilibrium.integral_cons` (law of motion). **`structure
  HistoryRecursiveEquilibrium`** (dist, capital, labour, value, saving; capital/labour means;
  feasibility, Bellman, optimality, law of motion `ω ↦ cons z' ω`), `capital_cons` (capital is
  mean saving, independent of `z'`), `toRecursive`, **`exists_historyRecursiveEquilibrium`**,
  **`logEconomy_exists_historyRecursiveEquilibrium`**. Standard axioms only.
* **TS5 (a) DONE** 2026-11-05 (`SequenceStateMarkov.lean`), in a stronger *local* form:
  `UniqueFrom z ν` (unique sequential eqm from one state); if `ω 0 = ω' 0`, `μ ω = μ ω'` and
  `UniqueFrom (ω 0) (μ ω)`, then `markov_seqPrices`, `markov_cons` (same distribution after
  every shock), `markov_seqPolicy`, `markov_seqValue`. Only uniqueness at visited states is
  needed. Global: under `UniqueSequentialEquilibrium`, `seqCapital_eq_eqPath`, `eq_nodeProb`,
  `eq_lawOfMotion`, `seqPolicy_eq_recursivePolicy` (the eqm is `Recursive.lean`'s Markov eqm
  on the distributions it visits). Standard axioms only.
* **TS5 (b) REFUTED as planned, not formalised.** The swap of the future subtrees of `ω, ω'`
  (same shock, same distribution) is *not* a fixed point in general: the ancestors
  `tail^k ω'` read capital on the subtree of `ω'` through `seqPrices` (their trees contain
  it), so after the swap their saving changes and so does `μ ω'` itself. History dependence
  is exactly the past's expectation of which continuation from `(z, μ)` is played (DGMM's
  expanded state). The correct weak statement is (a)'s local uniqueness. A genuine version of
  (b) would need two histories with no common ancestor, which do not exist (any two infinite
  histories share no ancestor only if they never coincide, but their pasts are still
  constrained); not pursued.
* **TS5 (c) OPEN** (research): fading memory / stability; not started.
