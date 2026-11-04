# Conditionally spotless stationary recursive equilibrium (Cao 2020 Thm 4, DGMM Prop 1.3)

Follows `STATIONARITY_PLAN.md` (S0–S6 complete:
`KSModel.exists_stationaryRecursiveEquilibrium`).

## What the refinement is (from the papers)

**Spotless beliefs** (DGMM p. 756, Cao §6 `P_F`). With states `J* ⊆ Z × Y` (`Z` the finite set of
exogenous shocks, `Y` = (distribution, value, policy)), a belief `ν ∈ P(J*)` is *spotless* if it
is concentrated on the graph of a function `Z → Y`: given tomorrow's shock, tomorrow's state is
deterministic. A spotless transition is free of sunspots.

**Conditionally spotless** (DGMM p. 757; Cao Definition 6(ii)). `Π(ξ) = ∫ ν dΛ(ν)` with `Λ`
concentrated on beliefs that are **both spotless and consistent with `ξ`** (`∈ G̃(ξ)`). Sunspots
remain, but they only pick among *spotless, individually consistent* continuations, and the
sunspot can be thought of as drawn before today's choices: agents' choices are optimal even
conditional on its outcome. Existence of a fully spotless stationary equilibrium is, in Cao's
words, an open question; it is not attempted.

**What it adds over S6.** In S6, `T ξ ∈ G̃(ξ)` only for the averaged belief: the household's
policy is optimal against the *average* continuation value, and `T ξ` could mix beliefs none of
which is consistent on its own. Conditional spotlessness says `T ξ` is an average of beliefs each
of which is consistent and sunspot-free.

**Proof** (DGMM Prop 1.3, used by Cao). `Y`-finite is our finite `Z`. Let
`g(ξ) = G̃(ξ) ∩ P_F` and `Ĝ(ξ) = {E η : η ∈ P(P(J*)), η(g ξ) = 1}` (barycentres of measures on
spotless consistent beliefs; DGMM write it as the closed convex hull and show it is this set).
* `g` has closed graph (spotless measures form a closed set when `Z` is finite and `J*` compact);
  `J*` is self-justified for `g` (the justified beliefs `Σ π δ_{nodeState [z']}` are spotless).
* `Ĝ` has nonempty (`δ` of a justified belief) convex (mixtures of `η`, `mean_mix`) values and
  closed graph (`{(ξ, η) : η(g ξ) = 1}` is closed: it is the preimage of
  `{ν : ν(Gr g) = 1}` under `(ξ, η) ↦ δ_ξ ⊗ η`, continuous by Mathlib's
  `ProbabilityMeasure.continuous_prod`; then `E` is continuous).
* `Ĝ ⊆ G̃`: the mean of a measure on the closed convex `G̃(ξ)` lies in it (`mean_mem`, S3).
* `exists_ergodic` for `Ĝ` gives `T`, ergodic `γ`, `T ξ ∈ Ĝ(ξ)` a.e.: conditionally spotless,
  and in `G̃` a.e.

As in S6 everything holds `γ`-a.e. (Cao states "for all `ξ ∈ Z*`", after modifying `T` on a null
set by measurable selection; not attempted).

## Milestones

* **SP1** (abstract, `MarkovEquilibrium/Spotless.lean` or `Barycentre.lean`): for `g ⊆ G`
  with `g` closed-graph and nonempty-valued, `G` closed-graph and convex-valued: `baryHull g`,
  `isClosed_graph_baryHull` (via `continuous_prod` and dirac continuity), convex, nonempty,
  `baryHull_subset` (`mean_mem`), and `exists_ergodic_bary`: ergodic `γ`, measurable `T`,
  `T ξ = E η` with `η (g ξ) = 1`, a.e.
* **SP2** (`KrusellSmith/Spotless.lean`): `spotless : Set (P(J*))`,
  `γ ∈ spotless ↔ ∃ f : Z → J*, γ {ξ' | ξ' = f ξ'.shock} = 1`. **Closed**: via the variance
  characterisation — for each `z'` and test `h ∈ C(J*)`,
  `γ{z'} ∫ 1_{z'} h² dγ = (∫ 1_{z'} h dγ)²` (closed conditions), equivalent to spotless because a
  probability measure on a compact metrizable space with zero variance for every continuous `h` is a
  Dirac mass (separate two support points by a continuous function). Alternative if this is
  awkward: sequences of `f_k` in the compact `J*^Z` plus closed thickenings, as in S2.
* **SP3** (`KrusellSmith/SpotlessEquilibrium.lean`): `justifiedBelief` is spotless;
  `spotlessExpectations ξ = expectations ξ ∩ spotless` has closed graph and nonempty values;
  structure `ConditionallySpotlessEquilibrium` (S6 fields plus: a.e. `ξ`, `∃ η`,
  `η (spotlessExpectations ξ) = 1 ∧ T ξ = E η`); theorem
  `exists_conditionallySpotlessEquilibrium` for every `KSModel`.

## Risks

* SP2's Dirac characterisation is the only new measure theory; the support of a measure on a
  compact metrizable space and Urysohn-type separating functions are in Mathlib.
* Dirac continuity `s ↦ δ_s` into `ProbabilityMeasure` (likely `ProbabilityMeasure.continuous_dirac`
  or via `tendsto_iff_forall_integral_tendsto`; easy either way).

## Status

* Planned 2026-11-05.
* **SP1 done** (`MarkovEquilibrium/Barycentre.lean`): `baryHull`, `mean_dirac`,
  `baryHull_nonempty`, `mix_mem_baryHull`, `baryHull_subset` (`mean_mem`),
  `prod_dirac_graphSet`, **`isClosed_graph_baryHull`** (via `ProbabilityMeasure.continuous_prod`
  and `continuous_diracProba`), **`exists_ergodic_baryHull`** (DGMM Prop 1.3, abstract).
* Next: SP2 (spotless beliefs on `J*`, closed).
