# A stationary recursive equilibrium on (z, K)

Goal: in the small-share class (where `minMPC_smallShare_unique_stationary` gives a unique,
continuous sequence-state equilibrium `μ*` and a unique ergodic stationary law `Λ*` of
`(z, μ)`), characterise exactly when aggregate shock and aggregate capital `(z, K)` are a
sufficient aggregate state for a **stationary recursive equilibrium**, and prove it under that
condition. This would be stronger than Cao (2020) §6 / DGMM: no value function or expectations in
the state, no sunspots, Cobb–Douglas prices.

## What Lee gives and what it does not

* LS1 `injOn_orbit_of_strictMono` (Lee Thm 1): `K` is injective along **one frozen-regime orbit**.
* LS2 / HistoryMarginals (Lee Thm 2): `μ*` forgets old shocks at rate `r*`.
* Neither prevents two histories (different spells, different past shocks) from reaching the same
  `(z, K)` with different `μ`, and generically different future `K` (saving is nonlinear in
  wealth: borrowing constraint, precautionary MPC heterogeneity). So exact `(z, K)` sufficiency is
  a **condition**, to be characterised (AK1–AK4) and then studied (AK5).

## Setting and the condition

* Ergodic set `A := range (stateOf μ*) = {(ξ 0, μ* ξ) : ξ ∈ ShockPath Z}` — compact (continuous
  image of compact `ShockPath`), `Λ* A = 1`, forward invariant (`cons`). Fibre
  `A_z = {ν : (z, ν) ∈ A}`; capital set `Kset z = K '' A_z ⊆ [0, ā]`, compact.
* Households only need **prices**, i.e. the future path of `(K, L)` on the shock tree.
* **`KSufficient`**: for histories `ω, ω'` with `ω 0 = ω' 0` and `K (μ* ω) = K (μ* ω')`, for every
  finite continuation `g : List Z`, `(K, L) (μ* (g ++ ω)) = (K, L) (μ* (g ++ ω'))`.
  (Under `EmploymentDesign`, `L` is a function of `z` and only the `K` part is a condition.)
* `KInjective` (`K` injective on each `A_z`) ⇒ `KSufficient`; `KSufficient` is weaker: distinct
  distributions in one `K`-fibre are allowed if they never separate the aggregate path.

## Milestones

* **AK0** (small, `AggregateState.lean`): `ergSet`, `isCompact_ergSet` (`continuous_seqState`),
  `stateLaw_ergSet` (`Λ* A = 1`), `cons` maps `A` into `A`; `Kset` compact.
* **AK1** aggregate tree on `(z, K)`: under `KSufficient`, `aggTree z k g` (the `(K, L)` at
  continuation `g` from any representative history) is well defined on `{(z, k) : k ∈ Kset z}`;
  `Ψ z k z' := (aggTree z k [z']).1` (equals mean saving, `capital_cons`); **continuity** of
  `aggTree` and `Ψ` by the closed-graph trick of `continuous_lawOfMotion` (graph = continuous image
  of compact `ShockPath`, compact codomain) — no injectivity needed.
* **AK2** recursive equilibrium on `(z, K)`: `structure AggStateRecursiveEquilibrium` — `Kset`,
  `Ψ`, labour `L̂ z k`, value `V z k a e`, saving `g z k a e`; Bellman + optimality with prices
  `R(z, k, L̂)`, `w(z, k, L̂)` and continuation at `(z', Ψ z k z')`; **consistency**: for every
  `(z, k)` some distribution in the fibre `A_z ∩ K⁻¹ k` has mean `k`, labour `L̂ z k`, and pushes
  forward under `g` into the fibre over `(z', Ψ z k z')` with mean `Ψ z k z'`. Built by factoring
  TS4's `HistoryRecursiveEquilibrium` (value and saving at `ω` depend only on the price tree below
  `ω`, `seqValue_eq` + household uniqueness) through `ω ↦ (ω 0, K (μ* ω))`.
* **AK3** stationarity on `(z, K)`: kernel `Q_K (z, k) = Σ_{z'} π z z' δ_{(z', Ψ z k z')}`;
  `Λ_K := Λ*.map (id × K)` is `Q_K`-invariant (`isInvariant_stateLaw`) and ergodic
  (`ergodic_stateLaw`); **unique** among `Q_K`-invariant laws on the `Kset` graph. Proof without a
  measurable selection: `Q_Kᵀ F (z, k)` equals expectations along `μ*` from any representative
  history (AK1), and burn-in (`dist2_run` / `abs_qIter_sub_eIter_le` pattern) puts it within
  `C r*ᵀ ω` of a function of `z` alone for `F` Lipschitz in `k` (`K` is asset-Lipschitz, so
  `F ∘ (id × K)` is `DistLip`); then the SS4 argument with Lipschitz tests on `Z × ℝ`
  (Stone–Weierstrass, Polish) gives equality.
* **AK4** necessity: if some `(Ψ, L̂)` on `(z, K)` reproduces the equilibrium aggregate tree from
  every history (`(K, L)` at `g ++ ω` is the `Ψ`-iterate from `(ω 0, K (μ* ω))`), then
  `KSufficient`. Headline **iff**: in the small-share class, a stationary recursive equilibrium on
  `(z, K)` consistent with the (unique) equilibrium exists **iff** `KSufficient`; then it is
  continuous, and its stationary law is unique and ergodic.
* **AK5** (research) when does `KSufficient` hold?
  * (a) `KInjective ⇒ KSufficient`; plus the fibre map `(z, k) ↦ ν` is then a homeomorphism onto
    `A_z` (continuous injection on compact), so the distribution itself is a function of `(z, K)`.
  * (b) A quantitative separation condition (iterated-function-system style): the `K`-gap from the
    most recent differing shock beats the most that older differences can add (`Δ > D r/(1 − r)`
    at every lag). Needs a **lower** bound on the aggregate saving response to a shock (positive
    unconstrained mass, minimum MPS), which we do not have; and propagation of a lag-`T`
    difference needs a cone condition `s_lo − r* > G⊥/η`, where `G⊥` is the feed of the
    non-`K` part of `μ` into `K'` through MPC heterogeneity — `O(1)` even at `α → 0`. Plausible
    only for fast forgetting (`θ` small: high depreciation, long periods).
  * (c) Expectation for KS-type persistence (`r ≈ 1 − δ ≈ 0.975` quarterly): `A_z` has
    dimension ≈ `log|Z| / log(1/r)` ≫ 1, so `K`-fibres are non-trivial and `KSufficient` likely
    fails. A proof of failure in an explicit economy would also be a result (not attempted yet).
* **AK6** (optional) approximate version without `KSufficient`: with a `(z, K)` selection, future
  aggregate gaps ≤ `L_K r*ᵗ · fibreDiam` and policy errors ≤ `G · fibreDiam / (1 − κ)`, where
  `fibreDiam` is the `Dist2` diameter of the `K`-fibres in `A`. Analytic, but only as small as the
  fibres, which we can bound only by `diam A`.

## Sizes (rough)

AK0 small; AK1 small–medium (closed graph, list continuations); AK2 medium (factoring the history
Bellman, consistency statement); AK3 medium (reuse SS4); AK4 small; AK5 research, outcome open;
AK6 small–medium.

## Status

* Planned 2026-11-07.
* **AK0 + AK1 DONE** 2026-11-07 (`AggregateState.lean`): `ShockPath.ofHistory`/`prepend`,
  `continuous_seqPrices_history`; `ergSet`, **`isCompact_ergSet`**, **`stateLaw_ergSet`**
  (`Λ* A = 1`), `stateOf_cons_mem_ergSet`, **`lawOfMotion_mem_ergSet`** (under uniqueness);
  `capAt`, **`KSufficient`** (stated on the whole price tree `seqPrices`), `KInjective`,
  **`KInjective.kSufficient`** (under uniqueness); `Kset`, `isCompact_Kset`; `aggTree`,
  **`aggTree_eq`**, `lawK`, `labourK`, `lawK_mem`, `aggTree_shift`, `stateAlong`,
  **`aggTree_eq_stateAlong`** (`lawK`, `labourK` generate the whole tree);
  **`continuousOn_aggTree`** / `continuousOn_lawK` / `continuousOn_labourK` (capital is a quotient
  map from the compact set of histories with shock `z`). Standard axioms only. Next AK2.
