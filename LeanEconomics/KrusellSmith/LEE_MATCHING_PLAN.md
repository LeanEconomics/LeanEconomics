# Lee's saddle paths and matched expectations on the sequence state

Goal: use Lee (2026 WP), *Dancing on the Saddles* (`HARBC_Examples/HanbaekLee/Lee_Saddle_2026.pdf`),
to give the fading-memory step TS5(c) of `SEQUENCE_STATE_PLAN.md`, and from it an error theorem
for the matched-expectations-path (MEP) method.

## What Lee proves (and assumes)

* **Theorem 1 / Prop 8** (monotone coordinate): along a frozen-regime orbit `Φ_{t+1} = Γ_A Φ_t`
  converging to the conditional steady state, a strictly monotone aggregate (e.g. `K`) is
  injective on the orbit and its limit, so it indexes the distribution *within a spell*.
* **Theorem 2** (synchronization): if the maps `Γ_A` are a *uniform contraction* at rate `λ` on
  a closed forward-invariant set `U` of finite diameter (Definition 7), then every infinite
  regime history has a unique consistent distribution `Φ*(ω)` (the backward limit, independent
  of the start), and two histories agreeing over their last `T` periods have distributions
  within `λ^T diam U`.
* Lee **assumes** an RCE with a Markov law of motion `Γ_endo(Φ, A)` and the contraction.

## Where it sits here

* The sequence-state equilibrium (TS3–TS4) is an assignment on infinite histories — Lee's
  `Φ*(ω)` is exactly such an object.
* A Markov law of motion exists under uniqueness: `eq_lawOfMotion` (TS5(a)); a proved class
  with uniqueness is Track A's `κ < 1`. Without uniqueness the update depends on future prices
  (no fixed map `Γ_A`), so the contraction would have to be placed on the household-plus-
  expectations block — not attempted.
* MEP: the branch `cons z' ω_t` has known capital (`capital_cons`: mean saving today, whatever
  `z'`); the continuation is taken from a matched date `s` with `z_s = z'`, `K_s ≈ K_{t+1}`.

## Milestones

* **LS1** (`KrusellSmith/Synchronization.lean`, abstract metric space, maps `Γ z z'` indexed by
  today's and tomorrow's shock): backward iteration `run`; **suffix synchronization** for every
  consistent assignment in `U` (`λ^T D`, no completeness needed); **uniqueness** of consistent
  assignments; **existence** (complete space, closed nonempty `U`) as the backward limit, and
  `dist (Φ ω) (run T ω x) ≤ λ^T D` from any start; **Lee Theorem 1** (strictly monotone /
  antitone coordinate converging to its value at the limit is injective on orbit ∪ limit).
* **LS2** (KS): under `UniqueSequentialEquilibrium` + uniform contraction of `lawOfMotion` in a
  metric on `P(AState)` (Lévy–Prokhorov), the sequence-state equilibrium is unique, equals the
  backward limit, and forgets old shocks at rate `λ^T`.
* **LS3** (matching): MEP error theorem — exact when the matched history has the same
  `(z, μ)` and uniqueness there (TS5(a)); `≤ λ^T diam` for distributions, and `→ 0` for value
  and policy (uniform continuity on compact `P(AState)`), when the matched history agrees with
  the branch's last `T` shocks; matching on `K` exact within a monotone spell (LS1 Thm 1).
* **LS4** (research): the contraction from primitives in a Wasserstein metric (policy slope in
  assets + price sensitivity of saving, Track A), possibly only in the `κ < 1` class.

## Status

* Planned 2026-11-05.
* **LS1 DONE** 2026-11-05 (`Synchronization.lean`): `History.drop`, `run`, `run_add`,
  `Consistent` (+ `consistent_iff_cons`, `Consistent.eq_run`), `UniformContraction` (Lee Def 7),
  `run_mem`, `UniformContraction.dist_run_le`; **`Consistent.dist_le_of_agree`** (suffix
  synchronization, any consistent assignment in `U`, no completeness), `Consistent.dist_run_le`
  (start washes out), **`Consistent.eq`** (uniqueness), **`exists_consistent`** (complete `X`,
  closed nonempty `U`, backward limit via `cauchySeq_of_le_geometric`);
  **`injOn_orbit_of_strictMono` / `_strictAnti`** (Lee Thm 1, the `t* = ∞` case; the finite-`t*`
  case is the same argument on a finite orbit, not stated). Standard axioms only.
* **LS2 DONE** 2026-11-05 (`SequenceStateSynchronization.lean`): metric left open — any injective
  `ι : P(AState) → X` into a metric space (Lévy–Prokhorov would need a metric on `AState`,
  whose `Idio E` factor has only the discrete topology; not set up). `lawMap`,
  `IsSeqStateEquilibrium.consistent` (under uniqueness), `LawContraction ι S c D` (Lee Def 7,
  hypothesis), `LawContraction.uniformContraction` (induced metric); **`dist_le_of_agree`**
  (fading memory), **`dist_run_le`** (burn-in from any start in `S`), **`eq_of_contraction`**
  (uniqueness), **`existsUnique_seqStateEquilibrium`** (`S = univ`). No instance of the
  contraction is exhibited yet (that is LS4). Standard axioms only.
* **LS3 DONE** 2026-11-05 (`SequenceStateMatching.lean`): `exists_uniform_of_embedding`
  (continuous injection on compact `P` → uniform control of continuous `G` on `P × Y`, via
  `ContinuousMap.curry` + Heine–Cantor on `range ι`); `recursiveValue`,
  `continuous_recursiveValue`, `seqValue_eq_recursiveValue`; `integral_assets_cons` (matching key:
  branch capital = mean saving); exact matching `matching_exact_seqPolicy/_seqValue/_prepend`;
  within-spell capital matching `eq_of_capital_eq_of_orbit`, `matching_capital_seqPolicy`
  (Lee Thm 1); approximate matching **`matching_seqPolicy`, `matching_seqValue`** (∀ ε ∃ T₀,
  agreement over `T + 1 ≥ T₀ + 1` shocks ⇒ policy/value within ε at every household state;
  needs `ι` continuous + injective, contraction on `univ`). Standard axioms only. Next LS4
  (research: contraction from primitives).

## LS4 route (2026-11-06)

* **Metric**: the asset-Lipschitz dual distance. `DistLE d ν ν'`: every bounded continuous `f`
  that is `L`-Lipschitz in assets (any behaviour across idiosyncratic states) integrates to within
  `L d`. It forces equal idiosyncratic marginals (indicators are `0`-Lipschitz), hence the same
  labour path, so only capital feeds back into prices — exactly Track A's setting. Equal
  marginals give `DistLE (2 assetCap)`; `DistLE 0` gives equality (Stone–Weierstrass:
  asset-Lipschitz functions are a point-separating subalgebra, AState is Polish).
* **Root distance in the tree**: `gapFrom θ d₀ P` (`d₀` at the root, `θ G + P` down), the
  two-root version of `integral_nodeDist_sub_le`.
* **Capital paths** (Track A, `κ < 1`): `λ^{|h|} |K_h − K'_h| ≤ d / (1 − κ)` for the equilibrium
  paths from `ν, ν'` (one step `η ↦ d + κ η`, iterated from `assetCap`).
* **Law of motion**: `DistLE (r d)` for tomorrow, `r = R̄ + G / (1 − κ)`, `G = ℓ C + A / m` (the
  root policy gain). `r < 1` needs `R̄ < 1` (saving slope bound `θ = R̄`; automatic in the
  `κ < 1` class, where `α` is tiny and `R ≈ 1 − δ`) and weak price feedback.
* **Sequence state**: if equilibrium marginals depend only on today's shock (KS's design of the
  employment process), fading memory `DistLE (r^T 2 assetCap)`, burn-in from any start with
  the right marginal, **uniqueness**, and an **explicit matching bound** on saving,
  `G r^T 2 assetCap / (1 − κ)`, and on capital paths.
* Not done: marginals that depend on history (labour then differs: needs prices Lipschitz in
  labour and Dobrushin mixing of the employment chain); the minimal-MPC slope bound that would
  allow `R̄ ≥ 1`.
* **LS4 DONE** 2026-11-06 (`LawContraction.lean`): `DistLE` (asset-Lipschitz dual distance),
  `DistLE.initMass_eq`, `distLE_of_initMass_eq` (`2 assetCap`), `DistLE.eq_of_zero`
  (Stone–Weierstrass via `assetLipSubalgebra`, Polish AState); `gapFrom`,
  `integral_nodeDist_sub_le_of_distLE`; `ContractionHyp.eqPath_gap` (`d / (1 − κ)`),
  `recursivePolicy_gap` (`G d / (1 − κ)`), **`distLE_lawOfMotion`** (rate
  `lawRate = R̄ + G / (1 − κ)`); on the sequence state, with marginals depending only on today's
  shock: **`distLE_of_agree`**, **`distLE_run`**, **`seqPolicy_gap_of_agree`**,
  `seqCapital_gap_of_agree` (explicit matching bounds), **`eq_of_lawRate_lt_one`** (uniqueness).
  Standard axioms only. Open: history-dependent marginals; minimal-MPC slope for `R̄ ≥ 1`;
  ~~numeric check~~ superseded by the analytic small-share theorem below.
* **Small capital shares DONE** 2026-11-06 (`SmallShare.lean`, analytic, no numerics): for CRRA
  (any `γ > 0`) and clamped Cobb–Douglas with depreciation `δ > 0`, all other parameters fixed,
  `exists_smallShare`: ∃ `α₀ > 0` such that for every share `α ∈ (0, α₀)`, with `λ = 1`,
  `κ < 1` and `lawRate < 1`; `smallShare_contraction`: unique sequential equilibrium + a
  `ContractionHyp` with both. Proof: every constant is an explicit continuous expression in `α`
  at `α = 0` (`smallR`, …, `smallRate`, identified by `rfl`), where `ℓ = 0`, `κ = 0`,
  `r = 1 − δ`. Standard axioms only.
* **Employment marginals + exactly one equilibrium DONE** 2026-11-06 (`EmploymentMarginals.lean`,
  09265a3): `EmploymentDesign` (KS's marginals `m z` carried into each other, transitions
  `≥ ε > 0`); `sum_abs_mul_le` (Doeblin contraction in `ℓ¹`);
  **`IsSeqStateEquilibrium.initMass_eq_design`** (every sequence-state equilibrium has marginal
  `m (ω 0)`), discharging LS4's marginal hypothesis;
  **`smallShare_existsUnique_seqStateEquilibrium`** (CRRA + clamped CD, `δ > 0`, small share:
  exactly one sequence-state equilibrium).
* **Minimal-MPC slope DONE** 2026-11-06 (`MinimalMPC.lean`, `SlopeContraction.lean`,
  `MinMPCSmallShare.lean`; `Contraction.lean` split into `ContractionBase` + `λR̄ < 1`):
  `abs_policy_sub_le_minMPC` (CRRA, returns in `[R̲, R̄]`, `(βR̄)^{1/γ} < R̲`, floor slack along
  iterates: saving slope `θ = R̄ (βR̄)^{1/γ}/R̲`; EGM power-mean step `mpcBound_bellman`,
  iterates `mpcBound_iterate`, limit via Berge on the continuation
  `continuousAt_argmax_selection`); `SlopeContraction` (Track A uniqueness `κ_θ = λG/(1−λθ)` and
  the LS4 law contraction `r_θ = θ + G/(1−κ_θ)`, only `λθ < 1` needed); CRRA instance
  `crraSavingSlope` (iterate floor slack `slackOf_iterate_radius`, `CobbDouglas.returnLo`);
  **`minMPC_smallShare`**, **`minMPC_smallShare_existsUnique_seqStateEquilibrium`** for
  `0 ≤ δ < 1` with `(β(1−δ))^{1/γ} < 1−δ`, and
  **`zeroDepreciation_smallShare_existsUnique_seqStateEquilibrium`** (`δ = 0`, no condition).
