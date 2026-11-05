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
  contraction is exhibited yet (that is LS4). Standard axioms only. Next LS3.
