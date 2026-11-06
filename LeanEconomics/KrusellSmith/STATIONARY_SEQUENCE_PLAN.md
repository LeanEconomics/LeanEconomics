# Stationarity directly from the sequential equilibrium

Goal: a stationary (and, for small capital shares, unique and ergodic) distribution of an actual
sequential equilibrium, obtained from the sequence-state equilibrium (TS1–TS4) without a recursive
state space and without sunspot randomisation (contrast `STATIONARITY_PLAN.md`, DGMM/Cao).

## Idea

A sequence-state equilibrium is a function `μ : History Z → P(AState)` of the infinite shock
history, and the history evolves exogenously, `ω ↦ cons z' ω` with probability `π(ω 0, z')`. If the
history is drawn from a law `P` that this extension leaves invariant, then `(ω 0, μ ω)` has the same
law every period: **the equilibrium is a factor of the stationary shock process**. Under uniqueness
`(z, μ)` is Markov (`eq_lawOfMotion`), so that law is an invariant measure of the equilibrium law of
motion; ergodicity passes to factors. The only economic input is that `μ` be measurable in `ω`;
in the small-share class fading memory makes `μ` continuous.

## Setting

* `H = History Z = ℕ → Z` (newest first), compact metrizable (finite `Z`, product topology).
* Extension kernel `Ext ω = Σ_{z'} π(ω 0, z') δ_{cons z' ω}` on `H`; Feller (`cons` continuous).
  The employment process is not in `H`: it lives inside the households' distribution.
* Equilibrium kernel `Q (z, ν) = Σ_{z'} π(z, z') δ_{(z', lawOfMotion z ν z')}` on `Z × P(AState)`,
  continuous under uniqueness (`continuous_lawOfMotion`).

## Milestones

* **SS0** (small, `HistoryMarginals.lean`): burn-in in the two-part distance, `dist2_run`: from any
  start `ν`, `T` periods back along the realized shocks, within `(da, dm)` with
  `da + ω dm ≤ r*^T ω` (the norm step of `dist2_of_agree` applied to `run`).
* **SS1** Shock histories (generic, finite `Z`):
  * `Ext` Feller; existence of an `Ext`-invariant `P` (Krylov–Bogolyubov: port
    `Distribution/Stationary.exists_isStationary` to a generic compact Feller kernel).
  * Cylinder identity: `P(ω₀ = z₀, …, ωₙ = zₙ) = π(z₁, z₀) · P(ω₀ = z₁, …, ωₙ₋₁ = zₙ)` from
    invariance; the `ω 0`-marginal is `π`-stationary. Hence, when `π` has a unique stationary
    distribution `p` (e.g. `π ≥ ε_Z > 0`), **`P` is unique**: cylinders are a generating π-system,
    with `P(cyl) = p(zₙ) π(zₙ, zₙ₋₁) ⋯ π(z₁, z₀)` — the stationary chain run backwards.
  * **Ergodic**: an invariant set `A` (`Ext ω A = 1` for a.e. `ω ∈ A`) has `P A ∈ {0, 1}` —
    conditioning `P` on `A` gives another invariant measure (as in `MarkovEquilibrium/Ergodic`
    `cond_mem`), so uniqueness forces `P A ∈ {0, 1}`.
* **SS2** Factor theorem (generic `KSModel`, any sequence-state equilibrium `μ`, `μ` measurable):
  * `Λ := P.map (ω ↦ (ω 0, μ ω))`; **tomorrow's state has law `Λ`**:
    `∫ Σ_{z'} π(ω 0, z') δ_{(z', μ (cons z' ω))} dP = Λ` (invariance of `P` + measurability).
    No uniqueness needed: a stationary sequential equilibrium for every measurable sequence-state
    equilibrium.
  * Under `UniqueSequentialEquilibrium`: `μ (cons z' ω) = lawOfMotion (ω 0) (μ ω) z'`, so
    **`Λ` is `Q`-invariant**; **ergodic** (the preimage of a `Q`-invariant set is `Ext`-invariant).
* **SS3** Continuity of `μ` in the small-share class: fading memory (`dist2_of_agree`) gives
  `Dist2` closeness `r*^T ω` for histories agreeing over `T + 1` shocks, i.e. uniform continuity in
  the product topology for asset-Lipschitz test functions; asset-Lipschitz functions with bounded
  oscillation are uniformly dense in `C(AState)` (Stone–Weierstrass, `assetLipSubalgebra`), so
  `μ : H → P(AState)` is **continuous** (weak topology), hence measurable.
* **SS4** Uniqueness of the stationary distribution (small shares, `aggProb ≥ ε_Z > 0`,
  `idioProb ≥ ε > 0`):
  * Test class: `F : Z × P(AState) → ℝ`, bounded, Lipschitz in `ν` for the norm `da + ω dm`
    (cylinder functions `g(z) h(∫ f₁ dν, …, ∫ f_k dν)`, `fᵢ` asset-Lipschitz, `h` Lipschitz).
  * Coupling estimate: `|Qᵀ F (z, ν) − Qᵀ F (z, ν')| ≤ Lip F · r*ᵀ ω` (burn-in SS0 along common
    shocks), and `|Qᵀ F (z, ·) − Qᵀ F (z', ·)|` controlled by mixing of the aggregate chain
    (`(1 − |Z| ε_Z)ᵀ`, the Doeblin bound of `sum_abs_mul_le`).
  * For `Q`-invariant `Λ'`: `|∫ F dΛ' − ∫ F dΛ| = |∫ Qᵀ F dΛ' − ∫ Qᵀ F dΛ| → 0`.
  * Separation: these `F` form a point-separating subalgebra of `C(Z × P(AState))`
    (`eq_of_forall_assetLip` separates `ν ≠ ν'`); `Z × P(AState)` is Polish, so
    `ext_of_forall_mem_subalgebra_integral_eq_of_polish` gives **`Λ' = Λ`**.
  * Unique ⇒ ergodic (consistent with SS2).
* **SS5** CRRA + clamped Cobb–Douglas headline: for small capital shares (both slope versions),
  with both chains bounded below, the unique sequence-state equilibrium `μ*` is continuous in the
  history; `Λ*` (law of `(ω 0, μ* ω)` under the unique `P`) is **the unique stationary
  distribution of the equilibrium law of motion, and it is ergodic**; every sequential
  equilibrium converges to the stationary process pathwise at rate `r*ᵀ` (SS0) and in law (SS4).

## Beyond small shares (open)

SS2 gives stationarity for any *measurable* sequence-state equilibrium, without uniqueness (the
equilibrium is then Markov on histories, not on `(z, μ)`). The Schauder fixed point (TS3) need not
be measurable in `ω`. A measurable selection would need a different fixed-point space (no
compact convex set of equicontinuous assignments is available without a contraction), or
randomisation — which leads back to the DGMM route.

## Sizes (rough)

SS0 small; SS1 medium (Krylov–Bogolyubov port, cylinder π-system); SS2 small–medium
(measurability bookkeeping); SS3 medium (Stone–Weierstrass density into the weak topology);
SS4 largest (coupling + separation on `Z × P(AState)`); SS5 small.

## Status

* Planned 2026-11-06.
* **SS0 DONE** 2026-11-06 (`HistoryMarginals.lean`): `SlopeContraction.dist2_run` — burn-in in the
  two-part distance from any start (no marginal condition), `da + ω dm ≤ r*^T ω`.
* **SS1 DONE** 2026-11-06 (`ShockHistory.lean`): `ShockVal`, `ShockPath` (compact metrizable
  Borel), `cons`, `extMeasure`/`ext` (extension kernel), `integral_ext`, **`continuous_ext`**
  (Feller); `IsInvariant`; **`exists_invariant_ergodic`** (DGMM Cor 1.1 with the singleton
  correspondence `{ext ξ}`; no Krylov–Bogolyubov port needed); prefix cylinders `cyl`,
  `measure_cyl_succ_succ` (`P(z₀, z₁, …) = π z₁ z₀ · P(z₁, …)`), `marginal_stationary`;
  **`eq_of_invariant`** (unique when `π` has one stationary distribution; finite-dimensional laws
  by `ext_of_singleton`, measurable cylinders generate the product σ-algebra);
  **`ergodic_of_invariant`**; `stationary_unique_of_minor` (`π ≥ ε > 0`). Standard axioms only.
  Next SS2 (factor theorem).
* **SS2 DONE** 2026-11-07 (`StationarySequence.lean`): `stateOf`, `stateLaw P μ`;
  **`stateLaw_tomorrow`** (any measurable sequence-state equilibrium, no uniqueness: tomorrow's
  aggregate state has today's law); `eqKernel` (equilibrium law of motion on
  `ShockVal Z × P(AState)`), `measurable_eqKernel`; **`isInvariant_stateLaw`** (under uniqueness,
  `stateLaw` is invariant for the equilibrium Markov process); **`ergodic_stateLaw`** (ergodic when
  the shock law is). Standard axioms only. Next SS3 (continuity of `μ` for small shares).
* **SS3 DONE** 2026-11-07 (`SequenceStateContinuity.lean`): `continuous_integral_of_assetLip`
  (fading memory ⇒ integrals of asset-Lipschitz tests continuous in the product topology);
  **`continuous_seqState`** (Stone–Weierstrass density of `assetLipSubalgebra` + uniform limits),
  `measurable_seqState`; **`minMPC_smallShare_stationary`**: CRRA + clamped CD, small share,
  employment transitions bounded below ⇒ unique, continuous sequence-state equilibrium whose
  aggregate-state law is invariant and ergodic for the equilibrium kernel. Standard axioms only.
  Next SS4 (uniqueness of the stationary distribution).
* **SS4 + SS5 DONE** 2026-11-07 (`StationaryUnique.lean`): `qStep`/`qIter` (equilibrium
  expectations), `eIter` (expectations along the sequence-state equilibrium), `IsEqInvariant`,
  `integral_qStep`/`integral_qIter` (invariance via `lintegral_bind`), `integral_fst`,
  `marginal_stationary`; `DistLip` test functions; **`abs_qIter_sub_eIter_le`** (burn-in against
  the equilibrium, `C r*ᵀ (da + ω dm)`); **`integral_eq_of_isInvariant`** (no aggregate mixing
  needed beyond a unique stationary distribution of `π`); `distLipSubalgebra`,
  `distLipSubalgebra_separatesPoints`; **`eq_of_isInvariant`** (unique invariant distribution);
  headline **`minMPC_smallShare_unique_stationary`**: CRRA + clamped CD, small share, both chains
  bounded below ⇒ unique continuous sequence-state equilibrium whose aggregate-state law is the
  unique, ergodic invariant distribution of the equilibrium Markov process. Standard axioms only.
  **Programme complete** (SS0–SS5).
