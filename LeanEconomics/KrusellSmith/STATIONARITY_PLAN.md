# Stationary recursive equilibrium with an ergodic measure (Cao 2020 §6, via DGMM 1994)

Goal: a **stationary recursive equilibrium** of the Krusell–Smith economy — a compact set `J*` of
states, a transition `Π : J* → P(J*)` (a measurable kernel, possibly randomising over continuation
equilibria: "sunspots"), with `Π(ξ)` in the expectations correspondence at every state, and an
**invariant, ergodic** measure `γ*` on `J*` — Cao (2020) Theorem 4, from Duffie, Geanakoplos,
Mas-Colell and McLennan (1994) Theorem 1.1 and Corollary 1.1. Ergodicity is what licenses
simulation and GMM moments. Cao's extra "conditionally spotless" refinement is left for later.

Our asset cap `assetCap` is exactly Cao's constraint (32), which §6 needs anyway: it makes
distributions live on a compact set, so weak convergence carries means.

## Part I — the abstract theorem (DGMM 1.1, Corollary 1.1)

Setting: `J` compact metrizable, `G : J → Set (ProbabilityMeasure J)` with closed graph and
nonempty convex values.

**Theorem (DGMM 1.1).** There are `μ ∈ P(J)` and a measurable kernel `Π : J → P(J)` with
`μ.bind Π = μ` and `Π s ∈ G s` for `μ`-a.e. `s`. **Corollary 1.1**: `μ` can be chosen ergodic
(every `Π`-invariant set has measure 0 or 1).

Proof plan (DGMM pp. 750–751):

1. **Measures as a compact convex set in a locally convex space.** Embed `P(J)` into
   `C(J) → ℝ` (product topology, locally convex, Hausdorff) by `μ ↦ (f ↦ ∫ f dμ)`. The weak topology
   is the induced one; the image is compact (Prokhorov: `CompactSpace (ProbabilityMeasure J)`) and
   convex (mixtures). Continuous linear functionals on the image are `ρ ↦ ∫ f dρ`.
2. **The correspondence on `P(J)`**: `Φ(μ) = {E (m₂ ν) : ν ∈ P(Gr G), m₁ ν = μ}`, with `m₁, m₂`
   the marginals and `E : P(P(J)) → P(J)` the mean (`∫ f dEη = ∫∫ f dρ dη`). Convex, closed graph
   (continuous images from the compact `P(Gr G)`), nonempty (finitely supported `μ` are dense;
   `m₁(P(Gr G))` is compact, hence closed, and contains them).
3. **Fan–Glicksberg** (port from `SetValuedFixedPoints`, with Kakutani): a fixed point
   `μ = E (m₂ ν)`, `m₁ ν = μ`.
4. **Disintegrate** `ν = μ ⊗ P` (Mathlib `condKernel`; `J × P(J)` is standard Borel since `P(J)` is
   compact metrizable). Set `Π s = E (P s)`: measurable, and `μ.bind Π = E (m₂ ν) = μ`.
5. **`Π s ∈ G s` a.e.** If `ρ ∉ G s` (closed convex), Hahn–Banach separates by some `f ∈ C(J)`;
   approximate `f` from a countable dense set (`C(J)` is separable for compact metric `J`). For
   each `f` in the countable set, `min_{G s} ∫ f ≤ ∫ f dΠ s ≤ max_{G s} ∫ f` a.e. (DGMM's
   contradiction with `ν(Gr G) = 1`). Countable intersection.
6. **Ergodic** (Corollary 1.1): Krein–Milman (`IsCompact.extremePoints_nonempty`) on the compact
   convex set of such invariant measures; an extreme point is ergodic (split along an invariant
   set otherwise).

## Part II — the Krusell–Smith application (Cao Theorem 4)

7. **States**: `Ξ = Z × P(AState) × (AState →ᵇ ℝ) × (AState →ᵇ ℝ)` (shock, distribution,
   households' value, saving policy), metrizable.
   `J* = {(z, μ, rootValue K, rootPolicy K) : K a sequential equilibrium from (z, μ)}`.
   **Compact**: a finite union over `z` of continuous images of the compact closed equilibrium
   graph (`isClosed_equilibriumGraph`, `isCompact_pi`), using continuity of the value function
   and policy in the path, uniformly in assets (`Continuity.lean`, `continuous_policy`, compact
   domain ⇒ continuous into the sup norm).
8. **Expectations correspondence** `G(ξ) ⊆ P(J*)` (Cao's `G̃`): `γ ∈ G(ξ)` iff
   (i) its marginal on (shock, distribution) is `Σ_{z'} π(z, z') δ_{(z', μ pushed by the policy)}`;
   (ii) the value is the Bellman value against `E_γ[Σ_{e'} q(e, e') v'(a', e')]`, attained by the
   policy. **Convex** (affine in `γ`); **closed graph** (maximum theorem; `maxValue` continuity
   already used in `Continuity.lean`).
9. **Self-justified**: for `ξ ∈ J*` from an equilibrium `K`, `γ = Σ_{z'} π(z, z') δ_{ξ_{[z']}}`,
   with `ξ_{[z']}` the root data of the continuation `shiftPath K [z']`, lies in `G(ξ)` and is
   supported on `J*` (continuation theorem; `valueFunction_shift`, `policy_shift`; this is V1/V2).
10. **Main theorem**: existence of a stationary recursive equilibrium `(J*, Π, γ*)` with `γ*`
    ergodic, for every `KSModel` (hence log / CRRA with unclamped Cobb–Douglas prices, by C4).

## Status

* **S0 done**: `FixedPoint/Schauder.lean`, `Kakutani.lean`, `FanGlicksberg.lean` ported from
  `LeanDynamicProgramming/DynamicProgramming` branch `ext-set-valued-fixed-points` (commit
  0016ead, `Extensions/SetValuedFixedPoints`), namespace `LeanEconomics.FixedPoint`.
  `fanGlicksberg`: nonempty compact convex `K` in a locally convex Hausdorff space, `F` with
  nonempty convex values in `K` and closed graph on `K` ⇒ fixed point.
* **S1 done** (`MarkovEquilibrium/Measures.lean`): `embed : P(J) → ((J →ᵇ ℝ≥0) → ℝ)`,
  `isEmbedding_embed`, `mix`, `embed_mix`, `convex_range_embed`, `isCompact_range_embed`;
  **`borel_eq` / `borelSpace`** (Giry σ-algebra = Borel σ-algebra of the weak topology, not in
  Mathlib: portmanteau lower semicontinuity one way, second countability + Lindelöf the other),
  so `P(P(J))` is compact; `mean` (via `Measure.bind`), `lintegral_mean`, `continuous_mean`;
  `marginalFst/Snd` and continuity.
* **S2 done** (`MarkovEquilibrium/MeanFixedPoint.lean`): `exists_supported` (every `μ` is the
  first marginal of a measure supported on the closed graph; no density argument: push `μ` along
  measurable selections exact up to `ε`, from the first ball of a dense sequence containing the
  state, and take a weak limit point, using that closed thickenings `thickGraph` are weakly closed
  conditions shrinking to the graph); `Phi`, `convex_Phi` (`map_mix`, `mean_mix`),
  `isClosed_graphOn_Phi` (continuous image of the compact supporting measures);
  **`exists_mean_fixedPoint`**: `ν (Gr G) = 1 ∧ m₁ ν = E (m₂ ν)`. Convexity of `G s` not yet used.
* **S3 done** (`MarkovEquilibrium/Stationary.lean`): **`exists_stationary`** (DGMM Theorem 1.1):
  `μ`, measurable `T : J → P(J)`, `μ.bind T = μ`, `T s ∈ G s` a.e. Disintegration by
  `Measure.condKernel` (`isCompletelyMetrizableSpace` makes `P(J)` standard Borel); `T s = E (P s)`.
  Step 5 simplified: exact disintegration gives `P s (G s) = 1` a.e., then the barycentre lemma
  `mean_mem` (Hahn–Banach in the product; continuous functionals are finite coordinate
  combinations by `LinearMap.mem_span_iff_continuous`, so they commute with the mean). No
  separable `C(J)` needed.
* **S4 done** (`MarkovEquilibrium/Ergodic.lean`): **`exists_ergodic`** (DGMM Corollary 1.1): as
  `exists_stationary`, plus every `A` with `T s A = 1` a.e. on `A` has `μ A ∈ {0, 1}`. Krein–Milman
  on the compact `embed '' fixedPoints G` (no convexity needed); an extreme fixed point `ν` cannot
  be split: conditioning on `A × P(J)` and `Aᶜ × P(J)` gives fixed points (`cond_mem`, via
  `setLIntegral_invariant`, `compl_invariant`) mixing to `ν`. S3 refactored: `condLaw`,
  `transition`, `setLIntegral_transition`, `bind_transition`, `ae_transition_mem`.
  **Part I (abstract DGMM) complete.**
* Next: S5 (Krusell–Smith state space).

## Milestones

* **S0** Port Kakutani and Fan–Glicksberg into `LeanEconomics/FixedPoint/` (from
  `LeanDynamicProgramming/.../SetValuedFixedPoints`, branch `ext-set-valued-fixed-points`).
* **S1** Step 1 (embedding of `P(J)`), mixtures, the mean map `E`, marginals.
* **S2** Steps 2–3 (the correspondence `Φ`, nonemptiness by density, fixed point).
* **S3** Steps 4–5 (disintegration, kernel, a.e. membership by separation) — DGMM Theorem 1.1.
* **S4** Step 6 (ergodic) — DGMM Corollary 1.1.
* **S5** Steps 7–9 (KS state space, `J*` compact, `G` convex with closed graph, self-justified).
* **S6** Step 10 and corollaries.

## Risks

* **Size.** Part I is general measure theory not in Mathlib; expect it to be the bulk. It may
  belong in its own module (`Probability/StationaryMarkov` or similar), reusable beyond KS.
* Density of finitely supported probability measures in `P(J)` (step 2) may need proving; an
  alternative is nonemptiness via a direct construction for each `μ`.
* Measurability of `Π` and the a.e. argument need the disintegration on the closed subset
  `Gr G ⊆ J × P(J)`; standard Borelness of `P(J)` must be assembled (compact metrizable ⇒ Polish).
* Continuity of the root value into the **sup norm** (step 7): `Continuity.lean` gives pointwise /
  weighted statements; may need an equicontinuity or compactness upgrade.
* What is proved is DGMM's sunspot-randomised equilibrium; Cao's "conditionally spotless"
  refinement and Santos–Peralta-Alva's Feller conditions are not attempted.
