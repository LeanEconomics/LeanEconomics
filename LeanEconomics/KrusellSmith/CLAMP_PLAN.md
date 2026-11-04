# Removing the capital clamp (after Cao 2020, Lemma 9)

Goal: for CRRA utility (log included) and Cobb–Douglas production, show that in **every**
sequential equilibrium of the clamped economy, capital stays in `[capLo, capHi]` at every node.
Then prices are the true (unclamped) Cobb–Douglas marginal products everywhere, and existence
(sequential, and the value-state recursive equilibrium) holds for the unclamped economy.
`capHi ≥ assetCap` makes the upper clamp slack for free; the work is the lower bound.

## Cao's argument, and how it changes here

Cao (Lemma 9, part 1) works by induction: suppose `K_{t−1} ≥ K̲` but `K_t < K̲`. Then the return at
`t` is huge, so the Euler equation forces consumption at `t − 1` to be a small fraction `ρ` of
consumption at `t`. Aggregated, that says output at `t − 1` is mostly saved, contradicting
`K_t < K̲`. He uses: Euler with `π = min` transition probability, Jensen with convex `u'`
(`u''' ≥ 0`), bounded relative risk aversion (`ρ(α) = α^{-1/σ̄}`), the fact that `K_t` is the same
for all children, and Cobb–Douglas asymptotics (`F ~ K^α`, `F_K ~ K^{α−1}`).

Differences in our model:

1. **The asset cap.** The Euler inequality `u'(c) ≥ β E[R u'(c')]` (`euler_ge`) needs saving
   below `assetCap`. For households at the cap, use `c = cash − assetCap ≤ (R a + w ē) · a'/assetCap`
   with `a' = assetCap`, so for **every** household
   `c_h ≤ ρ · E[c_child] + (a'/assetCap) · (R_h · assetCap + w_h · ē)`.
   Integrating, the extra term is at most `K_c R_h + K_c w_h ē / assetCap`, with `K_c = ∫ a'`.
2. **No homogeneity at the parent.** Aggregate consumption at `h` is
   `R_h K_h + w_h L_h − K_c`. Subtracting the cap term leaves
   `R_h (K_h − K_c) + w_h (L_h − K_c ē/assetCap) − K_c`, and with `K_c < capLo ≤ K_h` this is at
   least `wageLo · (effLo − capLo ē/assetCap) − capLo`. Only the wage lower bound
   (`CobbDouglas.wageLo_le_wage`) is needed.
3. **Clamped prices at the child.** If `K_c < capLo` the child faces the clamped price
   `R(capLo, L_c)`, still high. Aggregate child consumption is at most cash on hand:
   `R_c K_c + w_c L_c ≤ (1 − δ) capLo + z̄ capLo^α L_c^{1−α}` (Cobb–Douglas homogeneity at
   `capLo`).
4. **CRRA instead of bounded relative risk aversion**: `ρ(A) = A^{-1/γ}` exactly, from
   `c^{-γ} ≥ A m^{-γ}`.
5. **Diagonal persistence**: keep only the child with the same aggregate shock, so we only need
   `π = min_z aggProb z z > 0`.

**The condition on `capLo`** (B):

    wageLo(capLo) · (effLo − capLo · effHi / assetCap) − capLo
      > (β π R_lo(capLo))^{−1/γ} · ((1 − δ) capLo + z̄ capLo^α effHi^{1−α}),

with `R_lo(capLo) = 1 − δ + α z̲ capLo^{α−1} effHi^{1−α}` and
`wageLo(capLo) = (1 − α) z̲ capLo^α effHi^{−α}`. The left side is of order `capLo^α`, the right of
order `capLo^{α + (1−α)/γ}`, so (B) holds for all small `capLo`, with an explicit threshold.

## Status

* **C1 done** (`Aggregates.lean`): `cashAt`, `savingAt`, `consumptionAt`, `effFn` as bounded
  continuous functions; `meanCapital_cons` (child capital = mean saving at the parent, for every
  `z'`), `integral_cashAt` (= `R_h ∫ a + w_h L_h`), `integral_consumptionAt`,
  `integral_consumptionAt_eq` (along an equilibrium: `R_h K_h + w_h L_h − K_{z'::h}`),
  `integral_consumptionAt_cons` (child consumption as the parent's expectation). The names
  `nodeCash` etc. were taken (`Continuity.lean`).
* **C2 done** (`CRRAEuler.lean`): `convexOn_rpow_neg` (`c ↦ c^{-γ}` convex on `(0, ∞)`, via
  monotone derivative); `consumption_le_child` (below the cap:
  `c ≤ (β π R')^{-1/γ} Σ_{e'} idioProb(z, z, e, e') c'(a', e')` at the same-shock child, from
  `euler_ge`, one child, Jensen, rpow inversion; needs `R' > 0`); `consumption_le` (every
  household, adding `(a'/assetCap)(R · assetCap + w ē)`). Generic in `M` with `u' = c^{-γ}` above
  the floor and `Slack`.
* **C3 done** (`CapitalBound.lean`): `aggregate_le` (integrated bound:
  `R_h K_h + w_h L_h − K_c ≤ (βπR_c)^{-1/γ}(R_c K_c + w_c L_c) + K_c (R_h + w_h ē/cap)`), and
  `capital_ge`: generic in the price functions — if capital starts at least `k` and condition
  `hB` holds (for `K_h ≥ k > K_c ≥ 0`, `L, L' ∈ [Llo, Lhi]`:
  `(βπR(z,K_c,L'))^{-1/γ}(R(z,K_c,L') k + w(z,K_c,L') L') < w(z,K_h,L)(L − kē/cap) − k`), capital
  is at least `k` at every node. Needs `π ≤ aggProb z z`, `grossReturn > 0`, `Slack`.
* **C4 done** (`CobbDouglasCapital.lean`): constants `wageConst` D, `eulerConst` C₁,
  `outputConst` C₂ (independent of `capLo`); `LowerClampOK` / `CapLoOK`
  (`k ≤ 1`, `kē ≤ cap·L̲/2`, `k^{1−α} < D/2`, `C₁(1+C₂)k^{(1−α)/γ} < D/2`); `priceCondition`
  (Cobb–Douglas satisfies `hB` at `k = capLo`); `exists_capLo` (explicit threshold `k₀`);
  `crra_capital_mem` (every SE from mean ≥ capLo stays in `[capLo, capHi]`, if
  `assetCap ≤ capHi`, `π ≤ aggProb z z`, labour clamp = efficiency range);
  `crra_unclamped_prices`, `crra_exists_unclamped_equilibrium`. **Clamp never binds.**
* Next: C5 (MATLAB `k₀` at KS calibrations).

## Milestones

### C1. Aggregation identities (any `KSModel`; `Aggregates.lean`)

* `meanCapital_cons`: capital at every child `z' :: h` is `∫ policy dμ_h`, the same for all
  `z'` (from `integral_pushNode` with `f = assets`, `Σ nextProb = 1`).
* consumption at a node as a bounded continuous function on `AState` (`continuous_policy`);
  `∫ consumption dμ_h = R_h K_h + w_h L_h − K_child` along an equilibrium;
  `∫ cash dμ_h = R_h K_h + w_h L_h`;
* the child's consumption integrates back to the parent (`integral_pushNode`).

### C2. The per-household bound (CRRA, `KSInada` floored model)

* `consumption_le_child`: if saving `< assetCap`, then
  `c_h ≤ (β π R_child)^{−1/γ} Σ_{e'} idioProb(z_h, z_h, e, e') c_child(a', e')` at the child
  `z_h :: h`. From `euler_ge`, dropping other children, Jensen for the convex `c ↦ c^{−γ}`, and
  rpow algebra.
* the cap version, and the combined bound valid for every household.

### C3. The aggregate inequality and the induction (`CapitalBound.lean`)

* integrate C2 over `μ_h`, using C1;
* if `K_h ≥ capLo` and `K_child < capLo`, then (B) fails: contradiction;
* induction on the tree: if the initial mean is at least `capLo` and (B) holds, every sequential
  equilibrium has `K_h ∈ [capLo, assetCap]` at every node.

### C4. Unclamped theorems

* `crraEconomy` with `capHi ≥ assetCap` and (B): every sequential equilibrium has unclamped
  Cobb–Douglas prices at every node; so a sequential equilibrium of the unclamped economy exists
  (with the asset cap), and so does the value-state recursive equilibrium.
* `exists_capLo`: an explicit `capLo* > 0` such that (B) holds for all `capLo ≤ capLo*`.

### C5. Numbers

MATLAB: `capLo*` at Krusell–Smith style calibrations, compared with steady-state capital (it is
a clamp that provably never binds, so its size matters only for the initial condition
`mean μ₀ ≥ capLo`).

## Risks

* Jensen for `c ↦ c^{−γ}`: Mathlib has `convexOn_rpow` only for `p ≥ 1`; prove convexity on
  `Ioi 0` from the second derivative (`convexOn_of_deriv2_nonneg`) or via `convexOn_inv`-style
  lemmas.
* Integrability and measurability of consumption at a node: continuous and bounded, so fine.
* `KSEnvironment` needs `π = min_z aggProb z z > 0` (new hypothesis), and `labLo = effLo`,
  `labHi = effHi` as in `logEconomy_exists_equilibrium`.
* The induction needs the initial distribution's mean to be at least `capLo` (as in Cao).
