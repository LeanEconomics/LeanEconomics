# Extending the existence results (2026-11-08)

User request: "do 1, 2, and 5, 6" from the list of improvements to existence.

## 1. The asset cap — DONE (`AssetCap.lean`, f102ee6 + aeea86d)

* `policy_le_of_slope`: saving ≤ `w̄ e + θ a` when saving is `θ`-Lipschitz in assets.
* `policy_lt_assetCap_of_slope`: `θ < 1`, `w̄ e + θ ā < ā` ⇒ saving strictly below the cap at every
  state, along every price path. Threshold `w̄ e / (1 − θ)` does not involve the cap.
* `withCap`, `capEmb`, `valueFunction_capEmb`, `policy_capEmb`, `nodeDist_capEmb`,
  **`isSequentialEquilibrium_capEmb_iff`**: shrinking the cap to `ā₀` with large-cap saving from
  below `ā₀` staying below `ā₀` changes no sequential equilibrium from distributions on `[0, ā₀]`.
* **`minMPC_smallShare_capIrrelevant`**: small-share CRRA/CD instance.
* Limit: needs `θ < 1` (minimal-MPC slope; small return spread). The CRRA floor depends on the cap
  through the value bound, so the comparison is within one economy and its smaller-cap versions.

## 2. Borrowing limit — DONE (core refactor + `Borrowing.lean`, dfccbe5)

* `KSModel.borrowLimit b ≥ 0`; asset coordinate = position + b ∈ `[0, ā]`; cash
  `R a + w e − R b`; `consFloor ≤ w e − R b` (income at the limit covers the floor); price functions
  read the shifted mean. Same fields on `KSInada`; all existing constructions set `b = 0`.
* ~35 files adapted; statements that spell out cash gained `− R b`; `cashScale = ā + b + Σ e`.
* Results that genuinely need `b = 0` now assume it: `savingMonotone_of`, Light's step
  (`incDiff_bellman` and up), `capital_ge` / `aggregate_le` (Cao Lemma 9 aggregation). A higher
  return hurts debtors, so the complementarity route is a no-borrowing route.
* The corner economy is generalised (net-income lower bounds `w̲ e − R̄ b`).
* **`crraBorrow_exists_sequentialEquilibrium`**: CRRA, clamped CD prices of actual capital
  `K − b`, `0 ≤ b < w̲ e̲ / R̄`.

## 5. Measurable sequence-state equilibrium beyond small shares — ATTEMPTED, STALLED

Goal: a sequence-state equilibrium `μ : History → P(AState)` measurable in the history, without a
contraction.

Routes examined (on paper, before coding):

* **Young-measure space** (measurable `μ` modulo `P`-null sets, weak-* topology of
  `L¹(P; C(AState))*`): compact convex, and capital at a node `g` (an integral against
  `μ ∘ prepend g`) is weak-* continuous in `μ`. But the household's policy is a nonlinear function of
  the whole price path at `ω`, and weak-* convergence of the capital paths is not pointwise, so the
  update is not continuous. This is the obstruction DGMM remove by randomisation.
* **Pullback from the far past** (`μ_T(ω)` = run from a fixed `ν` started `T` periods back, each
  measurable): limits need a single subsequence for all `ω`. Ultralimits are not shift-invariant
  and not measurable in general; Banach limits are shift-invariant but do not commute with the
  nonlinear law of motion.
* **What does go through**: (a) contraction classes (done: `StationaryUnique.lean`, measurable and
  continuous); (b) with exogenous prices the law of motion is linear in `ν`, so Cesàro/Banach
  averaging commutes with it, but pointwise convergence (hence measurability) still needs forgetting
  of the initial condition; (c) under uniqueness, an invariant *random* measure for the skew product
  `(ξ, ν) ↦ (shift ξ, Γ(ξ, ν))` on `ShockPath × P(AState)` with shock marginal `P` (Crauel-type,
  Krylov–Bogolyubov) — a randomised equilibrium, weaker than the DGMM result already proved.

Conclusion: no new pure measurable result without new ideas. Candidate idea for later: compactness
in `L¹` (strong) via a uniform modulus of the policy in the *price path* plus a uniform modulus of
the equilibrium price path in the history — i.e. a quantitative version of the closed-graph
continuity, which is what the contraction supplies.

## 6. Minimal-state recursive equilibrium for Cobb–Douglas without uniqueness — PLAN ONLY

Known: under uniqueness (`isRecursive`) and for complementarity economies via the greatest
equilibrium (`GreatestEquilibrium.lean`, needs `SavingMonotone`, fails for CD and now also needs
`b = 0`). A minimal-state RE exists iff a consistent selection of sequential equilibria exists on
the reachable `(z, μ)`.

Routes:

* **R1 another order.** With CD, `∂(R a + w e)/∂K = R_K a + w_K e` has the sign of `K e − L a`: higher
  capital raises the cash of the asset-poor and lowers that of the asset-rich. An order on
  cross-sections under which saving is monotone in the capital path would need to rank households
  by `K e − L a`. Candidate: dominance in *cash on hand* rather than assets, or a two-sided order
  (poor up, rich down). First task: test whether Tarski's greatest-fixed-point argument survives
  with such an order on capital paths, at least for log utility with constant savings rates in
  wealth (where saving is affine in cash).
* **R2 selection by continuation.** Build a selection on the reachability graph forward from roots;
  conflicts arise exactly when two roots reach the same `(z', μ')` with different inherited
  continuations. Characterise when the reachability graph is a forest (no conflicts) — e.g. when
  `μ ↦ lawOfMotion` is injective on reachable sets.
* **R3 randomisation** (Cao's generalized RE / DGMM): already available; not the minimal state.

Honest assessment: R1 is the only route that could give the result; it is open research and may
fail. Nothing coded.

### R1 attempted 2026-11-08 — negative

* `CobbDouglasRedistribution.lean`: **`cash_deriv`**, `∂(R a + w e)/∂K = α(1−α) A K^{α−2} L^{−α}
  (K e − L a)`; **`integral_redistribution_eq_zero`**, the change integrates to zero over any
  cross-section with mean assets `K` and mean efficiency `L` (Euler's theorem).
* Consequences (argued, not formalised): (i) a one-node rise in capital raises the saving of
  households with `a/e < K/L` and lowers the others' (future prices unchanged, saving increasing in
  cash), so **no order containing one-node perturbations of capital makes every household's saving
  monotone** — R1 as stated cannot work; (ii) with saving affine in cash at a common slope the
  redistribution has no aggregate effect, and the remaining future-price effects (lower returns,
  higher wages) both lower saving, so the aggregate equilibrium map is **order-reversing**.
* What an order-reversing map gives: Tarski on `f ∘ f` yields least/greatest fixed points
  `K_lo ≤ K_hi` of `f²` with `f K_lo = K_hi`, `f K_hi = K_lo`, bracketing every equilibrium;
  uniqueness iff they coincide. No consistent selection in general.
* Remaining idea: an order-reversing map with a *contracting* `f²` on the bracket, or selection by
  continuation (R2). Item 6 stays open.

### The bracket route (started 2026-11-08)

Idea: if the equilibrium map `f` reverses order, `g = f ∘ f` preserves it; Tarski gives the least
and greatest fixed points `lo ≤ hi` of `g`, `f` swaps them, every equilibrium lies between; if `g`
is concave at the top (Krasnosel'skii: `φ hi ≤ g (t hi)` with `φ > t`) and `lo ≥ t₀ hi`, then
`lo = hi`: unique sequential equilibrium, hence the minimal-state RE.

* **B1 DONE** (`AntitoneEquilibrium.lean`): `AntitoneBracket.sq`, `map_lfp_sq`, `map_gfp_sq`,
  `lfp_sq_le`, `le_gfp_sq`, `eq_of_lfp_eq_gfp`; **`eq_of_concave`** (Krasnosel'skii on paths
  `ι → ℝ`); `eqFn`, `EqMapAntitone`, `SqConcaveAtTop`, `lfp_eq_gfp`,
  **`uniqueSequentialEquilibrium_of_antitone`**, **`isRecursive_of_antitone`**. Standard axioms.
* **B2 (open): `EqMapAntitone`.** Must be aggregate (R1: individual saving is monotone in no order).
  Subtlety found: the zero-sum redistribution (`integral_redistribution_eq_zero`) needs mean assets
  equal to the capital path's value — true at fixed points, not off them. Off equilibrium, a rise in
  `K(h)` changes aggregate cash at `h` by `∝ L (K(h) − Ā(h))`, where `Ā` is actual mean assets, with
  sign depending on whether the path over- or under-shoots. So antitonicity of `eqFn` needs either
  a restriction to a sub-lattice where `K ≥ Ā` (or `≤`), or a different map (e.g. one using
  actual mean assets in prices). First task: identify a lattice of paths invariant under `f` on
  which the redistribution term has a sign.
* **B3 (open): `SqConcaveAtTop`.** Scaling the capital path by `t < 1` raises returns and lowers
  wages along the whole tree; need two rounds of optimal saving to respond at least
  proportionally-plus. Plausible for log utility (saving rates nearly constant in wealth); the
  lower-bound condition `lo ≥ t₀ hi` should follow from the capital lower bound `capital_ge`
  (Cobb–Douglas, `b = 0`).

### B2 started 2026-11-08

* **The original map cannot work**: `eqFn` prices node `h` at the path's own `K h`, households hold
  mean `Ā h`; aggregate cash moves with `K h` at `∝ L (K h − Ā h)`
  (`CobbDouglasRedistribution.integral_cash_change`). Where the path overshoots, raising `K h`
  raises cash and saving, against the expectations effect; with little weight on the future
  (small `β`) it wins. So `EqMapAntitone` fails in general, even with a representative agent.
* **The expectations map** (`ExpectationsMap.lean`): households expect `K` for the future, today's
  prices clear at actual `Ā h` (`expDist`: the price path at node `h` is `K` with entry `h` replaced
  by `(Ā h, L h)`). **`expMap_eq_iff`**: its fixed points are exactly the sequential equilibria.
  The bracket theorem is now generic in the map (`uniqueSequentialEquilibrium_of_antitoneMap`);
  **`uniqueSequentialEquilibrium_of_expMap`**: `ExpMapAntitone` + concave square ⇒ uniqueness ⇒
  minimal state. Standard axioms.
* **What `ExpMapAntitone` needs** (`K ≤ K'` ⇒ realised `Ā ≥ Ā'`), by induction down the tree:
  (a) *expectations*: at a node with the same distribution, higher expected future capital (lower
  future returns, higher future wages) lowers every household's saving — a comparative static of
  the household problem in the future price path, with the current price fixed; for log utility
  the return effect on financial wealth cancels and the wage/human-wealth effect lowers saving,
  but the borrowing constraint and precautionary terms need care;
  (b) *propagation*: a lower realised distribution must give lower saving next period at the same
  expectations. With prices at actual `Ā`, aggregate cash `F(Ā, L) + (1 − δ) Ā` is increasing in
  `Ā`, but the distribution matters beyond its mean (redistribution again, now between two
  distributions with different means), so (b) needs dominance of the distributions, which (a) does
  not give household by household.
* Next concrete target: (a) for log utility as a household-level theorem (saving antitone in the
  future capital path at fixed current cash), then (b) in the representative-agent case, where the
  distribution is its mean.

### B2 step (a) DONE 2026-11-11 (`WageComparativeStatics.lean`)

* `consumptionOf_le_consumptionOf`: same label, at least as much cash, flatter continuation ⇒ at
  least as much consumption (any smooth utility).
* Wage channel (any smooth utility, borrowing allowed): `incDiff_bellman_wage`,
  `incDiff_iterate_wage`, `incDiff_valueFunction_wage`, **`policy_le_of_wages`** — same returns,
  higher wages along the path, no more cash today ⇒ weakly less saving.
* Combined Cobb–Douglas channel (CRRA `0 < γ ≤ 1`, `b = 0`): `incDiff_bellman_cd` (Light's
  rescaling at `t a`, `t = R'/R`, plus the consumption comparison), `incDiff_iterate_cd`,
  **`policy_le_of_cd`** — lower returns and higher wages along the path ⇒ weakly less saving.
* `CobbDouglas.grossReturn_anti`, `CobbDouglas.wage_mono`; **`crra_policy_le_of_capital`**: in the
  CRRA/CD economy, a higher expected capital path (same labour) lowers every household's saving at
  given cash. Floor and cap slackness along the iterates are hypotheses, as in Light's step.

What (a) gives in the expectations map: at the root, both paths face today's price at the same
actual `Ā`, so `expMap K' ≤ expMap K` at the first children. **Remaining (b)**: below the root the
two distributions differ (`ν' ≤` `ν` in mean, not yet in dominance), and today's prices clear at
different `Ā`. Needed: the realised distributions are ordered by dominance (`ν' ≼ ν`) and saving at
a dominated distribution with lower `Ā` is lower. Dominance propagates through saving that is
monotone in assets (`nodeDist_dominates`) once policies are ordered state by state — which (a)
gives only at equal current cash. With prices at the lower `Ā'`, current cash is redistributed
(rich lose return, poor gain wage), so state-by-state ordering of cash fails again; the
representative-agent case (one efficiency level, distribution = its mean) avoids this and is the
next target.
