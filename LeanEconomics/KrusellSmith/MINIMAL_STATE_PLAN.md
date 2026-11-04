# Recursive equilibrium on the minimal state without uniqueness (monotone route)

Cao (2020): "the existence of recursive equilibrium with the natural minimal state space in
Krusell and Smith's economy remains elusive". What exists here: `Recursive.lean` (minimal state
`(z, μ)` under `UniqueSequentialEquilibrium`), uniqueness by contraction when `κ < 1`
(`Contraction.lean`; `κ ≈ 10¹⁵` at realistic parameters), and recursive / stationary equilibria
on the value-function state (`ValueState*.lean`, `StationaryEquilibrium.lean`,
`SpotlessEquilibrium.lean`).

## The idea

`Recursive.lean` uses uniqueness only through one consequence: the selected equilibrium is
**consistent** — the continuation below `[z']` of the equilibrium selected at `(z, μ)` is the
equilibrium selected at the child state `(z', μ_{[z']})`. Any consistent selection gives a
recursive equilibrium on the minimal state. The monotone route builds one without uniqueness: the
**greatest** sequential equilibrium, by Tarski, when the equilibrium map is monotone.

**Hypothesis (H), savings rise with aggregate capital**: for every shock `z`, initial masses `m₀`
and capital paths `K ≤ K'` (pointwise on nodes), every household saves weakly more along `K'`:
`policy z (pricePath z m₀ K) s ≤ policy z (pricePath z m₀ K') s` for every state `s`.

**Proof sketch.**
1. Under (H) the equilibrium map `Φ_{z,μ}` (capital path ↦ mean-saving path) is isotone: node
   distributions are ordered by first-order stochastic dominance in assets (given the
   idiosyncratic state), because policies are ordered (H) and nondecreasing in assets
   (`policy_mono`), and the idiosyncratic transition does not depend on assets.
2. `[0, assetCap]^{nodes}` is a complete lattice; `Φ` maps it to itself and fixes the root at
   mean assets (`meanCapital_nil`). Tarski: a greatest fixed point `K̄(z, μ)`, the greatest
   sequential equilibrium.
3. **Consistency.** Let `μ'` be the distribution at `[z']` along `K̄(z, μ)` and `K' = K̄(z', μ')`.
   * `shift K̄(z, μ) [z'] ≤ K'`: the continuation is an equilibrium from `(z', μ')`
     (`IsSequentialEquilibrium.continuation`).
   * `K' ≤ shift K̄(z, μ) [z']`: splice `K'` into `K̄(z, μ)` below `[z']` to get `K'' ≥ K̄`. Off the
     subtree `K'' = K̄ = Φ K̄ ≤ Φ K''`. On it, `Φ K''` is mean saving from the distribution at `[z']`
     along `K''` (`meanCapital_shift`), which dominates `μ'` (root saving is higher by (H); same
     idiosyncratic masses), so `Φ K'' ≥ Φ_{z',μ'} K' = K'` (monotonicity in the initial
     distribution). So `K''` is a post-fixed point, `K'' ≤ K̄`, and on the subtree `K' ≤ shift K̄`.
   * Induction on nodes: `shift K̄(z, μ) h = K̄(z_h, μ_h)` for every `h`.
4. Step 1 of `Recursive.lean` with `K̄` in place of `eqPath`: law of motion, policy and
   `isRecursive`. No continuity in `μ` is claimed (the greatest selection is only upper
   semicontinuous); Cao's generalized recursive equilibria are not continuous either.

## Scope: where (H) can hold

**(H) fails with diminishing returns.** Raising capital at the current node changes cash by
`R_K a + w_K e`. With Cobb–Douglas, `R_K < 0 < w_K` and the sign is that of `K e − L a`, negative
for households with assets above `K e / L`. They save less, so (H) fails, whatever utility.
Standard Krusell–Smith is therefore **not** covered.

**Where (H) is plausible: complementarities.** The return weakly increasing in aggregate capital
(capital externalities, increasing returns), the wage independent of capital, and log utility
(γ ≤ 1 more generally):
* current node: cash `R(K) a + w̄ e` rises with `K`;
* future nodes: with log utility a higher future return lowers the present value of future labour
  income and leaves the substitution and income effects on capital income cancelling, so saving
  rises (cf. Light 2018 on savings rising in the return when RRA ≤ 1). This is a comparative
  static of the household problem with borrowing constraints and uncertainty and must be
  **proved**; it is the research risk of the plan.

These are the economies where multiplicity of sequential equilibria is most plausible
(self-fulfilling high and low capital paths), so the result complements the contraction route,
which needs weak feedback.

## Milestones

* **MR1** (`ConsistentSelection.lean`): structure `ConsistentSelection` (a selection
  `sel z μ` of sequential equilibria with `shift (sel z μ) [z'] = sel z' (μ along sel at [z'])`);
  `isRecursive` for any consistent selection (law of motion, policy, every node, by induction);
  uniqueness yields one (`Recursive.lean` recovered). Small, independent of (H).
* **MR2** (`StochasticOrder.lean`): the order `ν ≼ ν'` (integrals of bounded continuous
  functions nondecreasing in assets for each idiosyncratic state); `pushNode` monotone in the
  measure and in the policy when policies are nondecreasing in assets; `nodeDist` and
  `meanCapital` monotone in the initial distribution (same idiosyncratic masses) and in the path
  of policies.
* **MR3** (`GreatestEquilibrium.lean`): `Φ` as an `OrderHom` on `List Z → Icc 0 assetCap`
  under (H); `greatestEquilibrium z μ := OrderHom.gfp`; it is a sequential equilibrium and the
  largest one; the splicing lemma; consistency; **theorem**: under (H), a recursive equilibrium on
  the minimal state exists.
* **MR4** (`Complementarity.lean`, research): (H) for log utility, constant wage, return
  nondecreasing in capital. Route: compare Euler conditions along two return paths
  (`euler_compare`, `Sensitivity.lean`) and propagate down the tree; first the deterministic
  case, then idiosyncratic risk. Also the obstruction lemma for diminishing returns, to make the
  scope statement formal.

## Risks

* MR4 may be false as stated with borrowing constraints and idiosyncratic risk, or need extra
  conditions (e.g. bounds on how fast the return rises). MR1–MR3 do not depend on it.
* MR3's splice needs the price path on the spliced subtree; labour along it depends only on
  idiosyncratic masses (`initMass_nodeDist`), equal for both paths.
* Lattice API: `Set.Icc.completeLattice` needs `Fact (0 ≤ assetCap)`; pi of complete lattices.

## Status

* Planned 2026-11-05.
* **MR1 done** (`KrusellSmith/ConsistentSelection.lean`): structure `ConsistentSelection`
  (`sel`, `sel_spec`, `sel_shift` one step down); `shiftPath_sel_and_nodeProb` (consistency at
  every node, by induction with `nodeDist_shift`, `pricePath_shift`); `lawOfMotion`,
  `recursivePolicy`, `policy_eq_recursivePolicy`, **`isRecursive`**;
  `UniqueSequentialEquilibrium.consistentSelection` (uniqueness gives one).
* **MR2 done** (`KrusellSmith/StochasticOrder.lean`): `AssetMono`, `AssetDominates`,
  `policy_mono_assets`, `assetMono_expectedNext`, `expectedNext_le`, **`nodeDist_dominates`**
  (dominance in the initial distribution plus higher saving at every state propagates to every
  node), **`meanCapital_le`**. One lemma covers both MR3 comparisons.
* **MR3 done** (`KrusellSmith/GreatestEquilibrium.lean`): `SavingMonotone` (hypothesis H),
  `eqMap` (monotone on the complete lattice `List Z → Icc 0 assetCap`), `greatest` (`OrderHom.gfp`),
  `greatest_spec`, `le_greatest`, `le_greatest_of_post`, `splice`, **`greatest_shift`**
  (consistency by the splice / post-fixed-point argument), **`SavingMonotone.consistentSelection`**,
  **`SavingMonotone.isRecursive`**: under (H), a recursive equilibrium on the minimal state exists,
  with no uniqueness assumption.
* **MR4 analysed 2026-11-05** (see "MR4 refined" below); nothing coded.

## MR4 refined (analysis, 2026-11-05)

**A second obstruction: the asset cap.** Even with a constant wage and log utility, (H) fails
for a household that will be at the cap next period. Three-period check (log, cap `k̄ > w`):
if the cap binds at date 1, the date-0 Euler equation gives
`a₁ = β x₀/(1+β) + (k̄ − w)/((1+β) R₁)`, **decreasing** in the date-1 return `R₁`. A higher
return only raises the consumption of someone who cannot save more, and with RRA = 1 that lowers
the marginal value of saving. This needs `β R₁` large (the cap must bind next period from below
it), so it is ruled out when the cap is slack along optimal paths. The same lesson as
Carroll–Kimball (`not_concaveOn_consumptionFn_of_cap_binds`, memory: cap removed by calibration).

**Revised target (H) holds when**: (i) the wage does not depend on capital; (ii) the return is
nondecreasing in capital; (iii) relative risk aversion ≤ 1 (log included); (iv) consumption is
concave in cash at every node (Carroll–Kimball on the tree); (v) the asset cap never binds;
(vi) consumption is positive.

**Decomposition.** At node `h`, the household's objective depends on its state only through cash
`R_h a + w e` and the idiosyncratic state, and on the path only through `R_h` and the
continuation value at the children, which depends only on prices in the subtree. So (H) splits:
* **(H1) saving rises with cash** at a fixed continuation (Topkis: `u(x − a')` has increasing
  differences in `(x, a')` for concave `u`). General; no new hypotheses. Raising `K_h` raises
  cash under (i), (ii).
* **(H2) saving rises with the continuation's marginal value**: if the continuation `v'` has
  increasing differences over `v` in next assets, saving is higher at every cash (Topkis).
* **(H3) propagation (Light's step on the tree)**: higher returns at the node and a continuation
  with increasing differences give a node value with increasing differences. Light's proof
  (`Models/IncomeFluctuationRateStep.lean`, `contIncreasingDifferences_withRate`) uses (iii),
  (iv), (v), the envelope equality and the rescaling `cash(a, R₁) = cash(t a, R₂)`, all node by
  node, so it should port; the infinite tree needs horizon induction then a limit, as in
  `Contraction.lean` (`weighted_du_gap`).

**Assets to port** (LeanEconomics `Models/`, ~11k lines, constant-rate income-fluctuation
problem): Carroll–Kimball (`IncomeFluctuationCarrollKimball`, `concaveOn_consumptionFnOf_*`),
envelope equality (`hasDerivAt_bellman`), Light (`IncomeFluctuationRateMonotone`,
`IncomeFluctuationRateStep`), cap slackness (`crra_policyOf_lt_assetCap`), CES witnesses.

**MR4 milestones.**
* **MR4a** (`SavingMonotoneReduction.lean`): (H1), (H2), and `SavingMonotone` from
  "constant wage + return nondecreasing in capital + increasing differences of continuations
  along higher return paths" (`ContIncreasingDifferencesTree`). Self-contained, moderate.
* **MR4b**: Carroll–Kimball concavity on the tree (node-varying returns).
* **MR4c**: the envelope equality on the tree and Light's propagation step, giving
  `ContIncreasingDifferencesTree` under (iii)–(vi); the cap-slack calibration.
* **MR4d**: a concrete complementarity economy (log or CES γ < 1, return rising in capital,
  constant wage) satisfying all hypotheses, hence a recursive equilibrium on the minimal state
  without uniqueness, in an economy where uniqueness is not known.

MR4b–c are a multi-session port; MR4a is useful on its own (it isolates exactly what must be
proved about the household problem).
