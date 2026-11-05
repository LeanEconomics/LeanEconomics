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

**Reuse, not port** (2026-11-05). The `Models/IncomeFluctuation*` theorems cannot be applied
directly: `IncomeFluctuation` has one constant interest rate and a finite state type, while the
KS household faces node-varying returns on an infinite tree, and we compare return *paths*. What
is referenced directly is the generic analysis: `mul_marginal_le_of_scale`
(`Analysis/RelativeRiskAversion.lean`), `concave_increment_le`, the power-mean lemmas, and
probably `concaveOn_of_egm(_corner)` (check they do not depend on `IncomeFluctuation` section
variables). Only the dynamic-programming bookkeeping on the tree is redone (Bellman iteration,
envelope equality, the child-to-parent induction for concavity and increasing differences): a
few files, not 11k lines. Alternative: generalise `IncomeFluctuation` to state-dependent returns
and infinite state spaces and derive both (a refactor of finished work; only if wanted).

* **MR4a done** (`KrusellSmith/SavingMonotoneReduction.lean`): `policy_le_policy` (more cash +
  continuation with increasing differences ⇒ more saving; swap argument + uniqueness),
  `cont_increasingDifferences`, `WageIndependent`, `ReturnMonotone`,
  `ValueIncreasingDifferences`, **`savingMonotone_of`**. Remaining: prove
  `ValueIncreasingDifferences` (MR4b–c).

### MR4b plan: Carroll–Kimball on the tree (2026-11-05)

Target: for CRRA (log first) and the KS household along a price path, every Bellman iterate's
consumption function is concave in assets at every label, given the asset cap and the
consumption floor slack. Same induction as `Models/IncomeFluctuationIterate.lean`
(`concaveOn_consumptionFnOf_iterates_of_crra`), with the power mean over the children
`(z', e')` weighted by `shockProb`, and cash `R_h a + w_h e` affine in assets.

* **b1 done**: `Analysis/EGM.lean`, `concaveOn_of_egm_affine(_interior)` — the
  endogenous-gridpoint transfer for any affine budget; `IncomeFluctuation.concaveOn_of_egm` and
  `concaveOn_of_egm_corner` are now one-line corollaries (shared proof, no duplicate).
* **b2 done** (`KrusellSmith/AgainstContinuation.lean`): `ConcaveSlices` (preserved by the
  Bellman operator and every iterate from `0`), `contOf`, `concaveOn_contOf`, `policyOf`,
  `consumptionOf`, `bellman_eq_contOf`, `le_bellman_contOf`, **`eq_policyOf_of_objective`**
  (uniqueness under concave slices), **`policyOf_mono`**, **`consumptionOf_mono`**.
  Iterate norm bounds deferred to b5 (only needed for slackness calibrations).
* **b3 done** (`KrusellSmith/EulerOf.lean`): `SlackOf`, value sandwiches `bellman_sub_ge`,
  `bellman_sub_le` for one Bellman step, `eulerRhsOf`, **`eulerOf_ge`**, **`eulerOf_le`** (the
  household with continuation `T w₀`, children consuming against `w₀`). The envelope equality
  `∂(T w)/∂a = R u'(c)` is moved to MR4c, its only user (b4 needs only the Euler inequalities).
* **b4 done** (`KrusellSmith/CarrollKimballTree.lean`): `retSum`, `egmWeight` (probability ×
  child return, normalised — the returns differ across children, unlike the constant-rate
  model), `egmC = (β S)^{-1/γ} · powerMean(weights, -γ, children's consumption)`,
  `eulerRhsOf_eq`, `rpow_eulerRhsOf_eq_egmC`, `consumptionOf_le_egmC` (Euler ≥, cap slack),
  `consumptionOf_eq_egmC` (Euler =, above the borrowing limit), and
  **`concaveOn_consumptionOf_bellman`**: concave children ⇒ concave parent one Bellman step
  later (CRRA `u' = c^{-γ}` above the floor, positive returns, floor and cap slack). Power-mean
  lemmas and `concaveOn_of_egm_affine` used as they stand.
* **b5 done** (`KrusellSmith/CarrollKimballIterate.lean`): `utility_lt_utility` (strictly
  concave + nondecreasing ⇒ strictly increasing), `policyOf_zero` (no future: save nothing),
  `concaveOn_consumptionOf_zero` (consumption = cash, affine), and
  **`concaveOn_consumptionOf_iterate`**: for CRRA, positive returns, floor and cap slack along the
  iteration (explicit hypotheses), consumption against every `Tⁿ 0` is concave in assets at
  every label. **MR4b complete.** The fixed point is not needed (Light's step uses iterates).

### MR4c done (2026-11-05)

`KrusellSmith/LightTree.lean`: `hasDerivAt_bellman_tree` (envelope via
`ConcaveOn.hasDerivAt_of_lowerBound`), `policyOf_le_policyOf` (Topkis against continuations),
`IncDiff`, `incDiff_bellman` (Light's step with node-varying returns: rescale to equal cash,
then `mul_marginal_le_of_scale`), `incDiff_iterate`, `incDiff_valueFunction` (limit),
**`valueIncreasingDifferences_of`**, **`exists_consistentSelection_of_complementarity`**.

**Status of the monotone route:** a recursive equilibrium on the minimal state `(z, μ)` exists,
without uniqueness, for complementarity economies (wage independent of capital, return
nondecreasing in capital, CRRA γ ≤ 1), given positive returns and slackness of the consumption
floor and asset cap along the Bellman iterates. **Remaining (MR4d):** a concrete economy
discharging the slackness hypotheses (calibration, as `crra_policyOf_lt_assetCap` and
`KSInada.floorLevel_le_consumption` do elsewhere).

### MR4d done (2026-11-05) — monotone route complete

`KrusellSmith/ComplementarityWitness.lean`:
* Floor slack along iterates (`KSInada`, any marginal-Inada utility): `abs_bellman_le`,
  `abs_iterate_le` (iterates bounded by `valueBound`), `contOf_sub_le`,
  `floorLevel_le_consumptionOf` (the `floorLevel` argument against any bounded continuation with
  concave slices), `slackOf_iterate`.
* Cap slack from the budget constraint: `KSModel.policyOf_lt_assetCap` when
  `maxCash − floor < cap`.
* `compEconomy`: log utility, constant wage `w̄`, gross return `compReturn` rising from `Rlo` to
  `Rhi` in aggregate capital; **`compEconomy_exists_consistentSelection`** given
  `0 < Rlo ≤ Rhi`, `Rhi · cap + w̄ Σ e < cap`; **`example_exists_consistentSelection`** for a
  concrete two-shock, two-state economy (return rising from 1/2 to 3/4).

**Caveats.** Gross returns are below one in the witness (the cap is slack by the budget
constraint); returns above one need a cap calibration through the continuation's oscillation.
Nothing here shows sequential equilibrium is non-unique in these economies — the theorem holds
whether or not it is; the point is that it needs no uniqueness.
