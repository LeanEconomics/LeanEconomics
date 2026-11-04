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

* Planned 2026-11-05; nothing coded.
