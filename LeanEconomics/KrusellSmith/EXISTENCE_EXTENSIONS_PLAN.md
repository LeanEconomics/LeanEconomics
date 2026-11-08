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
