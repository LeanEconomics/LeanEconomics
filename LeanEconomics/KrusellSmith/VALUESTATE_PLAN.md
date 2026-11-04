# Recursive equilibrium with the value function as a state variable

Goal: an **unconditional** existence theorem for a recursive equilibrium of the Krusell–Smith
economy, on the state `(z, μ, v)`: aggregate shock, distribution of households, and the households'
current value function. This is Cao (2020, JET) Proposition 3 / Definition 5, and Miao (2006, JET)
Theorems 2–3 (Miao uses expected payoffs, the same object). No uniqueness, no measurable selection.

Why it works (Cao's remark): the period equilibrium conditions only involve **next period's value
functions**. So if, at every state, we pick *some* sequential equilibrium whose root value is `v`,
and carry forward the value it implies at each child, then the household's Bellman equation holds
node by node along the glued path, even though the continuation actually played below a child may
be a different equilibrium from the one used to compute that child's value. The infinite horizon is
handled by uniqueness of the bounded fixed point of the Bellman operator, which we already have
(`StochasticDynamicProgram.eq_valueFunction`).

Kubler–Schmedders (2002) show that in a related finite-agent economy the wealth distribution alone
can fail to be a sufficient state, so dropping `v` is not available without uniqueness
(`Contraction.lean` supplies uniqueness under weak price feedback).

## What we already have

* sequential equilibrium from every `(z, μ)` (`exists_sequentialEquilibrium`), plays the role of
  Cao's generalized recursive equilibrium correspondence `Q` — we can skip his finite-horizon
  `∩ Gⁿ(V⁰)` construction because our existence is directly for the infinite horizon;
* the continuation theorem (`IsSequentialEquilibrium.continuation`) — self-justification;
* re-rooting of the value function and policy (`valueFunction_shift`, `policy_shift`) and of
  distributions (`nodeDist_shift`) and labour (`labour_append`, `initMass_nodeDist`);
* Bellman with optimal saving (`exists_optimal_saving`, `policy_optimal`,
  `optimal_saving_unique`), fixed point uniqueness (`eq_valueFunction`).

## Status

* **V1 done** (`ValueState.lean`): `placeAt`, `nodeValue`, `rootValue`, `rootValue_shift`;
  `ExtState` (shock, dist, value, witness), `ExtState.path` (chosen witness), `prices`, `policy`,
  `path_nil` (capital = mean assets of `dist`), `extend`, `nextDist`, `next` (in `ExtState` by the
  continuation theorem), `value_eq_rootValue_eqPath` (collapse under uniqueness).
* **V2 done** (`ValueState.lean`): `ExtState.cash`, `maxSaving`, `shockProb`, `objective` (with
  next states' values); `cash_eq` (prices from `capital`, `labour` of `μ` only); `value_eq`
  (Bellman attained at `policy`), `objective_le_value`; `next_dist_eq` (push-forward at the root),
  `nextA_nil`, `integral_next`; `initMass_next` (labour); `KSModel.pushNode_congr` (for V3).
* **V3 done** (`ValueStateGlue.lean`, plus `StochasticDynamicProgram.norm_valueFunction_le`):
  `tree`, `gluedPath`, `gluedPrices`; `initMass_tree`, `labour_tree`, `cash_glued`; `gluedValue`
  (bounded by `utilityBound / (1 − β)`); `bellman_gluedValue`, `valueFunction_glued`,
  `policy_glued`, `nodeDist_glued`; **`isSequentialEquilibrium_glued`**, `nodeValue_glued`,
  `rootValue_glued`.
* Next: V4 (packaged theorems, payoff equivalence, CRRA / log corollaries).

## Milestones

### V1. The extended state (`ValueState.lean`)

* `rootValue z μ K : M.AState →ᵇ ℝ` — the household value function at the root along
  `pricePath z (initMass μ) K`, as a function of `(a, e)`.
* `ExtState := {ξ : Z × ProbabilityMeasure M.AState × (M.AState →ᵇ ℝ) // ∃ K, IsSequentialEquilibrium
  ξ.1 ξ.2.1 K ∧ rootValue ξ.1 ξ.2.1 K = ξ.2.2}` (Cao's set `J`).
* `exists_extState z μ`: every `(z, μ)` extends to some `ξ` (from existence).
* `sel ξ` — a chosen witness path (`Classical.choose`; no measurability asked).
* `ExtState.next ξ z'` — next state `(z', μ_[z'], v_[z'])`: distribution and value at the child
  `[z']` along `sel ξ`. In `ExtState` by the continuation theorem and `valueFunction_shift`.

### V2. The period equilibrium conditions on `ExtState` (Cao Def. 4, conditions 1–5)

* prices depend on `(z, μ)` only: capital at the root is mean assets of `μ`, labour is
  efficiency-weighted mass of `μ`;
* **Bellman**: `v x = max_{a'} u(cash − a') + β Σ prob · (next ξ z').v (a', e')`, attained by the
  policy `extPolicy ξ x` (the root policy of `sel ξ`);
* **distribution consistency**: `(next ξ z').μ` is the push-forward of `μ` under `extPolicy ξ`
  (`pushNode` at the root);
* **labour consistency**: idiosyncratic masses of `(next ξ z').μ` follow `stateMass` one step.

### V3. Gluing: a recursive equilibrium generates a sequential equilibrium (Miao Thm 2)

From `ξ₀ = (z₀, μ₀, v₀)`:

* `extTree ξ₀ : List Z → ExtState`, `extTree [] = ξ₀`, `extTree (z' :: h) = next (extTree h) z'`;
  `shock (extTree h) = shockAt z₀ h`.
* glued path `K* h := mean assets of (extTree h).μ`.
* **labour**: `initMass (extTree h).μ = stateMass z₀ (initMass μ₀) h` (induction, V2 labour), so
  prices along `pricePath z₀ (initMass μ₀) K*` at `h` are the prices of `extTree h`.
* **values**: `W (a, ⟨e, h⟩) := (extTree h).v (a, e)` is a bounded continuous function on
  `M.State` (label discrete: `continuous_prod_of_discrete_right`; uniform bound
  `‖valueFunction‖ ≤ ‖reward‖ / (1 − β)`, and the reward bound does not depend on the path —
  needs a small lemma in `DynamicProgramming/Stochastic.lean`). V2 Bellman node by node gives
  `bellman W = W` along `K*`, hence `W = valueFunction` (`eq_valueFunction`).
* **policy**: by `optimal_saving_unique`, the policy along `K*` at node `h` is
  `extPolicy (extTree h)`.
* **distributions**: by induction, `nodeDist z₀ μ₀ K* h = (extTree h).μ` (V2 consistency).
* **equilibrium**: `K* h = meanCapital … h`. So `K*` is a sequential equilibrium from
  `(z₀, μ₀)` whose root value is `v₀`.

### V4. Theorems

* `exists_recursiveEquilibrium_valueState`: the recursive equilibrium on `ExtState` exists and
  satisfies V2 at every state (Cao Prop. 3).
* `generates_sequentialEquilibrium`: from every `ξ₀`, the generated path is a sequential
  equilibrium; households' value at node `h` is `(extTree h).v` and they save by
  `extPolicy (extTree h)` (Miao Thm 2).
* `payoffEquivalent`: for every sequential equilibrium `K` from `(z, μ)`, the recursive
  equilibrium started at `(z, μ, rootValue K)` generates a sequential equilibrium with the same
  household values at the root (Miao Thm 3, second part).
* Under `UniqueSequentialEquilibrium`, `v` is a function of `(z, μ)` and this collapses to
  `Recursive.isRecursive` (consistency check).
* Corollaries for `KSInada` (log, CRRA) and the CRRA / log Cobb–Douglas economies.

## Out of scope (later, if wanted)

* **Measurability** of the selection and the maps (Miao; needs a Kuratowski–Ryll-Nardzewski type
  measurable selection theorem, not in Mathlib).
* **Stationarity / ergodic measure** (Cao §6 via DGMM 1994): compact self-justified set, convex
  values or randomisation, invariant measures on a space of measures.
* **Removing the capital clamp** via Cao Lemma 9 (uniform lower bound on equilibrium capital from
  bounded RRA and `u''' ≥ 0`).

## Risks

* The uniform bound on value functions across paths (needed for `W` to be bounded): the reward
  bound in `Household.reward` is `exists_bound_utility.choose`, independent of the path, so this
  should be routine.
* Bookkeeping between `M.AState` (`Idio E`) and `M.State` (`Label Z E`) at the root.
* Coercions `ProbabilityMeasure` ↔ `Measure` throughout.
