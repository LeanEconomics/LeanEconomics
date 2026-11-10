# The Coleman operator for the representative agent (plan, 2026-11-11)

Context: item 6 of `EXISTENCE_EXTENSIONS_PLAN.md` (a recursive equilibrium on the minimal state
for Cobb–Douglas without uniqueness). The bracket route on capital paths reduced B3 to an
elasticity bound that only small shares deliver. The classical representative-agent arguments
(Coleman 1991; Greenwood–Huffman 1995; Datta–Mirman–Reffett 2002) put the order argument on a
different operator: Euler-equation time iteration on consumption policy functions.

## Setting

Representative agent: one efficiency level, every household holds aggregate capital `k`.
State `(z, k)`, `k ∈ [0, ā]`. Cash `y(z, k) = R(z, k) k + w(z, k) L`, continuous and nondecreasing in
`k` (`CobbDouglas.repCash_mono`). A consumption policy `c(z, k)`; saving `s = y − c`.

**The Coleman operator.** Given `c`, at `(z, k)` solve for today's saving `s ∈ [0, ā]`, `s < y`:

  `u'(y − s) = β Σ_{z'} π(z, z') R(z', s) u'(c(z', s))`  (with corner inequalities at `0`, `ā`),

and set `(T c)(z, k) = y − s`.

## Milestones

* **CO1 Euler root** (pure real analysis, `ColemanEuler.lean`). For `u'` strictly decreasing,
  continuous and Inada on `(0, ∞)`, and a continuation `B(s)` antitone (and continuous for
  existence) on `[0, ā]`: the KKT point exists (IVT; Inada at `s → y`), is unique, saving rises
  with cash, and consumption rises with cash and with a lower continuation `B`.
* **CO2 the operator.** The lattice `𝒞` of policies with `c` nondecreasing in `k` and `y − c`
  nondecreasing in `k` (bounds `0 < c ≤ y`). The continuation of `c ∈ 𝒞` is antitone in `s`
  (`R` decreasing in capital for Cobb–Douglas, `u'(c)` decreasing). `T` maps `𝒞` to `𝒞` (CO1
  comparative statics in cash) and is monotone (`c ≤ c'` ⇒ lower continuation ⇒ `T c ≤ T c'`).
  Members of `𝒞` are continuous: `0 ≤ c(b) − c(a) ≤ y(b) − y(a)`.
* **CO3 fixed point.** `𝒞` is a complete lattice (both monotonicity constraints are preserved by
  arbitrary sups and infs); Tarski gives a greatest fixed point `c*`. Need: the lower bound
  `c > 0` survives infs (use the Euler root at `c = y`'s lower envelope, or a uniform floor).
* **CO4 verification.** The capital path `K_{t+1} = y(z_t, K_t) − c*(z_t, K_t)` is a sequential
  equilibrium of the KS model from every point mass: the household's saving at those prices
  solves its Euler equations with the corners, which with concavity and the bounded asset space
  is optimal (tangent-line verification, as for the corner economy).
* **CO5 minimal state.** The equilibria built from `c*` are consistent along the tree; for one
  efficiency level and point masses the minimal state is `(z, K)`: a recursive equilibrium on
  `(z, K)` exists **for every capital share**, without uniqueness.
* **CO6 (optional) uniqueness.** Datta–Mirman–Reffett: `T` concave in Krasnosel'skii's sense on
  `𝒞` ⇒ unique fixed point.

## Honest scope

CO1–CO3 are self-contained. CO4 is the largest step (the household problem on the tree at
Markov prices, with the floor and cap). The result reproduces known representative-agent theory;
its value is the template for an order argument on policies rather than paths, which is what
the heterogeneous case would need (an analogue of `𝒞` on cross-sections).

## Status

* Planned 2026-11-11.
* **CO1 DONE** 2026-11-11 (`ColemanEuler.lean`): `IsEulerRoot`; **`eulerRoot_cons_le`**
  (consumption rises with cash and when the continuation falls), **`eulerRoot_saving_le`** (saving
  rises with cash), `eulerRoot_unique`, **`exists_eulerRoot`** (corners or IVT; Inada at full
  saving when the cap is slack). Standard axioms. Next CO2 (the lattice `𝒞` and `T`).
* **CO2 + CO3 DONE** 2026-11-11 (`ColemanOperator.lean`): `Data` (π, β, u' strictly decreasing
  continuous positive Inada, `R` continuous nonnegative **nonincreasing in capital** with bound
  `R̄`, **`β R̄ ≤ 1`**, cash `y` continuous nondecreasing with `y ≥ m > 0`); the lattice `Pol`
  (`m ≤ c ≤ y`, consumption and saving nondecreasing) with pointwise infima, **complete**
  (`completeLatticeOfInf`); members continuous (`continuous_pol`); the continuation `cont`
  continuous, antitone in saving, `≤ u'(m)`; the operator **`T`** (Euler root of `CO1`) maps `Pol`
  to `Pol` (`inC_T`; `m ≤ T c` uses `β R̄ ≤ 1`) and is monotone; **`exists_fixed`** (Tarski,
  greatest fixed point): a policy solving the Euler equation with the corners at every state.
  Standard axioms. Limitation: `β R̄ ≤ 1` keeps the floor `m` invariant; the corner economy
  (`β R > 1`) is outside. Next CO4 (verification in the KS model).
* **CO4a + CO4b DONE** 2026-11-11 (`ColemanBridge.lean`): **`crraData`** — the
  representative-agent CRRA, Cobb–Douglas economy as Coleman data (`u' = c^{-γ}`, return and cash
  at labour = the efficiency, inside the labour box; `m = w̲ L`; hypothesis `β R̄ ≤ 1`);
  `savingBox`, **`capPath`** (capital on the tree from `(z₀, k₀)` under a policy),
  **`capPath_euler`** (at the Coleman fixed point the Euler root holds at every node against
  tomorrow's consumption at tomorrow's capital), `gfp_cons`.

### CO4c plan: Euler sufficiency on the tree

Statement: in the KS household problem along the price path `P(h) = (capPath h, L)`, the plan
"hold `capPath h` at node `h`" (state `(capPath h, ⟨default, h⟩)`, action `capPath (z' :: h)`) has
value equal to `valueFunction` at the root; hence (principle of optimality + uniqueness of the
optimal saving) the household's policy at `(capPath h, h)` is `capPath (z' :: h)` at every node.

Proof: for any feasible plan `p'` (`DynamicProgramming.Plan`), concavity gives
`u(c') − u(c) ≤ u'(c)(c' − c)`; with `c = R a − s + w L` (no borrowing) and `Δa_{n+1} = Δs_n`, the
sum to date `N` telescopes to `Σ_{n<N} βⁿ E[(β E_n[R' u'(c')] − u'(c)) Δs_n] + βᴺ E[u'(c_N) R_N Δa_N]`;
each summand is `≤ 0` by the KKT conditions (`= 0` interior; `Δs ≥ 0` at zero saving; `Δs ≤ 0` at
the cap); the remainder is `≤ βᴺ u'(m) R̄ ā → 0`. So `value p' ≤ value p`, and
`isGreatest_planValue` / `valueFunction_eq_seqValue` identify `value p` with the value function.
Needs: consumption above the KS floor along the path (`m ≥ floor`), the identification of
`Data.cont` with the household's expected marginal value, and the plan-expectation algebra of
`StochasticOptimality.lean`.

Then **CO4d**: the household policy at the aggregate state is the Coleman saving, so the point-mass
distribution follows `capPath` and mean capital is `capPath`: a sequential equilibrium.

* **CO4c DONE** 2026-11-11 (`ColemanSufficiency.lean`): plan bookkeeping (`labelOf`, `plan_label`,
  `histProb_eq`, `plan_assets_succ`, `planCons`, `planCons_sub` with no borrowing); `PlanEuler`
  (slack above the floor plus the Euler/KKT conditions at every history, with `nextMU`);
  **`value_le_of_euler`**: `value q ≤ value p + gap₀` for every feasible plan `q`, given
  bounded marginal utility along `p` (telescoping `telescope_le`, carried term
  `abs_carried_le`, concavity gaps `concGap_nonpos`); `utility_lt_tangent`;
  `policy_eq_policyAction`; **`policy_eq_of_euler`**: the household policy at the root is the
  plan's first saving. Standard axioms. Applies at any root, so at every node of the tree.
  Next **CO4d**: instantiate with the Coleman `capPath` — the rep-agent KS model whose
  prices are `P h = (capPath h, L)`, `returnAt`/`cash` = `D.R`/`D.y`, `nextMU` = `D.cont / β`,
  `planCons` = `gfp` (`gfp_cons`), `du ≤ u'(m)` as `D̄`, floor `≤ m` — then the point mass follows
  `capPath`: a sequential equilibrium.
* **CO4d DONE** 2026-11-11 (`ColemanEquilibrium.lean`): `Data.capPath_append` (the path from a
  node is the path started there); `colemanPrices`, **`colemanPlan`** (hold the Coleman capital of
  the node) in the CRRA household; `consFloor_lt_m` (CRRA floor `< m = w̲ L`); `cash_eq`
  (household cash = Coleman `y`); `colemanPlan_cons` (consumption = `gfp`); `nextMU_eq`
  (`β · nextMU = cont`); **`colemanPlan_euler`**; **`policy_eq_saving`** (household policy at
  the root = Coleman saving, via `policy_eq_of_euler` with `D̄ = m^{-γ}`); `repNode`,
  `nodeDist_dirac`; **`isSequentialEquilibrium_capPath`**: from every point mass the Coleman capital
  path is a sequential equilibrium of the representative-agent CRRA, Cobb–Douglas economy (one
  idiosyncratic state, labour in its box, `β R̄ ≤ 1`), **every capital share**. Standard axioms.
  Next **CO5**: the path is a function of `(z, K)` (`capPath (z'::h) = saving c* (z_h, K_h)`), so a
  recursive equilibrium on `(z, K)`.
* **CO5 DONE** 2026-11-11 (`ColemanRecursive.lean`): **`colemanRecursive`** — an
  `AggStateRecursiveEquilibrium` on `(z, K)`, `K ∈ [0, ā]`, for the representative-agent CRRA,
  Cobb–Douglas economy (labour in its box, `β R̄ ≤ 1`), **every capital share**, no uniqueness:
  `lawK z K z' = s*(z, K)` (Coleman saving), labour the efficiency, value/saving the household's at
  the Coleman prices from `(z, K)` (`pricesK`); Bellman and optimality via `valueFunction_next`
  (the price path from the next node is the Coleman path from `(z', s*(z, K))`,
  `shiftPath_pricesK`); consistent distributions the point mass at `K`, moved to the point mass at
  `lawK` by `savingR_root` (= `policy_eq_saving`). **`capPath_eq_lawK`**: the CO4d sequential
  equilibrium is generated by `lawK`. Standard axioms. Remaining: CO6 (optional uniqueness,
  Datta–Mirman–Reffett).
* **CO6 DONE (abstract form)** 2026-11-11 (`ColemanUnique.lean`): **`Data.fixed_unique`** — for
  marginal utility multiplicatively homogeneous (`u'(t x) = φ(t) u'(x)`; CRRA via
  `crraData_du_mul`) and a return **strictly decreasing** in capital on `[0, ā]`, the Coleman
  fixed point is unique (= `gfp T`). Proof (`le_of_fixed`): the minimal ratio `t = c₁/c₂` is
  attained; if `t < 1` the minimiser saves strictly more under `c₁`, and
  `u'(c₁) ≤ B₁(s₁) ≤ φ(t)B₂(s₁) < φ(t)B₂(s₂) ≤ φ(t)u'(c₂) = u'(c₁)` (`strictAntiOn_cont`). No
  `β R̄` condition needed beyond the operator's. Standard axioms.
  **Open:** the clamped Cobb–Douglas return of `crraData` is flat for capital `≤ capLo` (clamp,
  `capLo > 0`), so strictness fails there and uniqueness for the KS instance is not obtained. At a
  minimiser with `t < 1` equality propagates to `(z', s₁)` and requires `B₂` flat on `[s₂, s₁]`,
  i.e. both savings in the flat region; a separate argument for that region (e.g. the linear
  economy `R, w` constant) is needed.
