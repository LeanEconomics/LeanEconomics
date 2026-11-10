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
