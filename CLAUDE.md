# Lean Economics

Formalising economic theory in Lean 4 + Mathlib.

Principal: Robert Kirkby, computational economist. Background is numerical methods for
dynamic programming, quantitative macro, and heterogeneous-agent models (author of the
VFI Toolkit). That background shapes the priorities below: the interesting target is
recursive macroeconomics, which nobody has formalised yet.

Scope is **theory**, not numerics — proving the theorems economists rely on, not verifying
floating-point implementations of the algorithms.

---

## Environment state

Verified working as of 2026-09-14:

- `elan 4.2.4`, Lean toolchain pinned by `lean-toolchain`
- Mathlib `v4.34.0-rc2`, declared in `lakefile.toml`
- `lake exe cache get` has run (8747 oleans decompressed); `lake build` passes

Layout:

```
LeanEconomics/            <- repo root, contains lakefile.toml
├── LeanEconomics.lean    <- root module, imports the rest
├── LeanEconomics/        <- source lives here
│   └── Basic.lean
├── lakefile.toml
├── lean-toolchain
└── .lake/                <- build artefacts, do not commit, do not delete (see below)
```

### Two environment gotchas

1. **The repo sits inside Dropbox.** `.lake/` carries the extended attribute
   `com.dropbox.ignored=1` so Dropbox does not sync several GB of churning build output.
   The attribute is bound to that specific directory inode, not to the name. If `.lake` is
   ever deleted and recreated (e.g. `lake clean`), the flag is lost and must be reapplied:
   ```bash
   attr -s com.dropbox.ignored -V 1 .lake
   attr -g com.dropbox.ignored .lake   # should echo 1
   ```
   Prefer not to `lake clean` without a reason.

2. **First `import Mathlib` in a file costs 30–60s** of olean loading. Import specific
   modules rather than all of Mathlib once the file settles.

---

## Working conventions

- Run `lake build` after edits. Do not report a proof as done without a clean build.
- If `lean-lsp-mcp` is configured, use `lean_goal` to read proof state rather than
  inferring it from error text, and its LeanSearch/Loogle tools to find existing lemmas.
  Searching Mathlib for an existing result is almost always cheaper than proving it.
- **Never leave a silent `sorry`.** If a proof is incomplete, mark it
  `sorry -- TODO: <what remains>` and say so explicitly in the reply.
- Follow Mathlib naming conventions (`lowerCamelCase` for defs, `snake_case` descriptive
  names for theorems built from the statement, e.g. `bellman_isFixedPt_unique`).
- Mathlib renames things between versions. Verify any lemma name against the local copy
  (`exact?`, `apply?`, or Loogle) before relying on it — including names suggested in this
  file.
- State definitions at the generality economists actually use, not the maximum generality
  Lean permits. A Bellman operator on a compact state space with bounded continuous value
  functions is more useful here than one on an arbitrary topological space.

---

## Prior art (surveyed 2026-09)

Existing Lean work in economics clusters in game theory and social choice. Read before
building anything that overlaps.

| Project | Coverage | Status |
|---|---|---|
| [EconCSLib](https://github.com/gametheoryinlean/EconCSLib) | Strategic/extensive/coalitional games, social choice, fair division, matching, auctions, mechanism design, utility theory, fixed-point and minimax support | Most credible community effort. ~48 commits, has a blueprint separating proved results from targets. Paper: [arXiv 2606.16144](https://arxiv.org/html/2606.16144) |
| [Econlib](https://github.com/danlyng/Econlib) (Daniel Lyng) | Very broad: preferences and risk aversion, ~25 distributions, Markov chains, Berge's maximum theorem, KKT, monotone comparative statics, Nash existence, Kuhn's theorem, Arrow, median voter, Walrasian existence, both welfare theorems, the core | Claims no `sorry`. Single commit, unaudited — **verify before building on it**. Berge and monotone comparative statics are the parts most worth borrowing. Apache 2.0 |
| [math-xmum/Brouwer](https://github.com/math-xmum/Brouwer) | Scarf's combinatorial theorem → Brouwer → mixed Nash existence, ~4,768 lines | Paper: [arXiv 2607.05987](https://arxiv.org/html/2607.05987) (Lyu & Li) |
| [elazarg/GameTheory](https://github.com/elazarg/GameTheory) | Game theory basics | Smaller |
| [pavanamthomas/lean4-optimization-economics](https://github.com/pavanamthomas/lean4-optimization-economics) | Feasible sets, budget constraints, comparative reasoning | Smaller |

**The gap.** No formalisation exists of recursive macroeconomics: no Bellman operator as a
contraction, no convergence of value function iteration, no stochastic dynamic programming,
nothing on heterogeneous agents or stationary/invariant distributions. The nearest adjacent
work is on the reinforcement-learning side ([arXiv 2511.03618](https://arxiv.org/html/2511.03618)).
This is the natural place for this project to contribute.

---

## Candidate first targets

Roughly in dependency order. Stokey–Lucas–Prescott chapters 3–4 and 8–9 are the reference
texts; QuantEcon lectures are the informal source being formalised.

1. **Bellman operator as a contraction.** Define `T : (S →ᵇ ℝ) → (S →ᵇ ℝ)` for a bounded
   deterministic dynamic program on a compact state space, prove Blackwell's sufficient
   conditions (monotonicity + discounting) imply `ContractingWith β T`, then get existence
   and uniqueness of the fixed point from Mathlib.
2. **Convergence of value function iteration**, including the geometric error bound
   `‖Tⁿ v − v*‖ ≤ βⁿ/(1−β) · ‖Tv − v‖`, which is the practical stopping rule.
3. **Existence of an optimal policy** — the argmax is attained; this needs the maximum
   theorem, so check whether Econlib's Berge is usable first.
4. **Principle of optimality**: the fixed point of the Bellman operator equals the
   sequence-problem supremum.
5. **Stochastic extension**: transition kernels, the expectation operator, measurability of
   the value function.
6. Only then: invariant distributions, stationary equilibrium in a Bewley–Huggett–Aiyagari
   economy.

### Mathlib anchors to start from

Verify each against the local Mathlib before use.

- `ContractingWith`, `ContractingWith.fixedPoint`, `ContractingWith.fixedPoint_isFixedPt`,
  `ContractingWith.fixedPoint_unique` — Banach fixed point, the core of steps 1–2
- `LipschitzWith` — `ContractingWith K f` unfolds to `K < 1 ∧ LipschitzWith K f`
- `BoundedContinuousFunction` (notation `α →ᵇ β`) — the natural value-function space; it is
  already a complete metric space under the sup norm, which is what Banach needs
- `IsCompact.exists_isMaxOn` — attainment of the maximum, for step 3
- `MeasureTheory.Measure`, `ProbabilityTheory.Kernel` — for step 5 onward

---

## Related

Robert also has a plan to build a site presenting QuantEcon's proofs reformalised in Lean.
That is downstream of this library: the library provides the theorems, the site presents
them. Don't conflate the two — work here should be structured as a reusable library, not as
page-shaped one-offs.
