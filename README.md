# LeanEconomics

A project to formalise economic theory, and the properties of the algorithms used to solve
economic models, in Lean 4 against Mathlib.

Economic theory is full of results that are stated once, cited for decades, and rarely
re-derived under the conditions in which they are actually used. The same is true of the
algorithms that solve quantitative models: convergence and error bounds are proved for
idealised versions and applied to calibrated ones. A proof assistant does not permit either
gap. Every theorem in this repository is checked by the Lean kernel from the definitions
up; the hypotheses are exactly the hypotheses in the code, and the standard axioms of
Mathlib are the only thing taken on trust. There are no `sorry`s.

The scope is theory, not numerics: proving the theorems that economists and their
algorithms rely on, not verifying floating-point implementations.

## First target: stationary equilibrium in Bewley–Huggett–Aiyagari models

The first output is a machine-checked answer to a question that had been open since 1994.
**The stationary equilibrium of Aiyagari (1994) at his log calibration is unique.** With
his preferences and technology, no borrowing, and any finite Markov earnings process with
monotone transitions (every Tauchen discretisation he used, on any number of grid points),
at most one interest rate in (−δ, λ) clears the capital market, where λ = 1/β − 1; no
equilibrium exists above λ or below −4%; and the bisection he used to compute the rate is
proved to converge to it.

    theorem aiyagari1994_log_equilibriumRate_unique_Ioo   -- Equilibrium/AiyagariUniqueness.lean
    theorem aiyagariTauchen_equilibriumRate_unique_Ioo    -- Models/AiyagariTauchenWitness.lean
    theorem aiyagari1994_log_bisection                    -- Equilibrium/Bisection.lean

For risk aversion above one the argument reduces uniqueness to an inequality between two
consumption functions that holds numerically at every wealth level with an explicit
margin, and is not yet proved from primitives (`Equilibrium/SlackEuler.lean`). For Huggett
(1993) the obstruction is the borrowers, and the sharpest available bound on their effect
is in `Equilibrium/ShiftedDominance.lean` and `Equilibrium/SavingPropensity.lean`. The paper
in [`WriteUpResults/`](WriteUpResults/main.pdf) states the results in full, explains the
proof, and lists every theorem with its Lean name.

Getting there required formalising the theory underneath: the principle of optimality with
shocks and extended-real rewards, Berge's maximum theorem (absent from Mathlib), the Euler
inequalities of a constrained household without differentiating anything, Carroll–Kimball
concavity across the HARA class, the minimal marginal propensity to consume, Doeblin
uniqueness of the stationary distribution from the atom at the borrowing constraint, and
Light's three theorems on capital supply. Those pieces are general and are the foundation
for what comes next.

## Algorithms

Alongside the theory, the repository proves properties of solution methods as they are
used: convergence and error bounds for fixed-point iteration, including eventually
contracting maps and the fitted-value-iteration error bound of Sargent and Stachurski;
sufficiency of the Euler equation, which is what time iteration solves; certified bisection
on excess supply; a damped tâtonnement for strongly monotone excess-supply maps; and
Tauchen's discretisation, proved stochastic and monotone from Mathlib's Gaussian measure.
These live in `DynamicProgramming/`, `Models/ColemanReffett.lean`,
`Equilibrium/Bisection.lean`, `Analysis/StronglyMonotone.lean` and `Models/Tauchen.lean`.

## Layout

| Directory | Contents |
|---|---|
| `DynamicProgramming/` | Bellman operators, Blackwell, principle of optimality with shocks, extended-real rewards, weighted norms, ordered and eventually contracting fixed points, error bounds |
| `Topology/` | Berge's maximum theorem, both halves, real and extended-real |
| `Models/` | The income fluctuation problem and its consumption-function theory; utility classes (CRRA, log, HARA, CARA, Stone–Geary); Tauchen chains; calibrated witnesses |
| `Distribution/` | Stationary distributions on the compact state space: existence, Doeblin uniqueness, convergence |
| `Equilibrium/` | Capital supply and demand, Light's theorems, the Aiyagari and Huggett theorems, reductions for higher risk aversion, multiplicity, Lasry–Lions and mean-field uniqueness |
| `Analysis/` | Real-analysis lemmas the above need |
| `WriteUpResults/` | The paper on the first target |

Two conventions run through everything. Borrowing limits and asset caps are type
parameters, so a theorem proved once serves Aiyagari's economy and Huggett's alike. And
nothing is differentiated: Euler inequalities, Lipschitz bounds and comparative statics are
obtained from one-sided perturbations and secant slopes, in the manner of Clausen and Strub
(2020), because the value function of a constrained household is not known to be
differentiable where the constraint binds.

## Building

Install [elan](https://github.com/leanprover/elan). Then, from the repository root:

    lake exe cache get   # Mathlib's compiled oleans, once
    lake build

The toolchain is pinned in `lean-toolchain` and the Mathlib revision in `lakefile.toml`.
To check what a theorem depends on:

    lake env lean --run - <<'EOF'
    import LeanEconomics
    #print axioms LeanEconomics.IncomeFluctuation.aiyagari1994_log_equilibriumRate_unique_Ioo
    EOF

API documentation is built by CI and published at
https://leaneconomics.github.io/LeanEconomics/.

## Provenance

The development is written mostly by Claude (Anthropic), an AI coding model, working under
the direction of Robert Kirkby (Victoria University of Wellington), who sets the targets,
judges the economics, and reviews the results. The Lean kernel checks every proof; nothing
here depends on trusting either author. Results that belong in Mathlib are listed in
[`UPSTREAM.md`](UPSTREAM.md).

## Citing

    @misc{LeanEconomics,
      author = {{LeanEconomics Org [mostly Claude]}},
      title  = {LeanEconomics: Economic Theory and Solution Algorithms, Formalised in Lean},
      year   = {2026},
      note   = {\url{https://github.com/LeanEconomics/LeanEconomics}}
    }

## License

Apache 2.0, matching Mathlib. See [`LICENSE`](LICENSE).
