# Overlapping generations in Lean: the programme

Companion write-up to `WriteUps/WriteUpBIHA/` (separate PDF, same repository). Drafted 2026-09-22,
before any OLG Lean exists. Status lines are updated as work lands.

## Why OLG, and what it can give that the infinite horizon could not

Every obstacle met on Aiyagari uniqueness for risk aversion above one traces to the fixed
point: the elasticity condition fails in a tail the stationary distribution reaches, the
rate-response induction has a step multiplier `1/Þ > 1` and so cannot close as a supremum
argument, and the existence floor needs an ergodic identity that loses `‖u'‖²/Var`. A life cycle
removes all three at once:

* the household problem is a finite backward induction from an explicit terminal condition
  (`c_J = m`), so every comparative static is a finite induction: a multiplier `1/Þ` per step
  compounds to `Þ^{-J} ≈ 1.03`, harmless;
* wealth is bounded by `J` periods of accumulation, so any condition needs checking on a known
  bounded region;
* the age-1 distribution is common to every rate, so the ordering of policies pushes forward
  to an ordering of the whole age-profile of distributions by induction on age: Light's
  Theorem 2 with no Doeblin atom and no uniqueness of a stationary distribution.

The flagship target is therefore **uniqueness of the stationary equilibrium of a stochastic
life-cycle economy at CRRA `γ ∈ {3, 5}`**, the case the infinite horizon could not close.

## Models

* **D** (Diamond 1965): two periods, no risk, Cobb–Douglas, CRRA or log. Pure real analysis.
* **LC** (life cycle, v1): ages `j = 1..J`, certain lifetime, no bequests, no retirement;
  earnings `y_j(z) = e_j · y(z)` with `z` Aiyagari's Markov chain and `e_j` an age profile;
  borrowing limit 0; CRRA; age-1 wealth 0, `z_1` drawn from the stationary law; cohort weights
  `ω_j` (constant population, later `(1+n)^{-j}`); same firm as Aiyagari.
* **LC+** (v2): retirement with a pension, survival probabilities with accidental bequests
  redistributed (a second fixed point), population growth. Huggett (1996) is the reference.

## Targets, in order

### Phase 0 — Diamond (1965), standalone results (low risk, 1–2 sessions)
1. Steady state exists and is unique for log utility and Cobb–Douglas; dynamics
   `k_{t+1} = s w(k_t)/(1+n)` are monotone and globally convergent.
2. General CRRA: existence under Inada; a multiplicity witness (as `Multiplicity.lean` did for
   Aiyagari).
3. Dynamic inefficiency: a steady state with `r < n` is Pareto-dominated by an explicit
   transfer scheme; the golden rule.
4. Samuelson's pure-exchange OLG: autarkic and monetary steady states.
Module: `LeanEconomics/OLG/Diamond.lean`. These are "all of economic theory" items and the
first sections of the new PDF.

### Phase 1 — the finite-horizon household (2–3 sessions)
Build on the existing `IncomeFluctuation` structure: one `P_j` per age (income `y_j`), the
age-`j` value `V_j = bellman_{P_j} V_{j+1}` with `V_{J+1} = 0`, policies `g_j = policyOf V_{j+1}`.
Everything the repo proves for `bellman v` with an ARBITRARY continuation `v` transfers
without a fixed point: Euler inequalities above the floor and under the cap (`euler_ge`,
`euler_le`), uniqueness of the action, Carroll–Kimball concavity of `c_j` given concavity of
`c_{j+1}` (`concaveOn_consumptionFnOf_bellman_of_crra_via_hara`), monotonicity in wealth,
continuity. New: the age index, the terminal condition, the explicit wealth bound
`a_j ≤ Σ_{i<j} R^{j-i} y_max`, continuity of `g_j` in the rate by backward induction.
Module: `LeanEconomics/OLG/LifeCycle.lean`.

### Phase 2 — stationary equilibrium: existence and the chain (2 sessions)
Definitions: `μ_1` given; `μ_{j+1} = (g_j, π)_* μ_j`; `K(r) = Σ_j ω_j ∫ a dμ_j`; labour
exogenous; firm as in Aiyagari. Results:
1. `K` continuous in `r` (finite composition of continuous pushforwards; no Feller machinery).
2. Existence on `[r_lo, r_hi]` by the intermediate value theorem against the firm's demand,
   with the ceiling at `r_lo` from the budget and the floor at `r_hi` from the explicit
   life-cycle accumulation (no variance identity: a household that saves at all ages
   accumulates at least a computable amount — this is where finite horizon beats Aiyagari).
3. Theorem 2: `g_j^{(1)} ≤ g_j^{(2)}` for all `j` ⇒ `μ_j^{(1)} ≼_FOSD μ_j^{(2)}` for all `j`
   ⇒ `K(r_1) ≤ K(r_2)` (induction on age, monotone transitions as in `MonotoneTransitions`).
4. Theorem 3: single crossing against decreasing demand ⇒ uniqueness given Theorem 1.
Module: `LeanEconomics/OLG/Equilibrium.lean`.

### Phase 3 — Theorem 1 by backward induction (the research core; numerics first)
Statement: `g_j^{(1)}(a,z) ≤ g_j^{(2)}(a,z)` for all ages at rates `r_1 ≤ r_2`.
Route: age-indexed slack Euler chain. At age `j` the reduction of `SlackEuler` gives
Theorem 1 from the slack elasticity condition on the age-`(j+1)` consumption functions at the
pivot; the transfer lemma of `RateResponse` propagates an affine rate-response bound
`c_{j}^{(2)} - c_j^{(1)} ≤ Δr(α_j a + B_j)` backward from `(α_J, B_J) = (1, 0)`; the
constants are computed by an explicit recursion and the slack condition at each age is a
finite check on them. The obstruction of the infinite horizon (`transfer_multiplier_ge`)
does not bite: `J` steps, not a fixed point.
Session 1 is numerical (life-cycle EGM, γ = 3 and 5, Aiyagari's chain, `J = 60`): compute
both policies, check the slack condition at every age and wealth, run the constant recursion,
and locate any age where it fails. Decision point: if it holds, formalise (Phase 3b); if it
fails only at moderate ages/wealth, look for the age-dependent refinement; if it fails badly,
fall back to log utility, where Theorem 1 at each age follows from the rescaling proof
(`policy_mono_withRate_crra_of_range` is already an induction on Bellman iterates, i.e.
finite-horizon-ready).
Module: `LeanEconomics/OLG/RateMonotone.lean`.

### Phase 4 — extensions (LC+), as time allows
Retirement and pensions (government budget as a second equilibrium condition), survival and
accidental bequests (a bequest fixed point; existence by Brouwer in two dimensions),
population growth, Lasry–Lions with age as time (the finite-horizon core `LasryLions.lean`
applies directly; its monotonicity is again the elasticity condition, so this is a second
proof of uniqueness rather than a new route).

## The write-up

`WriteUps/WriteUpOLG/main.tex`, same style and macros as `WriteUps/WriteUpBIHA/` (`\lean{}`, `\formal{}`,
index appendix), own bibliography, sections: introduction; Diamond; the life-cycle household;
equilibrium; Theorem 1 (with the numerics); frontier; index of formal results. Started once
Phase 0 has content.

## Risks
* Phase 3 is the only genuine research risk; everything else is engineering on existing
  machinery.
* The age-indexed family `P_j` may want a small refactor of `IncomeFluctuation` (income as a
  parameter of the Bellman step rather than a structure field); decide in Phase 1.
* Measure-theoretic pushforwards of `μ_j` reuse `Distribution/` (kernels, Feller) but need the
  age-indexed statement; moderate.
