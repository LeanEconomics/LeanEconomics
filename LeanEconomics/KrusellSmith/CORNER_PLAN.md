# A corner economy: heterogeneous agents with `(z, K)` sufficient

Goal (OS4 option (a) of `ORDER_STRUCTURE_PLAN.md`): a Krusell–Smith economy **with idiosyncratic
heterogeneity** whose sequence-state equilibrium satisfies `KSufficient`, so that it is represented
by a recursive equilibrium on `(z, K)` (`kSufficient_iff_exists_represents`, AK4).

## The economy and the candidate

* Employment states `E` with a set of **savers** `S ⊆ E` (the employed) and the KS design: the
  employment marginal at shock `z` is `m z`, consistent under the transitions (`EmploymentDesign`).
* **Corner policy** `g e = ā` if `e ∈ S`, else `0`: the employed save up to the cap, the unemployed
  spend everything. It does not depend on assets.
* **Candidate assignment** `μc ω`: the law of `(g e₋, e)` with `e₋ ∼ m (ω 1)` and
  `e ∼ π (ω 1, ω 0, e₋, ·)`. Its employment marginal is `m (ω 0)` (design), its assets take two
  values, and capital is `ā · m (ω 1) S`.
* **Price tree**: capital at a node is `ā · m (parent shock) S`, labour `Σ_e m (shock) e · eff e`.
  Below the root it depends only on the shocks along the node and `ω 0`; **yesterday's shock
  `ω 1` enters only through root capital**. Hence `KSufficient μc` with no injectivity.

## The corner conditions (exact, along the candidate)

At a node with prices `(R, w)`, children `(z', R', w')` with probabilities `π z z'`, and
idiosyncratic transitions `p e e'`, with marginal utility `u'`:

* **(Emp)** employed, any assets `a`: saving the cap is optimal —
  `u'(R a + w eff e − ā) ≤ β Σ_{z', e'} π p R' u'(R' ā + w' eff e' − g e')`;
* **(Unemp)** unemployed, any `a`: saving nothing is optimal —
  `u'(R a + w eff e) ≥ β Σ_{z', e'} π p R' u'(w' eff e' − g e')`;
* **(Feas)** the employed can afford the cap and every candidate consumption is above the floor.

The worst cases are `a = 0` in (Emp) and `a = ā` in (Unemp). Both reduce to lower bounds on
employed income relative to the cap and to unemployment income (a large enough chance of
unemployment for the employed, of re-employment for the unemployed), so they are jointly
satisfiable.

## Milestones

* **C0** (`CornerEconomy.lean`): saver set, `cornerPolicy`, `cornerDist` (two-point assets),
  `μc`; `initMass_μc` (marginal `m (ω 0)`), `capital_μc` (`ā · m (ω 1) S`), the price tree
  `seqPrices μc` explicitly; **`kSufficient_μc`**.
* **C1** (policy evaluation): for any price path `P`, the value `Vg` of following `g` — fixed point
  of the policy-evaluation contraction on `State →ᵇ ℝ`; its structure
  `Vg (a, e, h) = u(cash_h (a, e) − g e) + C (e, h)` (continuation independent of assets).
* **C2** (verification): under (Emp), (Unemp), (Feas) along `P`, `bellman Vg = Vg`. At each state
  the objective `a' ↦ u(cash − a') + β Σ π p [u(cash'(a') − g e') + C']` is concave and
  differentiable; its derivative has the right sign at the corner, so the tangent line gives the
  maximum there (template: `ValueStateGlue.lean`). Then `valueFunction = Vg`
  (`eq_valueFunction`) and **`policy = g`** (`optimal_saving_unique` / `argmax_eq_singleton`).
* **C3** (equilibrium): with the policy equal to `g` along `seqPrices μc ω`, `μc = seqStep μc`
  (the push of `μc ω` depends only on its employment marginal), so **`μc` is a sequence-state
  equilibrium**; then a recursive equilibrium on `(z, K)` represents it.
* **C4** (primitives): CRRA, clamped Cobb–Douglas price bounds ⇒ sufficient inequalities for (Emp),
  (Unemp), (Feas) in terms of `β, γ, ā, eff, p`, price bounds; a concrete parameter witness
  (exact arithmetic, `norm_num`), as in `ComplementarityWitness.lean`.

## Scope and caveats

* Existence of a heterogeneous equilibrium with `(z, K)` sufficient; **uniqueness is not claimed**
  (the small-share contraction is not used), so the stationarity results of AK3 do not apply
  directly. The equilibrium is Markov in `(z_t, z_{t−1})` anyway.
* Heterogeneity is real (households differ by employment history and hold `0` or `ā`), but the
  asset distribution is degenerate: corners, not interior precautionary saving. It shows the
  sufficient-state question has a positive answer with heterogeneity; it does not speak to KS's
  interior, persistent regime.
* Risks: the policy-evaluation fixed point over the infinite node tree (C1); the clamped reward in
  the tangent-line step (C2); uniformity of the inequalities over the clamped CD price ranges (C4).

## Status

* Planned 2026-11-07.
* **C0 + C1 DONE** 2026-11-07. Generic `DynamicProgramming/PolicyEvaluation.lean`: `policyOp`,
  `blackwell_policyOp`, `policyValue`, `policyValue_eq`, **`policyValue_eq_valueFunction`**
  (verification), `bellman_eq_objective_policy`. `KrusellSmith/CornerEconomy.lean`: `cornerSave`,
  `cornerWeight`, `cornerPt`, `cornerMeasure`/`cornerDist` (finite sum of point masses), `μc`;
  `integral_cornerDist`, `capital_cornerDist` (`ā · saverMass y`), `initMass_cornerDist`
  (`D.m z`); `labourD`, `cornerTree`, `capAt_μc`, **`seqPrices_μc`**, **`kSufficient_μc`**;
  `cornerPolicy`, `cornerValue`, `cornerValue_eq`, `expectation_congr_assets`,
  **`cornerValue_sub_reward`**. Standard axioms only. Next C2 (verification under (Emp), (Unemp),
  (Feas)).
* **C2 DONE** 2026-11-07 (`CornerVerification.lean`): `CornerFeas` (strict: floor + corner saving
  below labour income), `cornerNext`, `cornerRHS`, `CornerEmp`, `CornerUnemp` (stated along any
  price path `P`, against the corner policy's own next-period consumption); `floor_lt_cornerCons`,
  `cornerPolicy_mem_feasible`, `utility_le_tangent`, `cornerValue_split`,
  **`objective_le_corner`** (tangent lines: gain from leaving the corner is
  `(g − a)(u'(c) − β E R' u'(c'))`), **`cornerValue_eq_valueFunction`**,
  **`policy_eq_cornerPolicy`**. Standard axioms only. Next C3 (`μc` is a sequence-state
  equilibrium).
* **C3 DONE** 2026-11-07 (`CornerEquilibrium.lean`): `CornerConditions` (the three conditions
  along `seqPrices μc ω` at every history), `pushNode_cornerDist` (one step from `cornerDist y z`
  is `cornerDist z z'`, by design consistency), **`isSeqStateEquilibrium_μc`**,
  **`exists_represents_μc`** (represented by a recursive equilibrium on `(z, K)`). Standard
  axioms only. Remaining: C4 (CRRA + clamped CD, conditions from primitives, witness).
* **C4 DONE** 2026-11-07. `CornerPrimitives.lean`: price bounds `R ∈ [Rlo, Rhi]`, `w ∈ [wlo, whi]`
  + uniform worst-case inequalities ⇒ the corner conditions along every price path
  (`cornerFeas/Emp/Unemp_of_bounds`, **`cornerConditions_of_bounds`**). `CornerWitness.lean`:
  `Bool × Bool` economy, log utility, clamped CD (share 1/2, δ = 0, TFP 1, capital box [1/4, 1],
  labour clamped at 1 ⇒ `R ∈ [3/2, 2]`, `w ∈ [1/4, 1/2]`), efficiencies 44/2, `ā = 1`, `β = 9/10`,
  employed shares 3/5 / 13/20 with consistent transitions; **`cornerWitness`**: sequence-state
  equilibrium + `KSufficient` + represented on `(z, K)`; `capAt_witness` (capital 3/5 or 13/20,
  inside the box). Exact arithmetic (`norm_num`), standard axioms only. **Corner programme
  complete.** Caveats: labour clamp degenerate (prices ignore labour); uniqueness not claimed.
* **Stationary law DONE** 2026-11-07 (`CornerStationary.lean`): `continuous_μc`; `lawKm_witness`
  (on the capital sets next capital is the employed share of today's shock); `bind_witness` (one
  step depends only on the shock marginal); `statLaw` (weight 1/4 on `(z', share z)`);
  **`cornerStationary`**: invariant, on the capital sets, unique there. With `cornerWitness`, a
  stationary recursive equilibrium on `(z, K)`. Ergodicity not stated separately.
