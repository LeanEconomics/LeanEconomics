# Order structure on the cross-sections: when is K injective?

Goal: prove `KInjective` (hence `KSufficient`, hence the stationary recursive equilibrium on
`(z, K)` of `minMPC_smallShare_aggregateState`) for economies **with** idiosyncratic
heterogeneity, by an order argument on whole cross-sections: if the cross-sections the equilibrium
visits at each shock form a **chain** for stochastic dominance, then capital determines the
cross-section (two comparable cross-sections with the same mean are equal). No linearity of
individual policies is needed.

## The order

`AssetDominates ν ν'` (`StochasticOrder.lean`, MR2): every bounded continuous function that is
nondecreasing in assets for each idiosyncratic state has a larger integral under `ν'`. Functions of
`e` alone are asset-monotone in both directions, so **dominance forces equal employment
marginals**; under the KS design (`EmploymentDesign`) all cross-sections at shock `z` have marginal
`m z`, so they can be comparable.

## The argument

Write `A_z` for the cross-sections visited at shock `z` and `Γ_{y,z} ν = lawOfMotion y ν z`, so
`μ*(cons z ω) = Γ_{ω 0, z} (μ* ω)`. Take two histories `ω, ω'` with `ω 0 = ω' 0`, first differing
at lag `T` (`y = ω T ≠ y' = ω' T`, say `y < y'` for an order on `Z`). Then:

* **(Sep) last-shock separation** orders the cross-sections one period after the difference:
  `Γ_{y, x} ν ≼ Γ_{y', x} ν'` for all `ν ∈ A_y`, `ν' ∈ A_{y'}` (`x = ω (T−1)`, the common shock);
* **(Mon) monotone law of motion** carries the order forward along the common shocks
  `ω (T−1), …, ω 0`: `ν ≼ ν' ⇒ Γ_{x,x'} ν ≼ Γ_{x,x'} ν'` on the visited cross-sections;
* so `μ* ω` and `μ* ω'` are comparable; equal capital then forces equality.

## Milestones

* **OS0** (measure theory, `OrderStructure.lean`): `AssetDominates` forces equal employment
  marginals; **`eq_of_dominates_of_mean_eq`**: `ν ≼ ν'` with equal mean assets ⇒ `ν = ν'`
  (conditional on each `e`, survival functions ordered and their integrals equal ⇒ equal a.e. ⇒
  equal by right continuity); antisymmetry of `≼`.
* **OS1** (abstract chain theorem): hypotheses (Mon) and (Sep) on the visited cross-sections ⇒
  every two cross-sections at the same shock are comparable (induction on the first-difference lag,
  using `eq_lawOfMotion`) ⇒ `KInjective` ⇒ `KSufficient` (`KInjective.kSufficient`) ⇒ everything
  in `AggregateStateIff.lean`. Certain.
* **OS2** (Mon from primitives): under uniqueness, the equilibrium price path from `ν` is isotone in
  `ν` (Tarski comparative statics: the greatest fixed point of a map isotone in path and parameter
  is isotone in the parameter; under uniqueness it is the equilibrium, `GreatestEquilibrium.lean`)
  when saving is isotone in the capital path (`SavingMonotone`, hypothesis (H) of MR3) — combined
  with `nodeDist_dominates` (MR2) this gives (Mon). (H) is proved for **complementarity
  economies** (constant wage, return nondecreasing in `K`, RRA ≤ 1; `savingMonotone_of`, MR4).
  **(H) fails for Cobb–Douglas** at the current node (cash `R(K) a + w(K) e` falls in `K` for the
  rich), so this route does not cover CD as stated.
* **OS3** (reduce Sep to extremes): with (Mon) and **shock monotonicity** (a higher current shock
  raises saving for every cross-section), `μ*` is isotone in the history for the product order
  (backward limit of isotone maps), each `A_y` is a compact chain with greatest element
  `μ*(y, z̄, z̄, …)` and least `μ*(y, z̲, z̲, …)`, and (Sep) reduces to finitely many comparisons:
  `Γ_{y,x} μ*(y, z̄^∞) ≼ Γ_{y',x} μ*(y', z̲^∞)` for `y < y'`.
* **OS4** (research, the crux): an economy satisfying the OS3 comparisons. They say one period of a
  better shock outweighs a permanent boom against a permanent bust — true only when the economy
  **forgets fast** (small saving slope relative to the shock effect on saving, e.g. high
  depreciation / long periods). Needs a **lower** bound on the aggregate saving response to the
  current shock (positive unconstrained mass, minimum MPS) against an upper bound on the spread of
  `A_y` (the burn-in bound). Uniqueness in the complementarity class needs its own small-feedback
  theorem (Track A with constant wage and small return slope; gross returns `< 1` as in MR4d).
* **OS5** (research) Cobb–Douglas: an order that CD equilibrium dynamics preserve on the visited
  cross-sections (FOSD in assets fails pointwise; candidates: dominance in cash on hand, or a
  weaker (Mon) required only on pairs of visited cross-sections with the same shock history since
  the difference), or a direct (Mon) for small shares where the price feedback is `O(α)` — but an
  `O(α)` error has no sign, so exact comparability does not follow from smallness alone.

## Honest assessment

OS0–OS1 are certain, OS2–OS3 likely in the complementarity class (reusing MR2–MR4). OS4 decides
whether the route yields any heterogeneous example; it is the order version of the separation
condition and will hold, if at all, only with fast forgetting. At KS-type persistence the extremes
of `A_y` and `A_{y'}` overlap (a bust after a long boom vs a boom after a long bust), so (Sep)
fails there and the chain argument cannot apply — which says nothing about `KSufficient` itself,
only that this sufficient condition is unavailable. OS5 is needed for the user's preferred CD case.

## OS4 analysis (2026-11-07, before coding)

**What (ExtremeSep) says about capital.** Means are ordered under dominance, so (ExtremeSep) with
Lemma A forces: for `y < y'`, *every* capital level reached one period after `y` is below every
level reached after `y'`. So `Kset z'` splits into blocks ordered by yesterday's shock, and
recursively by every earlier shock: **capital encodes the whole shock history**, like a base-`|Z|`
expansion (Cantor coding). Heuristically this needs the law of motion of capital to contract by a
factor `θ ≲ 1/|Z|` (each shock's image must fit disjointly), i.e. the economy forgets at least
half its capital deviation per period with two shocks. That is the opposite regime from KS's
approximate aggregation (high persistence); the order route cannot reach KS calibrations, and the
user's question there stays open.

**What (ShockMon) needs.** Compare `cons y τ` and `cons y' τ` (same past). Their cross-sections
have the same assets (capital is predetermined) and, if idiosyncratic transitions do not depend
on aggregate shocks, the same employment marginal: **the same cross-section**. Households then
differ only in today's prices and in the expected future. A better `y'` must raise every
household's saving, which needs:
* i.i.d. aggregate shocks (otherwise a persistent good shock raises expected future income and
  *lowers* saving through the income effect);
* the shock to hit the current wage (or return) upward, with saving increasing in cash on hand at
  a fixed continuation (true: assets enter only through cash);
* the induced higher capital path to raise saving further (`SavingMonotone`, complementarity).

New machinery needed: comparative statics of the household problem **across roots** (`z₀ = y` vs
`y'`; with i.i.d. shocks the subtrees have the same law), and of the equilibrium path in the root
shock (a variant of `eqPath_mono`).

**What (ExtremeSep) needs beyond that.** Coupling quantiles of the boom cross-section (richer) and
the bust cross-section (poorer): the wage gain `w(y') − w(y)` must outweigh the wealth gap times
the saving slope, for every quantile and employment state. That needs a **lower** bound on the
saving response to cash. At the borrowing constraint the response is zero, so the bound must come
from a structure where the constraint binds identically in both (or nowhere).

**Candidate economies.**
* (a) **Corner economy**: parameters where employed households always save the cap and
  unemployed save zero (Euler inequalities at the corners, `EulerOf.lean`). Cross-sections are
  two-point in assets, nondegenerate across employment; under the KS design capital is
  `ā × (yesterday's employment rate)`, so if employment rates differ across shocks, capital
  reveals yesterday's shock and the cross-section — `KInjective` directly, a genuinely
  heterogeneous (if degenerate in assets) example, outside the order route.
* (b) **Fast-forgetting complementarity economy**: i.i.d. aggregate shocks to the wage, return
  rising slightly in capital, aggregate-independent employment transitions, strong impatience
  (small saving slope). The order route applies if the corner issue in (ExtremeSep) can be
  handled; needs the cross-root comparative statics above. Substantial and may fail at the
  constraint.

## OS4(b): interior heterogeneity with a linear technology (plan 2026-11-08)

**Design.** Keep the order route (OS0–OS2: (Mon) + (Sep) ⇒ chain ⇒ `KInjective` ⇒ `KSufficient`)
but choose the economy so that its two hard hypotheses are free and the content sits in (Sep)
and interiority:

* **Linear technology** `Y = A(z) K + B(z) L`: prices are exact marginal products and depend on the
  shock only (`R` constant, `w(z)`). Then the household problem does not depend on the capital
  path at all, so `SavingMonotone` holds with equality and sequential equilibrium is unique (the
  distribution path does not depend on prices). A return rising in `K` would need a small-feedback
  uniqueness theorem we do not have; Cobb–Douglas fails `SavingMonotone`.
* **i.i.d. aggregate shocks and i.i.d. employment** (`aggProb z z' = π z'`,
  `idioProb z z' e e' = m e'`): the continuation value at the root does not depend on today's
  shock or employment (re-root with `valueFunction_shift`), so saving is one nondecreasing function
  of cash on hand.
* **Ordered cash** `R ā + w(y) e_hi ≤ w(y') e_lo` for `y < y'`: every household saves less after a
  worse shock than every household after a better one. So (Sep) holds directly, for any two
  cross-sections; (ShockMon), (ExtremeSep) and Lemma A are not needed.
* **Interior saving** from crude Euler bounds (tangent lines, value increments bounded by plans
  that copy the neighbour's saving): saving is positive at cash `x` when
  `1/x < β E[R/(w'e')]`, and below the cap when `1/(x−ā) > β E[R/((R−1)ā + w'e')]`. Both hold
  for every low-efficiency household after a good shock for suitable parameters (window exists
  only with `βR < 1` and moderate `β`; e.g. `e ∈ {1, 1/2}`, `w ∈ {1, 1/4}`, `R = 6/5`, `β = 1/2`,
  `ā = 5/24`).

**Milestones.**
* **OI0** (generic) `PricesExogenous`: households, policies and the distribution path do not
  depend on the capital path; `savingMonotone_of_exogenous`,
  `uniqueSequentialEquilibrium_of_exogenous`.
* **OI1** (generic) `IIDShocks`: the root continuation is the same function of next assets for
  every root shock and employment state.
* **OI2** (generic) two-root Topkis: less cash and the same continuation give less saving.
* **OI3** (generic) `OrderedCash` ⇒ (Sep) for every sequence-state equilibrium ⇒ `KSufficient`.
* **OI4** (generic, log utility) interior-saving bounds at the root.
* **OI5** witness: linear-technology economy; every sequence-state equilibrium has `(z, K)`
  sufficient and a positive mass of households saving strictly inside `(0, ā)` after every good
  shock.

**Honest limits.** Prices do not feed back from capital (linear technology), shocks are i.i.d., and
the household is impatient (`β = 1/2`, long periods: the crude interiority bounds have tiny
windows for `β ≥ 0.8`). Strict monotonicity of interior saving (hence an infinitely supported
cross-section) is not claimed.

## Status

* Planned 2026-11-07.
* **OS0 + OS1 DONE** 2026-11-07 (`OrderStructure.lean`): `AssetDominates.initMass_eq` (equal
  employment marginals); **`eq_of_dominates_of_mean_eq`** (proof shorter than planned: for an
  `L`-asset-Lipschitz `f`, both `f + L a` and `L a − f` are asset-monotone, so dominance + equal
  means give equal integrals, then `eq_of_forall_assetLip`); `Comparable`, `MonOnHistories`,
  `SepOnHistories`, `comparable_of_firstDiff`, **`comparable_of_sameShock`**,
  **`kInjective_of_chain`**, **`kSufficient_of_chain`**. Standard axioms only. Next OS2 ((Mon) from
  primitives in the complementarity class).
* **OS2 DONE** 2026-11-07 (`OrderMonotone.lean`): **`eqPath_mono`** (Tarski comparative statics:
  under `SavingMonotone` + uniqueness, `ν ≼ ν'` ⇒ equilibrium capital path from `ν` ≤ from `ν'`;
  labour equal because dominance forces equal marginals), **`lawOfMotion_dominates`**,
  **`monOnHistories_of_savingMonotone`** ((Mon) for every sequence-state equilibrium),
  **`kSufficient_of_savingMonotone`** (with (Sep)). Standard axioms only. Remaining hypothesis:
  (Sep). Next OS3 (reduce (Sep) to extreme histories).
* **OS3 DONE** 2026-11-07 (`OrderExtremes.lean`): `ShockMonOnHistories` (a better newest shock
  with the same past dominates after a common next shock — stated on histories, so no
  cross-marginal order is needed: all comparisons are at the same current shock);
  `dominates_of_singleDiff`, **`dominates_of_le`** (Lemma A: pointwise better history with the
  same shock dominates — one lag at a time, then the limit via continuity of `μ`); `zMax`, `zMin`,
  `ExtremeSep`; **`sepOnHistories_of_extremes`**; **`kSufficient_of_extremes`**
  (`SavingMonotone` + uniqueness + continuity + (ShockMon) + (ExtremeSep) ⇒ `KSufficient`).
  Standard axioms only. Remaining hypotheses on the equilibrium: (ShockMon), (ExtremeSep). Next
  OS4 (an economy satisfying them, with uniqueness, in the complementarity class).
* **OS4(b) OI0–OI5 DONE** 2026-11-08 via the linear-technology design.
  * `ExogenousPrices.lean` (OI0–OI3): `policy_congr`, `savingMonotone_of_exogenous`,
    `uniqueSequentialEquilibrium_of_exogenous`, `cont_root_eq`, `policy_le_policy_of_cont`,
    `sepOnHistories_of_orderedCash`, **`kSufficient_of_orderedCash`**.
  * `InteriorSaving.lean` (OI4): `value_sub_ge`, `value_sub_le`, `policy_pos_of`,
    `policy_lt_cap_of`.
  * `InteriorWitness.lean` (OI5): `e ∈ {1, 3/4}`, `w ∈ {1, 1/3}`, `R = 6/5`, `β = 1/2`,
    `ā = 25/72`, floor `1/100`, `δ = 1/3000`; **`interiorWitness`** / **`exists_interiorWitness`**:
    `(z, K)` sufficient in every sequence-state equilibrium, and after every good shock the
    low-efficiency half saves strictly inside `(0, ā)`.
  * Standard axioms only. Written up in WriteUpKrusellSmith §9.
