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
