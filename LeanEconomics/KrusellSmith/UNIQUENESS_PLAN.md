# Uniqueness of sequential equilibrium by contraction (Track A)

Goal: under explicit conditions on primitives, `Φ` (capital path ↦ mean saving path) is a
contraction in a depth-weighted sup norm, so `UniqueSequentialEquilibrium` holds and
`Recursive.lean` delivers a recursive equilibrium on the minimal state with no remaining
hypothesis.

Setting: `KSInada` (any CRRA `γ > 0`, income floor `y̲ > 0`), floored economy with
`c̲ = floorLevel / 2`, so optimal consumption lies in `[c_lo, c_hi] = [floorLevel, topCons]` at
every node, for every path (`floorLevel_le_consumption`). Labour is exogenous, so prices at a
node depend on the path only through `K_n`.

## Hypotheses to add

* (U) utility `C¹` on `(0, ∞)`, and on `[c_lo, c_hi]` its derivative satisfies
  `m (y − x) ≤ u'(x) − u'(y) ≤ M (y − x)` for `x ≤ y` (CRRA: `m = γ c_hi^{-γ-1}`,
  `M = γ c_lo^{-γ-1}`).
* (P) prices Lipschitz in capital: `|R(z,K,L) − R(z,K',L)| ≤ ℓ_R |K − K'|`,
  `|w(z,K,L) − w(z,K',L)| ≤ ℓ_w |K − K'|` (clamped Cobb–Douglas: explicit on the clamp box).
* (I) impatience against the largest return: `β R̄ θ < 1`, where `θ` bounds the slope of saving
  in assets. First version `θ = R̄` (saving and consumption both nondecreasing in cash), so
  `β R̄² < 1`; refine later with the minimal MPC (`Models/MinimalMPC.lean`, Carroll–Shanker),
  `θ = (β R̄)^{1/γ}`.

## Status

* **M1 done** (`Euler.lean`, `Monotone.lean`, `Sensitivity.lean`). The envelope theorem turned out
  unnecessary: the Euler inequalities with corners come from value-difference sandwiches and
  continuity of `u'` alone (`euler_ge`, `euler_le`), and the comparison of Euler roots
  (`euler_compare`) needs no Lipschitz bound on the right-hand side. The per-node bound is
  `du_consumption_sub_le`.
* **M2 done in its first form** (`policy_mono`, `policy_sub_le`): saving is nondecreasing in assets
  with slope at most the gross return, so `θ = R̄`.
* Next: M3 (distributions), M4 (assembly).

## Milestones

### M1. Household sensitivity in the marginal-utility metric (the core)

For two paths `K, K'`, write `ρ_n = sup_a |u'(c_n^K(a)) − u'(c_n^{K'}(a))|` (consumption at
assets `a`, node `n`, all idiosyncratic states). Show

    ρ_n ≤ C₀ |K_n − K'_n| + β (C₁ E|K_child − K'_child| + R̄ E ρ_child).

Ingredients (tree versions of stationary results already in the repo):
1. envelope `V_n'(a) = R_n u'(c_n(a))` (Clausen–Strub lazy agent, `IncomeFluctuationEnvelope`);
2. functional Euler equation with corners (borrowing limit `a' = 0`, cap `a' = ā`; the
   consumption floor is slack) — necessity only (`ColemanReffett.isEulerSolution_consumptionFn`);
3. consumption nondecreasing in assets at every node (concavity of `V`, already proved);
4. comparison of roots: increasing `φ(a') = u'(x − a')` against decreasing
   `G(a') = β E[R_child u'(c_child(a'))]`; perturbing `G` by `δ` and cash by `Δx` moves
   `u'(c)` by at most `δ + Lip(G)·|Δx|`, corners being 1-Lipschitz clamps
   (`euler_root_le` is the order version);
5. unrolling the recursion over the infinite subtree: `ρ` is bounded, so
   `ρ_n ≤ Σ_j (β R̄)^j E[C |ΔK at depth j below n|]` with geometric tail.

Policy difference: `|a'^K_n(a) − a'^{K'}_n(a)| ≤ |Δcash| + ρ_n / m`.

### M2. Saving slope `θ`

`0 ≤ a'_n(a) − a'_n(b) ≤ θ (a − b)` for `b ≤ a`; first `θ = R̄` from monotonicity of consumption
and saving in cash.

### M3. Distributions (Lipschitz-dual distance, no Wasserstein library needed)

`d_n = sup { |∫ f dμ_n − ∫ f dμ'_n| : f bounded, 1-Lipschitz in assets }`. Push-forward:
`d_child ≤ θ d_n + sup_a |a'^K_n(a) − a'^{K'}_n(a)|`; mean capital is 1-Lipschitz in `d`.

### M4. Assembly

Weighted norm `‖ΔK‖_λ = sup_n λ^{depth n} |ΔK_n|` with `β R̄ < λ < 1/θ`. Future influences
decay like `(β R̄/λ)^j`, past ones like `(θ λ)^j`, so

    ‖Φ(K) − Φ(K')‖_λ ≤ ε · C(primitives) / ((1 − β R̄/λ)(1 − θ λ)) · ‖K − K'‖_λ,

with `ε = max(ℓ_R, ℓ_w)`. Two fixed points are bounded, so their weighted distance is finite and
the contraction forces it to zero: uniqueness, then `Recursive.isRecursive` unconditionally.

### M5. Cobb–Douglas instance and numbers

Lipschitz constants of clamped Cobb–Douglas prices on `[capLo, capHi]`; evaluate `ε*` at
realistic parameters in MATLAB to see how restrictive the theorem is.

## Honest scope

The condition `ε < ε*` says general-equilibrium price feedback is weak. It will not cover the
standard Krusell–Smith calibration; it does give an unconditional existence theorem for recursive
equilibrium on the minimal state for a class of Krusell–Smith economies, plus Lipschitz
dependence of equilibrium on the initial distribution and a convergent iteration.
