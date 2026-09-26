# Uniqueness in Bewley–Aiyagari and stochastic OLG models: a literature survey against our dead ends

Written 2026-09-27, after the OLG μ=1 certificate (all 59 stages, `numerics/rational/allstages.log`)
and the write-up (`main.pdf`). Purpose: find routes to uniqueness that the project has not tried,
and check each against the recorded dead ends (appendix of the write-up; memory
`leaneconomics-approaches`). Sources read in full or in the relevant sections are listed at the end;
local copies live in `~/Dropbox/Papers_and_Textbooks/Econ_Papers/Completed/Bewley-Huggett-Aiyagari/`.

## Summary, ranked by what it is worth to the project

1. **The OLG μ=1 theorem already follows from the stationary development, with no certificate and
   for every calibration.** Light (2020)'s proof of Theorem 1 is an induction on Bellman iterates
   from zero, and those iterates ARE the stage values. The project formalised the induction step for
   the stationary problem (`Models/IncomeFluctuationRateStep.lean`,
   `incDiffSlices_bellman_withRate`) and then, on the OLG side, hunted the same statement
   (`ValueGap` in `OLG/RateMonotone.lean`) through consumption bounds instead. See §1.
2. **The moment question is answered, sharply.** For `U ≥ 0` with `E U = 1`,
   `E[U^{1+1/γ}] ≤ (1 + Var U)^{1/γ}`, attained by a two-point law; with a known lower bound on `U`
   the extremal is the two-point law on `{lo, 1 + Var/(1−lo)}`. Beats the Lyapunov step
   `(1+Var)^{(γ+1)/(2γ)}` for every `γ > 1`. Elementary proof (quadratic majorant). See §2.
3. **Where multiplicity actually lives** (Walsh & Young 2025; Walsh 2026): never below
   `γ ≈ 1.49`, `δ < 0.19` or `ρ < 0.47` in 24,000 random Aiyagari draws; always with a disaster
   income state; the extra steady states sit at NEGATIVE net return `r < δ` (Walsh conjectures this is
   necessary). Our OLG range `r ∈ [4%, 6%]` is on the positive side. See §3.
4. **Average monotonicity without pointwise monotonicity** (Hu & Shmaya 2019): coupling on a common
   shock path plus Kac's lemma. It is the infinite-horizon form of our increment route, and its
   content is an ordering DURING excursions that we do not have at `γ > 1`. See §4.
5. Everything else surveyed is either `RRA ≤ 1` again (Toda 2019, Light 2023, Bloise–Citanna 2015,
   Achdou et al. 2022), closed-form CARA (Toda 2017), a condition that fails at standard calibrations
   (Pröhl 2018: `β(1−δ)^{1−γ} < 1`), or structurally inapplicable (polynomial/Descartes methods,
   many-commodity patient-consumer stability, FBSDE local uniqueness, mean-field monotonicity —
   the last already closed in §8 of the write-up). See §5.

## 1. Light's induction is the stage induction

Light (2020, Economic Theory; the 2018 WP is in the folder) proves, for the stationary income
fluctuation problem with CRRA `γ ≤ 1`, that `g(a, s, R₂) ≥ g(a, s, R₁)` at every state (his Theorem
1). His proof (Appendix, p. 14) is:

> Let `f` be concave in `a` with `f'(·, R₂) ≥ f'(·, R₁)`. Then `(Tf)'(·, R₂) ≥ (Tf)'(·, R₁)`.
> Define `f_n = Tⁿ f`; conclude `f_n'` is increasing in `R` for every `n`, pass to the limit.

Three ingredients in the step: the budget coincidence at `(a, R₁)` and `(R₁a/R₂, R₂)`; the
envelope `(Tf)' = R u'(σ_f)`; and his Lemma 3 (`α/z(αx)` increasing in `α` for concave positive `z`)
applied to `σ_f(·, R₂)`, which needs `σ_f` CONCAVE (his Lemma 4, Carroll–Kimball) and `c u'(c)`
increasing (`γ ≤ 1`). The induction starts from any concave `f`, in particular `f = 0`.

The project has all of this in Lean for the stationary problem:

* `Models/IncomeFluctuationRateStep.lean: incDiffSlices_bellman_withRate` — for ARBITRARY
  continuations `v, w` with concave slices, `IncDiffSlices v w ⟹ IncDiffSlices (T_{r₁} v) (T_{r₂} w)`,
  given positive consumption, cap slack, concavity of `consumptionFnOf w` (the higher-rate one), and
  `MonotoneOn (fun y => y * du y)` (RRA ≤ 1). `incDiffSlices_zero` is the base.
* `contIncreasingDifferences_withRate` then runs exactly the induction above on
  `bellman^[n] 0` at the two rates (its `hstep`) and passes to the limit.

In the OLG, `OLG/LifeCycle.lean: stageValue k = bellman^[k] 0` on the same structure
`IncomeFluctuation Z 0 assetCap`, and `OLG/RateMonotone.lean: ValueGap h₁ h₂ θ k` is
`IncDiffSlices (stageValue k at r₁) (stageValue k at r₂)` with a margin `θ`. So:

* `hstep` of `contIncreasingDifferences_withRate`, restated for `stageValue`, is `ValueGap` with
  `θ = 0` at every stage `k`, by induction with `incDiffSlices_bellman_withRate`, whose hypotheses
  at stage `k` are the OLG's own objects: `concaveOn_stageConsumption` (the `hcw`), the cap-slack
  hypothesis already carried by `PropensityFloor.lean` (`hslack`), `PositiveConsumptionAll`.
* `stagePolicy_mono_of_valueGap` needs `0 < θ`. Either prove the `θ = 0` version (the by-contra
  in its proof uses the margin only to break a tie; with `u` strictly concave the lower-rate
  argmax is unique, so weak increasing differences suffice — the standard Topkis/Milgrom–Shannon
  argument, and the same one `policy_le_of_cont_increasingDifferences` runs at the fixed point),
  or chain `policyOf_withRate` + `policy_le_of_cont_increasingDifferences` + `stagePolicy_mono`
  as the stationary file does.
* Then `olgCapital_le_of_valueGap` and `olgEquilibriumRate_unique` close as they stand.

What this gives: Theorem 1 at every state and age, hence a monotone capital supply and a UNIQUE
stationary OLG equilibrium, for CRRA with `γ ≤ 1` (in the current development, `γ = 1` by the
`crra_pinch`), ANY `β`, any rate pair with `RateOK` and cap slack, ANY finite Markov earnings
process, any horizon. The certificate (`cert.py`, 10.5 h) certified one rational calibration at
`γ = 1`; this covers all of them, and it is the theorem Light proved, transplanted. Numerically the
statement was already seen to hold: `numerics/condB.m` found `ValueGap` true at log with relative
margin `+7e-6` (near-tight, as a theorem with equality at corners should be) and false from `γ = 2`.

Why it was missed: the OLG hunt of 2026-09-23 tried to discharge `ValueGap` from the consumption
SANDWICHES (whose width `κ_k H_k` is exactly what drives the gap, so they cannot see it — recorded
correctly as the obstruction) and did not go back to the operator step already proved for the
stationary case. Nothing in the stationary step uses stationarity.

What it does NOT give: anything at `γ > 1`, where `c u'(c)` is decreasing and Light's pivotal
inequality fails pointwise — consistent with Theorem 1 failing pointwise above `γ ≈ 3.4` and
`ValueGap` failing from `γ = 2`. The certificate machinery stays the only route above one, and §2
is about its loose link.

## 2. The moment question, closed

The two-rate chain (`mul_le_mul_of_euler_pair`, `damped_le_one`) needs the gradient sum
`A = Σ_w u^{1+1/γ}` with `u = (C/M)^{-γ}`, `E_w u = 1` exactly, and the write-up's loose link is the
Lyapunov step `A ≤ (1 + Var_w u)^{(γ+1)/(2γ)}`, which "fails from `γ ≈ 1.5`". The sharp bound given
mean and variance is a classical Chebyshev–Markov–Krein problem (Karlin & Studden 1966, ch. II–IV:
for a T-system `{1, x, x², φ}` the extremum of `E φ` under three fixed moments is attained at a
principal representation, two atoms one of which is an endpoint). For `φ(x) = x^p`, `p = 1 + 1/γ
∈ (1, 2)`, `φ''' < 0`, so the maximum is at the LOWER principal representation `{lo, ξ}`.

**Theorem (elementary form).** Let `U ≥ 0` be a random variable with `E U = 1` and
`E U² = 1 + v`, and `1 < p < 2`. Then `E U^p ≤ (1 + v)^{p−1}`, with equality for the two-point law
`P(U = 1+v) = 1/(1+v)`, `P(U = 0) = v/(1+v)`.

*Proof.* With `m = 1 + v`, `x^p ≤ (2−p) m^{p−1} x + (p−1) m^{p−2} x²` for all `x ≥ 0`: the
difference `g(s) = (2−p)s + (p−1)s² − s^p` at `s = x/m` has `g(0) = g(1) = g'(1) = 0`,
`g''(s) = (p−1)(2 − p s^{p−2})` negative then positive, so `g ≥ 0` on the convex part `[s*, ∞)` (a
minimum of value `0` at `1`) and on the concave part `[0, s*]` (above its chord from `(0,0)` to
`(s*, g(s*) ≥ 0)`). Take expectations: `E U^p ≤ (2−p) m^{p−1} + (p−1) m^{p−2} · m = m^{p−1}`. ∎

With `p − 1 = 1/γ`: `A ≤ (1 + Var)^{1/γ}`, against Lyapunov's `(1 + Var)^{(γ+1)/(2γ)}`; the
exponents agree at `γ = 1` (both give `A = 1 + Var`, the identity `sum_mul_sq_eq_one_add_variance`)
and the new one is smaller for every `γ > 1`. Checked numerically on 20,000 random laws
(`A ≤ bound`, max ratio 0.99999999997).

**With a lower bound.** If moreover `U ≥ lo > 0` (we have one: `C ≤ min(κ(m + H_arith), m)` gives
`u ≥ (C_max/M)^{-γ}`), the extremal is the two-point law on `{lo, ξ}`, `ξ = 1 + v/(1 − lo)`, weight
`(1−lo)/(ξ−lo)` on `ξ`, and `A ≤ (1 − w_ξ) lo^p + w_ξ ξ^p`. Brute force over three-point laws on
`[lo, 10]` confirms the two-point value is the maximum to 4e-5 (random search) in four cases. Numbers
at `γ = 2, Var = 0.041`: Lyapunov 1.0306; `lo = 0`: 1.0203; `lo = 0.5`: 1.0167; `lo = 0.8`: 1.0154.
The proof of the `lo` version is the same quadratic majorant with contacts at `lo` (simple) and `ξ`
(double); not written out here.

Lean cost: one polynomial inequality on `ℝ≥0` (`rpow` with exponent in `(1,2)`) plus
`Finset.sum` linearity — the style of `Analysis/PowerMean.lean: sum_mul_sq_eq_one_add_variance`.
Immediate follow-up (numerical, before any Lean): rerun the two-regime/certificate arithmetic at
`γ = 1.5, 2, 3` with `(1+Var)^{1/γ}` (or the `lo` form) in place of the Lyapunov step, to see whether
the allowance `Þ₁/(q(1−κ_k R₁)) − 1` is met. If it is, the branch-and-bound certificate over the
admissible box extends verbatim, since the certificate bounds `Var` and not `A`.

## 3. Where multiplicity lives, and what it suggests to prove

* Walsh & Young (2025 WP, "Equilibrium multiplicity in Aiyagari and Krusell–Smith"): 24,000
  uniform draws of `(β, γ ∈ [0,8], ρ_e, σ_e, δ, α)`, half with a disaster state; 250 draws with
  multiplicity, ALL with the disaster state, always exactly three steady states, never with
  `γ < 1.49`, `ρ_e < 0.47` or `δ < 0.19`; the lowest rate is near `αδ`. Mechanism: at low returns
  agents hoard capital against long disaster spells, so supply turns back up as `r` falls.
* Walsh (2026, arXiv 2609.03730, 3 Sep 2026): first ANALYTIC construction of three steady states
  (`γ = 3`, two states, `ε → 0`, `R < 1`). Tools: (i) a lower bound on stationary supply from the
  Euler equation iterated `N` periods along the worst path, `c_N ≥ ((βR)^N q_N)^{1/γ} c`, combined
  with the feasibility ceiling `c_N ≤ R^N g + ε(1−R^N)/(1−R)` and the stationary budget identity
  `C = L − (1−R) A`; (ii) an upper bound via the Coleman operator (Li–Stachurski). He conjectures
  negative net return is NECESSARY for multiplicity.
* Toda & Walsh (2024 JME survey, Table 1): every known Bewley uniqueness result is `RRA ≤ 1`
  (plus CARA closed forms); "the field needs more results" for `RRA > 1`. Kirkby (2019) is cited
  for the computational claim that standard calibrations are unique.

For us: (a) our `γ = 5` failure of Theorem 1 is at ZERO wealth in the HIGHEST earnings state at
`r ≥ 4%` — a different mechanism from disaster hoarding at `r < δ`, and one that the literature's
multiplicity examples do not exercise; the OLG range is positive-return throughout. (b) A target
theorem the evidence supports: uniqueness whenever the candidate range has `R ≥ 1`, at any `γ`, or
at least for `γ ≤ 1.49`. No proof idea beyond ours. (c) Walsh's supply bounds are our
floor/ceiling machinery with the stationary budget identity substituted for the distribution; the
substitution `C = L − (1−R)A` is what makes his constants usable, and our existence floor
(`rhi` within `1e-27` of `λ`) might benefit from the same substitution.

## 4. Average monotonicity without pointwise monotonicity (Hu & Shmaya)

Hu & Shmaya (2019 JET, "Unique monetary equilibrium with inflation in a stationary Bewley–Aiyagari
model"; WP 2017 read): pure-currency Bewley economy, lump-sum transfer `b`; the individual policy is
NOT monotone in `b` in the FOSD sense (so Acemoglu–Jensen's "positive shock" machinery does not
apply), yet average consumption `∫ c_b dλ_b` is strictly increasing in `b` (their Lemma 2). Proof:
couple the two agents on one endowment path; on days High has more wealth, `c_b` increasing in
wealth and in `b` orders consumption pointwise; over a maximal excursion where High is poorer, the
budget identity (entered richer, left poorer, same endowments, more transfer) orders TOTAL
consumption over the excursion; Kac's lemma turns per-excursion accounting into stationary
expectations. Light (2020, §4.2) names this as the only step towards "monotonicity of average
savings without individual monotonicity".

Against our problem: this is exactly the shape of the increment route (`OLG/Increment.lean`:
coupling on a common earnings path, negative parts accumulated linearly, mass-weighted failure) —
in the life cycle the sum over ages replaces Kac's lemma, and no ergodicity is needed. What Hu &
Shmaya have and we lack at `γ > 1` is an ordering on the good days: `c_b` increasing in `b` at fixed
wealth, i.e. pointwise monotonicity in the parameter, which for us IS the failing Theorem 1. And
the target differs: average consumption monotone gives, via the stationary budget
`E c = E y + r E a`, only `r₂ E a₂ ≥ r₁ E a₁`, i.e. `E a₂ ≥ (r₁/r₂) E a₁` — at Aiyagari's
calibration the single-crossing margin needs `K/r ≈ 117` against `|D'| ≈ 39` in wage units, so
this alone is three times too weak. Recorded as the one genuinely different technique in the
literature; not a route as it stands.

## 5. The rest, briefly

* **Achdou, Han, Lasry, Lions, Moll (2022 REStud), Prop. 5**: continuous-time Huggett/Aiyagari,
  `IES ≥ 1`, no borrowing ⇒ `∂c/∂r < 0` pointwise ⇒ unique. Proof via Olivi's (2017)
  decomposition `∂c/∂r = (1/u''(c₀)) E∫₀^τ e^{−∫ξ} u'(c_t) dt + (1/u''(c₀)) E∫₀^τ e^{−∫ξ}
  u''(c_t) c'(a_t) a_t dt` (substitution `< 0`, income `> 0`), stopped at the time `τ` the
  constraint binds. Same content as our duration identity `Φ = Y[(w/R)(T_c − T_y) − K]` and
  re-pricing identity, in derivative form; the stopping at the constraint is the one feature ours
  lacks (our `Φ` sums over the whole life). They write that `IES ≥ 1` is "likely overly strong"
  since saving rises with `r` through interest income even when consumption does — our
  `stagePolicy_le_iff_consumption_le` says the same.
* **Pröhl (2018 WP, ECB version read; 2019 SSRN 3250651 not accessible from here)**: uniqueness
  of the recursive equilibrium in Krusell–Smith (hence Aiyagari steady states, per Walsh & Young)
  by monotone operator theory, under `β(1−δ)^{1−γ} < 1` for `γ > 1`. At `β = 0.96, δ = 0.08`:
  1.043 at `γ = 2` (fails), needs `δ ≲ 0.02`. The only `γ > 1` analytic condition in the
  literature, and it is a small-depreciation condition, not a risk-aversion one. Worth reading the
  full SSRN paper for whether the constant is an artefact of her operator norm.
* **Light & Weintraub (2022 OR)**: MFE uniqueness via monotone Markov kernels + FOSD — already
  formalised for the stationary chain (`aiyagari-equilibrium-uniqueness`, second route); needs
  pointwise policy monotonicity in the aggregate, i.e. Theorem 1 again.
* **Acemoglu & Jensen (2015 JPE)**: comparative statics of least/greatest equilibria, no
  uniqueness; the FOSD "positive shock" machinery is Light's Theorem 2, done.
* **Toda (2019 JME)** random discount factors, `RRA ≤ 1`; **Light (2023 OR)** many goods, CES
  `ES ≥ 1`, iid; **Bloise & Citanna (2015 JME)** limited commitment, `RRA ≤ 1`; **Toda (2017
  JEDC)** CARA Huggett: uniqueness for AR(1) income, multiplicity for negatively correlated PT
  components — all via affine CARA policies. None transfers.
* **Loi & Matta (2021 arXiv 2107.01947; 2023 JET)**: two goods, `c` impatience types, CRRA
  `γ ∈ (1, c/(c−1)]` ⇒ unique, by Newton's symmetric polynomials + Descartes' rule of signs on a
  polynomial excess demand. Needs polynomial excess demand; our supply is a DP output. Dead.
* **arXiv 2605.02817 (2026)**, "Equilibrium stability and uniqueness with a large number of
  commodities and patient consumers": substitution effects accumulate with the effective number of
  dated commodities `N_β = Σβⁿ` while income effects do not, under a preference-diversification
  condition (A5). Identical preferences make (A5) degenerate (explicitly), no risk, no constraints.
  Dead for us, though the mechanism (long horizons favour substitution) is the intuition behind
  our `Þ^{−J} ≈ 1.03` compounding in `PLAN.md`.
* **Chen, Ellingsrud, Harang, Irarrazabal, Mayorcas (2025, arXiv 2509.05170; MFE 2026)**:
  continuous-time OLG with idiosyncratic income, FBSDE/Pontryagin; existence and LOCAL uniqueness
  of the interest-rate path, CRRA, natural borrowing limit, semi-explicit policies. Not a global
  stationary-uniqueness route.
* **Mean field games** (Lasry–Lions monotonicity, Graber–Matter 2024, Cannarsa–Capuani 2026):
  closed in §8 of the write-up (collapse lemma `monotone_of_comonotone_of_strictMono`).
* **arXiv 2608.29488 (2026)**, "Conditional impatience and concavity of consumption functions":
  finite-horizon saving with stochastic discounting/returns/income/limits; consumption functions
  concave iff inverse absolute prudence is concave, under `E[βR] ≤ 1`; HARA without it. Relevant
  only if return risk is added (our `concaveOn_stageConsumption` is the CRRA case).
* **Bayraktar (2026, arXiv 2605.05127)**: finite-grid conditional uniqueness (strict
  monotonicity assumed). Nothing.

## Sources

Light, B. (2020) Uniqueness of equilibrium in a Bewley–Aiyagari model, Econ. Theory 69, 435–450
(WP 2018-04-23 read). Toda, A. A. & Walsh, K. J. (2024) Recent advances on uniqueness of
competitive equilibrium, J. Math. Econ. 113, 103008. Walsh, K. J. & Young, E. R. (2025 WP)
Equilibrium multiplicity in Aiyagari and Krusell–Smith. Walsh, K. J. (2026) Proof of steady-state
multiplicity in Aiyagari, arXiv:2609.03730. Açıkgöz, Ö. (2018) JET 173, 18–55. Achdou, Han,
Lasry, Lions & Moll (2022) REStud 89, 45–86 (NBER WP 23732 read). Hu, T.-W. & Shmaya, E. (2019)
JET 180, 368–382 (WP 2017-03-10 read). Light, B. & Weintraub, G. (2022) Oper. Res. 70, 585–605.
Acemoglu, D. & Jensen, M. K. (2015) JPE 123, 587–640. Pröhl, E. (2018) Approximating equilibria
with ex-post heterogeneity and aggregate risk (ECB conference version); (2019) Existence and
uniqueness of recursive equilibria with aggregate and idiosyncratic risk, SSRN 3250651. Toda, A. A.
(2017) JEDC 84, 77–90; (2019) JME 104, 101–113. Loi, A. & Matta, S. (2021) arXiv:2107.01947; (2023)
JET 207. Karlin, S. & Studden, W. J. (1966) Tchebycheff Systems. arXiv:2605.02817, 2509.05170,
2608.29488, 2605.05127.
