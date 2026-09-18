/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.CapitalSupplyMonotone
import LeanEconomics.Equilibrium.DebtorRate

/-!
# Dominance up to a shift

The FOSD coupling of `CapitalSupplyMonotone` needs the policies ordered at every state. With
borrowing, `DebtorRate` gives the order only up to a loss `γ = (r₂ - r₁)·|floor|` at debtor
states. This file runs the coupling with that loss carried along.

`DominatesShift δ μ ν` says `∫ h dμ ≤ ∫ h dν + δ L` for every test function `h` that rises
with assets and is `L`-Lipschitz in assets. One period of the motion turns a policy gap of `γ`
and an asset-Lipschitz constant `K` of the dominating policy into a new shift `δ K + γ`: the
gap enters once, and the old shift is scaled by how strongly tomorrow's assets respond to
today's (`DominatesShift.pushProb`). Iterating, the shift after `n` periods is
`γ (1 + K + ⋯ + K^{n-1})`, bounded by `γ/(1 - K)` when `K < 1`; dominance survives weak limits;
and applied to the asset coordinate it bounds aggregate capital:
`K₁ ≤ K₂ + γ/(1 - K)` (`aggregateCapital_le_add_of_policy_le_add`). For Huggett this is
`huggett_aggregateCapital_le_add`, with `γ = (r₂ - r₁)·|floor|` from the debtor loss term.

Two things are honest about the constant. The contraction `K < 1` of the saving policy in
assets — a marginal propensity to save below one — is a hypothesis; what this development
proves is only `K ≤ R`, which is useless here. And the bound is one-sided and of first order
in the rate gap, the same order as the substitution gain it would have to be weighed against;
so it makes the Huggett frontier precise without closing it.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetFloor assetCap : ℝ}

/-! ### The test class and the shifted order -/

omit [Fintype Z] [Nonempty Z] [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z] in
/-- `L`-Lipschitz in assets, at each income state. -/
def LipAsset (L : ℝ) (h : (↥(Icc assetFloor assetCap) × Z) →ᵇ ℝ) : Prop :=
  ∀ (z : Z) (a b : ↥(Icc assetFloor assetCap)), h (a, z) - h (b, z) ≤ L * |(a : ℝ) - b|

omit [Fintype Z] [Nonempty Z] [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z] in
/-- **Dominance up to a shift**: `∫ h dμ ≤ ∫ h dν + δ L` for every monotone `L`-Lipschitz `h`. -/
def DominatesShift (δ : ℝ) (μ ν : ProbabilityMeasure (↥(Icc assetFloor assetCap) × Z)) : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∀ h : (↥(Icc assetFloor assetCap) × Z) →ᵇ ℝ, MonoAsset h → LipAsset L h →
    ∫ s, h s ∂(μ : Measure _) ≤ ∫ s, h s ∂(ν : Measure _) + δ * L

omit [Fintype Z] [Nonempty Z] [DiscreteTopology Z] [BorelSpace Z] in
theorem DominatesShift.refl (μ : ProbabilityMeasure (↥(Icc assetFloor assetCap) × Z)) :
    DominatesShift 0 μ μ := fun L _ _ _ _ => by simp

omit [Fintype Z] [Nonempty Z] [DiscreteTopology Z] [BorelSpace Z] in
theorem DominatesShift.mono {δ δ' : ℝ} (hδ : δ ≤ δ')
    {μ ν : ProbabilityMeasure (↥(Icc assetFloor assetCap) × Z)} (h : DominatesShift δ μ ν) :
    DominatesShift δ' μ ν := fun L hL g hg hLg => by
  have := h L hL g hg hLg
  nlinarith [mul_le_mul_of_nonneg_right hδ hL]

set_option linter.unusedFintypeInType false in
omit [Nonempty Z] in
/-- **Shifted dominance survives weak limits.** -/
theorem DominatesShift.of_tendsto {δ : ℝ}
    {μs νs : ℕ → ProbabilityMeasure (↥(Icc assetFloor assetCap) × Z)}
    {μ ν : ProbabilityMeasure (↥(Icc assetFloor assetCap) × Z)}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hd : ∀ n, DominatesShift δ (μs n) (νs n)) : DominatesShift δ μ ν := fun L hL h hh hLh =>
  le_of_tendsto_of_tendsto
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ h)
    ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν h).add tendsto_const_nhds)
    (Eventually.of_forall fun n => hd n L hL h hh hLh)

/-! ### One period -/

variable (P Q : IncomeFluctuation Z assetFloor assetCap)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The operator respects a policy gap**, on monotone Lipschitz test functions. -/
theorem markovOp_le_add_of_policy_le_add {γ : ℝ} (hγ : 0 ≤ γ)
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s ≤ Q.policy s + γ)
    {L : ℝ} (hL : 0 ≤ L) {h : P.State →ᵇ ℝ} (hh : MonoAsset h) (hLh : LipAsset L h)
    (s : P.State) : P.markovOp h s ≤ Q.markovOp h s + L * γ := by
  simp only [markovOp_apply]
  have hterm : ∀ z' : Z, h (P.nextState s z') - h (Q.nextState s z') ≤ L * γ := by
    intro z'
    have hgap : P.policy (P.incl s) ≤ Q.policy (Q.incl s) + γ := hpol (P.incl s) (P.incl_mem s)
    by_cases hle : P.policy (P.incl s) ≤ Q.policy (Q.incl s)
    · have := hh z' (P.nextAssets s) (Q.nextAssets s) hle
      have : h (P.nextState s z') ≤ h (Q.nextState s z') := this
      nlinarith [mul_nonneg hL hγ]
    · push Not at hle
      have h1 := hLh z' (P.nextAssets s) (Q.nextAssets s)
      have habs : |(P.nextAssets s : ℝ) - Q.nextAssets s|
          = P.policy (P.incl s) - Q.policy (Q.incl s) := by
        rw [abs_of_pos (by change (0 : ℝ) < P.policy (P.incl s) - Q.policy (Q.incl s); linarith)]
        rfl
      rw [habs] at h1
      calc h (P.nextState s z') - h (Q.nextState s z')
          ≤ L * (P.policy (P.incl s) - Q.policy (Q.incl s)) := h1
        _ ≤ L * γ := mul_le_mul_of_nonneg_left (by linarith) hL
  calc ∑ z', P.prob s z' * h (P.nextState s z')
      = ∑ z', Q.prob s z' * h (P.nextState s z') := by
        refine Finset.sum_congr rfl fun z' _ => ?_
        rw [show P.prob s z' = Q.prob s z' from hprob _ _]
    _ ≤ ∑ z', Q.prob s z' * (h (Q.nextState s z') + L * γ) :=
        Finset.sum_le_sum fun z' _ =>
          mul_le_mul_of_nonneg_left (by linarith [hterm z']) (Q.prob_nonneg _ _)
    _ = ∑ z', Q.prob s z' * h (Q.nextState s z') + L * γ := by
        rw [Finset.sum_congr rfl fun z' _ => mul_add (Q.prob s z') _ _, Finset.sum_add_distrib,
          ← Finset.sum_mul, Q.prob_sum, one_mul]

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The operator scales the Lipschitz constant by that of the policy.** -/
theorem lipAsset_markovOp {K : ℝ}
    (hpolK : ∀ (z : Z) (a b : ℝ), a ∈ Icc assetFloor assetCap → b ∈ Icc assetFloor assetCap →
      |Q.policy (a, z) - Q.policy (b, z)| ≤ K * |a - b|)
    {L : ℝ} (hL : 0 ≤ L) {h : Q.State →ᵇ ℝ} (hLh : LipAsset L h) :
    LipAsset (K * L) (Q.markovOp h) := by
  intro z a b
  simp only [markovOp_apply]
  have hterm : ∀ z' : Z, h (Q.nextState (a, z) z') - h (Q.nextState (b, z) z')
      ≤ K * L * |(a : ℝ) - b| := by
    intro z'
    have h1 := hLh z' (Q.nextAssets (a, z)) (Q.nextAssets (b, z))
    have h2 : |(Q.nextAssets (a, z) : ℝ) - Q.nextAssets (b, z)| ≤ K * |(a : ℝ) - b| :=
      hpolK z a b a.2 b.2
    calc h (Q.nextState (a, z) z') - h (Q.nextState (b, z) z')
        ≤ L * |(Q.nextAssets (a, z) : ℝ) - Q.nextAssets (b, z)| := h1
      _ ≤ L * (K * |(a : ℝ) - b|) := mul_le_mul_of_nonneg_left h2 hL
      _ = K * L * |(a : ℝ) - b| := by ring
  have hp : ∀ z', Q.prob (a, z) z' = Q.prob (b, z) z' := fun _ => rfl
  calc ∑ z', Q.prob (a, z) z' * h (Q.nextState (a, z) z')
        - ∑ z', Q.prob (b, z) z' * h (Q.nextState (b, z) z')
      = ∑ z', Q.prob (a, z) z' * (h (Q.nextState (a, z) z') - h (Q.nextState (b, z) z')) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun z' _ => ?_
        rw [hp z']; ring
    _ ≤ ∑ z', Q.prob (a, z) z' * (K * L * |(a : ℝ) - b|) :=
        Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left (hterm z') (Q.prob_nonneg _ _)
    _ = K * L * |(a : ℝ) - b| := by rw [← Finset.sum_mul, Q.prob_sum, one_mul]

/-- **One period of shifted dominance.** A policy gap `γ` and an asset-Lipschitz constant `K`
for the dominating policy turn a shift `δ` into `δ K + γ`. -/
theorem DominatesShift.pushProb {γ K : ℝ} (hγ : 0 ≤ γ) (hK : 0 ≤ K)
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s ≤ Q.policy s + γ)
    (hpolK : ∀ (z : Z) (a b : ℝ), a ∈ Icc assetFloor assetCap → b ∈ Icc assetFloor assetCap →
      |Q.policy (a, z) - Q.policy (b, z)| ≤ K * |a - b|)
    {δ : ℝ} {μ ν : ProbabilityMeasure P.State} (hd : DominatesShift δ μ ν) :
    DominatesShift (δ * K + γ) (P.pushProb μ) (Q.pushProb ν) := by
  intro L hL h hh hLh
  rw [coe_pushProb, coe_pushProb, P.integral_push _ h, Q.integral_push _ h]
  have h1 : ∫ s, P.markovOp h s ∂(μ : Measure P.State)
      ≤ ∫ s, (Q.markovOp h s + L * γ) ∂(μ : Measure P.State) :=
    integral_mono ((P.markovOp h).integrable _) (((Q.markovOp h).integrable _).add
      (integrable_const _))
      (fun s => markovOp_le_add_of_policy_le_add P Q hγ hprob hpol hL hh hLh s)
  have h2 : ∫ s, (Q.markovOp h s + L * γ) ∂(μ : Measure P.State)
      = ∫ s, Q.markovOp h s ∂(μ : Measure P.State) + L * γ := by
    rw [integral_add ((Q.markovOp h).integrable _) (integrable_const _)]
    simp
  have h3 := hd (K * L) (mul_nonneg hK hL) (Q.markovOp h) (Q.monoAsset_markovOp hh)
    (lipAsset_markovOp Q hpolK hL hLh)
  rw [h2] at h1
  nlinarith

/-! ### Iteration, the limit, and capital -/

/-- **Shifted dominance along the coupled paths**: after `n` periods the shift is
`γ (1 + K + ⋯ + K^{n-1})`. -/
theorem dominatesShift_iterate {γ K : ℝ} (hγ : 0 ≤ γ) (hK : 0 ≤ K)
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s ≤ Q.policy s + γ)
    (hpolK : ∀ (z : Z) (a b : ℝ), a ∈ Icc assetFloor assetCap → b ∈ Icc assetFloor assetCap →
      |Q.policy (a, z) - Q.policy (b, z)| ≤ K * |a - b|)
    (μ₀ : ProbabilityMeasure P.State) (n : ℕ) :
    DominatesShift (γ * ∑ i ∈ Finset.range n, K ^ i) (P.pushProb^[n] μ₀) (Q.pushProb^[n] μ₀) := by
  induction n with
  | zero => simpa using DominatesShift.refl μ₀
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have := ih.pushProb P Q hγ hK hprob hpol hpolK
    have hsum : (γ * ∑ i ∈ Finset.range k, K ^ i) * K + γ
        = γ * ∑ i ∈ Finset.range (k + 1), K ^ i := by
      have hshift : ∑ i ∈ Finset.range k, K ^ i * K = ∑ i ∈ Finset.range k, K ^ (i + 1) :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_range_succ', pow_zero, mul_add, mul_one, mul_assoc, Finset.sum_mul, hshift]
    rw [← hsum]
    exact this

/-- **The shift stays bounded when the policy contracts in assets** (`K < 1`): dominance up to
`γ/(1 - K)` at every date, hence at the stationary distributions. -/
theorem dominatesShift_of_policy_le_add {γ K : ℝ} (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hK1 : K < 1)
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s ≤ Q.policy s + γ)
    (hpolK : ∀ (z : Z) (a b : ℝ), a ∈ Icc assetFloor assetCap → b ∈ Icc assetFloor assetCap →
      |Q.policy (a, z) - Q.policy (b, z)| ≤ K * |a - b|)
    {μ₀ μ ν : ProbabilityMeasure P.State}
    (hP : Tendsto (fun m => P.pushProb^[m] μ₀) atTop (𝓝 μ))
    (hQ : Tendsto (fun m => Q.pushProb^[m] μ₀) atTop (𝓝 ν)) :
    DominatesShift (γ / (1 - K)) μ ν := by
  refine DominatesShift.of_tendsto hP hQ fun n => ?_
  refine (dominatesShift_iterate P Q hγ hK hprob hpol hpolK μ₀ n).mono ?_
  have hroom : 0 < 1 - K := by linarith
  have hgeom : ∑ i ∈ Finset.range n, K ^ i ≤ 1 / (1 - K) := by
    rw [le_div_iff₀ hroom, mul_comm, mul_neg_geom_sum]
    linarith [pow_nonneg hK n]
  calc γ * ∑ i ∈ Finset.range n, K ^ i ≤ γ * (1 / (1 - K)) :=
        mul_le_mul_of_nonneg_left hgeom hγ
    _ = γ / (1 - K) := by ring

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem lipAsset_assetCoord : LipAsset 1 P.assetCoord := fun _ a b => by
  simp only [assetCoord_apply, one_mul]
  exact le_abs_self _

omit [BorelSpace Z] in
/-- **Aggregate capital under shifted dominance.** -/
theorem aggregateCapital_le_add_of_dominatesShift {δ : ℝ} {μ ν : ProbabilityMeasure P.State}
    (hd : DominatesShift δ μ ν) : P.aggregateCapital μ ≤ P.aggregateCapital ν + δ := by
  have := hd 1 zero_le_one P.assetCoord (monoAsset_assetCoord P) (lipAsset_assetCoord P)
  simpa [aggregateCapital] using this

/-- **Aggregate capital is at most `γ/(1-K)` below the dominating economy's.** -/
theorem aggregateCapital_le_add_of_policy_le_add {γ K : ℝ} (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hK1 : K < 1)
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s ≤ Q.policy s + γ)
    (hpolK : ∀ (z : Z) (a b : ℝ), a ∈ Icc assetFloor assetCap → b ∈ Icc assetFloor assetCap →
      |Q.policy (a, z) - Q.policy (b, z)| ≤ K * |a - b|)
    {μ₀ μ ν : ProbabilityMeasure P.State}
    (hP : Tendsto (fun m => P.pushProb^[m] μ₀) atTop (𝓝 μ))
    (hQ : Tendsto (fun m => Q.pushProb^[m] μ₀) atTop (𝓝 ν)) :
    P.aggregateCapital μ ≤ P.aggregateCapital ν + γ / (1 - K) :=
  P.aggregateCapital_le_add_of_dominatesShift
    (dominatesShift_of_policy_le_add P Q hγ hK hK1 hprob hpol hpolK hP hQ)

/-! ### Huggett -/

/-- **Huggett: capital supply at a higher rate is at most `(r₂ - r₁)·|floor|/(1 - K)` below
capital supply at the lower rate**, given the elasticity condition at every state, cap slack,
and an asset-Lipschitz constant `K < 1` for the higher-rate policy. The loss term is the
debtor's extra interest bill, from `policy_le_policy_add_withRate_of_marginal_at`. -/
theorem huggett_aggregateCapital_le_add (P : IncomeFluctuation Z assetFloor assetCap)
    {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂) (hfl : assetFloor ≤ 0)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₂ h₂).policy s < assetCap)
    (helas : ∀ b ∈ Icc assetFloor assetCap, ∀ z : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z b)
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z b))
    {K : ℝ} (hK : 0 ≤ K) (hK1 : K < 1)
    (hpolK : ∀ (z : Z) (a b : ℝ), a ∈ Icc assetFloor assetCap → b ∈ Icc assetFloor assetCap →
      |(P.withRate r₂ h₂).policy (a, z) - (P.withRate r₂ h₂).policy (b, z)| ≤ K * |a - b|)
    {μ₀ μ₁ μ₂ : ProbabilityMeasure P.State}
    (hP : Tendsto (fun m => (P.withRate r₁ h₁).pushProb^[m] μ₀) atTop (𝓝 μ₁))
    (hQ : Tendsto (fun m => (P.withRate r₂ h₂).pushProb^[m] μ₀) atTop (𝓝 μ₂)) :
    P.aggregateCapital μ₁ ≤ P.aggregateCapital μ₂ + (r₂ - r₁) * (-assetFloor) / (1 - K) := by
  have hγ : 0 ≤ (r₂ - r₁) * (-assetFloor) := mul_nonneg (by linarith) (by linarith)
  have hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s ≤ (P.withRate r₂ h₂).policy s + (r₂ - r₁) * (-assetFloor) := by
    intro s hs
    obtain ⟨a, z⟩ := s
    have h := P.policy_le_policy_add_withRate_of_marginal_at h₁ h₂ hr hderiv hanti hpc₁ hpc₂
      hslack₁ hslack₂ hs z
      (fun z' => helas _ ((P.withRate r₁ h₁).policy_mem_region _) z')
    have hmax : max 0 (-a) ≤ -assetFloor := by
      rcases le_total 0 a with h0 | h0
      · rw [max_eq_left (by linarith)]; linarith
      · rw [max_eq_right (by linarith)]; linarith [hs.1]
    have := mul_le_mul_of_nonneg_left hmax (by linarith : (0 : ℝ) ≤ r₂ - r₁)
    linarith
  exact aggregateCapital_le_add_of_policy_le_add (P.withRate r₁ h₁) (P.withRate r₂ h₂) hγ hK hK1
    (fun _ _ => rfl) hpol hpolK hP hQ

end IncomeFluctuation

end LeanEconomics
