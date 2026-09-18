/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.ElasticityReduction

/-!
# The elasticity reduction on an invariant region

`ElasticityReduction` asks for `R₁ u'(c₁) ≤ R₂ u'(c₂)` at EVERY asset level. For `γ > 1` that is
false at high wealth: by Ma and Toda (2022, Corollary 2.10) the consumption function is
asymptotically linear with slope the minimal MPC `κ(R) = 1 - (βR)^{1/γ}/R`, which rises with
`R` when `γ > 1`, so `c₂/c₁ → κ₂R₂/(κ₁R₁)` exceeds `(R₂/R₁)^{1/γ}`
(`crra_elasticity_fails_of_asymptotic_mpc`). Saving itself still rises with the rate out there
— `a' ≈ (βR)^{1/γ} · b`, increasing in `R` for every `γ` — but the sufficient condition does not
see it.

What the chain actually needs is the condition on the states the economy VISITS. Theorem 1 uses
the elasticity condition only at tomorrow's assets `policy₁(a, z)`
(`policy_le_policy_withRate_of_marginal_at`); Theorem 2 couples the two economies from a common
start and uses the policy order only along the coupled paths. So if some interval `[floor, ā]`
is invariant under the lower-rate policy, the condition on `[floor, ā]` alone orders the
policies there (`policy_le_policy_withRate_of_marginal_on`), the coupling started inside the
interval never leaves it (`push_aboveSet_eq_zero`), and the stationary distributions are
ordered (`dominates_of_policy_le_on`). Uniqueness of the equilibrium rate follows with the
elasticity condition assumed only on the invariant interval
(`equilibriumRate_unique_of_marginal_on`, `crra_equilibriumRate_unique_of_marginal_on`).

For Aiyagari's `μ = 3, 5` this is the honest form of the reduction: the condition is
plausibly true on the ergodic support and provably false beyond it.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

/-! ### The elasticity condition for CRRA, and its failure at high wealth -/

/-- For CRRA the elasticity condition `R₁ c₁^{-γ} ≤ R₂ c₂^{-γ}` says `(c₂/c₁)^γ ≤ R₂/R₁`. -/
theorem crra_elasticity_iff {γ R₁ R₂ c₁ c₂ : ℝ} (hR₁ : 0 < R₁)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    R₁ * c₁ ^ (-γ) ≤ R₂ * c₂ ^ (-γ) ↔ (c₂ / c₁) ^ γ ≤ R₂ / R₁ := by
  have h1 : 0 < c₁ ^ γ := Real.rpow_pos_of_pos hc₁ _
  have h2 : 0 < c₂ ^ γ := Real.rpow_pos_of_pos hc₂ _
  rw [Real.rpow_neg hc₁.le, Real.rpow_neg hc₂.le, ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_le_div_iff₀ h1 h2, Real.div_rpow hc₂.le hc₁.le, div_le_div_iff₀ h1 hR₁]
  constructor <;> intro h <;> linarith

/-- **The elasticity condition fails at high wealth whenever the asymptotic slopes of the two
consumption functions are too far apart.** With Ma--Toda's slopes `L_i = κ(R_i) R_i` and
`γ > 1`, `(L₂/L₁)^γ = (κ₂/κ₁)^γ (R₂/R₁)^γ > R₂/R₁`, so the hypothesis holds and the condition
fails for all large `b`. -/
theorem crra_elasticity_fails_of_asymptotic_mpc {γ R₁ R₂ L₁ L₂ : ℝ} {c₁ c₂ : ℝ → ℝ}
    (hγ : 0 < γ) (hL₁ : 0 < L₁)
    (h₁ : Tendsto (fun b => c₁ b / b) atTop (𝓝 L₁))
    (h₂ : Tendsto (fun b => c₂ b / b) atTop (𝓝 L₂))
    (hgap : R₂ / R₁ < (L₂ / L₁) ^ γ) :
    ∃ b : ℝ, R₂ / R₁ < (c₂ b / c₁ b) ^ γ := by
  have hratio : Tendsto (fun b => c₂ b / c₁ b) atTop (𝓝 (L₂ / L₁)) := by
    refine (h₂.div h₁ hL₁.ne').congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
    simp only [Pi.div_apply]
    field_simp
  have hpow : Tendsto (fun b => (c₂ b / c₁ b) ^ γ) atTop (𝓝 ((L₂ / L₁) ^ γ)) :=
    hratio.rpow_const (Or.inr hγ.le)
  exact (hpow.eventually (lt_mem_nhds hgap)).exists

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetFloor assetCap : ℝ}

/-! ### The coupling stays in an invariant region -/

/-- The states with assets above `ā`. -/
def AboveSet (ā : ℝ) : Set (↥(Icc assetFloor assetCap) × Z) := {s | ā < (s.1 : ℝ)}

omit [Fintype Z] [Nonempty Z] in
theorem measurableSet_aboveSet (ā : ℝ) :
    MeasurableSet (AboveSet (assetFloor := assetFloor) (assetCap := assetCap) (Z := Z) ā) :=
  measurableSet_lt measurable_const (continuous_subtype_val.comp continuous_fst).measurable

variable (P Q : IncomeFluctuation Z assetFloor assetCap)

/-- **A region closed under the policy is null for the motion if it was null before.** -/
theorem push_aboveSet_eq_zero {ā : ℝ}
    (hinv : ∀ s : P.State, (s.1 : ℝ) ≤ ā → P.policy (P.incl s) ≤ ā)
    (μ : Measure P.State) (hμ : μ (AboveSet ā) = 0) : P.push μ (AboveSet ā) = 0 := by
  have hA := measurableSet_aboveSet (assetFloor := assetFloor) (assetCap := assetCap) (Z := Z) ā
  rw [push, Measure.sum_apply _ hA]
  refine ENNReal.tsum_eq_zero.mpr fun z' => ?_
  rw [Measure.map_apply (P.measurable_nextState z') hA,
    withDensity_apply _ (hA.preimage (P.measurable_nextState z'))]
  refine setLIntegral_measure_zero _ _ (measure_mono_null ?_ hμ)
  intro s hs
  simp only [mem_preimage, AboveSet, mem_ofPred_eq, nextState, nextAssets] at hs ⊢
  by_contra h
  push Not at h
  exact absurd hs (not_lt.mpr (hinv s h))

/-- **One period preserves dominance, with the policy order needed only below `ā`**, provided
the first distribution lives below `ā`. -/
theorem Dominates.pushProb_on {ā : ℝ}
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → s.1 ≤ ā → P.policy s ≤ Q.policy s)
    {μ ν : ProbabilityMeasure P.State} (hμ : (μ : Measure P.State) (AboveSet ā) = 0)
    (hd : Dominates μ ν) : Dominates (P.pushProb μ) (Q.pushProb ν) := by
  intro h hh
  rw [coe_pushProb, coe_pushProb, P.integral_push _ h, Q.integral_push _ h]
  refine le_trans (integral_mono_ae ((P.markovOp h).integrable _)
    ((Q.markovOp h).integrable _) ?_) (hd _ (Q.monoAsset_markovOp hh))
  have hae : ∀ᵐ s ∂(μ : Measure P.State), (s.1 : ℝ) ≤ ā := by
    rw [ae_iff]
    simpa [AboveSet, not_le] using hμ
  filter_upwards [hae] with s hs
  simp only [markovOp_apply]
  refine Finset.sum_le_sum fun z' _ => ?_
  rw [show P.prob s z' = Q.prob s z' from hprob _ _]
  refine mul_le_mul_of_nonneg_left ?_ (Q.prob_nonneg _ _)
  exact hh z' _ _ (hpol (P.incl s) (P.incl_mem s) hs)

/-- **Stationary distributions are ordered when the policies are ordered on an interval the
lower-rate policy leaves invariant**, the coupling started inside it. -/
theorem dominates_of_policy_le_on {ā : ℝ}
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → s.1 ≤ ā → P.policy s ≤ Q.policy s)
    (hinv : ∀ s : P.State, (s.1 : ℝ) ≤ ā → P.policy (P.incl s) ≤ ā)
    {μ₀ μ ν : ProbabilityMeasure P.State} (h₀ : (μ₀ : Measure P.State) (AboveSet ā) = 0)
    (hP : Tendsto (fun m => P.pushProb^[m] μ₀) atTop (𝓝 μ))
    (hQ : Tendsto (fun m => Q.pushProb^[m] μ₀) atTop (𝓝 ν)) :
    Dominates μ ν := by
  refine Dominates.of_tendsto hP hQ fun n => ?_
  have key : ∀ n : ℕ,
      ((P.pushProb^[n] μ₀ : ProbabilityMeasure P.State) : Measure P.State) (AboveSet ā) = 0
        ∧ Dominates (P.pushProb^[n] μ₀) (Q.pushProb^[n] μ₀) := by
    intro n
    induction n with
    | zero => exact ⟨h₀, Dominates.refl μ₀⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine ⟨?_, ih.2.pushProb_on P Q hprob hpol ih.1⟩
      rw [coe_pushProb]
      exact P.push_aboveSet_eq_zero hinv _ ih.1
  exact (key n).2

/-- **Capital supply is monotone in the rate when the policy is, on an invariant interval.** -/
theorem monotoneOn_capitalSupply_of_policy_mono_on {rlo rhi ā : ℝ}
    (Pf : ℝ → IncomeFluctuation Z assetFloor assetCap)
    (hprob : ∀ r r' : ℝ, ∀ z z' : Z,
      (Pf r).transitionMatrix z z' = (Pf r').transitionMatrix z z')
    (hpol : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → s.1 ≤ ā → (Pf r).policy s ≤ (Pf r').policy s)
    (hinv : ∀ r ∈ Icc rlo rhi, ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → s.1 ≤ ā →
      (Pf r).policy s ≤ ā)
    (μ₀ : ProbabilityMeasure P.State) (h₀ : (μ₀ : Measure P.State) (AboveSet ā) = 0)
    (ν : ℝ → ProbabilityMeasure P.State)
    (hconv : ∀ r ∈ Icc rlo rhi, Tendsto (fun m => (Pf r).pushProb^[m] μ₀) atTop (𝓝 (ν r))) :
    MonotoneOn (fun r => P.aggregateCapital (ν r)) (Icc rlo rhi) := fun r hr r' hr' hrr =>
  dominates_of_policy_le_on (Pf r) (Pf r') (hprob r r') (hpol r hr r' hr' hrr)
    (fun s hs => hinv r hr ((Pf r).incl s) ((Pf r).incl_mem s) hs) h₀
    (hconv r hr) (hconv r' hr') P.assetCoord (monoAsset_assetCoord P)

end IncomeFluctuation

/-! ### The reduction on an invariant interval -/

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **Theorem 1 on an invariant interval**: the elasticity condition on `[0, ā]`, and `[0, ā]`
invariant under the lower-rate policy, order the policies on `[0, ā]`. -/
theorem policy_le_policy_withRate_of_marginal_on {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁)
    (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂) {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r₂ h₂).policy s < assetCap)
    {ā : ℝ} (hinv₁ : ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → s.1 ≤ ā →
      (P.withRate r₁ h₁).policy s ≤ ā)
    (helas : ∀ b ∈ Icc (0 : ℝ) assetCap, b ≤ ā → ∀ z : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z b)
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z b))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (haā : a ≤ ā) (z : Z) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy (a, z) :=
  P.policy_le_policy_withRate_of_marginal_at h₁ h₂ hr hderiv hanti hpc₁ hpc₂ hslack₁ hslack₂ ha z
    (fun z' => helas _ ((P.withRate r₁ h₁).policy_mem_region _) (hinv₁ (a, z) ha haā) z')

variable [MeasurableSpace Z] [BorelSpace Z]

/-- **The equilibrium rate is unique on `[rlo, rhi]` under the elasticity condition on an
invariant interval `[0, ā]`**, for any period utility, given the Doeblin data. -/
theorem equilibriumRate_unique_of_marginal_on {rlo rhi ā α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ : 0 < rlo + δ) (hrlo : 0 < 1 + rlo) (hlohi : rlo ≤ rhi) (hā : 0 ≤ ā)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ)))
    (hpc : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).PositiveConsumption)
    (hslack : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ s : ℝ × Z,
      s.1 ∈ Icc (0 : ℝ) assetCap → (P.withRate r hrr).policy s < assetCap)
    (hinv : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ s : ℝ × Z,
      s.1 ∈ Icc (0 : ℝ) assetCap → s.1 ≤ ā → (P.withRate r hrr).policy s ≤ ā)
    (helas : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ hrr : P.RateOK r, ∀ hrr' : P.RateOK r', ∀ b ∈ Icc (0 : ℝ) assetCap, b ≤ ā → ∀ z : Z,
        (1 + r) * du ((P.withRate r hrr).consumptionFn z b)
          ≤ (1 + r') * du ((P.withRate r' hrr').consumptionFn z b))
    (huniq : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      ∃! μ : ProbabilityMeasure P.State, (P.withRate r hrr).IsStationary μ)
    (htend : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ₀ μ : ProbabilityMeasure P.State,
      (P.withRate r hrr).IsStationary μ →
        Tendsto (fun m => (P.withRate r hrr).pushProb^[m] μ₀) atTop (𝓝 μ))
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (hμ₁ : (P.withRate r₁ hrr₁).IsStationary μ₁) (hμ₂ : (P.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : P.aggregateCapital μ₁ = normalisedDemand α δ r₁)
    (he₂ : P.aggregateCapital μ₂ = normalisedDemand α δ r₂) : r₁ = r₂ := by
  classical
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  -- the selection of stationary distributions, through the clamped rate
  have hE : ∀ r : ℝ, ∃! μ : ProbabilityMeasure P.State,
      (P.withRate (clampRate rlo rhi r)
        (rateOK_of_floor_zero (one_add_clampRate_pos hrlo hlohi r))).IsStationary μ :=
    fun r => huniq _ (clampRate_mem hlohi r) _
  set ν : ℝ → ProbabilityMeasure P.State := fun r => (hE r).choose with hνdef
  have hν : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).IsStationary (ν r) := by
    intro r hr hrr
    have hc : clampRate rlo rhi r = r := clampRate_eq hr
    rw [← P.withRate_congr hc _ hrr]
    exact (hE r).choose_spec.1
  have hid : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate r hrr).IsStationary μ → μ = ν r := by
    intro r hr hrr μ hμ
    have hc : clampRate rlo rhi r = r := clampRate_eq hr
    refine (hE r).choose_spec.2 μ ?_
    rw [P.withRate_congr hc _ hrr]
    exact hμ
  -- Theorem 1 on the invariant interval, along the rate family
  have hpol : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → s.1 ≤ ā →
        (P.rateFamily hrlo hlohi r).policy s ≤ (P.rateFamily hrlo hlohi r').policy s := by
    intro r hr r' hr' hle s hs hsā
    have hrok : P.RateOK r := rateOK_of_floor_zero (by linarith [hr.1])
    have hr'ok : P.RateOK r' := rateOK_of_floor_zero (by linarith [hr'.1])
    rw [P.rateFamily_eq _ _ hr hrok, P.rateFamily_eq _ _ hr' hr'ok]
    obtain ⟨a, z⟩ := s
    exact P.policy_le_policy_withRate_of_marginal_on hrok hr'ok hle hderiv hanti (hpc r hr hrok)
      (hpc r' hr' hr'ok) (hslack r hr hrok) (hslack r' hr' hr'ok) (hinv r hr hrok)
      (helas r hr r' hr' hle hrok hr'ok) hs hsā z
  have hinv' : ∀ r ∈ Icc rlo rhi, ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap → s.1 ≤ ā →
      (P.rateFamily hrlo hlohi r).policy s ≤ ā := by
    intro r hr s hs hsā
    have hrok : P.RateOK r := rateOK_of_floor_zero (by linarith [hr.1])
    rw [P.rateFamily_eq _ _ hr hrok]
    exact hinv r hr hrok s hs hsā
  -- the coupling starts at zero assets
  set s₀ : P.State := (⟨0, ⟨le_rfl, hcap0⟩⟩, Classical.ofNonempty) with hs₀
  have h₀ : ((⟨Measure.dirac s₀, inferInstance⟩ : ProbabilityMeasure P.State) : Measure P.State)
      (AboveSet ā) = 0 := by
    have hA := measurableSet_aboveSet (assetFloor := (0 : ℝ)) (assetCap := assetCap) (Z := Z) ā
    change Measure.dirac s₀ (AboveSet ā) = 0
    rw [Measure.dirac_apply' _ hA]
    refine Set.indicator_of_notMem ?_ _
    simp only [AboveSet, mem_ofPred_eq, hs₀, not_lt]
    exact hā
  -- Theorem 2: capital supply is monotone along the selection
  have hmono : MonotoneOn (fun r => P.aggregateCapital (ν r)) (Icc rlo rhi) := by
    refine P.monotoneOn_capitalSupply_of_policy_mono_on (P.rateFamily hrlo hlohi)
      (fun _ _ _ _ => rfl) hpol hinv' ⟨Measure.dirac s₀, inferInstance⟩ h₀ ν ?_
    intro r hr
    have hrr : P.RateOK r := rateOK_of_floor_zero (by linarith [hr.1])
    rw [P.rateFamily_eq _ _ hr hrr]
    exact htend r hr hrr _ _ (hν r hr hrr)
  -- Theorem 3: single crossing
  rw [hid r₁ h₁ hrr₁ μ₁ hμ₁] at he₁
  rw [hid r₂ h₂ hrr₂ μ₂ hμ₂] at he₂
  exact eq_of_monotoneOn_of_strictAntiOn hmono (normalisedDemand_strictAntiOn hα0 hα1 hδ)
    h₁ h₂ he₁ he₂

/-- **CRRA, any `γ > 0`, elasticity condition on an invariant interval.** -/
theorem crra_equilibriumRate_unique_of_marginal_on {γ rlo rhi ā α δ : ℝ} (hγ0 : 0 < γ)
    (hα0 : 0 < α) (hα1 : α < 1) (hδ : 0 < rlo + δ) (hu : P.u = crraUtility γ)
    (hunb : P.Unbounded) (hβ : 0 < (P.discount : ℝ)) (hrlo : 0 < 1 + rlo) (hlohi : rlo ≤ rhi)
    (hā : 0 ≤ ā) (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hκ : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, 0 < (P.withRate r hrr).minMPC γ)
    (hthr : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      (1 - (P.withRate r hrr).minMPC γ) * (P.maxIncome + (1 + r) * assetCap) < assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hreach : ∀ z, 0 < P.transitionMatrix z z₀) {a₀ : ℝ} (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hcorn : ∀ r ∈ Icc rlo rhi, (P.discount : ℝ) * (1 + r) * P.minIncome ^ (-γ)
      < (P.income z₀ + (1 + r) * a₀) ^ (-γ))
    (hinv : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ s : ℝ × Z,
      s.1 ∈ Icc (0 : ℝ) assetCap → s.1 ≤ ā → (P.withRate r hrr).policy s ≤ ā)
    (helas : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ hrr : P.RateOK r, ∀ hrr' : P.RateOK r', ∀ b ∈ Icc (0 : ℝ) assetCap, b ≤ ā → ∀ z : Z,
        (1 + r) * ((P.withRate r hrr).consumptionFn z b) ^ (-γ)
          ≤ (1 + r') * ((P.withRate r' hrr').consumptionFn z b) ^ (-γ))
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (hμ₁ : (P.withRate r₁ hrr₁).IsStationary μ₁) (hμ₂ : (P.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : P.aggregateCapital μ₁ = normalisedDemand α δ r₁)
    (he₂ : P.aggregateCapital μ₂ = normalisedDemand α δ r₂) : r₁ = r₂ := by
  classical
  have hβR' : ∀ r ∈ Icc rlo rhi, (P.discount : ℝ) * (1 + r) < 1 := fun r hr => by
    nlinarith [hr.2, hβ]
  have hpcAll : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      (P.withRate r hrr).PositiveConsumptionAll :=
    fun r _ hrr => (P.withRate r hrr).positiveConsumptionAll_of_unbounded hunb
  have hposIt : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ n : ℕ, ∀ z : Z,
      ∀ a ∈ Icc (0 : ℝ) assetCap, 0 < (P.withRate r hrr).consumptionFnOf
        (((P.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a :=
    fun r hr hrr n z a ha =>
      hpcAll r hr hrr _ ((P.withRate r hrr).concaveSlices_iterate_zero n) z a ha
  have hthr' : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (1 - (P.withRate r hrr).minMPC γ)
      * ((P.withRate r hrr).maxIncome + (1 + (P.withRate r hrr).interest) * assetCap)
      < assetCap := fun r hr hrr => hthr r hr hrr
  have hβRw : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      ((P.withRate r hrr).discount : ℝ) * (1 + (P.withRate r hrr).interest) < 1 :=
    fun r hr _ => hβR' r hr
  refine P.equilibriumRate_unique_of_marginal_on hα0 hα1 hδ hrlo hlohi hā
    (du := fun c => c ^ (-γ)) (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility γ hc)
    (fun x hx y _ hxy => Real.rpow_lt_rpow_of_neg hx hxy (by linarith))
    (fun r _ hrr => (P.withRate r hrr).positiveConsumption_of_unbounded hunb)
    (fun r hr hrr s hs => ?_) hinv helas ?_ ?_ h₁ h₂ hrr₁ hrr₂ hμ₁ hμ₂ he₁ he₂
  · obtain ⟨a, z⟩ := s
    exact (P.withRate r hrr).crra_policy_lt_cap_of_minMPC hγ0 hu rfl (hκ r hr hrr) hβ
      (hβRw r hr hrr) (hposIt r hr hrr) (hthr' r hr hrr) hs z
  · intro r hr hrr
    exact (P.withRate r hrr).crra_existsUnique_isStationary_of_euler_corner_monotone hγ0 hu rfl
      (hκ r hr hrr) hβ (hβRw r hr hrr) (P.monotoneTransitions_withRate hmono hrr)
      (hpcAll r hr hrr) (hthr' r hr hrr) hz₀ hreach ha₀ hle (hcorn r hr)
  · intro r hr hrr μ₀ μ hμ
    exact (P.withRate r hrr).crra_tendsto_pushProb_of_euler_corner_monotone hγ0 hu rfl
      (hκ r hr hrr) hβ (hβRw r hr hrr) (P.monotoneTransitions_withRate hmono hrr)
      (hpcAll r hr hrr) (hthr' r hr hrr) hz₀ hreach ha₀ hle (hcorn r hr) μ₀ hμ

end IncomeFluctuation

end LeanEconomics
