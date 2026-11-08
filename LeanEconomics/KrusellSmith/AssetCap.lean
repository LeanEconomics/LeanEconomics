/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ApproxAggregation

/-!
# The asset cap does not bind

Every existence result works on a compact asset set `[0, ā]`. Here the cap is shown to be
irrelevant once it is large.

* **`policy_le_of_slope`**: when saving is `θ`-Lipschitz in assets (`SavingSlope θ`, e.g. the
  minimal-MPC slope `θ = R̄ (β R̄)^{1/γ} / R̲`), saving is at most the largest labour income plus
  `θ a`: the poorest household saves at most its income, and saving rises at most at `θ`.
* **`policy_lt_assetCap_of_slope`**: with `θ < 1` and `w̄ e + θ ā < ā` for every `e`, saving is
  strictly below the cap at every state, along every price path. The threshold
  `ā* = w̄ ē / (1 − θ)` does not involve the cap.
* **Cap irrelevance** (`withCap`): the same economy with a smaller cap `ā₀ ≤ ā`. If saving in the
  economy with cap `ā` stays below `ā₀` at every state with assets below `ā₀`, then
  - the value function and policy of the small-cap economy are the restrictions of the large-cap
    ones (`valueFunction_capEmb`, `policy_capEmb`);
  - distributions on `[0, ā₀]` move the same way in both (`nodeDist_capEmb`);
  - and **the sequential equilibria from such distributions are the same**
    (`isSequentialEquilibrium_capEmb_iff`).
* **`minMPC_smallShare_capIrrelevant`**: in the small-share CRRA, Cobb–Douglas economy, the cap is
  slack at every state once it exceeds `ā*`, and shrinking it to any `ā₀ ≥ ā*` changes no
  sequential equilibrium.
-/

open MeasureTheory Set BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

/-! ### The cap is slack -/

/-- **Saving is at most labour income plus `θ` times assets.** -/
theorem policy_le_of_slope {θ : ℝ} (hθ : M.SavingSlope θ) (z₀ : Z) (K : List Z → ℝ × ℝ)
    (s : M.State) :
    M.policy z₀ K s ≤ M.wageBound * M.efficiency s.2.idio + θ * s.1 := by
  obtain ⟨a, l⟩ := s
  have h1 := hθ z₀ K a ⟨0, le_rfl, M.assetCap_pos.le⟩ l
  have h2 : M.policy z₀ K (⟨0, le_rfl, M.assetCap_pos.le⟩, l)
      ≤ M.cash z₀ K (⟨0, le_rfl, M.assetCap_pos.le⟩, l) - M.consFloor :=
    (M.policy_mem z₀ K _).2.trans (min_le_right _ _)
  have h3 : M.cash z₀ K (⟨0, le_rfl, M.assetCap_pos.le⟩, l)
      = M.wageAt z₀ K l.node * M.efficiency l.idio := by
    simp [cash]
  have h4 : M.wageAt z₀ K l.node * M.efficiency l.idio ≤ M.wageBound * M.efficiency l.idio :=
    mul_le_mul_of_nonneg_right (M.wage_le _ _ _) (M.efficiency_nonneg _)
  have ha : (0 : ℝ) ≤ a := a.2.1
  have hc : (((⟨0, le_rfl, M.assetCap_pos.le⟩ : ↥(Icc (0 : ℝ) M.assetCap)) : ℝ)) = 0 := rfl
  rw [hc, sub_zero, abs_of_nonneg ha] at h1
  have h5 := le_abs_self (M.policy z₀ K (a, l) - M.policy z₀ K (⟨0, le_rfl, M.assetCap_pos.le⟩, l))
  have hf := M.consFloor_nonneg
  change M.policy z₀ K (a, l) ≤ M.wageBound * M.efficiency l.idio + θ * a
  linarith

/-- **The cap never binds** when `θ < 1` and the cap exceeds `w̄ e / (1 − θ)`. -/
theorem policy_lt_assetCap_of_slope {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : M.SavingSlope θ)
    (hcap : ∀ e, M.wageBound * M.efficiency e + θ * M.assetCap < M.assetCap) (z₀ : Z)
    (K : List Z → ℝ × ℝ) (s : M.State) : M.policy z₀ K s < M.assetCap := by
  have h1 := policy_le_of_slope hθ z₀ K s
  have h2 := mul_le_mul_of_nonneg_left s.1.2.2 hθ0
  linarith [hcap s.2.idio]

/-! ### Cap irrelevance -/

variable (M) in
/-- **The same economy with another cap.** -/
def withCap (c : ℝ) (hc : 0 < c) : KSModel Z E :=
  { M with assetCap := c, assetCap_pos := hc }

variable (c : ℝ) (hc : 0 < c) (hle : c ≤ M.assetCap)

/-- The embedding of states of the small-cap economy into those of the large-cap one. -/
def capEmb (s : (M.withCap c hc).State) : M.State :=
  (⟨s.1, s.1.2.1, s.1.2.2.trans hle⟩, s.2)

theorem continuous_capEmb : Continuous (capEmb c hc hle (M := M)) :=
  ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd

/-- The embedding, as a continuous map. -/
def capEmbMap : C((M.withCap c hc).State, M.State) := ⟨capEmb c hc hle, continuous_capEmb c hc hle⟩

/-- The embedding of household positions. -/
def capEmbA (x : (M.withCap c hc).AState) : M.AState :=
  (⟨x.1, x.1.2.1, x.1.2.2.trans hle⟩, x.2)

theorem continuous_capEmbA : Continuous (capEmbA c hc hle (M := M)) :=
  ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd

theorem measurable_capEmbA : Measurable (capEmbA c hc hle (M := M)) :=
  (continuous_capEmbA c hc hle).measurable

variable {c hc hle}

theorem mem_feasible_capEmb {z₀ : Z} {K : List Z → ℝ × ℝ} {s : (M.withCap c hc).State} {a : ℝ}
    (ha : a ∈ ((M.withCap c hc).household z₀ K).feasible s) :
    a ∈ (M.household z₀ K).feasible (capEmb c hc hle s) :=
  ⟨ha.1, le_min ((ha.2.trans (min_le_left _ _)).trans hle) (ha.2.trans (min_le_right _ _))⟩

/-- On the small-cap economy's feasible choices, its objective against the restriction of a
function is the large-cap objective. -/
theorem objective_capEmb (z₀ : Z) (K : List Z → ℝ × ℝ) (V : M.State →ᵇ ℝ)
    {s : (M.withCap c hc).State} {a : ℝ}
    (ha : a ∈ ((M.withCap c hc).household z₀ K).feasible s) :
    ((M.withCap c hc).household z₀ K).objective (V.compContinuous (capEmbMap c hc hle)) s a
      = (M.household z₀ K).objective V (capEmb c hc hle s) a := by
  have ha' := mem_feasible_capEmb (hle := hle) ha
  simp only [StochasticDynamicProgram.objective, StochasticDynamicProgram.expectation,
    (M.withCap c hc).reward_eq_of_mem_feasible z₀ K ha, M.reward_eq_of_mem_feasible z₀ K ha',
    (M.withCap c hc).transition_eq_of_mem_feasible z₀ K ha,
    M.transition_eq_of_mem_feasible z₀ K ha', compContinuous_apply]
  rfl

section

variable (z₀ : Z) (K : List Z → ℝ × ℝ)
  (hslack : ∀ s : (M.withCap c hc).State, M.policy z₀ K (capEmb c hc hle s) ≤ c)
include hslack

/-- **The small-cap value function is the restriction of the large-cap one**, when large-cap
saving from below `ā₀` stays below `ā₀`. -/
theorem valueFunction_capEmb :
    ((M.withCap c hc).household z₀ K).valueFunction
      = (M.household z₀ K).valueFunction.compContinuous (capEmbMap c hc hle) := by
  set V := (M.household z₀ K).valueFunction
  symm
  refine ((M.withCap c hc).household z₀ K).eq_valueFunction ?_
  ext s
  rw [StochasticDynamicProgram.bellman_apply, compContinuous_apply]
  change ((M.withCap c hc).household z₀ K).bellmanFn _ s = V (capEmb c hc hle s)
  have hp := M.policy_mem z₀ K (capEmb c hc hle s)
  have hpf : M.policy z₀ K (capEmb c hc hle s) ∈ ((M.withCap c hc).household z₀ K).feasible s :=
    ⟨hp.1, le_min (hslack s) (hp.2.trans (min_le_right _ _))⟩
  have hV : V (capEmb c hc hle s)
      = (M.household z₀ K).objective V (capEmb c hc hle s) (M.policy z₀ K (capEmb c hc hle s)) := by
    rw [← M.policy_optimal z₀ K, (M.household z₀ K).bellman_valueFunction]
  refine le_antisymm (((M.withCap c hc).household z₀ K).bellmanFn_le _ fun a ha => ?_) ?_
  · rw [objective_capEmb z₀ K V ha]
    calc _ ≤ (M.household z₀ K).bellmanFn V (capEmb c hc hle s) :=
          (M.household z₀ K).le_bellmanFn V (mem_feasible_capEmb ha)
      _ = V (capEmb c hc hle s) := by
          change (M.household z₀ K).bellman V _ = _
          rw [(M.household z₀ K).bellman_valueFunction]
  · rw [hV, ← objective_capEmb z₀ K V hpf]
    exact ((M.withCap c hc).household z₀ K).le_bellmanFn _ hpf

/-- **The small-cap policy is the restriction of the large-cap one.** -/
theorem policy_capEmb (s : (M.withCap c hc).State) :
    (M.withCap c hc).policy z₀ K s = M.policy z₀ K (capEmb c hc hle s) := by
  set V := (M.household z₀ K).valueFunction
  have hp := M.policy_mem z₀ K (capEmb c hc hle s)
  have hpf : M.policy z₀ K (capEmb c hc hle s) ∈ ((M.withCap c hc).household z₀ K).feasible s :=
    ⟨hp.1, le_min (hslack s) (hp.2.trans (min_le_right _ _))⟩
  have hW := valueFunction_capEmb z₀ K hslack
  refine (M.withCap c hc).optimal_saving_unique z₀ K ((M.withCap c hc).policy_mem z₀ K s) hpf
    ((M.withCap c hc).policy_optimal z₀ K s).symm ?_
  have h1 : ((M.withCap c hc).household z₀ K).bellmanFn
      ((M.withCap c hc).household z₀ K).valueFunction s = V (capEmb c hc hle s) := by
    change ((M.withCap c hc).household z₀ K).bellman _ s = _
    rw [((M.withCap c hc).household z₀ K).bellman_valueFunction, hW, compContinuous_apply]
    rfl
  rw [h1, hW, objective_capEmb z₀ K V hpf, ← M.policy_optimal z₀ K,
    (M.household z₀ K).bellman_valueFunction]

omit hslack in
theorem nextA_capEmb (hslack : ∀ s : (M.withCap c hc).State,
      M.policy z₀ K (capEmb c hc hle s) ≤ c) (h : List Z) (e' : E)
    (x : (M.withCap c hc).AState) :
    capEmbA c hc hle ((M.withCap c hc).nextA z₀ K h e' x) = M.nextA z₀ K h e' (capEmbA c hc hle x) := by
  have hp := policy_capEmb z₀ K hslack (x.1, ⟨x.2.idio, h⟩)
  have hm := M.policy_mem_Icc z₀ K (capEmb c hc hle (x.1, ⟨x.2.idio, h⟩))
  have hm' := (M.withCap c hc).policy_mem_Icc z₀ K (x.1, ⟨x.2.idio, h⟩)
  refine Prod.ext (Subtype.ext ?_) rfl
  change ((M.withCap c hc).clampAssets ((M.withCap c hc).policy z₀ K (x.1, ⟨x.2.idio, h⟩)) : ℝ)
    = (M.clampAssets (M.policy z₀ K (capEmb c hc hle (x.1, ⟨x.2.idio, h⟩))) : ℝ)
  rw [(M.withCap c hc).clampAssets_of_mem hm', M.clampAssets_of_mem hm]
  exact hp

/-! ### Distributions and sequential equilibria -/

/-- **Distributions below the small cap move the same way in both economies.** -/
theorem nodeDist_capEmb (ν : Measure (M.withCap c hc).AState) [IsProbabilityMeasure ν] :
    ∀ h, M.nodeDist z₀ (ν.map (capEmbA c hc hle)) K h
      = ((M.withCap c hc).nodeDist z₀ ν K h).map (capEmbA c hc hle)
  | [] => rfl
  | z' :: h => by
    have ih := nodeDist_capEmb ν h
    have := (M.withCap c hc).isProbabilityMeasure_nodeDist z₀ ν K h
    change M.pushNode z₀ K h z' (M.nodeDist z₀ (ν.map (capEmbA c hc hle)) K h)
      = ((M.withCap c hc).pushNode z₀ K h z' ((M.withCap c hc).nodeDist z₀ ν K h)).map
        (capEmbA c hc hle)
    rw [ih]
    set ν₁ := (M.withCap c hc).nodeDist z₀ ν K h
    have hφ := (measurable_capEmbA c hc hle (M := M)).aemeasurable (μ := ν₁)
    have : IsProbabilityMeasure (ν₁.map (capEmbA c hc hle)) := (Measure.isProbabilityMeasure_map_iff hφ).2 inferInstance
    have : IsProbabilityMeasure ((M.withCap c hc).pushNode z₀ K h z' ν₁) :=
      (M.withCap c hc).isProbabilityMeasure_pushNode _ _ _ _ _
    have : IsProbabilityMeasure (M.pushNode z₀ K h z' (ν₁.map (capEmbA c hc hle))) :=
      M.isProbabilityMeasure_pushNode _ _ _ _ _
    have : IsProbabilityMeasure
        (((M.withCap c hc).pushNode z₀ K h z' ν₁).map (capEmbA c hc hle)) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_capEmbA c hc hle).aemeasurable).2 inferInstance
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    calc ∫ x, f x ∂(M.pushNode z₀ K h z' (ν₁.map (capEmbA c hc hle)))
        = ∫ x, M.expectedNext z₀ K h z' f x ∂(ν₁.map (capEmbA c hc hle)) :=
          M.integral_pushNode z₀ K h z' _ f
      _ = ∫ x, M.expectedNext z₀ K h z' f (capEmbA c hc hle x) ∂ν₁ :=
          integral_map hφ (M.expectedNext z₀ K h z' f).continuous.aestronglyMeasurable
      _ = ∫ x, (M.withCap c hc).expectedNext z₀ K h z'
            (f.compContinuous ⟨capEmbA c hc hle, continuous_capEmbA c hc hle⟩) x ∂ν₁ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          change ∑ e', M.nextProb z₀ h z' e' (capEmbA c hc hle x)
              * f (M.nextA z₀ K h e' (capEmbA c hc hle x))
            = ∑ e', (M.withCap c hc).nextProb z₀ h z' e' x
              * f (capEmbA c hc hle ((M.withCap c hc).nextA z₀ K h e' x))
          refine Finset.sum_congr rfl fun e' _ => ?_
          rw [nextA_capEmb z₀ K hslack h e' x]
          rfl
      _ = ∫ x, f (capEmbA c hc hle x) ∂((M.withCap c hc).pushNode z₀ K h z' ν₁) :=
          ((M.withCap c hc).integral_pushNode z₀ K h z' _ _).symm
      _ = ∫ x, f x ∂(((M.withCap c hc).pushNode z₀ K h z' ν₁).map (capEmbA c hc hle)) :=
          (integral_map (measurable_capEmbA c hc hle).aemeasurable
            f.continuous.aestronglyMeasurable).symm

omit hslack in
theorem stateMass_withCap (z₀ : Z) (m₀ : E → ℝ) :
    ∀ h, (M.withCap c hc).stateMass z₀ m₀ h = M.stateMass z₀ m₀ h
  | [] => rfl
  | z' :: h => by
    funext e'
    simp only [stateMass, stateMass_withCap z₀ m₀ h]
    rfl

omit hslack in
theorem pricePath_withCap (z₀ : Z) (m₀ : E → ℝ) (K : List Z → ℝ) :
    (M.withCap c hc).pricePath z₀ m₀ K = M.pricePath z₀ m₀ K := by
  funext h
  simp only [pricePath, labour, stateMass_withCap]
  rfl

omit hslack in
theorem initMass_capEmb (ν : Measure (M.withCap c hc).AState) :
    M.initMass (ν.map (capEmbA c hc hle)) = (M.withCap c hc).initMass ν := by
  funext e
  simp only [initMass, measureReal_def]
  change ((ν.map (capEmbA c hc hle)) (M.idioSet e)).toReal = (ν ((M.withCap c hc).idioSet e)).toReal
  rw [Measure.map_apply (measurable_capEmbA c hc hle) (M.measurableSet_idioSet e)]
  rfl

theorem meanCapital_capEmb (ν : Measure (M.withCap c hc).AState) [IsProbabilityMeasure ν]
    (h : List Z) :
    M.meanCapital z₀ (ν.map (capEmbA c hc hle)) K h = (M.withCap c hc).meanCapital z₀ ν K h := by
  unfold meanCapital
  rw [nodeDist_capEmb z₀ K hslack ν h, integral_map (measurable_capEmbA c hc hle).aemeasurable
    M.assets.continuous.aestronglyMeasurable]
  rfl

end

/-- **The sequential equilibria from distributions below the small cap are the same in both
economies**, when large-cap saving from below `ā₀` stays below `ā₀` along every price path. -/
theorem isSequentialEquilibrium_capEmb_iff
    (hslack : ∀ (z₀ : Z) (K : List Z → ℝ × ℝ) (s : (M.withCap c hc).State),
      M.policy z₀ K (capEmb c hc hle s) ≤ c)
    (z₀ : Z) (ν : Measure (M.withCap c hc).AState) [IsProbabilityMeasure ν] (K : List Z → ℝ) :
    M.IsSequentialEquilibrium z₀ (ν.map (capEmbA c hc hle)) K
      ↔ (M.withCap c hc).IsSequentialEquilibrium z₀ ν K := by
  unfold IsSequentialEquilibrium
  rw [initMass_capEmb]
  refine forall_congr' fun h => ?_
  rw [meanCapital_capEmb z₀ _ (hslack z₀ _) ν h, pricePath_withCap]

/-- **Slack from the saving slope**: if `w̄ e + θ ā₀ ≤ ā₀`, large-cap saving from below `ā₀` stays
below `ā₀`. -/
theorem capSlack_of_slope {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : M.SavingSlope θ)
    (hcap : ∀ e, M.wageBound * M.efficiency e + θ * c ≤ c) (z₀ : Z) (K : List Z → ℝ × ℝ)
    (s : (M.withCap c hc).State) : M.policy z₀ K (capEmb c hc hle s) ≤ c := by
  have h1 := policy_le_of_slope hθ z₀ K (capEmb c hc hle s)
  have h2 : θ * ((capEmb c hc hle s).1 : ℝ) ≤ θ * c := mul_le_mul_of_nonneg_left s.1.2.2 hθ0
  linarith [hcap (capEmb c hc hle s).2.idio]

end KSModel

section SmallShare

variable [Nonempty Z] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)

/-- **The asset cap is irrelevant for small capital shares**: in the CRRA, clamped Cobb–Douglas
economy with `0 ≤ δ < 1` and `(β (1 − δ))^{1/γ} < 1 − δ`, below some capital share the
minimal-MPC saving slope `θ` is below one; then saving never reaches a cap above
`w̄ e / (1 − θ)`, and shrinking the cap to any `ā₀` with `w̄ e + θ ā₀ ≤ ā₀` leaves every sequential
equilibrium from distributions on `[0, ā₀]` unchanged. -/
theorem minMPC_smallShare_capIrrelevant (hδ1 : T.depreciation < 1)
    (hgap : (V.discount * (1 - T.depreciation)) ^ (1 / γ) < 1 - T.depreciation) :
    ∃ α₀ > 0, ∀ α (h0 : 0 < α), α < α₀ → ∃ hα : α < 1,
      ∃ S : (crraModel V (T.withShare α h0 hα) hγ).SlopeContraction, S.θ < 1 ∧
        ((∀ e, (crraModel V (T.withShare α h0 hα) hγ).wageBound
            * (crraModel V (T.withShare α h0 hα) hγ).efficiency e
            + S.θ * (crraModel V (T.withShare α h0 hα) hγ).assetCap
            < (crraModel V (T.withShare α h0 hα) hγ).assetCap) →
          ∀ z₀ K s, (crraModel V (T.withShare α h0 hα) hγ).policy z₀ K s
            < (crraModel V (T.withShare α h0 hα) hγ).assetCap) ∧
        ∀ (c : ℝ) (hc : 0 < c) (hle : c ≤ (crraModel V (T.withShare α h0 hα) hγ).assetCap),
          (∀ e, (crraModel V (T.withShare α h0 hα) hγ).wageBound
            * (crraModel V (T.withShare α h0 hα) hγ).efficiency e + S.θ * c ≤ c) →
          ∀ (z₀ : Z) (ν : Measure ((crraModel V (T.withShare α h0 hα) hγ).withCap c hc).AState)
            [IsProbabilityMeasure ν] (K : List Z → ℝ),
            (crraModel V (T.withShare α h0 hα) hγ).IsSequentialEquilibrium z₀
                (ν.map (KSModel.capEmbA c hc hle)) K
              ↔ ((crraModel V (T.withShare α h0 hα) hγ).withCap c hc).IsSequentialEquilibrium z₀ ν
                K := by
  obtain ⟨α₀, hα₀, h⟩ := minMPC_smallShare V T hγ hδ1 hgap
  refine ⟨α₀, hα₀, fun α h0 hα => ?_⟩
  obtain ⟨h1, S, hκ, hr⟩ := h α h0 hα
  have hθ : S.θ < 1 := by
    have := div_nonneg S.gain_nonneg (sub_pos.2 hκ).le
    unfold KSModel.SlopeContraction.rate at hr
    linarith
  refine ⟨h1, S, hθ, fun hcap z₀ K s =>
    KSModel.policy_lt_assetCap_of_slope S.θ_nonneg S.slope hcap z₀ K s,
    fun c hc hle hcap z₀ ν _ K => ?_⟩
  exact KSModel.isSequentialEquilibrium_capEmb_iff
    (KSModel.capSlack_of_slope S.θ_nonneg S.slope hcap) z₀ ν K

end SmallShare

end KrusellSmith

end LeanEconomics
