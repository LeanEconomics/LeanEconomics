/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Euler
import LeanEconomics.KrusellSmith.Labour

/-!
# Aggregate cash, saving and consumption at a node

Milestone C1 of `CLAMP_PLAN.md`. Cash on hand, saving and consumption of a household at node `h`,
as bounded continuous functions of its assets and idiosyncratic state (`cashAt`, `savingAt`,
`consumptionAt`), and the identities that link their integrals over the distribution of
households:

* `meanCapital_cons`: capital at every child `z' :: h` is mean saving at `h`, the same for every
  `z'`;
* `integral_cashAt`: aggregate cash on hand is `R_h K_h + w_h L_h`, with `K_h` mean assets and
  `L_h` aggregate labour;
* `integral_consumptionAt_eq`: along a sequential equilibrium, aggregate consumption at `h` is
  `R_h K_h + w_h L_h − K_{z' :: h}`;
* `integral_consumptionAt_cons`: aggregate consumption at a child is the parent's expectation of
  its households' consumption there, at the saving they chose.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z) (K : List Z → ℝ × ℝ)

theorem continuous_toNode (h : List Z) :
    Continuous fun x : M.AState => ((x.1, ⟨x.2.idio, h⟩) : M.State) :=
  continuous_fst.prodMk ((continuous_of_discreteTopology
    (f := fun i : Idio E => (⟨i.idio, h⟩ : Label Z E))).comp continuous_snd)

theorem continuous_policy_node (h : List Z) :
    Continuous fun x : M.AState => M.policy z₀ K (x.1, ⟨x.2.idio, h⟩) :=
  Continuous.comp (g := fun p : (List Z → ℝ × ℝ) × M.State => M.policy z₀ p.1 p.2)
    (f := fun x : M.AState => (K, ((x.1, ⟨x.2.idio, h⟩) : M.State)))
    (M.continuous_policy z₀) (continuous_const.prodMk (M.continuous_toNode h))

theorem consumption_mem (s : M.State) : M.consumption z₀ K s ∈ Icc M.consFloor M.maxCash := by
  have hp := M.policy_mem z₀ K s
  have hc := M.cash_le_maxCash z₀ K s
  have h1 : M.policy z₀ K s ≤ M.cash z₀ K s - M.consFloor := hp.2.trans (min_le_right _ _)
  simp only [consumption]
  constructor <;> linarith [hp.1]

/-- **Saving at node `h`**, as a bounded continuous function of assets and idiosyncratic
state. -/
noncomputable def savingAt (h : List Z) : M.AState →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => M.policy z₀ K (x.1, ⟨x.2.idio, h⟩)) (M.continuous_policy_node z₀ K h) M.assetCap
    fun x => by
      have hp := M.policy_mem_Icc z₀ K (x.1, ⟨x.2.idio, h⟩)
      rw [Real.norm_of_nonneg hp.1]
      exact hp.2

/-- **Cash on hand at node `h`.** -/
noncomputable def cashAt (h : List Z) : M.AState →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => M.cash z₀ K (x.1, ⟨x.2.idio, h⟩))
    ((M.continuous_cash z₀ K).comp (M.continuous_toNode h)) M.maxCash
    fun x => by
      rw [Real.norm_of_nonneg (M.cash_nonneg z₀ K _)]
      exact M.cash_le_maxCash z₀ K _

/-- **Consumption at node `h`.** -/
noncomputable def consumptionAt (h : List Z) : M.AState →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => M.consumption z₀ K (x.1, ⟨x.2.idio, h⟩))
    (((M.continuous_cash z₀ K).comp (M.continuous_toNode h)).sub
      (M.continuous_policy_node z₀ K h)) M.maxCash
    fun x => by
      have hc := M.consumption_mem z₀ K (x.1, ⟨x.2.idio, h⟩)
      rw [Real.norm_of_nonneg (M.consFloor_nonneg.trans hc.1)]
      exact hc.2

theorem savingAt_apply (h : List Z) (x : M.AState) :
    M.savingAt z₀ K h x = M.policy z₀ K (x.1, ⟨x.2.idio, h⟩) := rfl

theorem cashAt_apply (h : List Z) (x : M.AState) :
    M.cashAt z₀ K h x = M.cash z₀ K (x.1, ⟨x.2.idio, h⟩) := rfl

theorem consumptionAt_apply (h : List Z) (x : M.AState) :
    M.consumptionAt z₀ K h x = M.consumption z₀ K (x.1, ⟨x.2.idio, h⟩) := rfl

theorem consumptionAt_eq (h : List Z) (x : M.AState) :
    M.consumptionAt z₀ K h x = M.cashAt z₀ K h x - M.savingAt z₀ K h x := rfl

/-- Efficiency, as a bounded continuous function. -/
noncomputable def effFn : M.AState →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => M.efficiency x.2.idio)
    ((continuous_of_discreteTopology (f := fun i : Idio E => M.efficiency i.idio)).comp
      continuous_snd) (∑ e, M.efficiency e)
    fun x => by
      rw [Real.norm_of_nonneg (M.efficiency_nonneg _)]
      exact Finset.single_le_sum (fun e _ => M.efficiency_nonneg e) (Finset.mem_univ _)

variable (μ₀ : Measure M.AState) [IsProbabilityMeasure μ₀]

/-- **Capital at every child is mean saving at the parent**, whatever the next aggregate
shock. -/
theorem meanCapital_cons (z' : Z) (h : List Z) :
    M.meanCapital z₀ μ₀ K (z' :: h) = ∫ x, M.savingAt z₀ K h x ∂(M.nodeDist z₀ μ₀ K h) := by
  have := M.isProbabilityMeasure_nodeDist z₀ μ₀ K h
  change ∫ x, M.assets x ∂(M.pushNode z₀ K h z' (M.nodeDist z₀ μ₀ K h)) = _
  rw [M.integral_pushNode z₀ K h z' _ M.assets]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hp := M.policy_mem_Icc z₀ K (x.1, ⟨x.2.idio, h⟩)
  have ha : ∀ e', M.assets (M.nextA z₀ K h e' x) = M.savingAt z₀ K h x := by
    intro e'
    change ((M.clampAssets (M.policy z₀ K (x.1, ⟨x.2.idio, h⟩)) : ℝ)) = _
    rw [M.clampAssets_of_mem hp]
    rfl
  change ∑ e', M.nextProb z₀ h z' e' x * M.assets (M.nextA z₀ K h e' x) = _
  rw [Finset.sum_congr rfl fun e' _ => by rw [ha e'], ← Finset.sum_mul, M.sum_nextProb, one_mul]

/-- **Aggregate cash on hand** is the return on mean assets plus the wage on aggregate
labour. -/
theorem integral_cashAt (h : List Z) :
    ∫ x, M.cashAt z₀ K h x ∂(M.nodeDist z₀ μ₀ K h)
      = M.returnAt z₀ K h * ∫ x, M.assets x ∂(M.nodeDist z₀ μ₀ K h)
        + M.wageAt z₀ K h * M.labour z₀ (M.initMass μ₀) h := by
  have := M.isProbabilityMeasure_nodeDist z₀ μ₀ K h
  rw [M.labour_eq_integral z₀ μ₀ K h]
  have e : (fun x => M.cashAt z₀ K h x)
      = fun x => M.returnAt z₀ K h * M.assets x + M.wageAt z₀ K h * M.effFn x := rfl
  rw [e, integral_add ((M.assets.integrable _).const_mul _) ((M.effFn.integrable _).const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

/-- Aggregate consumption is aggregate cash on hand less aggregate saving. -/
theorem integral_consumptionAt (h : List Z) :
    ∫ x, M.consumptionAt z₀ K h x ∂(M.nodeDist z₀ μ₀ K h)
      = ∫ x, M.cashAt z₀ K h x ∂(M.nodeDist z₀ μ₀ K h)
        - ∫ x, M.savingAt z₀ K h x ∂(M.nodeDist z₀ μ₀ K h) := by
  have := M.isProbabilityMeasure_nodeDist z₀ μ₀ K h
  rw [← integral_sub ((M.cashAt z₀ K h).integrable _) ((M.savingAt z₀ K h).integrable _)]
  rfl

/-- **Aggregate consumption along a sequential equilibrium**: `R_h K_h + w_h L_h − K_{z' :: h}`,
for every next aggregate shock `z'`. -/
theorem integral_consumptionAt_eq {Kc : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium z₀ μ₀ Kc) (h : List Z) (z' : Z) :
    ∫ x, M.consumptionAt z₀ (M.pricePath z₀ (M.initMass μ₀) Kc) h x
        ∂(M.nodeDist z₀ μ₀ (M.pricePath z₀ (M.initMass μ₀) Kc) h)
      = M.returnAt z₀ (M.pricePath z₀ (M.initMass μ₀) Kc) h * Kc h
        + M.wageAt z₀ (M.pricePath z₀ (M.initMass μ₀) Kc) h * M.labour z₀ (M.initMass μ₀) h
        - Kc (z' :: h) := by
  rw [integral_consumptionAt, integral_cashAt, ← meanCapital_cons _ _ _ _ z' h]
  have h1 : Kc h = ∫ x, M.assets x ∂(M.nodeDist z₀ μ₀ (M.pricePath z₀ (M.initMass μ₀) Kc) h) :=
    hK h
  rw [← h1, ← hK (z' :: h)]

/-- **Aggregate consumption at a child** is the parent's expectation of its households'
consumption there, at the saving they chose. -/
theorem integral_consumptionAt_cons (z' : Z) (h : List Z) :
    ∫ x, M.consumptionAt z₀ K (z' :: h) x ∂(M.nodeDist z₀ μ₀ K (z' :: h))
      = ∫ x, ∑ e', M.idioProb (shockAt z₀ h) z' x.2.idio e'
          * M.consumption z₀ K (M.stateAt (M.savingAt z₀ K h x) ⟨e', z' :: h⟩)
          ∂(M.nodeDist z₀ μ₀ K h) := by
  have := M.isProbabilityMeasure_nodeDist z₀ μ₀ K h
  exact M.integral_pushNode z₀ K h z' (M.nodeDist z₀ μ₀ K h) (M.consumptionAt z₀ K (z' :: h))

end KSModel

end KrusellSmith

end LeanEconomics
