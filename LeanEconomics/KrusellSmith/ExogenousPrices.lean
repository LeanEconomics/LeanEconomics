/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.OrderMonotone
import LeanEconomics.KrusellSmith.SavingMonotoneReduction
import LeanEconomics.KrusellSmith.ValueState

/-!
# Separation from ordered cash on hand

Milestones OI0–OI3 of `ORDER_STRUCTURE_PLAN.md` (OS4(b)).

* **`PricesExogenous`**: the return and the wage depend on the aggregate shock only (a linear
  technology `Y = A(z) K + B(z) L`, whose marginal products are exact). Then the household problem
  does not depend on the path of capital (`policy_congr`), so savings rise (weakly) with capital
  (`savingMonotone_of_exogenous`) and sequential equilibrium is unique
  (`uniqueSequentialEquilibrium_of_exogenous`).
* **`IIDShocks`**: aggregate shocks and employment are drawn independently of today's shock and
  employment. Then the continuation value at the root of the tree is the same function of next
  assets for every root shock, price path and employment state (`cont_root_eq`).
* `policy_le_policy_of_cont` (two-root Topkis): with the same continuation, less cash gives less
  saving.
* **`OrderedCash`**: after a worse shock every household has less cash than every household after a
  better one. With the above, every household saves less after the worse shock, so the next
  cross-sections are ordered whatever the current ones are: **(Sep)**
  (`sepOnHistories_of_orderedCash`). With (Mon) (`monOnHistories_of_savingMonotone`) the chain
  argument gives **`kSufficient_of_orderedCash`**: `(z, K)` is a sufficient state for every
  sequence-state equilibrium.
-/

open MeasureTheory Set BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **Prices depend on the aggregate shock only.** -/
def PricesExogenous : Prop :=
  ∀ (z : Z) (K L K' L' : ℝ), M.grossReturn z K L = M.grossReturn z K' L' ∧
    M.wage z K L = M.wage z K' L'

/-- **Aggregate shocks and employment are drawn independently of today's state.** -/
def IIDShocks : Prop :=
  (∀ z y z' : Z, M.aggProb z z' = M.aggProb y z') ∧
    ∀ (z y z' : Z) (e f e' : E), M.idioProb z z' e e' = M.idioProb y z' f e'

/-- **Ordered cash on hand**: after a worse shock every household has less cash than every
household after a better one. -/
def OrderedCash [LinearOrder Z] : Prop :=
  ∀ y y' : Z, y < y' → ∀ (K L K' L' : ℝ) (a b : ↥(Icc (0 : ℝ) M.assetCap)) (e f : E),
    M.grossReturn y K L * a + M.wage y K L * M.efficiency e
      ≤ M.grossReturn y' K' L' * b + M.wage y' K' L' * M.efficiency f

variable {M}

/-! ### OI0: the household does not depend on the path of capital -/

section Exogenous

variable (hX : M.PricesExogenous)
include hX

theorem cash_congr (z₀ : Z) (K K' : List Z → ℝ × ℝ) (s : M.State) :
    M.cash z₀ K s = M.cash z₀ K' s := by
  have h := hX (shockAt z₀ s.2.node) (K s.2.node).1 (K s.2.node).2 (K' s.2.node).1
    (K' s.2.node).2
  simp only [cash, returnAt, wageAt, h.1, h.2]

theorem feasible_congr (z₀ : Z) (K K' : List Z → ℝ × ℝ) (s : M.State) :
    (M.household z₀ K).feasible s = (M.household z₀ K').feasible s := by
  change Icc 0 (M.maxSaving z₀ K s) = Icc 0 (M.maxSaving z₀ K' s)
  simp only [maxSaving, cash_congr hX z₀ K K' s]

theorem objective_congr (z₀ : Z) (K K' : List Z → ℝ × ℝ) (v : M.State →ᵇ ℝ) (s : M.State)
    (a : ℝ) : (M.household z₀ K).objective v s a = (M.household z₀ K').objective v s a := by
  simp only [StochasticDynamicProgram.objective, StochasticDynamicProgram.expectation]
  congr 1
  change M.utility (M.clampedConsumption z₀ K (s, a))
    = M.utility (M.clampedConsumption z₀ K' (s, a))
  simp only [clampedConsumption, cash_congr hX z₀ K K' s]

theorem bellman_congr (z₀ : Z) (K K' : List Z → ℝ × ℝ) (v : M.State →ᵇ ℝ) :
    (M.household z₀ K).bellman v = (M.household z₀ K').bellman v := by
  ext s
  simp only [StochasticDynamicProgram.bellman_apply, maxValue]
  rw [feasible_congr hX z₀ K K' s]
  congr 1
  exact Set.image_congr fun a _ => objective_congr hX z₀ K K' v s a

theorem valueFunction_congr (z₀ : Z) (K K' : List Z → ℝ × ℝ) :
    (M.household z₀ K).valueFunction = (M.household z₀ K').valueFunction := by
  refine (M.household z₀ K').eq_valueFunction ?_
  rw [← bellman_congr hX z₀ K K', (M.household z₀ K).bellman_valueFunction]

/-- **The policy does not depend on the path of capital.** -/
theorem policy_congr (z₀ : Z) (K K' : List Z → ℝ × ℝ) (s : M.State) :
    M.policy z₀ K s = M.policy z₀ K' s := by
  have hmem := M.policy_mem z₀ K s
  rw [feasible_congr hX z₀ K K' s] at hmem
  refine M.optimal_saving_unique z₀ K' hmem (M.policy_mem z₀ K' s) ?_ ?_
  · rw [← valueFunction_congr hX z₀ K K', ← objective_congr hX z₀ K K']
    change _ = (M.household z₀ K').bellman _ s
    rw [← bellman_congr hX z₀ K K']
    exact (M.policy_optimal z₀ K s).symm
  · exact (M.policy_optimal z₀ K' s).symm

/-- **Savings rise (weakly) with capital**: they do not depend on it. -/
theorem savingMonotone_of_exogenous : M.SavingMonotone :=
  fun z _ _ _ _ s => (policy_congr hX z _ _ s).le

/-- **Sequential equilibrium is unique**: the distribution path does not depend on prices. -/
theorem uniqueSequentialEquilibrium_of_exogenous : M.UniqueSequentialEquilibrium := by
  intro z μ K K' hK hK'
  have hnd : ∀ (P P' : List Z → ℝ × ℝ) (h : List Z),
      M.nodeDist z (μ : Measure M.AState) P h = M.nodeDist z (μ : Measure M.AState) P' h := by
    intro P P' h
    induction h with
    | nil => rfl
    | cons z' h ih =>
      change M.pushNode z P h z' (M.nodeDist z (μ : Measure M.AState) P h)
        = M.pushNode z P' h z' (M.nodeDist z (μ : Measure M.AState) P' h)
      rw [ih]
      exact M.pushNode_congr rfl (fun e' x => by simp only [nextA, policy_congr hX z P P'])
        z' _
  funext h
  rw [hK h, hK' h]
  unfold meanCapital
  rw [hnd _ (M.pricePath z (M.initMass (μ : Measure M.AState)) K') h]

/-! ### OI1: the root continuation with i.i.d. shocks -/

/-- **The continuation at the root** is the same function of next assets for every root shock,
price path and employment state. -/
theorem cont_root_eq (hI : M.IIDShocks) (y y' : Z) (P P' : List Z → ℝ × ℝ) {s s' : M.State}
    (hs : s.2.node = []) (hs' : s'.2.node = []) (a' : ℝ) :
    M.cont y P s a' = M.cont y' P' s' a' := by
  simp only [cont]
  refine Finset.sum_congr rfl fun ze _ => ?_
  congr 1
  · change M.aggProb (shockAt y s.2.node) ze.1
        * M.idioProb (shockAt y s.2.node) ze.1 s.2.idio ze.2
      = M.aggProb (shockAt y' s'.2.node) ze.1
        * M.idioProb (shockAt y' s'.2.node) ze.1 s'.2.idio ze.2
    rw [hI.1 _ (shockAt y' s'.2.node), hI.2 _ (shockAt y' s'.2.node) _ _ s'.2.idio]
  · rw [hs, hs']
    have e1 := DFunLike.congr_fun (M.valueFunction_shift y P [ze.1]) (M.stateAt a' ⟨ze.2, []⟩)
    have e2 := DFunLike.congr_fun (M.valueFunction_shift y' P' [ze.1]) (M.stateAt a' ⟨ze.2, []⟩)
    rw [compContinuous_apply] at e1 e2
    have e3 := DFunLike.congr_fun
      (valueFunction_congr hX ze.1 (shiftPath P [ze.1]) (shiftPath P' [ze.1]))
      (M.stateAt a' ⟨ze.2, []⟩)
    exact e1.symm.trans (e3.trans e2)

end Exogenous

/-! ### OI2: two-root Topkis -/

/-- **Less cash and the same continuation give less saving**, across roots and price paths. -/
theorem policy_le_policy_of_cont {y y' : Z} {P P' : List Z → ℝ × ℝ} {s s' : M.State}
    (hcash : M.cash y P s ≤ M.cash y' P' s') (hcont : ∀ a, M.cont y P s a = M.cont y' P' s' a) :
    M.policy y P s ≤ M.policy y' P' s' := by
  set p := M.policy y P s
  set p' := M.policy y' P' s'
  set x := M.cash y P s
  set x' := M.cash y' P' s'
  by_contra hlt
  rw [not_le] at hlt
  have hp := M.policy_mem y P s
  have hp' := M.policy_mem y' P' s'
  have hpx : p ≤ x - M.consFloor := hp.2.trans (min_le_right _ _)
  -- each could take the other's saving
  have hf' : p' ∈ (M.household y P).feasible s := ⟨hp'.1, hlt.le.trans hp.2⟩
  have hf : p ∈ (M.household y' P').feasible s' :=
    ⟨hp.1, le_min (hp.2.trans (min_le_left _ _)) (by
      change p ≤ x' - M.consFloor
      linarith)⟩
  have h2 := M.le_valueFunction y' P' hf
  have v1 : (M.household y P).valueFunction s = M.utility (x - p) + M.discount * M.cont y P s p :=
    M.valueFunction_eq_cont y P s
  have v2 : (M.household y' P').valueFunction s'
      = M.utility (x' - p') + M.discount * M.cont y' P' s' p' :=
    M.valueFunction_eq_cont y' P' s'
  have hb1 : M.discount * M.cont y P s p = M.discount * M.cont y' P' s' p := by rw [hcont]
  have hb2 : M.discount * M.cont y P s p' = M.discount * M.cont y' P' s' p' := by rw [hcont]
  -- increasing differences of utility, from concavity
  have hcf : M.consFloor ≤ x - p := by linarith
  have hu := concave_increment_le M.strictConcaveOn_utility.concaveOn
    (x := x - p) (y := x' - p) (d := p - p') (by linarith) (by linarith) (mem_Ici.2 hcf)
    (mem_Ici.2 (by linarith))
  have e1 : x' - p + (p - p') = x' - p' := by ring
  have e2 : x - p + (p - p') = x - p' := by ring
  rw [e1, e2] at hu
  -- the household with less cash is indifferent to the other's saving
  have htie : M.utility (x - p') + M.discount * M.cont y P s p'
      = (M.household y P).valueFunction s := by
    have h1 := M.le_valueFunction y P hf'
    linarith
  exact absurd (M.eq_policy_of_objective y P hf' htie) hlt.ne

/-! ### OI3: (Sep) from ordered cash -/

/-- Integrals under two probability measures are ordered when every value of the first integrand
is below every value of the second. -/
theorem integral_le_of_forall_le {X : Type*} [MeasurableSpace X] {ν ν' : Measure X}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] {g h : X → ℝ} (hg : Integrable g ν)
    (hh : Integrable h ν') (hle : ∀ x x', g x ≤ h x') : ∫ x, g x ∂ν ≤ ∫ x, h x ∂ν' := by
  have hc : ∀ x', ∫ x, g x ∂ν ≤ h x' := fun x' => by
    have := integral_mono hg (integrable_const (h x')) fun x => hle x x'
    simpa using this
  have := integral_mono (integrable_const (∫ x, g x ∂ν)) hh hc
  simpa using this

variable [LinearOrder Z]

/-- **(Sep)**: with prices depending on the shock only, i.i.d. shocks and ordered cash, the
cross-section after a worse shock is dominated by the one after a better shock, whatever the
current cross-sections. -/
theorem sepOnHistories_of_orderedCash (hX : M.PricesExogenous) (hI : M.IIDShocks)
    (hO : M.OrderedCash) {μ : History Z → ProbabilityMeasure M.AState}
    (hμ : M.IsSeqStateEquilibrium μ) : SepOnHistories μ := by
  intro ω ω' hlt z' f hf
  have h1 := congrArg (fun ν : History Z → ProbabilityMeasure M.AState =>
    (ν (History.cons z' ω) : Measure M.AState)) hμ
  have h2 := congrArg (fun ν : History Z → ProbabilityMeasure M.AState =>
    (ν (History.cons z' ω') : Measure M.AState)) hμ
  rw [← h1, ← h2, M.coe_seqStep_cons, M.coe_seqStep_cons, M.integral_pushNode,
    M.integral_pushNode]
  refine integral_le_of_forall_le ((M.expectedNext (ω 0) (M.seqPrices μ ω) [] z' f).integrable _)
    ((M.expectedNext (ω' 0) (M.seqPrices μ ω') [] z' f).integrable _) fun x x' => ?_
  refine Finset.sum_le_sum fun e' _ => ?_
  have hp : M.nextProb (ω 0) [] z' e' x = M.nextProb (ω' 0) [] z' e' x' :=
    hI.2 _ _ _ _ _ _
  rw [hp]
  refine mul_le_mul_of_nonneg_left (hf _ _ rfl ?_) (M.nextProb_nonneg (ω' 0) [] z' e' x')
  change (M.clampAssets (M.policy (ω 0) (M.seqPrices μ ω) (x.1, ⟨x.2.idio, []⟩)) : ℝ)
    ≤ M.clampAssets (M.policy (ω' 0) (M.seqPrices μ ω') (x'.1, ⟨x'.2.idio, []⟩))
  refine Subtype.coe_le_coe.2 (monotone_projIcc M.assetCap_pos.le
    (policy_le_policy_of_cont ?_ (cont_root_eq hX hI _ _ _ _ rfl rfl)))
  exact hO _ _ hlt _ _ _ _ x.1 x'.1 x.2.idio x'.2.idio

/-- **`(z, K)` is a sufficient state** for every sequence-state equilibrium, when prices depend on
the shock only, shocks are i.i.d., and cash on hand is ordered by the shock. -/
theorem kSufficient_of_orderedCash (hX : M.PricesExogenous) (hI : M.IIDShocks)
    (hO : M.OrderedCash) {μ : History Z → ProbabilityMeasure M.AState}
    (hμ : M.IsSeqStateEquilibrium μ) : KSufficient μ :=
  kSufficient_of_savingMonotone (savingMonotone_of_exogenous hX)
    (uniqueSequentialEquilibrium_of_exogenous hX) hμ (sepOnHistories_of_orderedCash hX hI hO hμ)

end KSModel

end KrusellSmith

end LeanEconomics
