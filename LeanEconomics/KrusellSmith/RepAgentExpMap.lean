/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ExpectationsMap
import LeanEconomics.KrusellSmith.WageComparativeStatics
import LeanEconomics.KrusellSmith.RepAgentCash

/-!
# The expectations map reverses order: representative agent

Step (b) of milestone B2 (`EXISTENCE_EXTENSIONS_PLAN.md`), with one idiosyncratic state.

* With one idiosyncratic state the mass is one at every node and labour is the efficiency
  (`stateMass_unique`, `labour_unique`); a point mass is pushed to a point mass
  (`pushNode_dirac`), so from a point mass the expectations distributions are point masses at
  `repPath` (`expDist_dirac`).
* **`repPath_anti`**: a higher expected capital path gives lower realised capital at every node.
  By induction: at node `h`, shift the tree to `h`; below the new root the price paths are the
  expected ones, ordered (`crra_policy_le_of_capital`, step (a)); at the root, today's prices clear
  at realised capital, lower under the higher expectations by induction, and cash
  `R(A) A + w(A) L` rises with `A` (`CobbDouglas.repCash_mono`), so cash is lower too.
* **`expMap_antitone_dirac`**: the expectations map from every point mass reverses order — for
  CRRA with `0 < γ ≤ 1`, Cobb–Douglas prices, labour inside its box, and the floor and cap slack
  along the Bellman iterates of every price path (the hypotheses of Light's step).
-/

open MeasureTheory Set

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) [Unique E]

theorem stateMass_unique (z₀ : Z) (m₀ : E → ℝ) : ∀ (h : List Z) (e : E),
    M.stateMass z₀ m₀ h e = m₀ default
  | [], e => by rw [Unique.eq_default e]; rfl
  | z' :: h, e' => by
    simp only [stateMass, Fintype.sum_unique]
    rw [stateMass_unique z₀ m₀ h default]
    have := M.idioProb_sum (shockAt z₀ h) z' default
    rw [Fintype.sum_unique] at this
    rw [Unique.eq_default e', this, mul_one]

theorem initMass_dirac (x : M.AState) : M.initMass (Measure.dirac x) default = 1 := by
  have hset : {y : M.AState | y.2.idio = default} = univ :=
    eq_univ_of_forall fun y => Unique.eq_default _
  change (Measure.dirac x).real {y : M.AState | y.2.idio = default} = 1
  rw [hset, probReal_univ]

theorem labour_unique (z₀ : Z) (x : M.AState) (h : List Z) :
    M.labour z₀ (M.initMass (Measure.dirac x)) h = M.efficiency default := by
  simp only [labour, Fintype.sum_unique, stateMass_unique, initMass_dirac, one_mul]

theorem pushNode_dirac (z₀ : Z) (K : List Z → ℝ × ℝ) (h : List Z) (z' : Z) (x : M.AState) :
    M.pushNode z₀ K h z' (Measure.dirac x) = Measure.dirac (M.nextA z₀ K h default x) := by
  have : IsProbabilityMeasure (M.pushNode z₀ K h z' (Measure.dirac x)) :=
    M.isProbabilityMeasure_pushNode _ _ _ _ _
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [M.integral_pushNode, integral_dirac, integral_dirac, Fintype.sum_unique]
  have h1 : M.nextProb z₀ h z' default x = 1 := by
    have := M.idioProb_sum (shockAt z₀ h) z' x.2.idio
    rwa [Fintype.sum_unique] at this
  rw [h1, one_mul]

open Classical in
/-- **The representative household's assets** under expectations `K`, from `x₀`: at every node it
saves against the path `K` with today's entry replaced by realised capital and labour. -/
noncomputable def repPath (z₀ : Z) (x₀ : M.AState) (K : List Z → ℝ) : List Z → M.AState
  | [] => x₀
  | _ :: h => M.nextA z₀ (Function.update (M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K) h
      ((repPath z₀ x₀ K h).1, M.labour z₀ (M.initMass (Measure.dirac x₀)) h)) h default
      (repPath z₀ x₀ K h)

open Classical in
/-- **From a point mass the expectations distributions are point masses** at `repPath`. -/
theorem expDist_dirac (z₀ : Z) (x₀ : M.AState) (K : List Z → ℝ) :
    ∀ h, M.expDist z₀ (Measure.dirac x₀) K h = Measure.dirac (M.repPath z₀ x₀ K h)
  | [] => rfl
  | z' :: h => by
    have ih := expDist_dirac z₀ x₀ K h
    change M.pushNode z₀ (Function.update (M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K) h
        (∫ x, M.assets x ∂(M.expDist z₀ (Measure.dirac x₀) K h),
          M.labour z₀ (M.initMass (Measure.dirac x₀)) h)) h z'
        (M.expDist z₀ (Measure.dirac x₀) K h) = _
    rw [ih, integral_dirac, pushNode_dirac]
    rfl

open Classical in
/-- **The induction down the tree**: if, at every node shifted to the root, lower realised capital
and the higher expected path give lower saving, realised capital is lower at every node. -/
theorem repPath_anti_of (z₀ : Z) (x₀ : M.AState) {K K' : List Z → ℝ}
    (hcomp : ∀ (h : List Z) (a a' : ↥(Icc (0 : ℝ) M.assetCap)), (a' : ℝ) ≤ a →
      M.policy (shockAt z₀ h) (shiftPath (Function.update
          (M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K') h
          ((a' : ℝ), M.labour z₀ (M.initMass (Measure.dirac x₀)) h)) h) (a', ⟨default, []⟩)
        ≤ M.policy (shockAt z₀ h) (shiftPath (Function.update
          (M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K) h
          ((a : ℝ), M.labour z₀ (M.initMass (Measure.dirac x₀)) h)) h) (a, ⟨default, []⟩)) :
    ∀ h, ((M.repPath z₀ x₀ K' h).1 : ℝ) ≤ ((M.repPath z₀ x₀ K h).1 : ℝ)
  | [] => le_rfl
  | z' :: h => by
    have ih := repPath_anti_of z₀ x₀ hcomp h
    have hval : ∀ (Q : List Z → ℝ × ℝ) (x : M.AState),
        ((M.nextA z₀ Q h default x).1 : ℝ)
          = M.policy (shockAt z₀ h) (shiftPath Q h) (x.1, ⟨default, []⟩) := fun Q x => by
      rw [M.policy_shift z₀ Q h]
      change ((M.clampAssets (M.policy z₀ Q (x.1, ⟨x.2.idio, h⟩)) : ℝ)) = _
      rw [M.clampAssets_of_mem (M.policy_mem_Icc z₀ Q _), Unique.eq_default x.2.idio]
      rfl
    rw [repPath, repPath, hval, hval]
    exact hcomp h _ _ ih

end KSModel

/-! ### Order reversal for CRRA, Cobb–Douglas -/

variable [Unique E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)

open Classical in
/-- **A higher expected capital path gives lower realised capital at every node**, for the
representative agent. -/
theorem repPath_anti (hγ1 : γ ≤ 1)
    (hLbox : T.clampLab (V.efficiency default) = V.efficiency default)
    (hsl : ∀ (z : Z) (P : List Z → ℝ × ℝ) (n : ℕ), (crraModel V T hγ).SlackOf z P
      ((((crraModel V T hγ).household z P).bellman)^[n] 0))
    (hcap : ∀ (z : Z) (P : List Z → ℝ × ℝ) (n : ℕ) (s : (crraModel V T hγ).State),
      (crraModel V T hγ).policyOf z P ((((crraModel V T hγ).household z P).bellman)^[n] 0) s
        < (crraModel V T hγ).assetCap)
    (z₀ : Z) (x₀ : (crraModel V T hγ).AState) {K K' : List Z → ℝ}
    (hKK : ∀ h, K h ≤ K' h) (h : List Z) :
    (((crraModel V T hγ).repPath z₀ x₀ K' h).1 : ℝ)
      ≤ (((crraModel V T hγ).repPath z₀ x₀ K h).1 : ℝ) := by
  refine (crraModel V T hγ).repPath_anti_of z₀ x₀ (fun h a a' hle => ?_) h
  set m₀ := (crraModel V T hγ).initMass (Measure.dirac x₀)
  -- below the new root the price paths are the expected ones
  have hbelow : ∀ (Q : List Z → ℝ) (A : ℝ) (g : List Z), g ≠ [] →
      shiftPath (Function.update ((crraModel V T hγ).pricePath z₀ m₀ Q) h
        (A, (crraModel V T hγ).labour z₀ m₀ h)) h g
        = (crraModel V T hγ).pricePath z₀ m₀ Q (g ++ h) := by
    intro Q A g hg
    rw [shiftPath_apply, Function.update_of_ne]
    intro he
    have := congrArg List.length he
    rw [List.length_append] at this
    have : g.length = 0 := by omega
    exact hg (List.length_eq_zero_iff.1 this)
  have hroot : ∀ (Q : List Z → ℝ) (A : ℝ),
      shiftPath (Function.update ((crraModel V T hγ).pricePath z₀ m₀ Q) h
        (A, (crraModel V T hγ).labour z₀ m₀ h)) h [] = (A, V.efficiency default) := fun Q A => by
    rw [shiftPath_apply, List.nil_append, Function.update_self,
      (crraModel V T hγ).labour_unique]
    rfl
  have hR : ∀ z k L, (crraModel V T hγ).grossReturn z k L = T.grossReturn z k L := fun _ _ _ => rfl
  have hw : ∀ z k L, (crraModel V T hγ).wage z k L = T.wage z k L := fun _ _ _ => rfl
  have hb : (crraModel V T hγ).borrowLimit = 0 := rfl
  have he : (crraModel V T hγ).efficiency default = V.efficiency default := rfl
  have hcash : ∀ (Q : List Z → ℝ) (A : ↥(Icc (0 : ℝ) (crraModel V T hγ).assetCap)),
      (crraModel V T hγ).cash (shockAt z₀ h) (shiftPath (Function.update
        ((crraModel V T hγ).pricePath z₀ m₀ Q) h ((A : ℝ), (crraModel V T hγ).labour z₀ m₀ h)) h)
        (A, ⟨default, []⟩)
        = T.grossReturn (shockAt z₀ h) A (V.efficiency default) * A
          + T.wage (shockAt z₀ h) A (V.efficiency default) * V.efficiency default := by
    intro Q A
    simp only [KSModel.cash, KSModel.returnAt, KSModel.wageAt, shockAt_nil, hroot, hR, hw, hb, he,
      mul_zero, sub_zero]
  refine crra_policy_le_of_capital V T hγ hγ1 (shockAt z₀ h) (fun g hg => ?_) (fun g hg => ?_)
    (hsl _ _) (hsl _ _) (hcap _ _) rfl ?_
  · rw [hbelow K _ g hg, hbelow K' _ g hg]
    exact hKK _
  · rw [hbelow K _ g hg, hbelow K' _ g hg]
    rfl
  · rw [hcash, hcash]
    exact T.repCash_mono _ hLbox a'.2.1 hle

/-- **The expectations map reverses order from every point mass**: CRRA with `0 < γ ≤ 1`,
Cobb–Douglas prices, one idiosyncratic state with efficiency inside the labour box, and the floor
and cap slack along the Bellman iterates of every price path. -/
theorem expMap_antitone_dirac (hγ1 : γ ≤ 1)
    (hLbox : T.clampLab (V.efficiency default) = V.efficiency default)
    (hsl : ∀ (z : Z) (P : List Z → ℝ × ℝ) (n : ℕ), (crraModel V T hγ).SlackOf z P
      ((((crraModel V T hγ).household z P).bellman)^[n] 0))
    (hcap : ∀ (z : Z) (P : List Z → ℝ × ℝ) (n : ℕ) (s : (crraModel V T hγ).State),
      (crraModel V T hγ).policyOf z P ((((crraModel V T hγ).household z P).bellman)^[n] 0) s
        < (crraModel V T hγ).assetCap)
    (z₀ : Z) (x₀ : (crraModel V T hγ).AState) :
    Antitone (KSModel.expMap (M := crraModel V T hγ) z₀ (diracProba x₀)) := by
  intro K K' hKK h
  change ∫ x, (crraModel V T hγ).assets x
      ∂((crraModel V T hγ).expDist z₀ (Measure.dirac x₀) (fun g => (K' g : ℝ)) h)
    ≤ ∫ x, (crraModel V T hγ).assets x
      ∂((crraModel V T hγ).expDist z₀ (Measure.dirac x₀) (fun g => (K g : ℝ)) h)
  rw [KSModel.expDist_dirac, KSModel.expDist_dirac, integral_dirac, integral_dirac]
  exact repPath_anti V T hγ hγ1 hLbox hsl hcap z₀ x₀ (fun g => hKK g) h

end KrusellSmith

end LeanEconomics
