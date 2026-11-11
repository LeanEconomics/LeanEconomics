/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ProportionalEquilibrium
import LeanEconomics.KrusellSmith.AggregateStateRecursive

/-!
# A recursive equilibrium on `(z, K)` for the proportional heterogeneous economy

The packaging step of route 2 of `CROSS_SECTION_PLAN.md`: permanent efficiency types holding assets
proportional to efficiency (`ProportionalEquilibrium.lean`).

**`propRecursive`**: an `AggStateRecursiveEquilibrium` whose aggregate state is `(z, K)`, with `K`
ranging over `[0, cap]`:

* capital moves by the Coleman saving of the aggregate economy, `lawK z K z' = s*(z, K)`; labour is
  mean efficiency `L`;
* value and saving at `(z, K, a, e)` are the household's — for **every** asset level `a` and type
  `e`, not only on the proportional path — at the prices of the Coleman capital path from `(z, K)`;
* the cross-section consistent with `(z, K)` is the proportional one (`propDist`): mass `p e` of
  type `e` at assets `θ_e K`. Each type saves its share (`savingP_point`, from `policy_eq_prop`),
  so it moves to the proportional cross-section at `lawK z K z'`.
-/

open Set Filter Topology MeasureTheory BoundedContinuousFunction
open LeanEconomics.StochasticDynamicProgram
open scoped NNReal ENNReal

namespace LeanEconomics

namespace KrusellSmith

namespace Coleman

variable {Z E : Type*} [Fintype Z] [Fintype E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ}
  (hγ : 0 < γ) {L : ℝ} (hL : 0 < L) (hLbox : T.clampLab L = L)
  (hβR : V.discount * T.returnBound ≤ 1) {cap : ℝ} (hcap : 0 < cap)

local notation "𝒟" => aggData V T hγ hL hLbox hβR hcap
local notation "𝒸" => OrderHom.gfp (Data.T (aggData V T hγ hL hLbox hβR hcap))
local notation "𝕄" => crraModel V T hγ

/-- Capital as a point of the box. -/
noncomputable def kBoxP (k : ℝ) : (𝒟).Box :=
  projIcc 0 (𝒟).cap (𝒟).cap_pos.le k

theorem kBoxP_eq {k : ℝ} (hk : k ∈ Icc 0 cap) :
    kBoxP V T hγ hL hLbox hβR hcap k = ⟨k, hk⟩ :=
  projIcc_of_mem (𝒟).cap_pos.le (show k ∈ Icc 0 (𝒟).cap from hk)

theorem kBoxP_val {k : ℝ} (hk : k ∈ Icc 0 cap) :
    ((kBoxP V T hγ hL hLbox hβR hcap k : (𝒟).Box) : ℝ) = k := by
  rw [kBoxP_eq V T hγ hL hLbox hβR hcap hk]

theorem kBoxP_coe (x : (𝒟).Box) : kBoxP V T hγ hL hLbox hβR hcap (x : ℝ) = x :=
  projIcc_val _ x

/-- The prices at `(z, K)`: those of the aggregate Coleman capital path from `(z, K)`. -/
noncomputable def pricesP (z : Z) (k : ℝ) : List Z → ℝ × ℝ :=
  propPrices V T hγ hL hLbox hβR hcap z (kBoxP V T hγ hL hLbox hβR hcap k)

/-- The household's value at `(z, K, a, e)`. -/
noncomputable def valueP (z : Z) (k : ℝ) (a : ↥(Icc (0 : ℝ) (𝕄).assetCap)) (e : E) : ℝ :=
  ((𝕄).household z (pricesP V T hγ hL hLbox hβR hcap z k)).valueFunction (a, ⟨e, []⟩)

/-- The household's saving at `(z, K, a, e)`. -/
noncomputable def savingP (z : Z) (k : ℝ) (a : ↥(Icc (0 : ℝ) (𝕄).assetCap)) (e : E) :
    ↥(Icc (0 : ℝ) (𝕄).assetCap) :=
  ⟨(𝕄).policy z (pricesP V T hγ hL hLbox hβR hcap z k) (a, ⟨e, []⟩), (𝕄).policy_mem_Icc _ _ _⟩

/-- The law of motion of capital: the Coleman saving of the aggregate economy. -/
noncomputable def lawKP (z : Z) (k : ℝ) (_z' : Z) : ℝ :=
  (𝒟).saving 𝒸 z (kBoxP V T hγ hL hLbox hβR hcap k)

theorem lawKP_mem (z : Z) (k : ℝ) (z' : Z) : lawKP V T hγ hL hLbox hβR hcap z k z' ∈ Icc 0 cap :=
  ⟨((𝒟).saving_spec 𝒸 z _).1, ((𝒟).saving_spec 𝒸 z _).2.1⟩

/-- From the next node the prices are those of the Coleman path from `(z', s*(z, K))`. -/
theorem shiftPath_pricesP (z : Z) (k : ℝ) (z' : Z) :
    shiftPath (pricesP V T hγ hL hLbox hβR hcap z k) [z']
      = pricesP V T hγ hL hLbox hβR hcap z' (lawKP V T hγ hL hLbox hβR hcap z k z') := by
  funext g
  simp only [shiftPath_apply, pricesP, propPrices, lawKP]
  rw [Data.capPath_append]
  change (((𝒟).capPath 𝒸 z' ((𝒟).savingBox 𝒸 z (kBoxP V T hγ hL hLbox hβR hcap k)) g : ℝ), L) = _
  rw [show (𝒟).saving 𝒸 z (kBoxP V T hγ hL hLbox hβR hcap k)
      = (((𝒟).savingBox 𝒸 z (kBoxP V T hγ hL hLbox hβR hcap k) : (𝒟).Box) : ℝ) from rfl,
    kBoxP_coe]

/-- Continuation values are the values at the next aggregate state. -/
theorem valueFunction_nextP (z : Z) (k : ℝ) (z' : Z) (a : ↥(Icc (0 : ℝ) (𝕄).assetCap)) (e' : E) :
    ((𝕄).household z (pricesP V T hγ hL hLbox hβR hcap z k)).valueFunction (a, ⟨e', [z']⟩)
      = valueP V T hγ hL hLbox hβR hcap z' (lawKP V T hγ hL hLbox hβR hcap z k z') a e' := by
  rw [valueP, ← shiftPath_pricesP]
  have h := DFunLike.congr_fun
    ((𝕄).valueFunction_shift z (pricesP V T hγ hL hLbox hβR hcap z k) [z']) (a, ⟨e', []⟩)
  exact h.symm

/-- Cash at the root of `(z, K)`. -/
theorem cash_rootP {z : Z} {k : ℝ} (hk : k ∈ Icc 0 cap) (a : ↥(Icc (0 : ℝ) (𝕄).assetCap))
    (e : E) :
    (𝕄).cash z (pricesP V T hγ hL hLbox hβR hcap z k) (a, ⟨e, []⟩)
      = (𝕄).grossReturn z k L * a + (𝕄).wage z k L * (𝕄).efficiency e
        - (𝕄).grossReturn z k L * (𝕄).borrowLimit := by
  change (𝕄).grossReturn z ((kBoxP V T hγ hL hLbox hβR hcap k : (𝒟).Box) : ℝ) L * a
      + (𝕄).wage z ((kBoxP V T hγ hL hLbox hβR hcap k : (𝒟).Box) : ℝ) L * (𝕄).efficiency e
      - (𝕄).grossReturn z ((kBoxP V T hγ hL hLbox hβR hcap k : (𝒟).Box) : ℝ) L
        * (𝕄).borrowLimit = _
  rw [kBoxP_val V T hγ hL hLbox hβR hcap hk]

variable [DecidableEq E] (hθ : ∀ e, scale V L e * cap ≤ V.assetCap)
  (hperm : ∀ z z' e e', V.idioProb z z' e e' = if e = e' then 1 else 0)

include hperm in
/-- **Each type saves its share at the proportional point.** -/
theorem savingP_point (hslack : ∀ (z : Z) (k : (𝒟).Box), (𝒟).saving 𝒸 z k < cap) {z : Z} {k : ℝ}
    (hk : k ∈ Icc 0 cap) (e : E) :
    ((savingP V T hγ hL hLbox hβR hcap z k
        (propPoint V T hγ hL hLbox hβR hcap hθ e ⟨k, hk⟩).1 e : ↥(Icc (0 : ℝ) (𝕄).assetCap)) : ℝ)
      = scale V L e * lawKP V T hγ hL hLbox hβR hcap z k z := by
  have h := policy_eq_prop V T hγ hL hLbox hβR hcap hθ hperm hslack z ⟨k, hk⟩ e
  have hP : pricesP V T hγ hL hLbox hβR hcap z k
      = propPrices V T hγ hL hLbox hβR hcap z ⟨k, hk⟩ := by
    rw [pricesP, kBoxP_eq V T hγ hL hLbox hβR hcap hk]
  change (𝕄).policy z (pricesP V T hγ hL hLbox hβR hcap z k)
      (propRoot V T hγ hL hLbox hβR hcap hθ e ⟨k, hk⟩)
    = scale V L e * (𝒟).saving 𝒸 z (kBoxP V T hγ hL hLbox hβR hcap k)
  rw [hP, kBoxP_eq V T hγ hL hLbox hβR hcap hk]
  exact h

variable (p : E → ℝ≥0) (hp : ∑ e, p e = 1) (hLsum : ∑ e, (p e : ℝ) * V.efficiency e = L)

/-- **A recursive equilibrium on `(z, K)`** for the proportional heterogeneous economy: permanent
efficiency types with masses `p`, CRRA utility, Cobb–Douglas prices, `β R̄ ≤ 1` and a slack capital
cap, at every capital share. -/
noncomputable def propRecursive (hslack : ∀ (z : Z) (k : (𝒟).Box), (𝒟).saving 𝒸 z k < cap) :
    (𝕄).AggStateRecursiveEquilibrium where
  Kset _ := Icc 0 cap
  lawK := lawKP V T hγ hL hLbox hβR hcap
  labourK _ _ := L
  value := valueP V T hγ hL hLbox hβR hcap
  saving := savingP V T hγ hL hLbox hβR hcap
  dist _ k := {ν | ∃ hk : k ∈ Icc 0 cap,
    (ν : Measure (𝕄).AState) = propDist V T hγ hL hLbox hβR hcap hθ p ⟨k, hk⟩}
  lawK_mem z k _ z' := lawKP_mem V T hγ hL hLbox hβR hcap z k z'
  dist_nonempty _ k hk := ⟨⟨propDist V T hγ hL hLbox hβR hcap hθ p ⟨k, hk⟩,
    isProbabilityMeasure_propDist V T hγ hL hLbox hβR hcap hθ p hp _⟩, hk, rfl⟩
  capital_eq _ k ν hν := by
    obtain ⟨hk, hν⟩ := hν
    rw [hν]
    exact integral_assets_propDist V T hγ hL hLbox hβR hcap hθ p hp hLsum ⟨k, hk⟩
  labour_eq z k ν hν := by
    obtain ⟨hk, hν⟩ := hν
    rw [hν]
    exact (labour_propDist V T hγ hL hLbox hβR hcap hθ hperm p hp hLsum z ⟨k, hk⟩ []).symm
  feasible z k hk a e := by
    have h := (𝕄).policy_mem z (pricesP V T hγ hL hLbox hβR hcap z k) (a, ⟨e, []⟩)
    have h2 := h.2.trans (min_le_right _ _)
    change (𝕄).policy z (pricesP V T hγ hL hLbox hβR hcap z k) (a, ⟨e, []⟩) ≤ _
    rw [← cash_rootP V T hγ hL hLbox hβR hcap hk a e]
    linarith
  bellman z k hk a e := by
    set D := (𝕄).household z (pricesP V T hγ hL hLbox hβR hcap z k)
    have hV : D.valueFunction (a, ⟨e, []⟩) = D.bellman D.valueFunction (a, ⟨e, []⟩) := by
      rw [D.bellman_valueFunction]
    rw [valueP, hV, (𝕄).policy_optimal z, (𝕄).objective_eq z _ _ ((𝕄).policy_mem z _ _),
      cash_rootP V T hγ hL hLbox hβR hcap hk]
    congr 2
    refine Finset.sum_congr rfl fun ze _ => ?_
    rw [(𝕄).clampAssets_of_mem ((𝕄).policy_mem_Icc z _ _), valueFunction_nextP]
    rfl
  optimal z k hk a e a' ha' := by
    set D := (𝕄).household z (pricesP V T hγ hL hLbox hβR hcap z k)
    have hfeas : (a' : ℝ) ∈ D.feasible (a, ⟨e, []⟩) := by
      refine ⟨a'.2.1, le_min a'.2.2 ?_⟩
      rw [cash_rootP V T hγ hL hLbox hβR hcap hk]
      linarith
    have hle := D.le_bellmanFn D.valueFunction hfeas
    have hV : D.bellmanFn D.valueFunction (a, ⟨e, []⟩) = D.valueFunction (a, ⟨e, []⟩) :=
      congrFun (congrArg DFunLike.coe D.bellman_valueFunction) _
    rw [hV, (𝕄).objective_eq z _ _ hfeas, cash_rootP V T hγ hL hLbox hβR hcap hk] at hle
    refine le_of_eq_of_le ?_ hle
    congr 2
    refine Finset.sum_congr rfl fun ze _ => ?_
    rw [(𝕄).clampAssets_of_mem a'.2, valueFunction_nextP]
    rfl
  lawOfMotion z k ν hν z' := by
    obtain ⟨hk, hν⟩ := hν
    have hpr := isProbabilityMeasure_propDist V T hγ hL hLbox hβR hcap hθ p hp
    have hP : pricesP V T hγ hL hLbox hβR hcap z k
        = propPrices V T hγ hL hLbox hβR hcap z ⟨k, hk⟩ := by
      rw [pricesP, kBoxP_eq V T hγ hL hLbox hβR hcap hk]
    refine ⟨⟨propDist V T hγ hL hLbox hβR hcap hθ p ((𝒟).capPath 𝒸 z ⟨k, hk⟩ [z']), hpr _⟩,
      ⟨lawKP_mem V T hγ hL hLbox hβR hcap z k z', ?_⟩, fun f => ?_⟩
    · change propDist V T hγ hL hLbox hβR hcap hθ p ((𝒟).capPath 𝒸 z ⟨k, hk⟩ [z']) = _
      congr 1
      refine Subtype.ext ?_
      change (𝒟).saving 𝒸 z ⟨k, hk⟩ = (𝒟).saving 𝒸 z (kBoxP V T hγ hL hLbox hβR hcap k)
      rw [kBoxP_eq V T hγ hL hLbox hβR hcap hk]
    · rw [hν]
      change ∫ x, f x ∂(propDist V T hγ hL hLbox hβR hcap hθ p ((𝒟).capPath 𝒸 z ⟨k, hk⟩ [z'])) = _
      rw [← nodeDist_propDist V T hγ hL hLbox hβR hcap hθ hperm p hp hLsum hslack z ⟨k, hk⟩ [z']]
      change ∫ x, f x ∂((𝕄).pushNode z (propPrices V T hγ hL hLbox hβR hcap z ⟨k, hk⟩) [] z'
        (propDist V T hγ hL hLbox hβR hcap hθ p ⟨k, hk⟩)) = _
      haveI := hpr ⟨k, hk⟩
      rw [(𝕄).integral_pushNode]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      refine Finset.sum_congr rfl fun e' _ => ?_
      have hA : (𝕄).nextA z (propPrices V T hγ hL hLbox hβR hcap z ⟨k, hk⟩) [] e' x
          = (savingP V T hγ hL hLbox hβR hcap z k x.1 x.2.idio, ⟨e'⟩) := by
        refine Prod.ext (Subtype.ext ?_) rfl
        change (((𝕄).clampAssets ((𝕄).policy z (propPrices V T hγ hL hLbox hβR hcap z ⟨k, hk⟩)
          (x.1, ⟨x.2.idio, []⟩)) : ↥(Icc (0 : ℝ) (𝕄).assetCap)) : ℝ)
          = (𝕄).policy z (pricesP V T hγ hL hLbox hβR hcap z k) (x.1, ⟨x.2.idio, []⟩)
        rw [(𝕄).clampAssets_of_mem ((𝕄).policy_mem_Icc z _ _), hP]
      rw [hA]
      rfl

/-- **Mean saving at the proportional cross-section is the law of motion**: each type saves its
share of `s*(z, K)`. -/
theorem propRecursive_saving (hslack : ∀ (z : Z) (k : (𝒟).Box), (𝒟).saving 𝒸 z k < cap) {z : Z}
    {k : ℝ} (hk : k ∈ Icc 0 cap) (e : E) :
    (((propRecursive V T hγ hL hLbox hβR hcap hθ hperm p hp hLsum hslack).saving z k
        (propPoint V T hγ hL hLbox hβR hcap hθ e ⟨k, hk⟩).1 e : ↥(Icc (0 : ℝ) (𝕄).assetCap)) : ℝ)
      = scale V L e
        * (propRecursive V T hγ hL hLbox hβR hcap hθ hperm p hp hLsum hslack).lawK z k z :=
  savingP_point V T hγ hL hLbox hβR hcap hθ hperm hslack hk e

end Coleman

end KrusellSmith

end LeanEconomics
