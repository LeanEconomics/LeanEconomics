/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ProportionalEquilibrium
import LeanEconomics.KrusellSmith.ProportionalUnique
import LeanEconomics.KrusellSmith.RepAgentUnique

/-!
# The proportional CRRA economy has exactly one sequential equilibrium

`ProportionalEquilibrium.lean` builds a sequential equilibrium of the heterogeneous economy with
permanent efficiency types and assets proportional to efficiency: the Coleman capital path of the
aggregate economy. `ProportionalUnique.lean` shows, by Negishi weights, that a proportional
equilibrium is the only allocation in which every type optimises and capital is mean assets. Here
the two are joined for CRRA utility and Cobb–Douglas prices.

* `crraUtility_mul`: CRRA utility is homogeneous, `u(σ x) = σ^{1−γ} u(x) + κ`, with `κ = log σ`
  when `γ = 1` and zero otherwise.
* `integral_nodeDist_propDist`: along *any* price path the cross-section from a proportional
  start is the finite mixture of the types, each following its own optimal saving.
* **`eq_capPath_of_prop`**: every sequential equilibrium from a proportional cross-section is the
  Coleman capital path. The competing equilibrium is not assumed proportional. Hypotheses beyond
  those of existence: every type has positive mass, and aggregate resources less the consumption
  floor never exceed the capital bound (`hbound`), so that every allocation respects it.
-/

open Set MeasureTheory BoundedContinuousFunction
open scoped NNReal ENNReal

namespace LeanEconomics

namespace KrusellSmith

/-- **CRRA utility is homogeneous.** -/
theorem crraUtility_mul {γ σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    crraUtility γ (σ * x)
      = σ ^ (1 - γ) * crraUtility γ x + (if γ = 1 then Real.log σ else 0) := by
  by_cases hγ1 : γ = 1
  · subst hγ1
    simp only [crraUtility, ite_true, sub_self, Real.rpow_zero, one_mul]
    rw [Real.log_mul hσ.ne' hx.ne']
    ring
  · rw [crraUtility_of_ne hγ1, crraUtility_of_ne hγ1, Real.mul_rpow hσ.le hx.le]
    simp only [hγ1, ↓reduceIte]
    ring

namespace Coleman

variable {Z E : Type*} [Fintype Z] [Fintype E]

variable [DecidableEq E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ) {L : ℝ}
  (hL : 0 < L) (hLbox : T.clampLab L = L) (hβR : V.discount * T.returnBound ≤ 1) {cap : ℝ}
  (hcap : 0 < cap) (hθ : ∀ e, scale V L e * cap ≤ V.assetCap)
  (hperm : ∀ z z' e e', V.idioProb z z' e e' = if e = e' then 1 else 0)
  (p : E → ℝ≥0) (hp : ∑ e, p e = 1) (hLsum : ∑ e, (p e : ℝ) * V.efficiency e = L)

local notation "𝒟" => aggData V T hγ hL hLbox hβR hcap
local notation "𝒸" => OrderHom.gfp (Data.T (aggData V T hγ hL hLbox hβR hcap))
local notation "𝕄" => crraModel V T hγ

include hp hperm hLsum in
/-- **The proportional equilibrium as data for the uniqueness theorem.** -/
noncomputable def propEq (hslack : ∀ (z : Z) (k : (𝒟).Box), (𝒟).saving 𝒸 z k < cap)
    (hppos : ∀ e, 0 < p e)
    (hbound : ∀ (z : Z) (k : ℝ), k ∈ Icc 0 cap →
      T.grossReturn z k L * k + T.wage z k L * L - (𝕄).consFloor ≤ cap)
    (z₀ : Z) (k₀ : (𝒟).Box) : (𝕄).PropEq z₀ where
  p e := p e
  p_pos e := by exact_mod_cast hppos e
  p_sum := by exact_mod_cast hp
  σ := scale V L
  σ_pos := scale_pos V hL
  σ_sum := by
    have : ∀ e, (p e : ℝ) * scale V L e = (p e : ℝ) * V.efficiency e / L := fun e => by
      rw [scale]
      ring
    rw [Finset.sum_congr rfl fun e _ => this e, ← Finset.sum_div, hLsum, div_self hL.ne']
  L := L
  σ_L := scale_mul V hL
  lam e := scale V L e ^ (1 - γ)
  lam_pos e := Real.rpow_pos_of_pos (scale_pos V hL e) _
  κ e := if γ = 1 then Real.log (scale V L e) else 0
  hom e _ hx := crraUtility_mul (scale_pos V hL e) hx
  concave := (strictConcaveOn_crraUtility hγ).concaveOn
  floor_pos := crraFloorLevel_half_pos V T hγ
  borrow := rfl
  support z k a := T.repCash_le_of_prices z hLbox k a
  capK := cap
  σ_cap := hθ
  bound := hbound
  K h := ((𝒟).capPath 𝒸 z₀ k₀ h : ℝ)
  K_mem h := ((𝒟).capPath 𝒸 z₀ k₀ h).2
  prop e h z' := by
    have hshift : shiftPath (propPrices V T hγ hL hLbox hβR hcap z₀ k₀) h
        = propPrices V T hγ hL hLbox hβR hcap (shockAt z₀ h) ((𝒟).capPath 𝒸 z₀ k₀ h) := by
      funext g
      simp only [shiftPath_apply, propPrices, Data.capPath_append (𝒟) 𝒸 z₀ k₀ g h]
    have h1 := (𝕄).policy_shift z₀ (propPrices V T hγ hL hLbox hβR hcap z₀ k₀) h
      (propRoot V T hγ hL hLbox hβR hcap hθ e ((𝒟).capPath 𝒸 z₀ k₀ h))
    rw [hshift, policy_eq_prop V T hγ hL hLbox hβR hcap hθ hperm hslack] at h1
    rw [(𝕄).clampAssets_of_mem (scale_mul_mem V hL hθ e ((𝒟).capPath 𝒸 z₀ k₀ h).2)]
    exact h1.symm

include hp hperm in
/-- **The cross-section from a proportional start, along any price path**: the mixture of the
types, each following its own optimal saving. -/
theorem integral_nodeDist_propDist (z₀ : Z) (k₀ : (𝒟).Box) (X : List Z → ℝ × ℝ)
    (o : E → List Z → (𝕄).State)
    (ho0 : ∀ e, o e [] = ((propPoint V T hγ hL hLbox hβR hcap hθ e k₀).1, ⟨e, []⟩))
    (hoc : ∀ e z' h, o e (z' :: h)
      = ((𝕄).clampAssets ((𝕄).policy z₀ X ((o e h).1, ⟨e, h⟩)), ⟨e, z' :: h⟩)) :
    ∀ (h : List Z) (f : (𝕄).AState →ᵇ ℝ),
      ∫ x, f x ∂((𝕄).nodeDist z₀ (propDist V T hγ hL hLbox hβR hcap hθ p k₀) X h)
        = ∑ e, (p e : ℝ) * f ((o e h).1, ⟨e⟩)
  | [], f => by
    change ∫ x, f x ∂(propDist V T hγ hL hLbox hβR hcap hθ p k₀) = _
    rw [integral_propDist]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ho0]
    rfl
  | z' :: h, f => by
    have := isProbabilityMeasure_propDist V T hγ hL hLbox hβR hcap hθ p hp k₀
    have : IsProbabilityMeasure ((𝕄).nodeDist z₀
        (propDist V T hγ hL hLbox hβR hcap hθ p k₀) X h) :=
      (𝕄).isProbabilityMeasure_nodeDist z₀ _ X h
    change ∫ x, f x ∂((𝕄).pushNode z₀ X h z'
      ((𝕄).nodeDist z₀ (propDist V T hγ hL hLbox hβR hcap hθ p k₀) X h)) = _
    rw [(𝕄).integral_pushNode]
    change ∫ x, (𝕄).expectedNext z₀ X h z' f x ∂_ = _
    rw [integral_nodeDist_propDist z₀ k₀ X o ho0 hoc h]
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    change ∑ e', (𝕄).nextProb z₀ h z' e' ((o e h).1, ⟨e⟩)
      * f ((𝕄).nextA z₀ X h e' ((o e h).1, ⟨e⟩)) = _
    rw [Finset.sum_eq_single e]
    · change V.idioProb _ z' e e * _ = _
      rw [hperm, ite_eq_left rfl, one_mul, hoc]
      rfl
    · intro e' _ he'
      change V.idioProb _ z' e e' * _ = 0
      rw [hperm, ite_eq_right (fun h => he' h.symm), zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h

include hp hperm hLsum in
/-- **Every sequential equilibrium from a proportional cross-section is the Coleman capital
path**: the proportional CRRA, Cobb–Douglas economy has exactly one sequential equilibrium. -/
theorem eq_capPath_of_prop (hslack : ∀ (z : Z) (k : (𝒟).Box), (𝒟).saving 𝒸 z k < cap)
    (hppos : ∀ e, 0 < p e)
    (hbound : ∀ (z : Z) (k : ℝ), k ∈ Icc 0 cap →
      T.grossReturn z k L * k + T.wage z k L * L - (𝕄).consFloor ≤ cap)
    (z₀ : Z) (k₀ : (𝒟).Box) {K' : List Z → ℝ}
    (hK' : (𝕄).IsSequentialEquilibrium z₀ (propDist V T hγ hL hLbox hβR hcap hθ p k₀) K') :
    K' = fun h => ((𝒟).capPath 𝒸 z₀ k₀ h : ℝ) := by
  set D := propEq V T hγ hL hLbox hβR hcap hθ hperm p hp hLsum hslack hppos hbound z₀ k₀ with hD
  have hprice : (𝕄).pricePath z₀
      ((𝕄).initMass (propDist V T hγ hL hLbox hβR hcap hθ p k₀)) K' = D.pr K' := by
    funext g
    exact Prod.ext rfl (labour_propDist V T hγ hL hLbox hβR hcap hθ hperm p hp hLsum z₀ k₀ g)
  refine D.eq_of_types hperm K' fun h => ?_
  have hst : ∀ e g, D.other K' e g = ((D.other K' e g).1, ⟨e, g⟩) := fun e g =>
    Prod.ext rfl (D.other_label K' e g)
  have ho0 : ∀ e, D.other K' e []
      = ((propPoint V T hγ hL hLbox hβR hcap hθ e k₀).1, ⟨e, []⟩) := fun e => by
    change ((𝕄).clampAssets (scale V L e * (k₀ : ℝ)), (⟨e, []⟩ : Label Z E)) = _
    rw [(𝕄).clampAssets_of_mem (scale_mul_mem V hL hθ e k₀.2)]
    rfl
  have hoc : ∀ e z' g, D.other K' e (z' :: g)
      = ((𝕄).clampAssets ((𝕄).policy z₀ (D.pr K') ((D.other K' e g).1, ⟨e, g⟩)),
        ⟨e, z' :: g⟩) := fun e z' g => by
    rw [← hst e g]
    rfl
  have hint := integral_nodeDist_propDist V T hγ hL hLbox hβR hcap hθ hperm p hp z₀ k₀
    (D.pr K') (D.other K') ho0 hoc h (𝕄).assets
  have := hK' h
  rw [KSModel.meanCapital, hprice, hint] at this
  exact this

end Coleman

end KrusellSmith

end LeanEconomics
