/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.RepAgentExpMap

/-!
# The bracket at one initial state, and B3 for the representative agent

Milestone B3 of `EXISTENCE_EXTENSIONS_PLAN.md`, representative-agent case.

* **`unique_of_antitone_at`**: the bracket argument at a single initial state `(z, μ)`: an
  order-reversing map whose fixed points include the sequential equilibria from `(z, μ)`, with the
  bottom of the bracket a positive fraction of the top and the square concave at the top, admits
  at most one sequential equilibrium from `(z, μ)`.
* `concave_of_elasticity`: the concavity hypothesis in quantitative form — if scaling the top of
  the bracket by `t` lowers the square by at most `c (1 − t)` of the top, with `c < 1`, the square
  is concave at the top (`φ = 1 − c (1 − t) > t`).
* **`crra_rep_unique_of_concave`**: for the representative agent (CRRA, `0 < γ ≤ 1`,
  Cobb–Douglas, efficiency inside the labour box, floor and cap slack along the iterates), from
  every point mass, the elasticity bound with `c < 1` and a positive bottom of the bracket give a
  unique sequential equilibrium. The expectations map reverses order there
  (`expMap_antitone_dirac`); **the elasticity bound is the open part of B3**.
-/

open MeasureTheory Set

namespace LeanEconomics

namespace KrusellSmith

/-- **Concavity at the top from an elasticity bound**: if `g (t hi) ≥ (1 − c (1 − t)) hi` for every
`t ∈ (0, 1)`, with `c < 1`, then `g` is concave at the top in Krasnosel'skii's sense. -/
theorem concave_of_elasticity {ι : Type*} {g : (ι → ℝ) → (ι → ℝ)} {hi : ι → ℝ} {c : ℝ}
    (hc : c < 1)
    (hel : ∀ t ∈ Ioo (0 : ℝ) 1, (1 - c * (1 - t)) • hi ≤ g (t • hi)) :
    ∀ t ∈ Ioo (0 : ℝ) 1, ∃ φ : ℝ, t < φ ∧ φ • hi ≤ g (t • hi) := by
  intro t ht
  refine ⟨1 - c * (1 - t), ?_, hel t ht⟩
  have : 0 < (1 - t) * (1 - c) := mul_pos (by linarith [ht.2]) (by linarith)
  nlinarith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

/-- **The bracket at one initial state**: an order-reversing map on capital paths whose fixed points
include the sequential equilibria from `(z, μ)`, whose bracket bottom is a positive fraction of its
top, and whose square is concave at the top, admits at most one sequential equilibrium from
`(z, μ)`. -/
theorem unique_of_antitone_at {z : Z} {μ : ProbabilityMeasure M.AState}
    {f : M.CapPath → M.CapPath} (hf : Antitone f)
    (hfix : ∀ {K : List Z → ℝ} (hK : M.IsSequentialEquilibrium z (μ : Measure M.AState) K),
      f (fun h => ⟨K h, M.equilibrium_mem_pi z μ hK h (mem_univ h)⟩)
        = fun h => ⟨K h, M.equilibrium_mem_pi z μ hK h (mem_univ h)⟩)
    (hpos : ∃ t₀ : ℝ, 0 < t₀ ∧
      t₀ • (fun h => (OrderHom.gfp (AntitoneBracket.sq hf) h : ℝ))
        ≤ fun h => (OrderHom.lfp (AntitoneBracket.sq hf) h : ℝ))
    (hconc : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ φ : ℝ, t < φ ∧
      φ • (fun h => (OrderHom.gfp (AntitoneBracket.sq hf) h : ℝ))
        ≤ fun h => (AntitoneBracket.sq hf
          (toCap (M := M) (t • fun h => (OrderHom.gfp (AntitoneBracket.sq hf) h : ℝ))) h : ℝ))
    {K K' : List Z → ℝ} (hK : M.IsSequentialEquilibrium z (μ : Measure M.AState) K)
    (hK' : M.IsSequentialEquilibrium z (μ : Measure M.AState) K') : K = K' := by
  set lo := OrderHom.lfp (AntitoneBracket.sq hf)
  set hi := OrderHom.gfp (AntitoneBracket.sq hf)
  set loR : List Z → ℝ := fun h => (lo h : ℝ)
  set hiR : List Z → ℝ := fun h => (hi h : ℝ)
  set G : (List Z → ℝ) → (List Z → ℝ) :=
    fun P h => (AntitoneBracket.sq hf (toCap (M := M) P) h : ℝ) with hG
  have hcap : toCap (M := M) loR = lo := toCap_val lo
  have hloR : G loR = loR := by
    funext h
    simp only [hG]
    rw [hcap, OrderHom.map_lfp]
  have hle : loR ≤ hiR := fun h => (OrderHom.lfp_le_gfp (AntitoneBracket.sq hf)) h
  have h0 : 0 ≤ hiR := fun h => (hi h).2.1
  have hmono : ∀ t ∈ Icc (0 : ℝ) 1, t • hiR ≤ loR → G (t • hiR) ≤ G loR := by
    intro t _ ht h
    simp only [hG]
    refine (AntitoneBracket.sq hf).monotone (fun g => ?_) h
    simp only [toCap, loR]
    exact monotone_projIcc _ (ht g)
  have heqR := eq_of_concave hloR hle h0 hmono hpos hconc
  have heq : lo = hi := funext fun h => Subtype.ext (congrFun heqR h)
  have key : ∀ {K : List Z → ℝ} (hK : M.IsSequentialEquilibrium z (μ : Measure M.AState) K),
      (fun h => (⟨K h, M.equilibrium_mem_pi z μ hK h (mem_univ h)⟩ : ↥(Icc (0 : ℝ) M.assetCap)))
        = lo := fun hK => AntitoneBracket.eq_of_lfp_eq_gfp hf heq (hfix hK)
  funext h
  exact congrArg Subtype.val (congrFun ((key hK).trans (key hK').symm) h)

end KSModel

/-! ### The representative agent -/

variable [Unique E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)

/-- **Representative-agent uniqueness from a point mass, conditional on B3**: the expectations map
reverses order (proved); if in addition its bracket bottom is a positive fraction of the top and its
square satisfies the elasticity bound with `c < 1`, the sequential equilibrium from the point mass
is unique. -/
theorem crra_rep_unique_of_concave (hγ1 : γ ≤ 1)
    (hLbox : T.clampLab (V.efficiency default) = V.efficiency default)
    (hsl : ∀ (z : Z) (P : List Z → ℝ × ℝ) (n : ℕ), (crraModel V T hγ).SlackOf z P
      ((((crraModel V T hγ).household z P).bellman)^[n] 0))
    (hcap : ∀ (z : Z) (P : List Z → ℝ × ℝ) (n : ℕ) (s : (crraModel V T hγ).State),
      (crraModel V T hγ).policyOf z P ((((crraModel V T hγ).household z P).bellman)^[n] 0) s
        < (crraModel V T hγ).assetCap)
    (z₀ : Z) (x₀ : (crraModel V T hγ).AState)
    (hpos : ∃ t₀ : ℝ, 0 < t₀ ∧
      t₀ • (fun h => (OrderHom.gfp (AntitoneBracket.sq
        (expMap_antitone_dirac V T hγ hγ1 hLbox hsl hcap z₀ x₀)) h : ℝ))
        ≤ fun h => (OrderHom.lfp (AntitoneBracket.sq
          (expMap_antitone_dirac V T hγ hγ1 hLbox hsl hcap z₀ x₀)) h : ℝ))
    {c : ℝ} (hc : c < 1)
    (hel : ∀ t ∈ Ioo (0 : ℝ) 1,
      (1 - c * (1 - t)) • (fun h => (OrderHom.gfp (AntitoneBracket.sq
        (expMap_antitone_dirac V T hγ hγ1 hLbox hsl hcap z₀ x₀)) h : ℝ))
        ≤ fun h => (AntitoneBracket.sq (expMap_antitone_dirac V T hγ hγ1 hLbox hsl hcap z₀ x₀)
          (KSModel.toCap (M := crraModel V T hγ) (t • fun h => (OrderHom.gfp (AntitoneBracket.sq
            (expMap_antitone_dirac V T hγ hγ1 hLbox hsl hcap z₀ x₀)) h : ℝ))) h : ℝ))
    {K K' : List Z → ℝ}
    (hK : (crraModel V T hγ).IsSequentialEquilibrium z₀ (Measure.dirac x₀) K)
    (hK' : (crraModel V T hγ).IsSequentialEquilibrium z₀ (Measure.dirac x₀) K') : K = K' := by
  have hf := expMap_antitone_dirac V T hγ hγ1 hLbox hsl hcap z₀ x₀
  refine KSModel.unique_of_antitone_at (μ := diracProba x₀) hf
    (fun hK => (KSModel.expMap_eq_iff z₀ (diracProba x₀) _).2 hK) hpos ?_ hK hK'
  exact concave_of_elasticity (g := fun P h => (AntitoneBracket.sq hf
    (KSModel.toCap (M := crraModel V T hγ) P) h : ℝ)) hc hel

end KrusellSmith

end LeanEconomics
