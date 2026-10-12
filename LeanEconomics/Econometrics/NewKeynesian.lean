/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The state of a New Keynesian model

Corrected Proposition 2′ needs the state transition to contract for every shock. This file records
what the New Keynesian benchmark contributes to that, in its nonlinear form.

* **Rotemberg pricing** (`RotembergNK`). The nonlinear equilibrium conditions (Euler equation,
  Rotemberg Phillips curve, labour supply, production, resource constraint with the quadratic
  price-adjustment cost, Taylor rule) are stated for a Markov policy `h` from the exogenous state
  `z = (log A, v)` to the allocation. `RotembergNK.conds_congr` shows the conditions at `z` depend
  on `h` only through `h z` and the next-period values `h (next z e)`: no past allocation enters,
  because the model has no predetermined endogenous variable. So in a Markov equilibrium the state
  is the exogenous shock vector, whose transition is `RotembergNK.next`, independent of `h`
  (`RotembergNK.statePath_eq`), and contracts for every shock in the max-norm with factor
  `max |ρₐ| |ρᵥ|` (`RotembergNK.next_contraction`), globally.
* **Exogenous AR(1) vectors** (`arStep_contraction`): `z' = ρ ⊙ z + ε` contracts in the sup norm
  with factor any `c ≥ |ρᵢ|`.
* **Calvo pricing** (`hasDerivAt_dispersionStep`, `dispersionStep_deriv_at_zeroInflation`). Price
  dispersion `Δ' = (1 - θ) p*^(-ε) + θ Π^ε Δ` is an endogenous state; its own derivative is
  `θ Π^ε`, which is the Calvo parameter `θ` at zero inflation.

What is NOT proved here is the existence (or uniqueness) of a Markov equilibrium of the nonlinear
model. That is assumed, as FRS's framework assumes a policy function exists; with a zero lower
bound on the interest rate it is known to fail to be unique (Benhabib, Schmitt-Grohé and Uribe
2001).
-/

open MeasureTheory Real

namespace LeanEconomics

namespace ApproxLikelihood

/-! ### Exogenous autoregressive states -/

/-- One step of a vector of independent AR(1) processes. -/
def arStep {n : ℕ} (ρ : Fin n → ℝ) (z ε : Fin n → ℝ) : Fin n → ℝ := fun i ↦ ρ i * z i + ε i

/-- **A vector AR(1) contracts for every shock** in the sup norm, with factor any bound on the
autoregressive coefficients. -/
theorem arStep_contraction {n : ℕ} {ρ : Fin n → ℝ} {c : ℝ} (hc : 0 ≤ c) (hρ : ∀ i, |ρ i| ≤ c)
    (z z' ε : Fin n → ℝ) : ‖arStep ρ z ε - arStep ρ z' ε‖ ≤ c * ‖z - z'‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i ↦ ?_
  have hi : ‖(z - z') i‖ ≤ ‖z - z'‖ := norm_le_pi_norm (z - z') i
  simp only [Pi.sub_apply, arStep, Real.norm_eq_abs] at hi ⊢
  rw [show ρ i * z i + ε i - (ρ i * z' i + ε i) = ρ i * (z i - z' i) by ring, abs_mul]
  exact mul_le_mul (hρ i) hi (abs_nonneg _) hc

/-! ### The nonlinear New Keynesian model with Rotemberg pricing -/

/-- Parameters: discount factor `β`, inverse intertemporal elasticity `σ`, inverse Frisch
elasticity `φ`, labour disutility `χ`, elasticity of substitution between goods `ε`,
Rotemberg adjustment cost `ψ`, Taylor-rule intercept `Rbar`, inflation and output responses
`φπ`, `φy`, output target `Ybar`, and the persistence of technology and the monetary shock. -/
structure RotembergNK where
  β : ℝ
  σ : ℝ
  φ : ℝ
  χ : ℝ
  ε : ℝ
  ψ : ℝ
  Rbar : ℝ
  φπ : ℝ
  φy : ℝ
  Ybar : ℝ
  ρa : ℝ
  ρv : ℝ

/-- The allocation in a period: consumption, gross inflation, gross nominal rate, output, hours
and the real wage. -/
structure Alloc where
  C : ℝ
  infl : ℝ
  R : ℝ
  Y : ℝ
  N : ℝ
  w : ℝ

namespace RotembergNK

variable (M : RotembergNK)

/-- The exogenous transition: `z = (log A, v)`, each an AR(1). -/
def next (z : ℝ × ℝ) (e : ℝ × ℝ) : ℝ × ℝ := (M.ρa * z.1 + e.1, M.ρv * z.2 + e.2)

/-- **The equilibrium conditions at the exogenous state `z`**, for a Markov policy `h` and a law
`ν` of next period's innovations. The current allocation is `h z`; expectations are integrals of
next period's allocation `h (next z e)`. No past allocation appears. -/
def conds (ν : Measure (ℝ × ℝ)) (h : ℝ × ℝ → Alloc) (z : ℝ × ℝ) : Prop :=
  let x := h z
  let A := Real.exp z.1
  -- consumption Euler equation
  1 = M.β * x.R * ∫ e, (((h (M.next z e)).C / x.C) ^ (-M.σ)) / (h (M.next z e)).infl ∂ν ∧
  -- Rotemberg Phillips curve
  (1 - M.ε) + M.ε * (x.w / A) - M.ψ * (x.infl - 1) * x.infl
      + M.β * M.ψ * ∫ e, ((h (M.next z e)).C / x.C) ^ (-M.σ) * ((h (M.next z e)).infl - 1)
          * (h (M.next z e)).infl * ((h (M.next z e)).Y / x.Y) ∂ν = 0 ∧
  -- labour supply
  x.w = M.χ * x.N ^ M.φ * x.C ^ M.σ ∧
  -- production
  x.Y = A * x.N ∧
  -- resource constraint, net of the quadratic price-adjustment cost
  x.C = x.Y * (1 - M.ψ / 2 * (x.infl - 1) ^ 2) ∧
  -- Taylor rule with monetary shock `v = z.2`
  x.R = M.Rbar * x.infl ^ M.φπ * (x.Y / M.Ybar) ^ M.φy * Real.exp z.2

/-- A **Markov equilibrium**: a policy from the exogenous state to the allocation satisfying the
equilibrium conditions at every state. Existence is assumed, not proved. -/
def IsMarkovEquilibrium (ν : Measure (ℝ × ℝ)) (h : ℝ × ℝ → Alloc) : Prop := ∀ z, M.conds ν h z

/-- **No predetermined endogenous variable.** The equilibrium conditions at `z` depend on the
policy only through its value at `z` and its values at next period's states `next z e`. -/
theorem conds_congr (ν : Measure (ℝ × ℝ)) {h₁ h₂ : ℝ × ℝ → Alloc} (z : ℝ × ℝ)
    (h0 : h₁ z = h₂ z) (h1 : ∀ e, h₁ (M.next z e) = h₂ (M.next z e)) :
    M.conds ν h₁ z ↔ M.conds ν h₂ z := by
  have hf : (fun e ↦ h₁ (M.next z e)) = fun e ↦ h₂ (M.next z e) := funext h1
  simp only [conds, h0]
  rw [show (fun e ↦ (((h₁ (M.next z e)).C / (h₂ z).C) ^ (-M.σ)) / (h₁ (M.next z e)).infl)
      = (fun e ↦ (((h₂ (M.next z e)).C / (h₂ z).C) ^ (-M.σ)) / (h₂ (M.next z e)).infl) by
        funext e; rw [h1 e]]
  rw [show (fun e ↦ ((h₁ (M.next z e)).C / (h₂ z).C) ^ (-M.σ) * ((h₁ (M.next z e)).infl - 1)
          * (h₁ (M.next z e)).infl * ((h₁ (M.next z e)).Y / (h₂ z).Y))
      = (fun e ↦ ((h₂ (M.next z e)).C / (h₂ z).C) ^ (-M.σ) * ((h₂ (M.next z e)).infl - 1)
          * (h₂ (M.next z e)).infl * ((h₂ (M.next z e)).Y / (h₂ z).Y)) by
        funext e; rw [h1 e]]

/-- The state path along a shock path: the exogenous transition alone. -/
def statePath (z₀ : ℝ × ℝ) (e : ℕ → ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => z₀
  | t + 1 => M.next (statePath z₀ e t) (e t)

/-- **The state of a Markov equilibrium is the exogenous shock vector.** Along any shock path the
allocation is `h` of the exogenous state, the conditions hold at every date, and the state evolves
by the exogenous transition, whatever the policy. -/
theorem statePath_eq (ν : Measure (ℝ × ℝ)) {h : ℝ × ℝ → Alloc} (hh : M.IsMarkovEquilibrium ν h)
    (z₀ : ℝ × ℝ) (e : ℕ → ℝ × ℝ) (t : ℕ) :
    M.conds ν h (M.statePath z₀ e t) ∧
      M.statePath z₀ e (t + 1) = M.next (M.statePath z₀ e t) (e t) :=
  ⟨hh _, rfl⟩

/-- **The New Keynesian state contracts for every shock**, globally, in the max-norm, with factor
`max |ρₐ| |ρᵥ|`. -/
theorem next_contraction (z z' e : ℝ × ℝ) :
    ‖M.next z e - M.next z' e‖ ≤ max |M.ρa| |M.ρv| * ‖z - z'‖ := by
  have hc : 0 ≤ max |M.ρa| |M.ρv| := le_max_of_le_left (abs_nonneg _)
  rw [Prod.norm_def, Prod.norm_def]
  simp only [next, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
  rw [show M.ρa * z.1 + e.1 - (M.ρa * z'.1 + e.1) = M.ρa * (z.1 - z'.1) by ring,
    show M.ρv * z.2 + e.2 - (M.ρv * z'.2 + e.2) = M.ρv * (z.2 - z'.2) by ring, abs_mul, abs_mul]
  refine max_le ?_ ?_
  · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (abs_nonneg _) hc
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (abs_nonneg _) hc

end RotembergNK

/-! ### Calvo pricing: price dispersion is an endogenous state -/

/-- One step of price dispersion under Calvo pricing, with reset-price ratio `pstar`, gross
inflation `infl`, Calvo parameter `θ` and elasticity `ε`. -/
noncomputable def dispersionStep (θ ε pstar infl Δ : ℝ) : ℝ :=
  (1 - θ) * pstar ^ (-ε) + θ * infl ^ ε * Δ

/-- The own derivative of price dispersion is `θ Π^ε`. -/
theorem hasDerivAt_dispersionStep (θ ε pstar infl Δ : ℝ) :
    HasDerivAt (fun Δ ↦ dispersionStep θ ε pstar infl Δ) (θ * infl ^ ε) Δ := by
  unfold dispersionStep
  simpa using ((hasDerivAt_id Δ).const_mul (θ * infl ^ ε)).const_add ((1 - θ) * pstar ^ (-ε))

/-- **At zero inflation the own coefficient of price dispersion is the Calvo parameter `θ`.** -/
theorem dispersionStep_deriv_at_zeroInflation (θ ε pstar Δ : ℝ) :
    HasDerivAt (fun Δ ↦ dispersionStep θ ε pstar 1 Δ) θ Δ := by
  simpa using hasDerivAt_dispersionStep θ ε pstar 1 Δ

end ApproxLikelihood

end LeanEconomics
