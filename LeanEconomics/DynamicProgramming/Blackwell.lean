/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Blackwell's sufficient conditions

An operator on bounded continuous functions that is *monotone* and *discounts* is a
contraction. This is the standard route to showing that a Bellman operator has a unique
fixed point: verifying monotonicity and discounting is elementary, whereas verifying the
contraction property directly is not.

The setting is the space `S →ᵇ ℝ` of bounded continuous real-valued functions on a state
space `S`, with the supremum norm. It is already a complete metric space, which is what
the Banach fixed point theorem needs.

## Main definitions

* `LeanEconomics.Blackwell β T` : `T` is monotone and discounts at rate `β`.
* `LeanEconomics.Blackwell.valueFunction` : the unique fixed point of `T`.

## Main results

* `LeanEconomics.Blackwell.contractingWith` : Blackwell's conditions imply `T` is a
  `β`-contraction.
* `LeanEconomics.Blackwell.isFixedPt_valueFunction`,
  `LeanEconomics.Blackwell.eq_valueFunction` : the value function is the unique solution
  of the fixed point equation `T v = v`.
* `LeanEconomics.Blackwell.tendsto_iterate_valueFunction` : value function iteration
  converges to it, from any starting guess.
* `LeanEconomics.Blackwell.norm_iterate_sub_valueFunction_le` : the geometric error bound
  `‖Tⁿ v - v*‖ ≤ βⁿ / (1 - β) * ‖T v - v‖`, which is the stopping rule used in practice.

## Examples

* `LeanEconomics.Blackwell.affine` : the affine operator `v ↦ f + β • v` satisfies the
  conditions. This is the degenerate case of a Bellman operator in which the agent has no
  choice to make, and it witnesses that the hypotheses are consistent.

## References

* Stokey, Lucas and Prescott, *Recursive Methods in Economic Dynamics*, theorem 3.3.
* Blackwell, *Discounted dynamic programming*, Ann. Math. Statist. 36 (1965).
-/

open scoped NNReal
open Filter Topology

namespace BoundedContinuousFunction

variable {S : Type*} [TopologicalSpace S]

/-- Any bounded continuous function is dominated by any other one shifted up by the
distance between them. -/
theorem le_add_const_norm_sub (v w : S →ᵇ ℝ) : v ≤ w + const S ‖v - w‖ := by
  rw [← sub_le_iff_le_add']
  exact sub_nonneg.mp (norm_sub_nonneg (v - w))

end BoundedContinuousFunction

namespace LeanEconomics

open BoundedContinuousFunction

variable {S : Type*} [TopologicalSpace S]

/-- **Blackwell's sufficient conditions** for an operator on bounded continuous functions
to be a contraction of modulus `β`.

`monotone` says a pointwise larger continuation value cannot lower the operator's value;
`discounting` says that raising the continuation value everywhere by a constant `c` raises
the operator's value by at most `β * c`. For a Bellman operator both are immediate: the
first because the objective is increasing in the continuation value, the second because
the continuation value enters multiplied by the discount factor. -/
structure Blackwell (β : ℝ≥0) (T : (S →ᵇ ℝ) → (S →ᵇ ℝ)) : Prop where
  /-- A pointwise larger continuation value gives a pointwise larger image. -/
  monotone : Monotone T
  /-- Adding a constant `c ≥ 0` to the continuation value raises the image by at most
  `β * c`. -/
  discounting : ∀ (v : S →ᵇ ℝ) (c : ℝ), 0 ≤ c → T (v + const S c) ≤ T v + const S (β * c)

namespace Blackwell

variable {β : ℝ≥0} {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)}

/-- The one-sided bound at the heart of Blackwell's argument: `T v` cannot exceed `T w`
by more than `β` times the distance between `v` and `w`. -/
theorem apply_le_add_const (h : Blackwell β T) (v w : S →ᵇ ℝ) :
    T v ≤ T w + const S (β * ‖v - w‖) :=
  (h.monotone (le_add_const_norm_sub v w)).trans (h.discounting w _ (norm_nonneg _))

/-- Blackwell's conditions make `T` Lipschitz with constant `β` in the supremum norm. -/
theorem norm_sub_le (h : Blackwell β T) (v w : S →ᵇ ℝ) : ‖T v - T w‖ ≤ β * ‖v - w‖ := by
  rw [norm_le (by positivity)]
  intro x
  have h₁ : T v x ≤ T w x + β * ‖v - w‖ := by simpa using h.apply_le_add_const v w x
  have h₂ : T w x ≤ T v x + β * ‖w - v‖ := by simpa using h.apply_le_add_const w v x
  rw [norm_sub_rev w v] at h₂
  rw [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem lipschitzWith (h : Blackwell β T) : LipschitzWith β T :=
  LipschitzWith.of_dist_le_mul fun v w => by
    simpa only [dist_eq_norm] using h.norm_sub_le v w

/-- **Blackwell's theorem**: a monotone operator that discounts at rate `β < 1` is a
contraction of modulus `β`. -/
theorem contractingWith (h : Blackwell β T) (hβ : β < 1) : ContractingWith β T :=
  ⟨hβ, h.lipschitzWith⟩

section ValueFunction

variable (h : Blackwell β T) (hβ : β < 1)

/-- The **value function**: the unique fixed point of an operator satisfying Blackwell's
conditions, obtained from the Banach fixed point theorem. -/
noncomputable def valueFunction : S →ᵇ ℝ :=
  ContractingWith.fixedPoint T (h.contractingWith hβ)

/-- The value function solves the fixed point equation. -/
theorem isFixedPt_valueFunction : T (h.valueFunction hβ) = h.valueFunction hβ :=
  (h.contractingWith hβ).fixedPoint_isFixedPt

/-- The value function is the *only* solution of the fixed point equation. -/
theorem eq_valueFunction {v : S →ᵇ ℝ} (hv : T v = v) : v = h.valueFunction hβ :=
  (h.contractingWith hβ).fixedPoint_unique hv

/-- **Value function iteration converges**, from any starting guess. -/
theorem tendsto_iterate_valueFunction (v : S →ᵇ ℝ) :
    Tendsto (fun n => T^[n] v) atTop (𝓝 (h.valueFunction hβ)) :=
  (h.contractingWith hβ).tendsto_iterate_fixedPoint v

/-- The geometric error bound for value function iteration: after `n` iterations from a
guess `v`, the distance to the value function is at most `βⁿ / (1 - β)` times the size of
the first update. This is the a priori bound behind the usual stopping rule. -/
theorem norm_iterate_sub_valueFunction_le (v : S →ᵇ ℝ) (n : ℕ) :
    ‖T^[n] v - h.valueFunction hβ‖ ≤ (β : ℝ) ^ n / (1 - β) * ‖T v - v‖ := by
  have key := (h.contractingWith hβ).apriori_dist_iterate_fixedPoint_le v n
  rw [dist_eq_norm, dist_eq_norm, norm_sub_rev v (T v)] at key
  calc ‖T^[n] v - h.valueFunction hβ‖ ≤ ‖T v - v‖ * (β : ℝ) ^ n / (1 - β) := key
    _ = (β : ℝ) ^ n / (1 - β) * ‖T v - v‖ := by ring

end ValueFunction

/-- The affine operator `v ↦ f + β • v`, a dynamic program with a single feasible action,
satisfies Blackwell's conditions. -/
theorem affine (f : S →ᵇ ℝ) (β : ℝ≥0) :
    Blackwell β (fun v => f + (β : ℝ) • v) where
  monotone := by
    intro v w hvw x
    have hx : v x ≤ w x := by simpa using hvw x
    have hβ : (0 : ℝ) ≤ β := β.coe_nonneg
    have : f x + (β : ℝ) * v x ≤ f x + (β : ℝ) * w x := by nlinarith
    simpa using this
  discounting := by
    intro v c _
    refine le_of_eq ?_
    ext x
    simp only [coe_add, coe_smul, const_apply, Pi.add_apply, smul_eq_mul]
    ring

end Blackwell

/-! ### Monotonicity of the value function

If the operator preserves monotone functions then so does its fixed point, because the
monotone functions are a *closed* subset of `S →ᵇ ℝ` and value function iteration converges
in norm. Nothing about the fixed point itself is needed, only that the property is closed
and preserved. This is the standard route to comparative statics. -/

section Monotone

variable [Preorder S]

/-- The monotone bounded continuous functions form a closed set: a supremum-norm limit of
monotone functions is monotone, since evaluation at a point is continuous. -/
theorem isClosed_monotone : IsClosed {v : S →ᵇ ℝ | Monotone ⇑v} := by
  have heq : {v : S →ᵇ ℝ | Monotone ⇑v}
      = ⋂ (x : S) (y : S) (_ : x ≤ y), {v : S →ᵇ ℝ | v x ≤ v y} := by
    ext v; simp [Monotone]
  rw [heq]
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ => ?_
  exact isClosed_le (BoundedContinuousFunction.lipschitz_eval_const x).continuous
    (BoundedContinuousFunction.lipschitz_eval_const y).continuous

/-- **The value function is monotone** whenever the operator preserves monotonicity. -/
theorem Blackwell.monotone_valueFunction {β : ℝ≥0} {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)}
    (h : Blackwell β T) (hβ : β < 1)
    (hT : ∀ v : S →ᵇ ℝ, Monotone ⇑v → Monotone ⇑(T v)) :
    Monotone ⇑(h.valueFunction hβ) := by
  have hiter : ∀ n : ℕ, Monotone ⇑(T^[n] (0 : S →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => intro x y _; simp
    | succ k ih => rw [Function.iterate_succ_apply']; exact hT _ ih
  exact isClosed_monotone.mem_of_tendsto (h.tendsto_iterate_valueFunction hβ 0)
    (Filter.Eventually.of_forall hiter)

end Monotone

/-! ### Concavity of the value function

The same closed-set argument as for monotonicity, and the reason it is wanted is the agent
distribution. Defining a distribution over states needs the optimal policy to be a
*function*, and `exists_optimal_action` only gives existence of a maximiser. Uniqueness
comes from strict concavity of the objective in the action, which needs the continuation
value to be concave -- that is, the value function. So this is the first link in the chain
from the value function to the stationary distribution. -/

section Concave

variable {S : Type*} [TopologicalSpace S] [AddCommMonoid S] [Module ℝ S]

/-- The concave bounded continuous functions form a closed set. -/
theorem isClosed_concaveOn : IsClosed {v : S →ᵇ ℝ | ConcaveOn ℝ Set.univ ⇑v} := by
  have heq : {v : S →ᵇ ℝ | ConcaveOn ℝ Set.univ ⇑v}
      = ⋂ (p : S × S × ℝ × ℝ) (_ : 0 ≤ p.2.2.1 ∧ 0 ≤ p.2.2.2 ∧ p.2.2.1 + p.2.2.2 = 1),
          {v : S →ᵇ ℝ | p.2.2.1 • v p.1 + p.2.2.2 • v p.2.1
            ≤ v (p.2.2.1 • p.1 + p.2.2.2 • p.2.1)} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · rintro ⟨-, hv⟩ p ⟨ha, hb, hab⟩
      exact hv (Set.mem_univ _) (Set.mem_univ _) ha hb hab
    · intro hv
      refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
      exact hv (x, y, a, b) ⟨ha, hb, hab⟩
  rw [heq]
  refine isClosed_iInter fun p => isClosed_iInter fun _ => ?_
  exact isClosed_le
    ((((BoundedContinuousFunction.lipschitz_eval_const p.1).continuous).const_smul p.2.2.1).add
      (((BoundedContinuousFunction.lipschitz_eval_const p.2.1).continuous).const_smul p.2.2.2))
    (BoundedContinuousFunction.lipschitz_eval_const
      (p.2.2.1 • p.1 + p.2.2.2 • p.2.1)).continuous

/-- **The value function is concave** whenever the operator preserves concavity. -/
theorem Blackwell.concaveOn_valueFunction {β : ℝ≥0} {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)}
    (h : Blackwell β T) (hβ : β < 1)
    (hT : ∀ v : S →ᵇ ℝ, ConcaveOn ℝ Set.univ ⇑v → ConcaveOn ℝ Set.univ ⇑(T v)) :
    ConcaveOn ℝ Set.univ ⇑(h.valueFunction hβ) := by
  have hiter : ∀ n : ℕ, ConcaveOn ℝ Set.univ ⇑(T^[n] (0 : S →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact ⟨convex_univ, fun x _ y _ a b _ _ _ => by simp⟩
    | succ k ih => rw [Function.iterate_succ_apply']; exact hT _ ih
  exact isClosed_concaveOn.mem_of_tendsto (h.tendsto_iterate_valueFunction hβ 0)
    (Filter.Eventually.of_forall hiter)

end Concave

end LeanEconomics
