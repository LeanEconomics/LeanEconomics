/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Fixed points: order, eventual contraction, approximation error, concavity

Four abstract results from Sargent and Stachurski, *Dynamic Programming* (Vol. 1 Ch. 2, 6, 7;
Vol. 2 Ch. 9), stated on bare metric or ordered spaces so that any operator in this development
can use them.

* **Parametric monotonicity** (Vol. 1, Prop. 2.2.7): if `T` dominates `S` pointwise, is
  order-preserving and globally stable, then `T`'s fixed point dominates every fixed point of
  `S`. `Blackwell.valueFunction_le` is the Blackwell-operator instance; this is the general
  statement, and the proof is the same three lines: `u = S u ≤ T u`, iterate, pass to the limit.
* **Eventually contracting maps** (Vol. 1, Thm. 6.1.5): if some iterate `f^[k]` is a contraction
  then `f` has a unique fixed point and `f^[n] x` converges to it from every `x`. This is what
  the spectral-radius conditions of Ma–Toda and Pröhl deliver, and it generalises Blackwell.
* **Fitted value iteration error bound** (Vol. 2, Thm. 9.1.3): with `T` and `T_σ` contractions
  of modulus `β` and a nonexpansive approximation `L`, the value of the greedy policy at
  termination is within `2(β e_N + d(L T v_N, T v_N))/(1-β)` of the optimum. This is the
  value-error input to Li's (2015) policy error bound.
* **Uniqueness for increasing concave maps** (Vol. 1, Prop. 7.1.2, the uniqueness half): an
  increasing concave self-map of `(0, ∞)` with a point below `x` mapped strictly up has at most
  one fixed point at or above that point. Du's theorem (Thm. 7.1.3) is the multidimensional
  version; only the one-dimensional uniqueness is recorded here.
-/

open Filter Topology Function Set

namespace LeanEconomics

/-! ### Parametric monotonicity -/

/-- **Ordered fixed points from a dominated operator** (Sargent–Stachurski Prop. 2.2.7). -/
theorem fixedPoint_le_of_dominates {V : Type*} [Preorder V] [TopologicalSpace V]
    [OrderClosedTopology V] {S T : V → V} (hST : ∀ u, S u ≤ T u) (hT : Monotone T)
    {uT : V} (hstab : ∀ u, Tendsto (fun n => T^[n] u) atTop (𝓝 uT))
    {uS : V} (hS : IsFixedPt S uS) : uS ≤ uT := by
  have hiter : ∀ n : ℕ, uS ≤ T^[n] uS := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc uS = S uS := hS.symm
        _ ≤ T uS := hST uS
        _ ≤ T (T^[k] uS) := hT ih
  exact ge_of_tendsto' (hstab uS) hiter

/-! ### Eventually contracting maps -/

/-- **A map with a contracting iterate has a unique fixed point.** -/
theorem eventuallyContracting_fixedPoint_unique {α : Type*} [MetricSpace α] {f : α → α}
    {K : NNReal} {k : ℕ} (hf : ContractingWith K f^[k]) {x y : α} (hx : IsFixedPt f x)
    (hy : IsFixedPt f y) : x = y :=
  hf.fixedPoint_unique' (hx.iterate k) (hy.iterate k)

/-- **Global stability of an eventually contracting map** (Sargent–Stachurski Thm. 6.1.5): the
iterates `f^[n] x` converge, from every `x`, to the fixed point of `f`. The `k` residue classes
of `n` mod `k` are each an orbit of the contraction `f^[k]`. -/
theorem tendsto_iterate_of_eventuallyContracting {α : Type*} [MetricSpace α] [Nonempty α]
    [CompleteSpace α] {f : α → α} {K : NNReal} {k : ℕ} (hk : 0 < k)
    (hf : ContractingWith K f^[k]) (x : α) :
    Tendsto (fun n => f^[n] x) atTop (𝓝 (hf.fixedPoint f^[k])) := by
  set x₀ := hf.fixedPoint f^[k] with hx₀
  have hfix : IsFixedPt f x₀ := hf.isFixedPt_fixedPoint_iterate
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- each residue class converges
  have hres : ∀ r : ℕ, ∃ N : ℕ, ∀ q ≥ N, dist (f^[k * q + r] x) x₀ < ε := by
    intro r
    have := Metric.tendsto_atTop.mp (hf.tendsto_iterate_fixedPoint (f^[r] x)) ε hε
    obtain ⟨N, hN⟩ := this
    refine ⟨N, fun q hq => ?_⟩
    have h1 : f^[k * q + r] x = (f^[k])^[q] (f^[r] x) := by
      rw [Function.iterate_add_apply, Function.iterate_mul]
    rw [h1]
    exact hN q hq
  choose N hN using hres
  refine ⟨k * ((Finset.range k).sup N + 1), fun n hn => ?_⟩
  have hdecomp : n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
  have hmod : n % k < k := Nat.mod_lt n hk
  have hq : (Finset.range k).sup N ≤ n / k := by
    have : (Finset.range k).sup N + 1 ≤ n / k := by
      rw [Nat.le_div_iff_mul_le hk]
      linarith
    omega
  have hNr : N (n % k) ≤ (Finset.range k).sup N :=
    Finset.le_sup (f := N) (Finset.mem_range.mpr hmod)
  rw [hdecomp]
  exact hN (n % k) (n / k) (le_trans hNr hq)

/-! ### The fitted value iteration error bound -/

/-- **Fitted value iteration: the greedy policy at termination is near-optimal**
(Sargent–Stachurski Vol. 2, Thm. 9.1.3). `T` is the Bellman operator with fixed point `v*`,
`Tσ` the policy operator of the `vN`-greedy policy with fixed point `vσ`, both contractions of
modulus `β`; `L` is the approximation operator, `vN = L (T vP)` the last iterate with
`eN = d(vN, vP)` the final step. -/
theorem dist_fixedPoint_le_of_fittedVFI {V : Type*} [MetricSpace V] {T Tσ L : V → V}
    {β : ℝ} (hβ1 : β < 1)
    (hT : ∀ v w, dist (T v) (T w) ≤ β * dist v w)
    (hTσ : ∀ v w, dist (Tσ v) (Tσ w) ≤ β * dist v w)
    (hL : ∀ v w, dist (L v) (L w) ≤ dist v w)
    {vstar vσ vN vP : V} (hstar : T vstar = vstar) (hσ : Tσ vσ = vσ)
    (hgreedy : Tσ vN = T vN) (hstep : vN = L (T vP)) :
    dist vstar vσ ≤ 2 / (1 - β) * (β * dist vN vP + dist (L (T vN)) (T vN)) := by
  have hroom : 0 < 1 - β := by linarith
  -- the residual at the last iterate
  have hres : dist (T vN) vN ≤ dist (T vN) (L (T vN)) + β * dist vN vP := by
    calc dist (T vN) vN ≤ dist (T vN) (L (T vN)) + dist (L (T vN)) vN := dist_triangle _ _ _
      _ = dist (T vN) (L (T vN)) + dist (L (T vN)) (L (T vP)) := by rw [hstep]
      _ ≤ dist (T vN) (L (T vN)) + dist (T vN) (T vP) := by
          have := hL (T vN) (T vP)
          linarith
      _ ≤ dist (T vN) (L (T vN)) + β * dist vN vP := by
          have := hT vN vP
          linarith
  -- distance to the true value function
  have h1 : (1 - β) * dist vstar vN ≤ dist (T vN) vN := by
    have := dist_triangle vstar (T vN) vN
    have h := hT vstar vN
    rw [hstar] at h
    nlinarith
  -- distance to the value of the greedy policy
  have h2 : (1 - β) * dist vN vσ ≤ dist (T vN) vN := by
    have := dist_triangle vN (T vN) vσ
    have h := hTσ vN vσ
    rw [hσ, hgreedy] at h
    have hsym : dist (T vN) vN = dist vN (T vN) := dist_comm _ _
    nlinarith
  have hsum : (1 - β) * dist vstar vσ ≤ 2 * dist (T vN) vN := by
    have := dist_triangle vstar vN vσ
    nlinarith
  rw [dist_comm (L (T vN)) (T vN)]
  rw [show 2 / (1 - β) * (β * dist vN vP + dist (T vN) (L (T vN)))
      = (2 * (β * dist vN vP + dist (T vN) (L (T vN)))) / (1 - β) by ring,
    le_div_iff₀ hroom]
  nlinarith

/-! ### Increasing concave self-maps -/

/-- **Uniqueness of the fixed point of an increasing concave map** (Sargent–Stachurski
Prop. 7.1.2, uniqueness half): if `g` is increasing and concave on `(0, ∞)`, `x ≤ y` are fixed
points, and some `a ≤ x` is mapped strictly up, then `x = y`. -/
theorem eq_of_fixedPt_of_concaveOn {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Ioi (0 : ℝ)) g)
    {x y a : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxy : x ≤ y) (hga : a < g a)
    (hx : g x = x) (hy : g y = y) : x = y := by
  by_contra hne
  have hlt : x < y := lt_of_le_of_ne hxy hne
  -- write `x` as a convex combination of `a` and `y`
  set μ : ℝ := (y - x) / (y - a) with hμ
  have hya : 0 < y - a := by linarith
  have hμ0 : 0 < μ := div_pos (by linarith) hya
  have hμ1 : μ ≤ 1 := by rw [hμ, div_le_one hya]; linarith
  have hcomb : μ * a + (1 - μ) * y = x := by
    rw [hμ]; field_simp; ring
  have hconc := hg.2 (mem_Ioi.mpr ha) (mem_Ioi.mpr (lt_of_lt_of_le ha (le_trans hax hxy)))
    hμ0.le (by linarith : 0 ≤ 1 - μ) (by ring)
  simp only [smul_eq_mul, hcomb, hx, hy] at hconc
  -- `x ≥ μ g a + (1-μ) y > μ a + (1-μ) y = x`
  nlinarith

end LeanEconomics
