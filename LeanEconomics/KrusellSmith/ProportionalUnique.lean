/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Policy

/-!
# The proportional economy: uniqueness among all equilibria, by Negishi weights

Route 3 of the heterogeneous-household programme (`CROSS_SECTION_PLAN.md`): a monotonicity
argument weighted by marginal utility. Households have **permanent** efficiency types; type `e`
has efficiency `σ_e L` and starts with assets `σ_e k₀`. A **proportional equilibrium**
(`PropEq`) is a capital path `K` along which type `e`, holding `σ_e K_h`, optimally saves
`σ_e K_{child}` (`ProportionalEquilibrium.lean` builds one).

**Theorem** (`PropEq.eq_of_types`). Let `K'` be the capital path of *any* allocation in which
every type saves optimally against the prices of `K'` and capital is mean assets. Then `K' = K`.
The competing allocation is not assumed proportional.

The proof compares values along the tree, with three recursions closed by one lemma
(`tree_nonneg`: a bounded function on the tree that dominates `β` times its mean over the children
is nonnegative).

* **Everyone gains at foreign prices** (`gapA_nonneg`). A household on the proportional path holds
  capital and labour in the aggregate proportion, so by the supporting-price inequality its cash is
  no lower at the prices of any other capital path. Hence `V_Q ≥ V_P` on the proportional path.
* **Values are proportional** (`W_eq`). Utility is homogeneous (`hom`:
  `u(σ_e x) = λ_e u(x) + κ_e`), so the normalised value `(V_P − κ_e / (1 − β)) / λ_e` of type `e`
  on the path solves the same linear recursion for every type.
* **The Negishi bound** (`G_le_H`). Weight type `e`'s normalised value in the `K'` allocation by
  `p_e σ_e`. By Jensen the weighted utilities are at most the utility of aggregate consumption
  `C'`; and a type with `σ ≥ 1`, at the prices of `K`, can hold `σ K'` and consume at least
  `σ C'`. So the weighted values `G` of the `K'` allocation are at most the normalised value `H`
  of that type holding `σ K'` at the prices of `K`.

At a node where the `K'` allocation is still proportional, the three give
`W ≤ G ≤ H = W`. So every type's value is the same at both price paths there, its proportional
saving attains the Bellman maximum at the prices of `K'`, and the maximiser is unique: the
allocation is proportional at the children. Induct from the root.
-/

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z)

/-- **A bounded function on the tree that dominates `β` times its mean over the children is
nonnegative.** -/
theorem tree_nonneg {f : List Z → ℝ} {B : ℝ} (hB : ∀ h, -B ≤ f h)
    (hstep : ∀ h, M.discount * ∑ z', M.aggProb (shockAt z₀ h) z' * f (z' :: h) ≤ f h)
    (h : List Z) : 0 ≤ f h := by
  have hβ0 := M.discount_pos.le
  have hB' : ∀ g, -|B| ≤ f g := fun g => (neg_le_neg (le_abs_self B)).trans (hB g)
  have hbound : ∀ n : ℕ, ∀ g : List Z, -(M.discount ^ n * |B|) ≤ f g := by
    intro n
    induction n with
    | zero => intro g; simpa using hB' g
    | succ n ih =>
      intro g
      refine le_trans ?_ (hstep g)
      have hsum : ∑ z', M.aggProb (shockAt z₀ g) z' * -(M.discount ^ n * |B|)
          ≤ ∑ z', M.aggProb (shockAt z₀ g) z' * f (z' :: g) :=
        Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left (ih _) (M.aggProb_nonneg _ _)
      rw [← Finset.sum_mul, M.aggProb_sum, one_mul] at hsum
      have := mul_le_mul_of_nonneg_left hsum hβ0
      rw [pow_succ]
      linarith
  by_contra hneg
  push Not at hneg
  have hB1 : 0 < |B| + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < -f h / (|B| + 1) from
    div_pos (by linarith) hB1) M.discount_lt_one
  have h1 := hbound n h
  rw [lt_div_iff₀ hB1, mul_add, mul_one] at hn
  linarith [pow_nonneg hβ0 n]

theorem valueFunction_eq_objective_policy (X : List Z → ℝ × ℝ) (s : M.State) :
    (M.household z₀ X).valueFunction s
      = (M.household z₀ X).objective (M.household z₀ X).valueFunction s (M.policy z₀ X s) := by
  have := M.policy_optimal z₀ X s
  rwa [(M.household z₀ X).bellman_valueFunction] at this

theorem bellmanFn_valueFunction (X : List Z → ℝ × ℝ) (s : M.State) :
    (M.household z₀ X).bellmanFn (M.household z₀ X).valueFunction s
      = (M.household z₀ X).valueFunction s :=
  congrFun (congrArg DFunLike.coe (M.household z₀ X).bellman_valueFunction) _

theorem objective_le_valueFunction (X : List Z → ℝ × ℝ) {s : M.State} {a : ℝ}
    (ha : a ∈ (M.household z₀ X).feasible s) :
    (M.household z₀ X).objective (M.household z₀ X).valueFunction s a
      ≤ (M.household z₀ X).valueFunction s := by
  have h2 := (M.household z₀ X).le_bellmanFn (M.household z₀ X).valueFunction ha
  rwa [M.bellmanFn_valueFunction z₀ X s] at h2

theorem abs_valueFunction_le (X : List Z → ℝ × ℝ) (s : M.State) :
    |(M.household z₀ X).valueFunction s| ≤ ‖(M.household z₀ X).valueFunction‖ := by
  rw [← Real.norm_eq_abs]
  exact (M.household z₀ X).valueFunction.norm_coe_le_norm s

section perm

variable [DecidableEq E]
  (hperm : ∀ z z' e e', M.idioProb z z' e e' = if e = e' then 1 else 0)

include hperm in
/-- With permanent types the expectation over next period's shocks is over the aggregate shock. -/
theorem sum_shockProb_perm (s : M.State) (a : ℝ) (F : Z × E → ℝ) :
    ∑ ze, M.shockProb z₀ ze (s, a) * F ze
      = ∑ z', M.aggProb (shockAt z₀ s.2.node) z' * F (z', s.2.idio) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [Finset.sum_eq_single s.2.idio]
  · change M.aggProb _ z' * M.idioProb _ z' s.2.idio s.2.idio * F _ = _
    rw [hperm]
    simp
  · intro e' _ he'
    change M.aggProb _ z' * M.idioProb _ z' s.2.idio e' * F _ = 0
    rw [hperm]
    simp [Ne.symm he']
  · exact fun h => absurd (Finset.mem_univ _) h

include hperm in
/-- The Bellman objective with permanent types. -/
theorem objective_perm (X : List Z → ℝ × ℝ) (v : M.State →ᵇ ℝ) {s : M.State} {a : ℝ}
    (ha : a ∈ (M.household z₀ X).feasible s) :
    (M.household z₀ X).objective v s a
      = M.utility (M.cash z₀ X s - a)
        + M.discount * ∑ z', M.aggProb (shockAt z₀ s.2.node) z'
            * v (M.clampAssets a, ⟨s.2.idio, z' :: s.2.node⟩) := by
  rw [M.objective_eq z₀ X v ha, M.sum_shockProb_perm z₀ hperm s a
    (fun ze => v (M.clampAssets a, ⟨ze.2, ze.1 :: s.2.node⟩))]

end perm

/-- **A proportional equilibrium** of an economy with permanent types: type `e` has efficiency
`σ_e L`, and holding `σ_e K_h` at node `h` it optimally saves `σ_e K_{child}`. Utility is
homogeneous along the type shares, prices support the aggregate allocation, and the bound `capK`
on aggregate capital is respected by every allocation (`bound`). -/
structure PropEq (M : KSModel Z E) (z₀ : Z) where
  /-- The mass of each type. -/
  p : E → ℝ
  p_pos : ∀ e, 0 < p e
  p_sum : ∑ e, p e = 1
  /-- Each type's share of the aggregates. -/
  σ : E → ℝ
  σ_pos : ∀ e, 0 < σ e
  σ_sum : ∑ e, p e * σ e = 1
  /-- Aggregate labour. -/
  L : ℝ
  σ_L : ∀ e, σ e * L = M.efficiency e
  lam : E → ℝ
  lam_pos : ∀ e, 0 < lam e
  κ : E → ℝ
  hom : ∀ e x, 0 < x → M.utility (σ e * x) = lam e * M.utility x + κ e
  concave : ConcaveOn ℝ (Ioi 0) M.utility
  floor_pos : 0 < M.consFloor
  borrow : M.borrowLimit = 0
  support : ∀ (z : Z) (k a : ℝ), M.grossReturn z a L * a + M.wage z a L * L
    ≤ M.grossReturn z k L * a + M.wage z k L * L
  /-- The bound on aggregate capital. -/
  capK : ℝ
  σ_cap : ∀ e, σ e * capK ≤ M.assetCap
  bound : ∀ (z : Z) (k : ℝ), k ∈ Icc 0 capK →
    M.grossReturn z k L * k + M.wage z k L * L - M.consFloor ≤ capK
  /-- The capital path. -/
  K : List Z → ℝ
  K_mem : ∀ h, K h ∈ Icc 0 capK
  prop : ∀ e h z', M.policy z₀ (fun g => (K g, L)) (M.clampAssets (σ e * K h), ⟨e, h⟩)
    = σ e * K (z' :: h)

namespace PropEq

variable {M z₀} (D : M.PropEq z₀)

/-- The prices of a capital path, with the aggregate labour of the economy. -/
def pr (J : List Z → ℝ) : List Z → ℝ × ℝ := fun g => (J g, D.L)

/-- Type `e` holding its share of capital `x` at node `h`. -/
noncomputable def hold (e : E) (x : ℝ) (h : List Z) : M.State :=
  (M.clampAssets (D.σ e * x), ⟨e, h⟩)

/-- Type `e` on the proportional path. -/
noncomputable def state (e : E) (h : List Z) : M.State := D.hold e (D.K h) h

theorem σ_mul_mem (e : E) {x : ℝ} (hx : x ∈ Icc 0 D.capK) : D.σ e * x ∈ Icc 0 M.assetCap :=
  ⟨mul_nonneg (D.σ_pos e).le hx.1,
    (mul_le_mul_of_nonneg_left hx.2 (D.σ_pos e).le).trans (D.σ_cap e)⟩

theorem hold_val (e : E) {x : ℝ} (hx : x ∈ Icc 0 D.capK) (h : List Z) :
    ((D.hold e x h).1 : ℝ) = D.σ e * x := by
  rw [hold, M.clampAssets_of_mem (D.σ_mul_mem e hx)]

/-- Aggregate resources at the prices of capital `k` when capital `x` is held. -/
noncomputable def res (z : Z) (k x : ℝ) : ℝ :=
  M.grossReturn z k D.L * x + M.wage z k D.L * D.L

/-- A type holding its share has its share of resources. -/
theorem cash_hold (J : List Z → ℝ) (e : E) {x : ℝ} (hx : x ∈ Icc 0 D.capK) (h : List Z) :
    M.cash z₀ (D.pr J) (D.hold e x h) = D.σ e * D.res (shockAt z₀ h) (J h) x := by
  change M.grossReturn (shockAt z₀ h) (J h) D.L * ((D.hold e x h).1 : ℝ)
    + M.wage (shockAt z₀ h) (J h) D.L * M.efficiency e
    - M.grossReturn (shockAt z₀ h) (J h) D.L * M.borrowLimit = _
  rw [D.hold_val e hx, D.borrow, ← D.σ_L e, res]
  ring

theorem prop' (e : E) (h : List Z) (z' : Z) :
    M.policy z₀ (D.pr D.K) (D.state e h) = D.σ e * D.K (z' :: h) := D.prop e h z'

/-- The successor of a state on the proportional path is on it. -/
theorem state_cons (e : E) (h : List Z) (z' : Z) :
    (M.clampAssets (M.policy z₀ (D.pr D.K) (D.state e h)), (⟨e, z' :: h⟩ : Label Z E))
      = D.state e (z' :: h) := by
  rw [D.prop' e h z']
  rfl

/-- The saving of a type on the proportional path is feasible at the prices of any capital path:
the household is no poorer there. -/
theorem policy_feasible (J : List Z → ℝ) (e : E) (h : List Z) :
    M.cash z₀ (D.pr D.K) (D.state e h) ≤ M.cash z₀ (D.pr J) (D.state e h)
      ∧ M.policy z₀ (D.pr D.K) (D.state e h)
        ∈ (M.household z₀ (D.pr J)).feasible (D.state e h) := by
  have hc : M.cash z₀ (D.pr D.K) (D.state e h) ≤ M.cash z₀ (D.pr J) (D.state e h) := by
    rw [state, D.cash_hold D.K e (D.K_mem h), D.cash_hold J e (D.K_mem h)]
    exact mul_le_mul_of_nonneg_left (D.support _ _ _) (D.σ_pos e).le
  exact ⟨hc, (M.policy_mem z₀ _ _).1,
    (M.policy_mem z₀ _ _).2.trans (min_le_min le_rfl (sub_le_sub_right hc _))⟩

section perm

variable [DecidableEq E]
  (hperm : ∀ z z' e e', M.idioProb z z' e e' = if e = e' then 1 else 0)

/-- The value gap of type `e` on the proportional path: prices of `J` against prices of `K`. -/
noncomputable def gapA (J : List Z → ℝ) (e : E) (h : List Z) : ℝ :=
  (M.household z₀ (D.pr J)).valueFunction (D.state e h)
    - (M.household z₀ (D.pr D.K)).valueFunction (D.state e h)

include hperm in
/-- Saving as on the proportional path, at the prices of `J`: the Bellman objective is at least
the value on the path plus the discounted mean gap at the children. -/
theorem objective_ge (J : List Z → ℝ) (e : E) (h : List Z) :
    (M.household z₀ (D.pr D.K)).valueFunction (D.state e h)
        + M.discount * ∑ z', M.aggProb (shockAt z₀ h) z' * D.gapA J e (z' :: h)
      ≤ (M.household z₀ (D.pr J)).objective (M.household z₀ (D.pr J)).valueFunction
          (D.state e h) (M.policy z₀ (D.pr D.K) (D.state e h)) := by
  obtain ⟨hc, hf⟩ := D.policy_feasible J e h
  set s := D.state e h with hs
  set a := M.policy z₀ (D.pr D.K) s with ha
  have hfP : a ∈ (M.household z₀ (D.pr D.K)).feasible s := M.policy_mem z₀ _ s
  rw [M.valueFunction_eq_objective_policy z₀ (D.pr D.K) s,
    M.objective_perm z₀ hperm _ _ hfP, M.objective_perm z₀ hperm _ _ hf]
  have hu : M.utility (M.cash z₀ (D.pr D.K) s - a) ≤ M.utility (M.cash z₀ (D.pr J) s - a) :=
    M.monotoneOn_utility (mem_Ici.2 (le_sub_comm.1 (hfP.2.trans (min_le_right _ _))))
      (mem_Ici.2 (le_sub_comm.1 (hf.2.trans (min_le_right _ _)))) (sub_le_sub_right hc _)
  have hsum : ∑ z', M.aggProb (shockAt z₀ s.2.node) z'
        * (M.household z₀ (D.pr D.K)).valueFunction (M.clampAssets a, ⟨s.2.idio, z' :: s.2.node⟩)
      + ∑ z', M.aggProb (shockAt z₀ h) z' * D.gapA J e (z' :: h)
      = ∑ z', M.aggProb (shockAt z₀ s.2.node) z'
        * (M.household z₀ (D.pr J)).valueFunction
          (M.clampAssets a, ⟨s.2.idio, z' :: s.2.node⟩) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z' _ => ?_
    have hst : (M.clampAssets a, (⟨s.2.idio, z' :: s.2.node⟩ : Label Z E))
        = D.state e (z' :: h) := D.state_cons e h z'
    rw [hst, gapA]
    change M.aggProb (shockAt z₀ h) z' * _ + _ = M.aggProb (shockAt z₀ h) z' * _
    ring
  rw [← hsum, mul_add]
  linarith

include hperm in
/-- **Everyone on the proportional path gains at foreign prices.** -/
theorem gapA_nonneg (J : List Z → ℝ) (e : E) (h : List Z) : 0 ≤ D.gapA J e h := by
  refine M.tree_nonneg z₀ (f := D.gapA J e)
    (B := ‖(M.household z₀ (D.pr J)).valueFunction‖
      + ‖(M.household z₀ (D.pr D.K)).valueFunction‖) (fun g => ?_) (fun g => ?_) h
  · have h1 := abs_le.1 (M.abs_valueFunction_le z₀ (D.pr J) (D.state e g))
    have h2 := abs_le.1 (M.abs_valueFunction_le z₀ (D.pr D.K) (D.state e g))
    rw [gapA]
    linarith
  · have h1 := D.objective_ge hperm J e g
    have h2 := M.objective_le_valueFunction z₀ (D.pr J) (D.policy_feasible J e g).2
    rw [gapA]
    linarith

/-- Aggregate consumption on the proportional path. -/
noncomputable def aggCons (h : List Z) : ℝ :=
  D.res (shockAt z₀ h) (D.K h) (D.K h) - D.K (z₀ :: h)

/-- The normalisation of type `e`'s value: undo the homogeneity of utility. -/
noncomputable def norm (e : E) (v : ℝ) : ℝ := (v - D.κ e / (1 - M.discount)) / D.lam e

omit [DecidableEq E] in
/-- The algebra of normalising a Bellman equation. -/
theorem norm_bellman (e : E) (u : ℝ) (π v : Z → ℝ) (hπ : ∑ z', π z' = 1) :
    D.norm e (D.lam e * u + D.κ e + M.discount * ∑ z', π z' * v z')
      = u + M.discount * ∑ z', π z' * D.norm e (v z') := by
  have hl := (D.lam_pos e).ne'
  have hβ : (1 - M.discount) ≠ 0 := (sub_pos.2 M.discount_lt_one).ne'
  have hsum : ∑ z', π z' * D.norm e (v z')
      = (∑ z', π z' * v z' - D.κ e / (1 - M.discount)) * (D.lam e)⁻¹ := by
    have hz : ∀ z', π z' * D.norm e (v z')
        = (π z' * v z' - π z' * (D.κ e / (1 - M.discount))) * (D.lam e)⁻¹ := fun z' => by
      rw [norm]
      ring
    rw [Finset.sum_congr rfl fun z' _ => hz z', ← Finset.sum_mul, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hπ, one_mul]
  rw [hsum, norm]
  field_simp
  ring

include hperm in
/-- **The value on the proportional path**: type `e` consumes its share of aggregate
consumption. -/
theorem value_state (e : E) (h : List Z) :
    0 < D.aggCons h ∧ (M.household z₀ (D.pr D.K)).valueFunction (D.state e h)
      = D.lam e * M.utility (D.aggCons h) + D.κ e
        + M.discount * ∑ z', M.aggProb (shockAt z₀ h) z'
            * (M.household z₀ (D.pr D.K)).valueFunction (D.state e (z' :: h)) := by
  set s := D.state e h with hs
  have hfP : M.policy z₀ (D.pr D.K) s ∈ (M.household z₀ (D.pr D.K)).feasible s :=
    M.policy_mem z₀ _ s
  have hcons : M.cash z₀ (D.pr D.K) s - M.policy z₀ (D.pr D.K) s = D.σ e * D.aggCons h := by
    rw [hs, D.prop' e h z₀, state, D.cash_hold D.K e (D.K_mem h), aggCons]
    ring
  have hfl : M.consFloor ≤ M.cash z₀ (D.pr D.K) s - M.policy z₀ (D.pr D.K) s :=
    le_sub_comm.1 (hfP.2.trans (min_le_right _ _))
  have hpos : 0 < D.aggCons h := by
    by_contra hle
    push Not at hle
    have h1 : 0 < D.σ e * D.aggCons h := by
      rw [← hcons]
      exact D.floor_pos.trans_le hfl
    have := mul_nonneg (D.σ_pos e).le (neg_nonneg.2 hle)
    linarith
  refine ⟨hpos, ?_⟩
  rw [M.valueFunction_eq_objective_policy z₀ (D.pr D.K) s, M.objective_perm z₀ hperm _ _ hfP,
    hcons, D.hom e _ hpos]
  congr 2
  refine Finset.sum_congr rfl fun z' _ => ?_
  have hst : (M.clampAssets (M.policy z₀ (D.pr D.K) s), (⟨s.2.idio, z' :: s.2.node⟩ : Label Z E))
      = D.state e (z' :: h) := D.state_cons e h z'
  rw [hst]
  rfl

/-- The normalised value of type `e` on the proportional path. -/
noncomputable def W (e : E) (h : List Z) : ℝ :=
  D.norm e ((M.household z₀ (D.pr D.K)).valueFunction (D.state e h))

include hperm in
theorem W_rec (e : E) (h : List Z) :
    D.W e h = M.utility (D.aggCons h)
      + M.discount * ∑ z', M.aggProb (shockAt z₀ h) z' * D.W e (z' :: h) := by
  rw [W, (D.value_state hperm e h).2, D.norm_bellman e _ _ _ (M.aggProb_sum _)]
  rfl

omit [DecidableEq E] in
theorem abs_norm_le (e : E) {v b : ℝ} (hv : |v| ≤ b) :
    |D.norm e v| ≤ (b + |D.κ e / (1 - M.discount)|) / D.lam e := by
  rw [norm, abs_div, abs_of_pos (D.lam_pos e)]
  exact div_le_div_of_nonneg_right
    (by have := abs_sub v (D.κ e / (1 - M.discount)); linarith) (D.lam_pos e).le

include hperm in
/-- **Values are proportional**: the normalised value on the proportional path is the same for
every type. -/
theorem W_eq (e e' : E) (h : List Z) : D.W e h = D.W e' h := by
  have key : ∀ e₁ e₂ : E, ∀ g, 0 ≤ D.W e₁ g - D.W e₂ g := by
    intro e₁ e₂ g
    refine M.tree_nonneg z₀ (f := fun g => D.W e₁ g - D.W e₂ g)
      (B := (‖(M.household z₀ (D.pr D.K)).valueFunction‖
          + |D.κ e₁ / (1 - M.discount)|) / D.lam e₁
        + (‖(M.household z₀ (D.pr D.K)).valueFunction‖
          + |D.κ e₂ / (1 - M.discount)|) / D.lam e₂) (fun g => ?_) (fun g => ?_) g
    · have h1 := abs_le.1 (D.abs_norm_le e₁ (M.abs_valueFunction_le z₀ (D.pr D.K) (D.state e₁ g)))
      have h2 := abs_le.1 (D.abs_norm_le e₂ (M.abs_valueFunction_le z₀ (D.pr D.K) (D.state e₂ g)))
      simp only [W]
      linarith
    · rw [D.W_rec hperm e₁ g, D.W_rec hperm e₂ g]
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
  linarith [key e e' h, key e' e h]

/-! ### Another allocation -/

variable (K' : List Z → ℝ)

/-- Type `e` in the allocation of `K'`: from its share of initial capital it saves optimally
against the prices of `K'`. -/
noncomputable def other (e : E) : List Z → M.State
  | [] => D.state e []
  | z' :: h => (M.clampAssets (M.policy z₀ (D.pr K') (other e h)), ⟨e, z' :: h⟩)

omit [DecidableEq E] in
theorem other_label (e : E) : ∀ h, (D.other K' e h).2 = ⟨e, h⟩
  | [] => rfl
  | _ :: _ => rfl

/-- Type `e`'s saving in the allocation of `K'`. -/
noncomputable def otherSaving (e : E) (h : List Z) : ℝ := M.policy z₀ (D.pr K') (D.other K' e h)

/-- Type `e`'s consumption in the allocation of `K'`. -/
noncomputable def otherCons (e : E) (h : List Z) : ℝ :=
  M.cash z₀ (D.pr K') (D.other K' e h) - D.otherSaving K' e h

/-- Aggregate consumption in the allocation of `K'`. -/
noncomputable def aggCons' (h : List Z) : ℝ := ∑ e, D.p e * D.otherCons K' e h

omit [DecidableEq E] in
theorem other_cons_val (e : E) (z' : Z) (h : List Z) :
    ((D.other K' e (z' :: h)).1 : ℝ) = D.otherSaving K' e h := by
  change ((M.clampAssets (M.policy z₀ (D.pr K') (D.other K' e h))) : ℝ) = _
  rw [M.clampAssets_of_mem (M.policy_mem_Icc z₀ _ _)]
  rfl

omit [DecidableEq E] in
theorem floor_le_otherCons (e : E) (h : List Z) : M.consFloor ≤ D.otherCons K' e h :=
  le_sub_comm.1 ((M.policy_mem z₀ (D.pr K') (D.other K' e h)).2.trans (min_le_right _ _))

omit [DecidableEq E] in
theorem floor_le_aggCons' (h : List Z) : M.consFloor ≤ D.aggCons' K' h := by
  have : ∑ e, D.p e * M.consFloor ≤ ∑ e, D.p e * D.otherCons K' e h :=
    Finset.sum_le_sum fun e _ =>
      mul_le_mul_of_nonneg_left (D.floor_le_otherCons K' e h) (D.p_pos e).le
  rwa [← Finset.sum_mul, D.p_sum, one_mul] at this

variable (hK' : ∀ h, K' h = ∑ e, D.p e * ((D.other K' e h).1 : ℝ))

omit [DecidableEq E] in
include hK' in
/-- The budgets of the types add up to aggregate resources. -/
theorem sum_cash_other (h : List Z) :
    ∑ e, D.p e * M.cash z₀ (D.pr K') (D.other K' e h)
      = D.res (shockAt z₀ h) (K' h) (K' h) := by
  have hc : ∀ e, M.cash z₀ (D.pr K') (D.other K' e h)
      = M.grossReturn (shockAt z₀ h) (K' h) D.L * ((D.other K' e h).1 : ℝ)
        + M.wage (shockAt z₀ h) (K' h) D.L * (D.σ e * D.L) := by
    intro e
    have hl := D.other_label K' e h
    rw [D.σ_L e]
    simp only [cash, returnAt, wageAt, hl, D.borrow, mul_zero, sub_zero]
    rfl
  simp only [hc, mul_add]
  rw [Finset.sum_add_distrib, res]
  congr 1
  · rw [hK' h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  · have : ∀ e, D.p e * (M.wage (shockAt z₀ h) (K' h) D.L * (D.σ e * D.L))
        = D.p e * D.σ e * (M.wage (shockAt z₀ h) (K' h) D.L * D.L) := fun e => by ring
    rw [Finset.sum_congr rfl fun e _ => this e, ← Finset.sum_mul, D.σ_sum, one_mul]

omit [DecidableEq E] in
include hK' in
theorem K'_cons (z' : Z) (h : List Z) : K' (z' :: h) = ∑ e, D.p e * D.otherSaving K' e h := by
  rw [hK']
  exact Finset.sum_congr rfl fun e _ => by rw [D.other_cons_val]

omit [DecidableEq E] in
include hK' in
/-- Aggregate resources are aggregate consumption plus next period's capital. -/
theorem res_eq (z' : Z) (h : List Z) :
    D.res (shockAt z₀ h) (K' h) (K' h) = D.aggCons' K' h + K' (z' :: h) := by
  rw [← D.sum_cash_other K' hK' h, D.K'_cons K' hK' z' h, aggCons', ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by rw [otherCons]; ring

omit [DecidableEq E] in
include hK' in
/-- **Every allocation respects the bound on aggregate capital.** -/
theorem K'_mem : ∀ h, K' h ∈ Icc 0 D.capK
  | [] => by
    have h0 : K' [] = D.K [] := by
      rw [hK']
      have : ∀ e, D.p e * ((D.other K' e []).1 : ℝ) = D.p e * D.σ e * D.K [] := fun e => by
        change D.p e * ((D.hold e (D.K []) []).1 : ℝ) = _
        rw [D.hold_val e (D.K_mem [])]
        ring
      rw [Finset.sum_congr rfl fun e _ => this e, ← Finset.sum_mul, D.σ_sum, one_mul]
    rw [h0]
    exact D.K_mem []
  | z' :: h => by
    have ih := K'_mem h
    have h1 := D.res_eq K' hK' z' h
    have h2 := D.floor_le_aggCons' K' h
    have h3 := D.bound (shockAt z₀ h) (K' h) ih
    have h4 : 0 ≤ K' (z' :: h) := by
      rw [D.K'_cons K' hK' z' h]
      exact Finset.sum_nonneg fun e _ =>
        mul_nonneg (D.p_pos e).le (M.policy_mem z₀ _ _).1
    simp only [res] at h1 h3
    exact ⟨h4, by linarith⟩

/-- The weighted normalised values of the types in the allocation of `K'`. -/
noncomputable def G (h : List Z) : ℝ :=
  ∑ e, D.p e * D.σ e
    * D.norm e ((M.household z₀ (D.pr K')).valueFunction (D.other K' e h))

include hperm in
/-- **The Negishi bound, households' side**: by Jensen the weighted utilities are at most the
utility of aggregate consumption. -/
theorem G_rec (h : List Z) :
    D.G K' h ≤ M.utility (D.aggCons' K' h)
      + M.discount * ∑ z', M.aggProb (shockAt z₀ h) z' * D.G K' (z' :: h) := by
  -- each type's normalised Bellman equation
  have hterm : ∀ e, D.norm e ((M.household z₀ (D.pr K')).valueFunction (D.other K' e h))
      = M.utility (D.otherCons K' e h / D.σ e)
        + M.discount * ∑ z', M.aggProb (shockAt z₀ h) z'
            * D.norm e ((M.household z₀ (D.pr K')).valueFunction (D.other K' e (z' :: h))) := by
    intro e
    set s := D.other K' e h with hs
    have hf : M.policy z₀ (D.pr K') s ∈ (M.household z₀ (D.pr K')).feasible s :=
      M.policy_mem z₀ _ s
    have hl : s.2 = ⟨e, h⟩ := D.other_label K' e h
    have hc : 0 < D.otherCons K' e h / D.σ e :=
      div_pos (D.floor_pos.trans_le (D.floor_le_otherCons K' e h)) (D.σ_pos e)
    have hu : M.utility (M.cash z₀ (D.pr K') s - M.policy z₀ (D.pr K') s)
        = D.lam e * M.utility (D.otherCons K' e h / D.σ e) + D.κ e := by
      rw [← D.hom e _ hc, mul_div_cancel₀ _ (D.σ_pos e).ne']
      rfl
    rw [M.valueFunction_eq_objective_policy z₀ (D.pr K') s, M.objective_perm z₀ hperm _ _ hf, hu,
      hl]
    exact D.norm_bellman e _ _ _ (M.aggProb_sum _)
  -- Jensen
  have hJ : ∑ e, D.p e * D.σ e * M.utility (D.otherCons K' e h / D.σ e)
      ≤ M.utility (D.aggCons' K' h) := by
    have := D.concave.le_map_sum (t := Finset.univ) (w := fun e => D.p e * D.σ e)
      (p := fun e => D.otherCons K' e h / D.σ e)
      (fun e _ => mul_nonneg (D.p_pos e).le (D.σ_pos e).le) D.σ_sum
      (fun e _ => div_pos (D.floor_pos.trans_le (D.floor_le_otherCons K' e h)) (D.σ_pos e))
    simp only [smul_eq_mul] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    rw [aggCons']
    refine Finset.sum_congr rfl fun e _ => ?_
    have := (D.σ_pos e).ne'
    field_simp
  have hswap : ∑ e, D.p e * D.σ e * (M.discount * ∑ z', M.aggProb (shockAt z₀ h) z'
        * D.norm e ((M.household z₀ (D.pr K')).valueFunction (D.other K' e (z' :: h))))
      = M.discount * ∑ z', M.aggProb (shockAt z₀ h) z' * D.G K' (z' :: h) := by
    simp only [G, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z' _ => Finset.sum_congr rfl fun e _ => by ring
  rw [G]
  simp only [hterm, mul_add]
  rw [Finset.sum_add_distrib, hswap]
  linarith

variable {eS : E} (heS : 1 ≤ D.σ eS)

/-- The normalised value, at the prices of `K`, of the large type `eS` holding its share of the
capital of `K'`. -/
noncomputable def H (eS : E) (h : List Z) : ℝ :=
  D.norm eS ((M.household z₀ (D.pr D.K)).valueFunction (D.hold eS (K' h) h))

include hperm hK' heS in
/-- **The Negishi bound, the large type's side**: at the prices of `K` it can hold its share of
the capital of `K'` and consume at least its share of aggregate consumption. -/
theorem H_rec (h : List Z) :
    M.utility (D.aggCons' K' h)
        + M.discount * ∑ z', M.aggProb (shockAt z₀ h) z' * D.H K' eS (z' :: h)
      ≤ D.H K' eS h := by
  have hmem := D.K'_mem K' hK'
  set s := D.hold eS (K' h) h with hs
  set a := D.σ eS * K' (z₀ :: h) with ha
  have hσ := D.σ_pos eS
  have hfloor := D.floor_le_aggCons' K' h
  -- cash at the prices of `K` covers the share of resources at the prices of `K'`
  have hcash : D.σ eS * (D.aggCons' K' h + K' (z₀ :: h)) ≤ M.cash z₀ (D.pr D.K) s := by
    rw [hs, D.cash_hold D.K eS (hmem h), ← D.res_eq K' hK' z₀ h]
    exact mul_le_mul_of_nonneg_left (D.support _ _ _) hσ.le
  have hcons : D.σ eS * D.aggCons' K' h ≤ M.cash z₀ (D.pr D.K) s - a := by
    rw [ha]
    linarith [mul_add (D.σ eS) (D.aggCons' K' h) (K' (z₀ :: h))]
  have hCpos : 0 < D.aggCons' K' h := D.floor_pos.trans_le hfloor
  have hge : D.aggCons' K' h ≤ D.σ eS * D.aggCons' K' h := by nlinarith
  have hamem := D.σ_mul_mem eS (hmem (z₀ :: h))
  have hf : a ∈ (M.household z₀ (D.pr D.K)).feasible s :=
    ⟨hamem.1, le_min hamem.2 (by linarith)⟩
  have hobj := M.objective_le_valueFunction z₀ (D.pr D.K) hf
  rw [M.objective_perm z₀ hperm _ _ hf] at hobj
  have hu : D.lam eS * M.utility (D.aggCons' K' h) + D.κ eS
      ≤ M.utility (M.cash z₀ (D.pr D.K) s - a) := by
    rw [← D.hom eS _ hCpos]
    exact M.monotoneOn_utility (mem_Ici.2 (hfloor.trans hge))
      (mem_Ici.2 ((hfloor.trans hge).trans hcons)) hcons
  have hchild : ∀ z', (M.clampAssets a, (⟨s.2.idio, z' :: s.2.node⟩ : Label Z E))
      = D.hold eS (K' (z' :: h)) (z' :: h) := by
    intro z'
    rw [ha, D.K'_cons K' hK' z₀ h, ← D.K'_cons K' hK' z' h]
    rfl
  simp only [hchild] at hobj
  change M.utility _ + M.discount * ∑ x, M.aggProb (shockAt z₀ h) x * _ ≤ _ at hobj
  have hnorm := D.norm_bellman eS (M.utility (D.aggCons' K' h))
    (fun z' => M.aggProb (shockAt z₀ h) z')
    (fun z' => (M.household z₀ (D.pr D.K)).valueFunction (D.hold eS (K' (z' :: h)) (z' :: h)))
    (M.aggProb_sum _)
  rw [H]
  change _ + M.discount * ∑ z', M.aggProb (shockAt z₀ h) z'
    * D.norm eS ((M.household z₀ (D.pr D.K)).valueFunction
      (D.hold eS (K' (z' :: h)) (z' :: h))) ≤ _
  rw [← hnorm, norm, norm]
  exact div_le_div_of_nonneg_right (by
    have : (M.household z₀ (D.pr D.K)).valueFunction s
        = (M.household z₀ (D.pr D.K)).valueFunction (D.hold eS (K' h) h) := rfl
    change _ ≤ (M.household z₀ (D.pr D.K)).valueFunction s - _
    linarith) (D.lam_pos eS).le

include hperm hK' heS in
/-- **The Negishi bound.** -/
theorem G_le_H (h : List Z) : D.G K' h ≤ D.H K' eS h := by
  have hmem := D.K'_mem K' hK'
  have key := M.tree_nonneg z₀ (f := fun g => D.H K' eS g - D.G K' g)
    (B := (‖(M.household z₀ (D.pr D.K)).valueFunction‖
        + |D.κ eS / (1 - M.discount)|) / D.lam eS
      + ∑ e, D.p e * D.σ e * ((‖(M.household z₀ (D.pr K')).valueFunction‖
        + |D.κ e / (1 - M.discount)|) / D.lam e)) (fun g => ?_) (fun g => ?_) h
  · linarith
  · have h1 := abs_le.1 (D.abs_norm_le eS
      (M.abs_valueFunction_le z₀ (D.pr D.K) (D.hold eS (K' g) g)))
    have h2 : D.G K' g ≤ ∑ e, D.p e * D.σ e * ((‖(M.household z₀ (D.pr K')).valueFunction‖
        + |D.κ e / (1 - M.discount)|) / D.lam e) :=
      Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left
        (abs_le.1 (D.abs_norm_le e (M.abs_valueFunction_le z₀ (D.pr K') (D.other K' e g)))).2
        (mul_nonneg (D.p_pos e).le (D.σ_pos e).le)
    simp only [H]
    linarith
  · have h1 := D.H_rec hperm K' hK' heS g
    have h2 := D.G_rec hperm K' g
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith

include hperm hK' heS in
/-- **The allocation of `K'` is the proportional one.** -/
theorem other_eq_state (e : E) : ∀ h, D.other K' e h = D.state e h := by
  have hall : ∀ h, ∀ e, D.other K' e h = D.state e h := by
    intro h
    induction h with
    | nil => intro e; rfl
    | cons z' h ih =>
      -- capital agrees at `h`
      have hKh : K' h = D.K h := by
        rw [hK']
        have : ∀ e, D.p e * ((D.other K' e h).1 : ℝ) = D.p e * D.σ e * D.K h := fun e => by
          rw [ih e, state, D.hold_val e (D.K_mem h)]
          ring
        rw [Finset.sum_congr rfl fun e _ => this e, ← Finset.sum_mul, D.σ_sum, one_mul]
      -- `W ≤ G ≤ H = W`
      have hGH := D.G_le_H hperm K' hK' heS h
      have hH : D.H K' eS h = D.W eS h := by rw [H, hKh]; rfl
      have hterm : ∀ e, 0 ≤ D.p e * D.σ e
          * (D.norm e ((M.household z₀ (D.pr K')).valueFunction (D.state e h)) - D.W e h) := by
        intro e
        refine mul_nonneg (mul_nonneg (D.p_pos e).le (D.σ_pos e).le) (sub_nonneg.2 ?_)
        rw [W, norm, norm]
        exact div_le_div_of_nonneg_right
          (by linarith [D.gapA_nonneg hperm K' e h, show D.gapA K' e h
            = (M.household z₀ (D.pr K')).valueFunction (D.state e h)
              - (M.household z₀ (D.pr D.K)).valueFunction (D.state e h) from rfl])
          (D.lam_pos e).le
      have hsum : ∑ e, D.p e * D.σ e
          * (D.norm e ((M.household z₀ (D.pr K')).valueFunction (D.state e h)) - D.W e h)
          = D.G K' h - D.W eS h := by
        simp only [mul_sub, Finset.sum_sub_distrib, G, ih]
        congr 1
        rw [Finset.sum_congr rfl fun e _ => by rw [D.W_eq hperm e eS h], ← Finset.sum_mul,
          D.σ_sum, one_mul]
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun e _ => hterm e).1
        (le_antisymm (by rw [hsum]; linarith) (Finset.sum_nonneg fun e _ => hterm e))
      intro e
      -- the two values agree at the common state
      have hval : (M.household z₀ (D.pr K')).valueFunction (D.state e h)
          = (M.household z₀ (D.pr D.K)).valueFunction (D.state e h) := by
        have h0 := hzero e (Finset.mem_univ e)
        have hpσ : D.p e * D.σ e ≠ 0 := (mul_pos (D.p_pos e) (D.σ_pos e)).ne'
        have h1 := sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hpσ)
        rw [W, norm, norm, div_left_inj' (D.lam_pos e).ne'] at h1
        linarith
      -- so the proportional saving is optimal at the prices of `K'`
      have hf := (D.policy_feasible K' e h).2
      have hobj := D.objective_ge hperm K' e h
      have hgap : 0 ≤ ∑ z'', M.aggProb (shockAt z₀ h) z'' * D.gapA K' e (z'' :: h) :=
        Finset.sum_nonneg fun z'' _ => mul_nonneg (M.aggProb_nonneg _ _)
          (D.gapA_nonneg hperm K' e _)
      have hle := M.objective_le_valueFunction z₀ (D.pr K') hf
      have hmax : (M.household z₀ (D.pr K')).objective (M.household z₀ (D.pr K')).valueFunction
          (D.state e h) (M.policy z₀ (D.pr D.K) (D.state e h))
          = (M.household z₀ (D.pr K')).bellmanFn (M.household z₀ (D.pr K')).valueFunction
            (D.state e h) := by
        rw [M.bellmanFn_valueFunction]
        have := mul_nonneg M.discount_pos.le hgap
        linarith
      have heq : M.policy z₀ (D.pr D.K) (D.state e h) = M.policy z₀ (D.pr K') (D.state e h) :=
        M.optimal_saving_unique z₀ (D.pr K') hf (M.policy_mem z₀ _ _) hmax
          (M.policy_optimal z₀ (D.pr K') _).symm
      change (M.clampAssets (M.policy z₀ (D.pr K') (D.other K' e h)), (⟨e, z' :: h⟩ : Label Z E))
        = _
      rw [ih e, ← heq]
      exact D.state_cons e h z'
  exact fun h => hall h e

include hperm hK' in
/-- **Uniqueness among all allocations.** If every type saves optimally against the prices of
`K'`, from its share of initial capital, and `K'` is mean assets at every node, then `K'` is the
proportional path. -/
theorem eq_of_types : K' = D.K := by
  -- a type with share at least one
  obtain ⟨eS, heS⟩ : ∃ e, 1 ≤ D.σ e := by
    by_contra hno
    push Not at hno
    have hlt : ∑ e, D.p e * D.σ e < ∑ e, D.p e * 1 := by
      have hne : (Finset.univ : Finset E).Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have := D.p_sum
        rw [hemp, Finset.sum_empty] at this
        exact zero_ne_one this
      exact Finset.sum_lt_sum_of_nonempty hne fun e _ =>
        mul_lt_mul_of_pos_left (hno e) (D.p_pos e)
    simp only [mul_one, D.p_sum, D.σ_sum] at hlt
    exact lt_irrefl _ hlt
  funext h
  rw [hK']
  have : ∀ e, D.p e * ((D.other K' e h).1 : ℝ) = D.p e * D.σ e * D.K h := fun e => by
    rw [D.other_eq_state hperm K' hK' heS e h, state, D.hold_val e (D.K_mem h)]
    ring
  rw [Finset.sum_congr rfl fun e _ => this e, ← Finset.sum_mul, D.σ_sum, one_mul]

end perm

end PropEq

end KSModel

end KrusellSmith

end LeanEconomics
