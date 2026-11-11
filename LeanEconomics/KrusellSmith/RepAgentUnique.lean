/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ColemanEquilibrium

/-!
# The representative agent: sequential equilibrium is unique

With one idiosyncratic state and a point mass of households, sequential equilibrium is unique,
for every CRRA coefficient and every capital share. No order structure and no contraction is used:
the argument is the decentralised form of the planner's problem.

**Prices support the allocation** (`PricesSupport`): holding capital `a`, a household has least
cash when prices are those of aggregate capital `a` itself,

    R(a) a + w(a) L ≤ R(k) a + w(k) L        for every `k`.

For Cobb–Douglas this is the tangent line of `t ↦ t^α`, and it survives the clamps of the price
box (`CobbDouglas.repCash_le_of_prices`).

**The argument** (`eq_of_isSequentialEquilibrium_dirac`). Let `K`, `K'` be equilibria from the same
point mass, with price paths `P`, `P'`.

* Along the `K'` tree the household of `K'` can, at the prices `P`, afford what it does at `P'`.
  So the gap `V_P − V_{P'}` at the node's state is at least `β` times its expectation over the
  children (`gap_step`); it is bounded, hence nonnegative at every node (`gap_nonneg`).
* The same holds with the roles exchanged. So at a node where `K = K'` the two values agree, the
  saving of `K'` attains the Bellman maximum at the prices `P`, and the maximiser is unique
  (`optimal_saving_unique`): `K` and `K'` agree at the children. Induct from the root.

With `ColemanEquilibrium.lean`: when `β R̄ ≤ 1` the Coleman capital path is **the** sequential
equilibrium from every point mass (`Coleman.eq_capPath`).
-/

open MeasureTheory Set

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace CobbDouglas

variable (T : CobbDouglas Z)

omit [Fintype Z] in
/-- **Cobb–Douglas prices support the allocation**: a household holding capital `a` has least
cash when prices are those of aggregate capital `a` (clamps included). -/
theorem repCash_le_of_prices (z : Z) {L : ℝ} (hL : T.clampLab L = L) (k a : ℝ) :
    T.grossReturn z a L * a + T.wage z a L * L ≤ T.grossReturn z k L * a + T.wage z k L * L := by
  set κ := T.clampCap k with hκdef
  set κ' := T.clampCap a with hκ'def
  have hκ : 0 < κ := T.clampCap_pos k
  have hκ' : 0 < κ' := T.clampCap_pos a
  have hLpos : 0 < L := hL ▸ T.clampLab_pos L
  have hα0 := T.share_pos
  have hα1 := T.share_lt_one
  set α := T.share
  set c := T.tfp z
  have hc : 0 < c := T.tfp_pos z
  set m := c * L ^ (1 - α) with hmdef
  have hm : 0 ≤ m := mul_nonneg hc.le (Real.rpow_nonneg hLpos.le _)
  have hLL : L ^ (-α) * L = L ^ (1 - α) := by
    rw [show (1 : ℝ) - α = -α + 1 by ring, Real.rpow_add_one hLpos.ne']
  have hkα : ∀ x : ℝ, 0 < x → x ^ α = x ^ (α - 1) * x := fun x hx => by
    rw [Real.rpow_sub_one hx.ne']
    field_simp
  have hR : ∀ K : ℝ, T.grossReturn z K L
      = (1 - T.depreciation) + α * m * T.clampCap K ^ (α - 1) := fun K => by
    simp only [grossReturn, hL, hmdef]
    ring
  have hw : ∀ K : ℝ, T.wage z K L * L = (1 - α) * m * T.clampCap K ^ α := fun K => by
    simp only [wage, hL, hmdef, ← hLL]
    ring
  rw [hR a, hR k, hw a, hw k, ← hκdef, ← hκ'def, hkα κ hκ, hkα κ' hκ']
  set r := κ ^ (α - 1)
  set r' := κ' ^ (α - 1)
  -- the tangent line at `κ`, evaluated at `κ'`
  have htan : r' * κ' ≤ r * κ + α * r * (κ' - κ) := by
    have := rpow_le_tangent hκ' hκ hα0.le hα1.le
    rwa [hkα κ hκ, hkα κ' hκ'] at this
  -- the return moves against the household's position relative to the clamp
  have hsign : 0 ≤ (r - r') * (a - κ') := by
    rcases lt_trichotomy a κ' with h | h | h
    · have hlo : κ' = T.capLo := by
        rcases max_choice T.capLo (min T.capHi a) with h' | h'
        · exact h'
        · have : κ' ≤ a := by
            rw [hκ'def, clampCap, h']
            exact min_le_right _ _
          linarith
      have hκκ : κ' ≤ κ := hlo ▸ (T.clampCap_mem k).1
      have : r ≤ r' := Real.rpow_le_rpow_of_nonpos hκ' hκκ (by linarith)
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · rw [h, sub_self, mul_zero]
    · have hhi : T.capHi ≤ κ' := by
        by_contra hlt
        push Not at hlt
        have h1 : min T.capHi a ≤ κ' := le_max_right _ _
        rcases min_choice T.capHi a with h' | h'
        · rw [h'] at h1; linarith
        · rw [h'] at h1; linarith
      have hκκ : κ ≤ κ' := (T.clampCap_mem k).2.trans hhi
      have : r' ≤ r := Real.rpow_le_rpow_of_nonpos hκ hκκ (by linarith)
      exact mul_nonneg (by linarith) (by linarith)
  have hdiff : 0 ≤ α * r * a + (1 - α) * (r * κ) - (α * r' * a + (1 - α) * (r' * κ')) := by
    have := mul_nonneg hα0.le hsign
    nlinarith
  have := mul_nonneg hm hdiff
  nlinarith

end CobbDouglas

namespace KSModel

variable (M : KSModel Z E) [Unique E]

/-- **Prices support the allocation**: holding capital `a ≥ 0`, the representative household has
least cash when prices are those of aggregate capital `a`. -/
def PricesSupport : Prop :=
  ∀ (z : Z) (k a : ℝ), 0 ≤ a →
    M.grossReturn z a (M.efficiency default) * a
        + M.wage z a (M.efficiency default) * M.efficiency default
      ≤ M.grossReturn z k (M.efficiency default) * a
        + M.wage z k (M.efficiency default) * M.efficiency default

variable (z₀ : Z) (x₀ : M.AState)

/-- The household at a point mass on the tree: the point mass is pushed along its saving. -/
noncomputable def pointNode (Q : List Z → ℝ × ℝ) : List Z → M.AState
  | [] => x₀
  | _ :: h => M.nextA z₀ Q h default (pointNode Q h)

/-- The household's state at node `h` along the tree from a point mass. -/
noncomputable def pointState (Q : List Z → ℝ × ℝ) (h : List Z) : M.State :=
  ((M.pointNode z₀ x₀ Q h).1, ⟨default, h⟩)

theorem nodeDist_pointMass (Q : List Z → ℝ × ℝ) :
    ∀ h, M.nodeDist z₀ (Measure.dirac x₀) Q h = Measure.dirac (M.pointNode z₀ x₀ Q h)
  | [] => rfl
  | z' :: h => by
    change M.pushNode z₀ Q h z' (M.nodeDist z₀ (Measure.dirac x₀) Q h) = _
    rw [nodeDist_pointMass Q h, M.pushNode_dirac]
    rfl

theorem pointState_cons (Q : List Z → ℝ × ℝ) (z' : Z) (h : List Z) :
    M.pointState z₀ x₀ Q (z' :: h)
      = (M.clampAssets (M.policy z₀ Q (M.pointState z₀ x₀ Q h)), ⟨default, z' :: h⟩) := by
  have : (M.pointNode z₀ x₀ Q h).2.idio = default := Unique.eq_default _
  simp only [pointState, pointNode, nextA, this]

theorem pointState_cons_val (Q : List Z → ℝ × ℝ) (z' : Z) (h : List Z) :
    ((M.pointState z₀ x₀ Q (z' :: h)).1 : ℝ) = M.policy z₀ Q (M.pointState z₀ x₀ Q h) := by
  rw [pointState_cons, M.clampAssets_of_mem (M.policy_mem_Icc z₀ Q _)]

variable {M z₀ x₀}

/-- In a sequential equilibrium from a point mass, capital is the household's assets. -/
theorem IsSequentialEquilibrium.eq_pointState {K : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium z₀ (Measure.dirac x₀) K) (h : List Z) :
    K h = (M.pointState z₀ x₀ (M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K) h).1 := by
  have := hK h
  rw [meanCapital, nodeDist_pointMass, integral_dirac] at this
  exact this

section gap

variable {K K' : List Z → ℝ} (hK : M.IsSequentialEquilibrium z₀ (Measure.dirac x₀) K)
  (hK' : M.IsSequentialEquilibrium z₀ (Measure.dirac x₀) K')

local notation "𝐏" => M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K
local notation "𝐐" => M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K'

include hK' in
/-- Along the `K'` tree the household has at least as much cash at the prices of `K`. -/
theorem cash_le_of_support (hS : M.PricesSupport) (hb : M.borrowLimit = 0) (h : List Z) :
    M.cash z₀ 𝐐 (M.pointState z₀ x₀ 𝐐 h) ≤ M.cash z₀ 𝐏 (M.pointState z₀ x₀ 𝐐 h) := by
  have ha : ((M.pointState z₀ x₀ 𝐐 h).1 : ℝ) = K' h := (hK'.eq_pointState h).symm
  have h0 : 0 ≤ K' h := ha ▸ (M.pointState z₀ x₀ 𝐐 h).1.2.1
  have := hS (shockAt z₀ h) (K h) (K' h) h0
  simp only [cash, returnAt, wageAt, pricePath, M.labour_unique, hb, mul_zero, sub_zero]
  rw [ha]
  exact this

/-- The gap between the two value functions at the state the `K'` household holds at node `h`. -/
noncomputable def gap (K K' : List Z → ℝ) (h : List Z) : ℝ :=
  (M.household z₀ (M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K)).valueFunction
      (M.pointState z₀ x₀ (M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K') h)
    - (M.household z₀ (M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K')).valueFunction
      (M.pointState z₀ x₀ (M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K') h)

include hK' in
/-- The saving of the `K'` household is feasible at the prices of `K`. -/
theorem policy_feasible_of_support (hS : M.PricesSupport) (hb : M.borrowLimit = 0) (h : List Z) :
    M.policy z₀ 𝐐 (M.pointState z₀ x₀ 𝐐 h) ∈ (M.household z₀ 𝐏).feasible (M.pointState z₀ x₀ 𝐐 h) :=
  ⟨(M.policy_mem z₀ 𝐐 _).1, (M.policy_mem z₀ 𝐐 _).2.trans
    (min_le_min le_rfl (sub_le_sub_right (cash_le_of_support (K := K) hK' hS hb h) _))⟩

include hK' in
/-- **The household of `K'`, saving as it does, at the prices of `K`**: the Bellman objective is at
least its own value plus the discounted expected gap at the children. -/
theorem objective_ge_of_support (hS : M.PricesSupport) (hb : M.borrowLimit = 0) (h : List Z) :
    (M.household z₀ 𝐐).valueFunction (M.pointState z₀ x₀ 𝐐 h)
        + M.discount * ∑ ze : Z × E,
            M.shockProb z₀ ze (M.pointState z₀ x₀ 𝐐 h, M.policy z₀ 𝐐 (M.pointState z₀ x₀ 𝐐 h))
              * M.gap (z₀ := z₀) (x₀ := x₀) K K' (ze.1 :: h)
      ≤ (M.household z₀ 𝐏).objective (M.household z₀ 𝐏).valueFunction
          (M.pointState z₀ x₀ 𝐐 h) (M.policy z₀ 𝐐 (M.pointState z₀ x₀ 𝐐 h)) := by
  set s := M.pointState z₀ x₀ 𝐐 h with hs
  set a := M.policy z₀ 𝐐 s with ha
  have hf' : a ∈ (M.household z₀ 𝐐).feasible s := M.policy_mem z₀ 𝐐 s
  have hf : a ∈ (M.household z₀ 𝐏).feasible s := policy_feasible_of_support hK' hS hb h
  have hcash := cash_le_of_support (K := K) hK' hS hb h
  have hv' : (M.household z₀ 𝐐).valueFunction s
      = (M.household z₀ 𝐐).objective (M.household z₀ 𝐐).valueFunction s a := by
    have := M.policy_optimal z₀ 𝐐 s
    rwa [(M.household z₀ 𝐐).bellman_valueFunction] at this
  rw [hv', M.objective_eq z₀ 𝐐 _ hf', M.objective_eq z₀ 𝐏 _ hf]
  have hu : M.utility (M.cash z₀ 𝐐 s - a) ≤ M.utility (M.cash z₀ 𝐏 s - a) :=
    M.monotoneOn_utility (mem_Ici.2 (le_sub_comm.1 (hf'.2.trans (min_le_right _ _))))
      (mem_Ici.2 (le_sub_comm.1 (hf.2.trans (min_le_right _ _)))) (sub_le_sub_right hcash _)
  have hsum : ∑ ze : Z × E, M.shockProb z₀ ze (s, a)
        * (M.household z₀ 𝐐).valueFunction (M.clampAssets a, ⟨ze.2, ze.1 :: s.2.node⟩)
      + ∑ ze : Z × E, M.shockProb z₀ ze (s, a) * M.gap (z₀ := z₀) (x₀ := x₀) K K' (ze.1 :: h)
      = ∑ ze : Z × E, M.shockProb z₀ ze (s, a)
        * (M.household z₀ 𝐏).valueFunction (M.clampAssets a, ⟨ze.2, ze.1 :: s.2.node⟩) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ze _ => ?_
    have hst : (M.clampAssets a, (⟨ze.2, ze.1 :: s.2.node⟩ : Label Z E))
        = M.pointState z₀ x₀ 𝐐 (ze.1 :: h) := by
      rw [M.pointState_cons, Unique.eq_default ze.2]
      rfl
    rw [hst, gap]
    ring
  have hβ := M.discount_pos.le
  rw [← hsum, mul_add]
  linarith

include hK' in
/-- **The gap is at least `β` times its expectation over the children.** -/
theorem gap_step (hS : M.PricesSupport) (hb : M.borrowLimit = 0) (h : List Z) :
    M.discount * ∑ ze : Z × E,
        M.shockProb z₀ ze (M.pointState z₀ x₀ 𝐐 h, M.policy z₀ 𝐐 (M.pointState z₀ x₀ 𝐐 h))
          * M.gap (z₀ := z₀) (x₀ := x₀) K K' (ze.1 :: h)
      ≤ M.gap (z₀ := z₀) (x₀ := x₀) K K' h := by
  have h1 := objective_ge_of_support (K := K) hK' hS hb h
  have h2 := (M.household z₀ 𝐏).le_bellmanFn (M.household z₀ 𝐏).valueFunction
    (policy_feasible_of_support (K := K) hK' hS hb h)
  have h3 : (M.household z₀ 𝐏).bellmanFn (M.household z₀ 𝐏).valueFunction
      (M.pointState z₀ x₀ 𝐐 h) = (M.household z₀ 𝐏).valueFunction (M.pointState z₀ x₀ 𝐐 h) :=
    congrFun (congrArg DFunLike.coe (M.household z₀ 𝐏).bellman_valueFunction) _
  rw [gap]
  linarith

include hK' in
/-- **The gap is nonnegative at every node.** -/
theorem gap_nonneg (hS : M.PricesSupport) (hb : M.borrowLimit = 0) (h : List Z) :
    0 ≤ M.gap (z₀ := z₀) (x₀ := x₀) K K' h := by
  set B := ‖(M.household z₀ 𝐏).valueFunction‖ + ‖(M.household z₀ 𝐐).valueFunction‖ with hB
  have hB0 : 0 ≤ B := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hβ0 := M.discount_pos.le
  have hbound : ∀ n : ℕ, ∀ g : List Z,
      -(M.discount ^ n * B) ≤ M.gap (z₀ := z₀) (x₀ := x₀) K K' g := by
    intro n
    induction n with
    | zero =>
      intro g
      have h1 := (M.household z₀ 𝐏).valueFunction.norm_coe_le_norm (M.pointState z₀ x₀ 𝐐 g)
      have h2 := (M.household z₀ 𝐐).valueFunction.norm_coe_le_norm (M.pointState z₀ x₀ 𝐐 g)
      rw [Real.norm_eq_abs] at h1 h2
      have := abs_le.1 h1
      have := abs_le.1 h2
      rw [gap, pow_zero, one_mul]
      linarith
    | succ n ih =>
      intro g
      refine le_trans ?_ (gap_step (K := K) hK' hS hb g)
      set p := (M.pointState z₀ x₀ 𝐐 g, M.policy z₀ 𝐐 (M.pointState z₀ x₀ 𝐐 g))
      have hsum : ∑ ze : Z × E, M.shockProb z₀ ze p * -(M.discount ^ n * B)
          ≤ ∑ ze : Z × E, M.shockProb z₀ ze p * M.gap (z₀ := z₀) (x₀ := x₀) K K' (ze.1 :: g) :=
        Finset.sum_le_sum fun ze _ => mul_le_mul_of_nonneg_left (ih _)
          (mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _))
      rw [← Finset.sum_mul, M.shockProb_sum z₀ p, one_mul] at hsum
      have := mul_le_mul_of_nonneg_left hsum hβ0
      rw [pow_succ]
      linarith
  by_contra hneg
  push Not at hneg
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < -M.gap (z₀ := z₀) (x₀ := x₀) K K' h / (B + 1)
    from div_pos (by linarith) (by linarith)) M.discount_lt_one
  have h1 := hbound n h
  have h2 : M.discount ^ n * B < -M.gap (z₀ := z₀) (x₀ := x₀) K K' h := by
    rw [lt_div_iff₀ (by linarith)] at hn
    have := mul_nonneg (pow_nonneg hβ0 n) (zero_le_one (α := ℝ))
    nlinarith [pow_nonneg hβ0 n]
  linarith

end gap

/-- **Uniqueness of sequential equilibrium from a point mass**, for the representative agent with
prices supporting the allocation. -/
theorem eq_of_isSequentialEquilibrium_dirac (hS : M.PricesSupport) (hb : M.borrowLimit = 0)
    {K K' : List Z → ℝ} (hK : M.IsSequentialEquilibrium z₀ (Measure.dirac x₀) K)
    (hK' : M.IsSequentialEquilibrium z₀ (Measure.dirac x₀) K') : K = K' := by
  set P := M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K with hP
  set Q := M.pricePath z₀ (M.initMass (Measure.dirac x₀)) K' with hQ
  funext h
  induction h with
  | nil => rw [hK.eq_pointState, hK'.eq_pointState]; rfl
  | cons z' h ih =>
    have hst : M.pointState z₀ x₀ P h = M.pointState z₀ x₀ Q h :=
      Prod.ext (Subtype.ext (by rw [← hK.eq_pointState, ← hK'.eq_pointState, ih])) rfl
    set s := M.pointState z₀ x₀ Q h with hs
    set a := M.policy z₀ Q s with ha
    -- the two values agree at the common state
    have hg1 : 0 ≤ M.gap (z₀ := z₀) (x₀ := x₀) K K' h := gap_nonneg hK' hS hb h
    have hg2 : 0 ≤ M.gap (z₀ := z₀) (x₀ := x₀) K' K h := gap_nonneg hK hS hb h
    rw [gap] at hg1 hg2
    rw [← hP, ← hQ] at hg1 hg2
    rw [hst] at hg2
    -- so the saving of `K'` attains the Bellman maximum at the prices of `K`
    have hf : a ∈ (M.household z₀ P).feasible s := policy_feasible_of_support hK' hS hb h
    have hobj := objective_ge_of_support (K := K) hK' hS hb h
    have hsum : 0 ≤ ∑ ze : Z × E, M.shockProb z₀ ze (s, a)
        * M.gap (z₀ := z₀) (x₀ := x₀) K K' (ze.1 :: h) :=
      Finset.sum_nonneg fun ze _ => mul_nonneg
        (mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _))
        (gap_nonneg hK' hS hb _)
    have hle := (M.household z₀ P).le_bellmanFn (M.household z₀ P).valueFunction hf
    have hfix : (M.household z₀ P).bellmanFn (M.household z₀ P).valueFunction s
        = (M.household z₀ P).valueFunction s :=
      congrFun (congrArg DFunLike.coe (M.household z₀ P).bellman_valueFunction) _
    have hmax : (M.household z₀ P).objective (M.household z₀ P).valueFunction s a
        = (M.household z₀ P).bellmanFn (M.household z₀ P).valueFunction s := by
      have := mul_nonneg M.discount_pos.le hsum
      rw [← hP, ← hQ] at hobj
      linarith
    have heq : a = M.policy z₀ P s :=
      M.optimal_saving_unique z₀ P hf (M.policy_mem z₀ P s) hmax (M.policy_optimal z₀ P s).symm
    rw [hK.eq_pointState, hK'.eq_pointState, M.pointState_cons_val, M.pointState_cons_val,
      ← hP, ← hQ, hst, ← heq]

end KSModel

/-! ### CRRA, Cobb–Douglas -/

namespace Coleman

variable [Unique E] (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)
  (hLbox : T.clampLab (V.efficiency default) = V.efficiency default)

include hLbox in
/-- Cobb–Douglas prices support the allocation in the CRRA model. -/
theorem crra_pricesSupport : (crraModel V T hγ).PricesSupport := fun z k a _ =>
  T.repCash_le_of_prices z hLbox k a

include hLbox in
/-- **Sequential equilibrium from a point mass is unique**: representative-agent CRRA,
Cobb–Douglas, labour inside its box; every `γ > 0`, every capital share. -/
theorem crra_eq_of_isSequentialEquilibrium_dirac (z₀ : Z) (x₀ : (crraModel V T hγ).AState)
    {K K' : List Z → ℝ}
    (hK : (crraModel V T hγ).IsSequentialEquilibrium z₀ (Measure.dirac x₀) K)
    (hK' : (crraModel V T hγ).IsSequentialEquilibrium z₀ (Measure.dirac x₀) K') : K = K' :=
  KSModel.eq_of_isSequentialEquilibrium_dirac (crra_pricesSupport V T hγ hLbox) rfl hK hK'

variable (hβR : V.discount * T.returnBound ≤ 1)

/-- **The Coleman capital path is the sequential equilibrium** from every point mass
(`β R̄ ≤ 1`). -/
theorem eq_capPath (z₀ : Z) (x₀ : (crraModel V T hγ).AState) {K : List Z → ℝ}
    (hK : (crraModel V T hγ).IsSequentialEquilibrium z₀ (Measure.dirac x₀) K) :
    K = fun h => ((crraData V T hγ hLbox hβR).capPath
      (OrderHom.gfp (Data.T (crraData V T hγ hLbox hβR))) z₀ ⟨x₀.1.1, x₀.1.2⟩ h : ℝ) :=
  crra_eq_of_isSequentialEquilibrium_dirac V T hγ hLbox z₀ x₀ hK
    (isSequentialEquilibrium_capPath V T hγ hLbox hβR z₀ x₀)

end Coleman

end KrusellSmith

end LeanEconomics
