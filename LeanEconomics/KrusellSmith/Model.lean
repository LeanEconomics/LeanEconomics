/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The Krusell–Smith economy: primitives and paths of aggregate capital

The first module of the existence proof for sequential equilibrium in a Krusell–Smith economy.
The proof finds the equilibrium as a fixed point, by `LeanEconomics.FixedPoint.schauderTychonoff`,
of the map that sends a path of aggregate capital to the path of mean assets it induces. This
module sets up the primitives and the domain of that map.

**Primitives** (`KSModel`). An aggregate shock `z` in a finite set `Z` follows a Markov chain
`aggProb`; an idiosyncratic state `e` in a finite set `E` moves with probabilities `idioProb z z'`
that may depend on today's and tomorrow's aggregate shock, as in Krusell and Smith (1998), where
unemployment rises in recessions. A household in state `e` supplies `efficiency e` units of labour
inelastically, saves in capital with `0 ≤ a' ≤ assetCap`, and discounts at `discount`. The gross
return and the wage are given functions of the aggregate shock, aggregate capital and aggregate
labour, continuous and bounded; with Cobb–Douglas production they are the marginal products,
clamped to a compact range (removing the clamp is a later step). Consumption may be required to
stay above a floor `consFloor` that labour income alone affords: the floor is `0` when utility is
finite at zero consumption, and a positive level that never binds at the optimum when utility
falls to `-∞` there (log and CRRA with `σ ≥ 1`, `LeanEconomics.KrusellSmith.KSInada`).

**The tree of histories.** From a given initial shock `z₀`, a node is the list of shocks drawn
since, newest first: the root is `[]` and the children of `h` are `z' :: h`. `shockAt z₀ h` is the
shock at node `h`. Aggregate labour on the tree is exogenous: the mass of households in each
idiosyncratic state evolves by `idioProb` along the tree from the initial masses (`stateMass`),
and labour at a node is their efficiency-weighted sum (`labour`).

**Paths of aggregate capital** (`capitalPaths`). A path assigns aggregate capital to every node;
capital at the root is the mean of the initial distribution and every value lies in
`[0, assetCap]`. In the product topology on `List Z → ℝ` this set is compact (Tychonoff) and
convex, and the space is locally convex and Hausdorff, which is what Schauder–Tychonoff needs.
-/

open Set

namespace LeanEconomics

namespace KrusellSmith

/-- The primitives of a **Krusell–Smith economy** with finitely many aggregate shocks `Z` and
idiosyncratic states `E`. -/
structure KSModel (Z E : Type*) [Fintype Z] [Fintype E] where
  /-- Transition probabilities of the aggregate shock. -/
  aggProb : Z → Z → ℝ
  aggProb_nonneg : ∀ z z', 0 ≤ aggProb z z'
  aggProb_sum : ∀ z, ∑ z', aggProb z z' = 1
  /-- Transition probabilities of the idiosyncratic state, given today's and tomorrow's
  aggregate shock. -/
  idioProb : Z → Z → E → E → ℝ
  idioProb_nonneg : ∀ z z' e e', 0 ≤ idioProb z z' e e'
  idioProb_sum : ∀ z z' e, ∑ e', idioProb z z' e e' = 1
  /-- Labour efficiency in each idiosyncratic state. -/
  efficiency : E → ℝ
  efficiency_nonneg : ∀ e, 0 ≤ efficiency e
  /-- The upper bound on asset holdings. -/
  assetCap : ℝ
  assetCap_pos : 0 < assetCap
  /-- The discount factor. -/
  discount : ℝ
  discount_pos : 0 < discount
  discount_lt_one : discount < 1
  /-- The gross return on capital, as a function of the aggregate shock, aggregate capital and
  aggregate labour. -/
  grossReturn : Z → ℝ → ℝ → ℝ
  continuous_grossReturn : ∀ z, Continuous fun p : ℝ × ℝ => grossReturn z p.1 p.2
  grossReturn_nonneg : ∀ z K L, 0 ≤ grossReturn z K L
  /-- An upper bound on the gross return. -/
  returnBound : ℝ
  grossReturn_le : ∀ z K L, grossReturn z K L ≤ returnBound
  /-- The wage, as a function of the aggregate shock, aggregate capital and aggregate labour. -/
  wage : Z → ℝ → ℝ → ℝ
  continuous_wage : ∀ z, Continuous fun p : ℝ × ℝ => wage z p.1 p.2
  wage_nonneg : ∀ z K L, 0 ≤ wage z K L
  /-- An upper bound on the wage. -/
  wageBound : ℝ
  wage_le : ∀ z K L, wage z K L ≤ wageBound
  /-- **The borrowing limit** `b ≥ 0`: households hold at least `-b`. The asset coordinate is the
  position shifted by `b`, in `[0, assetCap]`; debt service `R b` is deducted from cash, and the
  price functions read the shifted capital. `b = 0` is the no-borrowing economy. -/
  borrowLimit : ℝ
  borrowLimit_nonneg : 0 ≤ borrowLimit
  /-- A floor on consumption: `0` for utility finite at zero consumption; positive, and slack at
  the optimum, for utility that falls to `-∞` there (`LeanEconomics.KrusellSmith.KSInada`). -/
  consFloor : ℝ
  consFloor_nonneg : 0 ≤ consFloor
  /-- Labour income net of debt service at the borrowing limit affords the floor. -/
  consFloor_le_income : ∀ z K L e,
    consFloor ≤ wage z K L * efficiency e - grossReturn z K L * borrowLimit
  /-- Period utility of consumption. -/
  utility : ℝ → ℝ
  continuousOn_utility : ContinuousOn utility (Ici consFloor)
  strictConcaveOn_utility : StrictConcaveOn ℝ (Ici consFloor) utility
  monotoneOn_utility : MonotoneOn utility (Ici consFloor)

/-- The aggregate shock at node `h` of the tree of histories started at `z₀`: the newest shock
drawn, or `z₀` at the root. -/
def shockAt {Z : Type*} (z₀ : Z) (h : List Z) : Z := h.headD z₀

@[simp] theorem shockAt_nil {Z : Type*} (z₀ : Z) : shockAt z₀ ([] : List Z) = z₀ := rfl

@[simp] theorem shockAt_cons {Z : Type*} (z₀ z' : Z) (h : List Z) : shockAt z₀ (z' :: h) = z' := rfl

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- The mass of households in each idiosyncratic state at node `h`, from the initial masses
`m₀`: it evolves along the tree by the idiosyncratic transitions. -/
def stateMass (z₀ : Z) (m₀ : E → ℝ) : List Z → E → ℝ
  | [] => m₀
  | z' :: h => fun e' => ∑ e, stateMass z₀ m₀ h e * M.idioProb (shockAt z₀ h) z' e e'

/-- Aggregate labour at node `h`: the efficiency-weighted mass of households. -/
def labour (z₀ : Z) (m₀ : E → ℝ) (h : List Z) : ℝ :=
  ∑ e, M.stateMass z₀ m₀ h e * M.efficiency e

theorem stateMass_nonneg (z₀ : Z) {m₀ : E → ℝ} (hm₀ : ∀ e, 0 ≤ m₀ e) :
    ∀ h e, 0 ≤ M.stateMass z₀ m₀ h e
  | [], e => hm₀ e
  | _ :: h, _ => Finset.sum_nonneg fun e _ =>
      mul_nonneg (stateMass_nonneg z₀ hm₀ h e) (M.idioProb_nonneg _ _ _ _)

/-- Total mass is preserved along the tree. -/
theorem sum_stateMass (z₀ : Z) (m₀ : E → ℝ) : ∀ h, ∑ e, M.stateMass z₀ m₀ h e = ∑ e, m₀ e
  | [] => rfl
  | z' :: h => by
    simp only [stateMass]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, M.idioProb_sum, mul_one]
    exact sum_stateMass z₀ m₀ h

theorem labour_nonneg (z₀ : Z) {m₀ : E → ℝ} (hm₀ : ∀ e, 0 ≤ m₀ e) (h : List Z) :
    0 ≤ M.labour z₀ m₀ h :=
  Finset.sum_nonneg fun e _ =>
    mul_nonneg (M.stateMass_nonneg z₀ hm₀ h e) (M.efficiency_nonneg e)

/-- The **paths of aggregate capital**: capital `K₀` at the root and capital in `[0, assetCap]`
at every node. -/
def capitalPaths (K₀ : ℝ) : Set (List Z → ℝ) :=
  {K | K [] = K₀ ∧ ∀ h, K h ∈ Icc 0 M.assetCap}

theorem isCompact_capitalPaths (K₀ : ℝ) : IsCompact (M.capitalPaths K₀) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun _ : List Z => (isCompact_Icc : IsCompact (Icc 0 M.assetCap))) ?_ ?_
  · have hset : M.capitalPaths K₀ =
        {K | K [] = K₀} ∩ ⋂ h, (fun K : List Z → ℝ => K h) ⁻¹' Icc 0 M.assetCap := by
      ext K
      simp [capitalPaths]
    rw [hset]
    exact (isClosed_eq (continuous_apply _) continuous_const).inter
      (isClosed_iInter fun h => isClosed_Icc.preimage (continuous_apply h))
  · exact fun K hK h _ => hK.2 h

theorem convex_capitalPaths (K₀ : ℝ) : Convex ℝ (M.capitalPaths K₀) := by
  intro K hK K' hK' a b ha hb hab
  refine ⟨?_, fun h => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hK.1, hK'.1]
    rw [← add_mul, hab, one_mul]
  · exact (convex_Icc 0 M.assetCap) (hK.2 h) (hK'.2 h) ha hb hab

theorem capitalPaths_nonempty {K₀ : ℝ} (hK₀ : K₀ ∈ Icc 0 M.assetCap) :
    (M.capitalPaths K₀).Nonempty :=
  ⟨fun _ => K₀, rfl, fun _ => hK₀⟩

end KSModel

end KrusellSmith

end LeanEconomics
