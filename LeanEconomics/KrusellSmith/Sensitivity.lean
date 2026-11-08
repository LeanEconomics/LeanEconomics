/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Monotone

/-!
# How far marginal utility moves when prices move

Milestone M1 of the uniqueness argument (`UNIQUENESS_PLAN.md`). For two paths of capital and
labour `K` and `K'`, compare optimal consumption at the same state in the **marginal-utility
metric** `|u'(c^K) − u'(c^{K'})|`. At every node (`du_consumption_sub_le`)

  `|u'(c^K) − u'(c^{K'})| ≤ β Σ π (|ΔR'| · u'(c̲) + R̄ · B') + M (|ΔR| ā + |Δw| e)`,

where `ΔR, Δw` are the price differences at the node, `ΔR'` those at the children, `B'` bounds the
same gap at the children, `M` is a Lipschitz constant of `u'`, `c̲` a lower bound on consumption
and `R̄` the bound on the gross return. Unrolled down the tree with `β R̄ < 1`, this is the
sensitivity of consumption to prices; the assembly is the next module.

The core is `euler_compare`, pure real analysis: two consumers with Euler conditions at corners,
right-hand sides `F₁, F₂` (the first nonincreasing in saving) and cash `x₁, x₂` satisfy
`u'(c₁) − u'(c₂) ≤ β |F₁ − F₂| + M |x₁ − x₂|`. Either their saving and consumption are ordered
oppositely, or a corner binds, and then the gap is the cash difference; or the chain
`u'(c₁) ≤ β F₁(p₁) ≤ β F₁(p₂) ≤ β F₂(p₂) + β δ ≤ u'(c₂) + β δ` applies. No Lipschitz bound on the
right-hand side is needed, and no curvature ratio of utility appears.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

/-- **Comparison of Euler roots.** -/
theorem euler_compare {du F₁ F₂ : ℝ → ℝ} {floor cap β Mdu δ c₁ c₂ p₁ p₂ : ℝ}
    (hanti : ∀ x y, floor < x → x ≤ y → du y ≤ du x)
    (hLip : ∀ x y, floor < x → x ≤ y → du x - du y ≤ Mdu * (y - x)) (hMdu : 0 ≤ Mdu)
    (hβ : 0 ≤ β) (hc₁ : floor < c₁) (hc₂ : floor < c₂)
    (hp₁ : p₁ ∈ Icc 0 cap) (hp₂ : p₂ ∈ Icc 0 cap)
    (hF₁ : AntitoneOn F₁ (Icc 0 cap))
    (hle₁ : 0 < p₁ → du c₁ ≤ β * F₁ p₁)
    (hge₂ : p₂ < cap → β * F₂ p₂ ≤ du c₂)
    (hδ : |F₁ p₂ - F₂ p₂| ≤ δ) :
    du c₁ - du c₂ ≤ β * δ + Mdu * |(c₁ + p₁) - (c₂ + p₂)| := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  have hrest : 0 ≤ β * δ + Mdu * |(c₁ + p₁) - (c₂ + p₂)| :=
    add_nonneg (mul_nonneg hβ hδ0) (mul_nonneg hMdu (abs_nonneg _))
  by_cases hc : c₂ ≤ c₁
  · have := hanti c₂ c₁ hc₂ hc
    linarith
  push Not at hc
  have hgap := hLip c₁ c₂ hc₁ hc.le
  -- the cash difference covers any gap with consumption ordered against saving
  have hcash : c₂ - c₁ ≤ |(c₁ + p₁) - (c₂ + p₂)| → du c₁ - du c₂ ≤ β * δ
      + Mdu * |(c₁ + p₁) - (c₂ + p₂)| := fun h => by
    have := mul_le_mul_of_nonneg_left h hMdu
    nlinarith [mul_nonneg hβ hδ0]
  by_cases hp : p₁ < p₂
  · have h1 : c₂ - c₁ ≤ (c₂ + p₂) - (c₁ + p₁) := by linarith
    have h2 : (c₂ + p₂) - (c₁ + p₁) ≤ |(c₁ + p₁) - (c₂ + p₂)| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    exact hcash (h1.trans h2)
  push Not at hp
  by_cases h0 : p₁ = 0
  · have : p₂ = 0 := le_antisymm (h0 ▸ hp) hp₂.1
    exact hcash (by rw [h0, this, abs_sub_comm]; simpa using le_abs_self (c₂ - c₁))
  by_cases hcap : p₂ = cap
  · have : p₁ = cap := le_antisymm hp₁.2 (hcap ▸ hp)
    exact hcash (by rw [this, hcap, abs_sub_comm]; simpa using le_abs_self (c₂ - c₁))
  -- interior on both sides: the Euler chain
  have hp₁pos : 0 < p₁ := lt_of_le_of_ne hp₁.1 (Ne.symm h0)
  have hp₂cap : p₂ < cap := lt_of_le_of_ne hp₂.2 hcap
  have h1 := hle₁ hp₁pos
  have h2 : F₁ p₁ ≤ F₁ p₂ := hF₁ hp₂ hp₁ hp
  have h3 := hge₂ hp₂cap
  have h4 : F₁ p₂ ≤ F₂ p₂ + δ := by
    have := le_abs_self (F₁ p₂ - F₂ p₂)
    linarith
  have h5 := mul_le_mul_of_nonneg_left h2 hβ
  have h6 := mul_le_mul_of_nonneg_left h4 hβ
  nlinarith [mul_nonneg hMdu (abs_nonneg ((c₁ + p₁) - (c₂ + p₂)))]

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (U : M.SmoothUtility)

theorem SmoothUtility.du_anti {x y : ℝ} (hx : M.consFloor < x) (hxy : x ≤ y) :
    U.du y ≤ U.du x := by
  rcases hxy.lt_or_eq with hlt | rfl
  · have h1 := U.le_sub (x := y) (y := x) hx.le (hx.trans hlt) hlt.le
    have h2 := U.sub_le (x := y) (y := x) hx hlt.le
    have : (y - x) * U.du y ≤ (y - x) * U.du x := by linarith
    exact le_of_mul_le_mul_left this (sub_pos.2 hlt)
  · exact le_rfl

theorem SmoothUtility.du_nonneg {x : ℝ} (hx : M.consFloor < x) : 0 ≤ U.du x := by
  have h := U.sub_le (x := x + 1) (y := x) hx (by linarith)
  have hm := M.monotoneOn_utility (mem_Ici.2 hx.le) (mem_Ici.2 (by linarith : M.consFloor ≤ x + 1))
    (by linarith : x ≤ x + 1)
  linarith

variable (z₀ : Z)

/-- The Euler right-hand side is nonincreasing in saving: richer children consume more. -/
theorem eulerRhs_antitoneOn (K : List Z → ℝ × ℝ) (hsl : M.Slack z₀ K) (s : M.State) :
    AntitoneOn (M.eulerRhs U z₀ K s) (Icc 0 M.assetCap) := by
  intro a ha b hb hab
  refine Finset.sum_le_sum fun ze _ => ?_
  have hc := M.consumption_mono z₀ K ha hb hab ⟨ze.2, ze.1 :: s.2.node⟩
  have hd := U.du_anti (hsl (M.stateAt a ⟨ze.2, ze.1 :: s.2.node⟩)) hc
  have hpR : 0 ≤ M.shockProb z₀ ze (s, b) * M.returnAt z₀ K (ze.1 :: s.2.node) :=
    mul_nonneg (M.shockProb_nonneg' z₀ ze (s, b)) (M.returnAt_nonneg z₀ K _)
  exact mul_le_mul_of_nonneg_left hd hpR

/-- The sensitivity bound at one node, in the marginal-utility metric. -/
theorem du_consumption_sub_le {K K' : List Z → ℝ × ℝ} (hsl : M.Slack z₀ K)
    (hsl' : M.Slack z₀ K') {cLo Mdu : ℝ} (hcLo : M.consFloor < cLo)
    (hlo : ∀ s, cLo ≤ M.consumption z₀ K s)
    (hLip : ∀ x y, M.consFloor < x → x ≤ y → U.du x - U.du y ≤ Mdu * (y - x)) (hMdu : 0 ≤ Mdu)
    (s : M.State) (B : Z × E → ℝ)
    (hB : ∀ ze : Z × E, ∀ a' ∈ Icc 0 M.assetCap,
      |U.du (M.consumption z₀ K (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩))
        - U.du (M.consumption z₀ K' (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩))| ≤ B ze) :
    |U.du (M.consumption z₀ K s) - U.du (M.consumption z₀ K' s)|
      ≤ M.discount * ∑ ze : Z × E, M.shockProb z₀ ze (s, 0)
          * (|M.returnAt z₀ K (ze.1 :: s.2.node) - M.returnAt z₀ K' (ze.1 :: s.2.node)| * U.du cLo
            + M.returnBound * B ze)
        + Mdu * |M.cash z₀ K s - M.cash z₀ K' s| := by
  set δ := ∑ ze : Z × E, M.shockProb z₀ ze (s, 0)
    * (|M.returnAt z₀ K (ze.1 :: s.2.node) - M.returnAt z₀ K' (ze.1 :: s.2.node)| * U.du cLo
      + M.returnBound * B ze) with hδdef
  have hanti : ∀ x y, M.consFloor < x → x ≤ y → U.du y ≤ U.du x := fun x y hx hxy =>
    U.du_anti hx hxy
  -- the two right-hand sides are close at every saving
  have hFF : ∀ a' ∈ Icc 0 M.assetCap,
      |M.eulerRhs U z₀ K s a' - M.eulerRhs U z₀ K' s a'| ≤ δ := by
    intro a' ha'
    simp only [eulerRhs]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ze _ => ?_)
    set c1 := M.consumption z₀ K (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
    set c2 := M.consumption z₀ K' (M.stateAt a' ⟨ze.2, ze.1 :: s.2.node⟩)
    set R1 := M.returnAt z₀ K (ze.1 :: s.2.node)
    set R2 := M.returnAt z₀ K' (ze.1 :: s.2.node)
    set π := M.shockProb z₀ ze (s, a')
    have hπ : 0 ≤ π := M.shockProb_nonneg' z₀ ze (s, a')
    have hπ0 : π = M.shockProb z₀ ze (s, 0) := rfl
    have hR2 : 0 ≤ R2 := M.returnAt_nonneg z₀ K' _
    have hR2b : R2 ≤ M.returnBound := M.grossReturn_le _ _ _
    have hd1 : 0 ≤ U.du c1 := U.du_nonneg (hsl _)
    have hd1b : U.du c1 ≤ U.du cLo := U.du_anti hcLo (hlo _)
    have hBz := hB ze a' ha'
    have hBz0 : 0 ≤ B ze := (abs_nonneg _).trans hBz
    have e : π * R1 * U.du c1 - π * R2 * U.du c2
        = π * ((R1 - R2) * U.du c1 + R2 * (U.du c1 - U.du c2)) := by ring
    rw [e, abs_mul, abs_of_nonneg hπ, ← hπ0]
    refine mul_le_mul_of_nonneg_left ?_ hπ
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hd1]
      exact mul_le_mul_of_nonneg_left hd1b (abs_nonneg _)
    · rw [abs_mul, abs_of_nonneg hR2]
      exact mul_le_mul hR2b hBz (abs_nonneg _) (hR2.trans hR2b)
  have hβ := M.discount_pos.le
  -- the two Euler roots, through `euler_compare` both ways
  have hpm := M.policy_mem z₀ K s
  have hpm' := M.policy_mem z₀ K' s
  have hp := M.mem_Icc_of_mem_feasible z₀ K hpm
  have hp' := M.mem_Icc_of_mem_feasible z₀ K' hpm'
  have hx : M.consumption z₀ K s + M.policy z₀ K s = M.cash z₀ K s := by
    unfold consumption
    ring
  have hx' : M.consumption z₀ K' s + M.policy z₀ K' s = M.cash z₀ K' s := by
    unfold consumption
    ring
  have h12 := euler_compare (du := U.du) (δ := δ) (F₁ := M.eulerRhs U z₀ K s)
    (F₂ := M.eulerRhs U z₀ K' s) hanti hLip hMdu hβ (hsl s) (hsl' s) hp hp'
    (M.eulerRhs_antitoneOn U z₀ K hsl s)
    (fun h => M.euler_le U z₀ K hsl s h) (fun h => M.euler_ge U z₀ K' hsl' s h)
    (hFF _ hp')
  have h21 := euler_compare (du := U.du) (δ := δ) (F₁ := M.eulerRhs U z₀ K' s)
    (F₂ := M.eulerRhs U z₀ K s) hanti hLip hMdu hβ (hsl' s) (hsl s) hp' hp
    (M.eulerRhs_antitoneOn U z₀ K' hsl' s)
    (fun h => M.euler_le U z₀ K' hsl' s h) (fun h => M.euler_ge U z₀ K hsl s h)
    (by rw [abs_sub_comm]; exact hFF _ hp)
  rw [hx, hx'] at h12 h21
  rw [abs_sub_comm (M.cash z₀ K' s)] at h21
  rw [abs_le]
  constructor <;> linarith

/-- The cash difference at a node is the price difference times assets and efficiency. -/
theorem cash_sub_le (K K' : List Z → ℝ × ℝ) {a : ℝ} (ha : a ∈ Icc 0 M.assetCap)
    (l : Label Z E) :
    |M.cash z₀ K (M.stateAt a l) - M.cash z₀ K' (M.stateAt a l)|
      ≤ |M.returnAt z₀ K l.node - M.returnAt z₀ K' l.node| * (M.assetCap + M.borrowLimit)
        + |M.wageAt z₀ K l.node - M.wageAt z₀ K' l.node| * M.efficiency l.idio := by
  rw [M.cash_stateAt z₀ K ha, M.cash_stateAt z₀ K' ha]
  have e : M.returnAt z₀ K l.node * a + M.wageAt z₀ K l.node * M.efficiency l.idio
      - M.returnAt z₀ K l.node * M.borrowLimit
      - (M.returnAt z₀ K' l.node * a + M.wageAt z₀ K' l.node * M.efficiency l.idio
        - M.returnAt z₀ K' l.node * M.borrowLimit)
      = (M.returnAt z₀ K l.node - M.returnAt z₀ K' l.node) * (a - M.borrowLimit)
        + (M.wageAt z₀ K l.node - M.wageAt z₀ K' l.node) * M.efficiency l.idio := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_le]
    constructor <;> linarith [ha.1, ha.2, M.borrowLimit_nonneg, M.assetCap_pos]
  · rw [abs_mul, abs_of_nonneg (M.efficiency_nonneg _)]

end KSModel

end KrusellSmith

end LeanEconomics
