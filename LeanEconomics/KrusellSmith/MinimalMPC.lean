/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CarrollKimballIterate

/-!
# A minimal marginal propensity to consume on the tree

The contraction arguments (`Contraction.lean`, `LawContraction.lean`) bound how fast saving rises
with assets by the gross return, `θ = R̄` (`policy_sub_le`): saving and consumption both rise with
cash. With CRRA utility the household also consumes a fixed fraction of every extra unit of cash
(Carroll–Shanker's minimal MPC), and saving then rises at most at

  `θ = R̄ (β R̄)^{1/γ} / R̲`,

below one when `β R̄ < 1` and the return spread `R̄ / R̲` is small — gross returns above one
allowed.

**The step** (`mpcBound_bellman`). Write `MPCBound κ w` for "against the continuation `w`,
consumption rises by at least `κ` times the rise in cash, at every label". Suppose the children,
consuming against `w₀`, satisfy `MPCBound κ' w₀`. Raise assets so that saving rises by `Δs > 0`.
The Euler inequalities (`consumptionOf_le_egmC`, and `egmC_le_consumptionOf` here) bracket
consumption by the endogenous-gridpoint map, a constant `(β S)^{-1/γ}` times a power mean of
exponent `-γ` of the children's consumption. The children's consumption rises by at least
`κ' R̲ Δs` everywhere, and a power mean with negative exponent is concave and homogeneous, hence
superadditive (`powerMean_add_const_ge`), so consumption today rises by at least `ψ Δs` with
`ψ = A κ'`, `A = R̲ / (β R̄)^{1/γ}`. Cash splits into consumption and saving, so consumption takes
at least the share `ψ / (1 + ψ)` of the rise in cash.

**The iteration** (`mpcBound_iterate`). With no future the household consumes its cash
(`MPC = 1`); the map `κ ↦ A κ / (1 + A κ)` keeps `κ ≥ 1 − 1/A` when `A > 1`, so every Bellman
iterate from `0` has `MPCBound (1 − 1/A)`.

**The limit** (`tendsto_policyOf_iterate`). The iterates converge to the value function, and the
maximiser moves continuously with the continuation where it is unique — Berge's maximum theorem
with the continuation as the parameter (`StochasticDynamicProgram.continuousAt_argmax_selection`)
— so the iterates' saving converges to the policy, and the bound passes to the limit:
**`abs_policy_sub_le_minMPC`**, `|a'(a) − a'(b)| ≤ θ |a − b|`.

Hypotheses: CRRA marginal utility above the floor, returns in `[R̲, R̄]` with `R̲ > 0` and
`(β R̄)^{1/γ} < R̲`, and the consumption floor slack along the Bellman iterates. The asset cap may
bind.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

/-! ### Berge along the continuation -/

namespace StochasticDynamicProgram

variable {S A Z : Type*} [TopologicalSpace S] [TopologicalSpace A] [Fintype Z]
  (D : StochasticDynamicProgram S A Z)

/-- **The maximiser moves continuously with the continuation where it is unique.** -/
theorem continuousAt_argmax_selection (s : S) {v₀ : S →ᵇ ℝ} {p₀ : A}
    (h₀ : argmax (fun (v : S →ᵇ ℝ) (a : A) => D.objective v s a) (fun _ => D.feasible s) v₀
      = {p₀})
    {g : (S →ᵇ ℝ) → A}
    (hg : ∀ v, g v ∈ argmax (fun (v : S →ᵇ ℝ) (a : A) => D.objective v s a)
      (fun _ => D.feasible s) v) :
    ContinuousAt g v₀ := by
  have hf : Continuous ↿(fun (v : S →ᵇ ℝ) (a : A) => D.objective v s a) := by
    change Continuous fun p : (S →ᵇ ℝ) × A =>
      D.reward (s, p.2) + (D.discount : ℝ) * ∑ z, D.prob z (s, p.2) * p.1 (D.transition z (s, p.2))
    refine (D.reward.continuous.comp (continuous_const.prodMk continuous_snd)).add
      (continuous_const.mul (continuous_finsetSum _ fun z _ => ?_))
    exact ((D.prob z).continuous.comp (continuous_const.prodMk continuous_snd)).mul
      (continuous_eval.comp (continuous_fst.prodMk
        ((D.transition z).continuous.comp (continuous_const.prodMk continuous_snd))))
  have huhc := upperHemicontinuousAt_argmax hf (fun _ => D.feasible_nonempty s)
    (fun _ => D.isCompact_feasible s) (upperHemicontinuous_const (D.feasible s) v₀)
    (lowerHemicontinuous_const (D.feasible s) v₀)
  rw [ContinuousAt, tendsto_nhds]
  intro V hV hp
  have hg₀ : g v₀ = p₀ := by
    have := hg v₀
    rw [h₀] at this
    exact this
  rw [hg₀] at hp
  have hsub : argmax (fun (v : S →ᵇ ℝ) (a : A) => D.objective v s a) (fun _ => D.feasible s) v₀
      ⊆ V := by
    rw [h₀]
    simpa using hp
  filter_upwards [huhc.forall_isOpen V hV hsub] with v h
  exact h (hg v)

end StochasticDynamicProgram

/-! ### Power means: superadditive against constants -/

section PowerMean

variable {ι : Type*} [Fintype ι] {w : ι → ℝ} {p : ℝ} {x : ι → ℝ}

theorem powerMean_const_of_nonneg (hp : p ≠ 0) (hw1 : ∑ i, w i = 1) {c : ℝ} (hc : 0 ≤ c) :
    powerMean w p (fun _ => c) = c := by
  simp only [powerMean]
  rw [← Finset.sum_mul, hw1, one_mul, ← Real.rpow_mul hc, mul_one_div_cancel hp, Real.rpow_one]

/-- **A power mean with a negative exponent gains at least a common increment.** -/
theorem powerMean_add_const_ge (hp : p < 0) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hx : ∀ i, 0 < x i) {δ : ℝ} (hδ : 0 ≤ δ) :
    powerMean w p x + δ ≤ powerMean w p (fun i => x i + δ) := by
  rcases hδ.eq_or_lt with rfl | hδ
  · simp
  have hy : ∀ i : ι, 0 < (fun _ => δ) i := fun _ => hδ
  have hc := powerMean_concave hp hw hw1 hx hy (θ := 1 / 2) (φ := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  have hz : ∀ i, 0 < 1 / 2 * x i + 1 / 2 * δ := fun i => by
    have := hx i
    positivity
  have hs := powerMean_smul hp.ne (c := 2) (by norm_num) hw hw1 hz
  have e : (fun i => 2 * (1 / 2 * x i + 1 / 2 * δ)) = fun i => x i + δ := by
    funext i
    ring
  rw [e] at hs
  rw [hs, powerMean_const_of_nonneg hp.ne hw1 hδ.le] at *
  linarith

end PowerMean

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (U : M.SmoothUtility) (z₀ : Z) (K : List Z → ℝ × ℝ)

/-! ### The iterates' saving converges to the policy -/

/-- **Saving against the Bellman iterates converges to the saving policy.** -/
theorem tendsto_policyOf_iterate (s : M.State) :
    Tendsto (fun n => M.policyOf z₀ K (((M.household z₀ K).bellman)^[n] 0) s) atTop
      (𝓝 (M.policy z₀ K s)) := by
  have hc := (M.household z₀ K).continuousAt_argmax_selection s
    (v₀ := (M.household z₀ K).valueFunction) (p₀ := M.policy z₀ K s)
    (by exact M.argmax_eq_singleton z₀ K s) (g := fun v => M.policyOf z₀ K v s)
    fun v => ⟨M.policyOf_mem z₀ K v s, isMaxOn_iff.2
      (Classical.choose_spec ((M.household z₀ K).exists_optimal_action v s)).2.2⟩
  exact hc.tendsto.comp ((M.household z₀ K).tendsto_iterate_valueFunction 0)

/-! ### The minimal MPC, one Bellman step -/

/-- **Consumption rises by at least `κ` times the rise in cash**, against the continuation `w`,
at every label. -/
def MPCBound (κ : ℝ) (w : M.State →ᵇ ℝ) : Prop :=
  ∀ (l : Label Z E) {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ M.assetCap →
    κ * (M.returnAt z₀ K l.node * (b - a))
      ≤ M.consumptionOf z₀ K w (M.stateAt b l) - M.consumptionOf z₀ K w (M.stateAt a l)

theorem consumptionOf_sub (w : M.State →ᵇ ℝ) {a b : ℝ} (ha : a ∈ Icc 0 M.assetCap)
    (hb : b ∈ Icc 0 M.assetCap) (l : Label Z E) :
    M.consumptionOf z₀ K w (M.stateAt b l) - M.consumptionOf z₀ K w (M.stateAt a l)
      = M.returnAt z₀ K l.node * (b - a)
        - (M.policyOf z₀ K w (M.stateAt b l) - M.policyOf z₀ K w (M.stateAt a l)) := by
  simp only [consumptionOf]
  rw [M.cash_stateAt z₀ K ha, M.cash_stateAt z₀ K hb]
  ring

theorem returnAt_le_returnBound (h : List Z) : M.returnAt z₀ K h ≤ M.returnBound :=
  M.grossReturn_le _ _ _

theorem retSum_le (s : M.State) : M.retSum z₀ K s ≤ M.returnBound := by
  calc M.retSum z₀ K s ≤ ∑ ze : Z × E, M.shockProb z₀ ze (s, 0) * M.returnBound :=
        Finset.sum_le_sum fun ze _ => mul_le_mul_of_nonneg_left
          (M.returnAt_le_returnBound z₀ K _) (M.shockProb_nonneg' z₀ ze _)
    _ = M.returnBound := by rw [← Finset.sum_mul, M.shockProb_sum, one_mul]

variable {γ : ℝ} (hγ : 0 < γ) (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ))
  (hR : ∀ h, 0 < M.returnAt z₀ K h)

include hγ hdu hR in
/-- **Above the borrowing limit, consumption is at least the endogenous-gridpoint value of the
saving chosen** (the Euler inequality `u'(c) ≤ β E[R' u'(c')]`); the asset cap may bind. -/
theorem egmC_le_consumptionOf (w₀ : M.State →ᵇ ℝ) (hsl₀ : M.SlackOf z₀ K w₀) (s : M.State)
    (hsl : M.consFloor < M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s)
    (hpos : 0 < M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s) :
    M.egmC z₀ K w₀ γ s (M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s)
      ≤ M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s := by
  set c := M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s
  set p := M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s
  have hc : 0 < c := M.consFloor_nonneg.trans_lt hsl
  have he := M.eulerOf_le U z₀ K w₀ hsl₀ s hsl hpos
  rw [hdu c hsl] at he
  have hcg : 0 < c ^ (-γ) := Real.rpow_pos_of_pos hc _
  have hstep := Real.rpow_le_rpow_of_nonpos hcg he (show -(1 / γ) ≤ 0 by
    rw [neg_nonpos]; positivity)
  have hexp : (-γ) * (-(1 / γ)) = 1 := by field_simp
  rw [← Real.rpow_mul hc.le, hexp, Real.rpow_one] at hstep
  rw [← M.rpow_eulerRhsOf_eq_egmC U z₀ K hγ hdu hR w₀ hsl₀ s p]
  exact hstep

/-- The gain of the minimal-MPC recursion, `A = R̲ / (β R̄)^{1/γ}`. -/
noncomputable def mpcGain (M : KSModel Z E) (γ Rlo : ℝ) : ℝ :=
  Rlo / (M.discount * M.returnBound) ^ (1 / γ)

variable {Rlo : ℝ} (hRlo0 : 0 < Rlo) (hRlo : ∀ h, Rlo ≤ M.returnAt z₀ K h)

include hγ hdu hR hRlo0 hRlo in
/-- **The minimal-MPC step**: children consuming at least `κ'` of extra cash against `w₀` make
the household one Bellman step later consume at least `A κ' / (1 + A κ')` of it. -/
theorem mpcBound_bellman {w₀ : M.State →ᵇ ℝ} (hsl₀ : M.SlackOf z₀ K w₀)
    (hsl : M.SlackOf z₀ K ((M.household z₀ K).bellman w₀)) {κ' : ℝ} (hκ' : 0 ≤ κ')
    (hw₀ : M.MPCBound z₀ K κ' w₀) :
    M.MPCBound z₀ K (M.mpcGain γ Rlo * κ' / (1 + M.mpcGain γ Rlo * κ'))
      ((M.household z₀ K).bellman w₀) := by
  intro l a b ha hab hb
  set v := (M.household z₀ K).bellman w₀
  have ha' : a ∈ Icc 0 M.assetCap := ⟨ha, hab.trans hb⟩
  have hb' : b ∈ Icc 0 M.assetCap := ⟨ha.trans hab, hb⟩
  set sa := M.stateAt a l
  set sb := M.stateAt b l
  set pa := M.policyOf z₀ K v sa
  set pb := M.policyOf z₀ K v sb
  have hΔ := M.consumptionOf_sub z₀ K v ha' hb' l
  set Δx := M.returnAt z₀ K l.node * (b - a)
  have hΔx : 0 ≤ Δx := mul_nonneg (hR _).le (sub_nonneg.2 hab)
  have hβR : 0 < M.discount * M.returnBound :=
    mul_pos M.discount_pos ((hR []).trans_le (M.returnAt_le_returnBound z₀ K []))
  have hB : 0 < (M.discount * M.returnBound) ^ (1 / γ) := Real.rpow_pos_of_pos hβR _
  have hA0 : 0 ≤ M.mpcGain γ Rlo := div_nonneg hRlo0.le hB.le
  set ψ := M.mpcGain γ Rlo * κ'
  have hψ : 0 ≤ ψ := mul_nonneg hA0 hκ'
  have hψ1 : 0 < 1 + ψ := by linarith
  have hκ1 : ψ / (1 + ψ) ≤ 1 := (div_le_one hψ1).2 (by linarith)
  rw [hΔ]
  rcases le_or_gt pb pa with hp | hp
  · -- saving does not rise
    calc ψ / (1 + ψ) * Δx ≤ 1 * Δx := mul_le_mul_of_nonneg_right hκ1 hΔx
      _ ≤ Δx - (pb - pa) := by linarith
  -- saving rises: bracket both consumptions by the endogenous-gridpoint map
  have hpma := M.policyOf_mem z₀ K v sa
  have hpmb := M.policyOf_mem z₀ K v sb
  have hpa0 : 0 ≤ pa := hpma.1
  have hpbcap : pb ≤ M.assetCap := hpmb.2.trans (min_le_left _ _)
  have hpacap : pa < M.assetCap := hp.trans_le hpbcap
  have hpb0 : 0 < pb := hpa0.trans_lt hp
  have h1 := M.consumptionOf_le_egmC U z₀ K hγ hdu hR w₀ hsl₀ sa (hsl sa) hpacap
  have h2 := M.egmC_le_consumptionOf U z₀ K hγ hdu hR w₀ hsl₀ sb (hsl sb) hpb0
  have hsame : M.egmC z₀ K w₀ γ sb pb = M.egmC z₀ K w₀ γ sa pb := rfl
  rw [hsame] at h2
  -- the children's consumption rises by at least `κ' R̲ Δs`
  set δ := κ' * Rlo * (pb - pa)
  have hδ : 0 ≤ δ := mul_nonneg (mul_nonneg hκ' hRlo0.le) (sub_nonneg.2 hp.le)
  set xc : Z × E → ℝ := fun ze =>
    M.consumptionOf z₀ K w₀ (M.stateAt pa ⟨ze.2, ze.1 :: sa.2.node⟩)
  set yc : Z × E → ℝ := fun ze =>
    M.consumptionOf z₀ K w₀ (M.stateAt pb ⟨ze.2, ze.1 :: sa.2.node⟩)
  have hxc : ∀ ze, 0 < xc ze := fun ze =>
    M.consFloor_nonneg.trans_lt (hsl₀ _)
  have hyc : ∀ ze, 0 < yc ze := fun ze =>
    M.consFloor_nonneg.trans_lt (hsl₀ _)
  have hxy : ∀ ze, xc ze + δ ≤ yc ze := by
    intro ze
    have hc := hw₀ ⟨ze.2, ze.1 :: sa.2.node⟩ hpa0 hp.le hpbcap
    have hRc := hRlo (ze.1 :: sa.2.node)
    have : δ ≤ κ' * (M.returnAt z₀ K (ze.1 :: sa.2.node) * (pb - pa)) := by
      simp only [δ]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRc hκ')
        (sub_nonneg.2 hp.le)
    change xc ze + δ ≤ yc ze
    simp only [xc, yc]
    linarith
  have hw := M.egmWeight_nonneg z₀ K hR sa
  have hw1 := M.sum_egmWeight z₀ K hR sa
  have hγn : -γ < 0 := by linarith
  have hPM : powerMean (M.egmWeight z₀ K sa) (-γ) xc + δ
      ≤ powerMean (M.egmWeight z₀ K sa) (-γ) yc :=
    (powerMean_add_const_ge hγn hw hw1 hxc hδ).trans
      (powerMean_mono hγn hw hw1 (fun ze => (hxc ze).trans_le (le_add_of_nonneg_right hδ))
        hyc hxy)
  -- the constant of the endogenous-gridpoint map
  set C := (M.discount * M.retSum z₀ K sa) ^ (-(1 / γ))
  have hS := M.retSum_pos z₀ K hR sa
  have hβS : 0 < M.discount * M.retSum z₀ K sa := mul_pos M.discount_pos hS
  have hC : ((M.discount * M.returnBound) ^ (1 / γ))⁻¹ ≤ C := by
    simp only [C]
    rw [Real.rpow_neg hβS.le]
    refine inv_anti₀ (Real.rpow_pos_of_pos hβS _) ?_
    exact Real.rpow_le_rpow hβS.le
      (mul_le_mul_of_nonneg_left (M.retSum_le z₀ K sa) M.discount_pos.le) (by positivity)
  have hegm : M.egmC z₀ K w₀ γ sa pb - M.egmC z₀ K w₀ γ sa pa ≥ C * δ := by
    have e1 : M.egmC z₀ K w₀ γ sa pb = C * powerMean (M.egmWeight z₀ K sa) (-γ) yc := rfl
    have e2 : M.egmC z₀ K w₀ γ sa pa = C * powerMean (M.egmWeight z₀ K sa) (-γ) xc := rfl
    rw [e1, e2]
    have hC0 : 0 ≤ C := Real.rpow_nonneg hβS.le _
    nlinarith [mul_le_mul_of_nonneg_left hPM hC0]
  -- consumption rises by at least `ψ Δs`
  have hψΔ : ψ * (pb - pa) ≤ C * δ := by
    have e : ψ * (pb - pa) = ((M.discount * M.returnBound) ^ (1 / γ))⁻¹ * δ := by
      simp only [ψ, δ, mpcGain]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hC hδ
  have hkey : ψ * (pb - pa) ≤ Δx - (pb - pa) := by
    have : M.egmC z₀ K w₀ γ sa pb - M.egmC z₀ K w₀ γ sa pa
        ≤ M.consumptionOf z₀ K v sb - M.consumptionOf z₀ K v sa := by linarith
    rw [hΔ] at this
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hψ1]
  nlinarith [hkey]

include hγ hdu hR hRlo0 hRlo in
/-- **Every Bellman iterate from `0` has the minimal MPC `1 − 1/A`**, when `A > 1`. -/
theorem mpcBound_iterate (hA : 1 < M.mpcGain γ Rlo)
    (hsl : ∀ n : ℕ, M.SlackOf z₀ K (((M.household z₀ K).bellman)^[n] 0)) :
    ∀ n : ℕ, M.MPCBound z₀ K (1 - 1 / M.mpcGain γ Rlo)
      (((M.household z₀ K).bellman)^[n] 0) := by
  have hA0 : 0 < M.mpcGain γ Rlo := one_pos.trans hA
  have hκ0 : 0 ≤ 1 - 1 / M.mpcGain γ Rlo := by
    rw [sub_nonneg, div_le_one hA0]
    exact hA.le
  intro n
  induction n with
  | zero =>
    intro l a b ha hab hb
    have ha' : a ∈ Icc 0 M.assetCap := ⟨ha, hab.trans hb⟩
    have hb' : b ∈ Icc 0 M.assetCap := ⟨ha.trans hab, hb⟩
    rw [Function.iterate_zero_apply, M.consumptionOf_sub z₀ K 0 ha' hb' l,
      M.policyOf_zero z₀ K, M.policyOf_zero z₀ K, sub_self, sub_zero]
    have hΔx : 0 ≤ M.returnAt z₀ K l.node * (b - a) :=
      mul_nonneg (hR _).le (sub_nonneg.2 hab)
    have : 1 - 1 / M.mpcGain γ Rlo ≤ 1 := by
      have := div_nonneg zero_le_one hA0.le
      linarith
    calc _ ≤ 1 * (M.returnAt z₀ K l.node * (b - a)) := mul_le_mul_of_nonneg_right this hΔx
      _ = _ := one_mul _
  | succ n ih =>
    have hs := M.mpcBound_bellman U z₀ K hγ hdu hR hRlo0 hRlo (hsl n)
      (by have := hsl (n + 1); rwa [Function.iterate_succ_apply'] at this) hκ0 ih
    have e : M.mpcGain γ Rlo * (1 - 1 / M.mpcGain γ Rlo)
        / (1 + M.mpcGain γ Rlo * (1 - 1 / M.mpcGain γ Rlo)) = 1 - 1 / M.mpcGain γ Rlo := by
      have hne := hA0.ne'
      rw [mul_sub, mul_one, mul_one_div_cancel hne,
        show (1 : ℝ) + (M.mpcGain γ Rlo - 1) = M.mpcGain γ Rlo by ring, sub_div, div_self hne]
    rw [e] at hs
    rw [Function.iterate_succ_apply']
    exact hs

include hγ hdu hR hRlo0 hRlo in
/-- **The saving policy rises with assets at most at `R_h / A`**, the limit of the iterates. -/
theorem policy_sub_le_minMPC (hA : 1 < M.mpcGain γ Rlo)
    (hsl : ∀ n : ℕ, M.SlackOf z₀ K (((M.household z₀ K).bellman)^[n] 0))
    (l : Label Z E) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.assetCap) :
    M.policy z₀ K (M.stateAt b l) - M.policy z₀ K (M.stateAt a l)
      ≤ M.returnAt z₀ K l.node * (b - a) / M.mpcGain γ Rlo := by
  have ha' : a ∈ Icc 0 M.assetCap := ⟨ha, hab.trans hb⟩
  have hb' : b ∈ Icc 0 M.assetCap := ⟨ha.trans hab, hb⟩
  have hlim := (M.tendsto_policyOf_iterate z₀ K (M.stateAt b l)).sub
    (M.tendsto_policyOf_iterate z₀ K (M.stateAt a l))
  refine le_of_tendsto' hlim fun n => ?_
  have hm := M.mpcBound_iterate U z₀ K hγ hdu hR hRlo0 hRlo hA hsl n l ha hab hb
  rw [M.consumptionOf_sub z₀ K _ ha' hb' l] at hm
  have e : M.returnAt z₀ K l.node * (b - a) / M.mpcGain γ Rlo
      = M.returnAt z₀ K l.node * (b - a)
        - (1 - 1 / M.mpcGain γ Rlo) * (M.returnAt z₀ K l.node * (b - a)) := by ring
  rw [e]
  linarith

/-- The minimal-MPC saving slope, `θ = R̄ (β R̄)^{1/γ} / R̲`. -/
noncomputable def minMPCSlope (M : KSModel Z E) (γ Rlo : ℝ) : ℝ :=
  M.returnBound / M.mpcGain γ Rlo

include hγ hdu hR hRlo0 hRlo in
/-- **Saving is `θ`-Lipschitz in assets** with the minimal-MPC slope `θ = R̄ (β R̄)^{1/γ} / R̲`. -/
theorem abs_policy_sub_le_minMPC (hA : 1 < M.mpcGain γ Rlo)
    (hsl : ∀ n : ℕ, M.SlackOf z₀ K (((M.household z₀ K).bellman)^[n] 0))
    (a b : ↥(Icc (0 : ℝ) M.assetCap)) (l : Label Z E) :
    |M.policy z₀ K (a, l) - M.policy z₀ K (b, l)| ≤ M.minMPCSlope γ Rlo * |(a : ℝ) - b| := by
  have hA0 : 0 < M.mpcGain γ Rlo := one_pos.trans hA
  have ha : M.stateAt (a : ℝ) l = (a, l) := by simp only [stateAt, M.clampAssets_of_mem a.2]
  have hb : M.stateAt (b : ℝ) l = (b, l) := by simp only [stateAt, M.clampAssets_of_mem b.2]
  have key : ∀ x y : ↥(Icc (0 : ℝ) M.assetCap), (x : ℝ) ≤ y →
      |M.policy z₀ K (x, l) - M.policy z₀ K (y, l)| ≤ M.minMPCSlope γ Rlo * |(x : ℝ) - y| := by
    intro x y hxy
    have hx : M.stateAt (x : ℝ) l = (x, l) := by simp only [stateAt, M.clampAssets_of_mem x.2]
    have hy : M.stateAt (y : ℝ) l = (y, l) := by simp only [stateAt, M.clampAssets_of_mem y.2]
    have h1 := M.policy_mono z₀ K x.2 y.2 hxy l
    have h2 := M.policy_sub_le_minMPC U z₀ K hγ hdu hR hRlo0 hRlo hA hsl l x.2.1 hxy y.2.2
    rw [hx, hy] at h1 h2
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h1), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 hxy)]
    refine h2.trans ?_
    rw [minMPCSlope, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hA0.le
    exact mul_le_mul_of_nonneg_right (M.returnAt_le_returnBound z₀ K _) (sub_nonneg.2 hxy)
  rcases le_total (a : ℝ) b with h | h
  · exact key a b h
  · rw [abs_sub_comm, abs_sub_comm (a : ℝ)]
    exact key b a h

end KSModel

end KrusellSmith

end LeanEconomics
