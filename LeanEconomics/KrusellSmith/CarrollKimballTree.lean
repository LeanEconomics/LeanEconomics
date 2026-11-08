/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.EulerOf
import LeanEconomics.Analysis.PowerMean
import LeanEconomics.Analysis.EGM

/-!
# Carroll–Kimball on the tree: the induction step

Milestone MR4b, step b4, of `MINIMAL_STATE_PLAN.md`. For CRRA marginal utility `u'(c) = c^{-γ}`,
one Bellman step carries concave consumption functions at the children to a concave consumption
function at the parent — the step of Carroll and Kimball (1996), on the Krusell–Smith tree, where
the return differs across the children.

**The endogenous-gridpoint map** (`egmC`). The Euler equation `c^{-γ} = β Σ π R' c'^{-γ}`, with
`π` the shock probabilities and `R'` the children's returns, says that the consumption paired with
end-of-period assets `A` is
`(β S)^{-1/γ} · M_{-γ}(c'(A))`,
the weighted power mean of exponent `-γ` of the children's consumptions, with weights `π R' / S`,
`S = Σ π R'` (`egmWeight`, `retSum`). The weights depend on the node, not on `A`, so the power
mean is concave and nondecreasing in `A` when the children's consumption functions are
(`concaveOn_powerMean_comp`, `monotoneOn_powerMean_comp` from `Analysis/PowerMean`, used as they
stand).

**The step** (`concaveOn_consumptionOf_bellman`). The Euler inequalities of `EulerOf.lean` give
`c ≤ egmC (saving)` unless saving is at the cap (`consumptionOf_le_egmC`) and equality when saving
is above the borrowing limit (`consumptionOf_eq_egmC`); the shared endogenous-gridpoint transfer
`concaveOn_of_egm_affine` (`Analysis/EGM.lean`), with cash `R_h a + w_h e`, turns that into
concavity of the consumption function. Hypotheses: CRRA marginal utility above the floor,
positive returns, the consumption floor slack, the asset cap slack, and concave slices of the
continuation (for monotonicity of the children's consumption).
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (U : M.SmoothUtility) (z₀ : Z) (K : List Z → ℝ × ℝ)

/-- The probability-weighted sum of the children's returns. -/
noncomputable def retSum (s : M.State) : ℝ :=
  ∑ ze : Z × E, M.shockProb z₀ ze (s, 0) * M.returnAt z₀ K (ze.1 :: s.2.node)

/-- The weights of the endogenous-gridpoint power mean: probability times return, normalised. -/
noncomputable def egmWeight (s : M.State) (ze : Z × E) : ℝ :=
  M.shockProb z₀ ze (s, 0) * M.returnAt z₀ K (ze.1 :: s.2.node) / M.retSum z₀ K s

theorem retSum_pos (hR : ∀ h, 0 < M.returnAt z₀ K h) (s : M.State) : 0 < M.retSum z₀ K s := by
  have hsum : ∑ ze : Z × E, M.shockProb z₀ ze (s, 0) = 1 := M.shockProb_sum z₀ (s, 0)
  obtain ⟨ze, -, hze⟩ : ∃ ze ∈ (Finset.univ : Finset (Z × E)), 0 < M.shockProb z₀ ze (s, 0) := by
    by_contra h
    simp only [not_exists, not_and, not_lt] at h
    have : ∑ ze : Z × E, M.shockProb z₀ ze (s, 0) ≤ 0 :=
      Finset.sum_nonpos fun ze hze => h ze hze
    linarith
  refine Finset.sum_pos' (fun ze' _ => mul_nonneg (M.shockProb_nonneg' z₀ ze' (s, 0))
    (hR _).le) ⟨ze, Finset.mem_univ _, mul_pos hze (hR _)⟩

theorem egmWeight_nonneg (hR : ∀ h, 0 < M.returnAt z₀ K h) (s : M.State) (ze : Z × E) :
    0 ≤ M.egmWeight z₀ K s ze :=
  div_nonneg (mul_nonneg (M.shockProb_nonneg' z₀ ze (s, 0)) (hR _).le)
    (M.retSum_pos z₀ K hR s).le

theorem sum_egmWeight (hR : ∀ h, 0 < M.returnAt z₀ K h) (s : M.State) :
    ∑ ze : Z × E, M.egmWeight z₀ K s ze = 1 := by
  simp only [egmWeight]
  rw [← Finset.sum_div]
  exact div_self (M.retSum_pos z₀ K hR s).ne'

/-- **The endogenous-gridpoint map on the tree**: the consumption the Euler equation pairs with
end-of-period assets `A` at `s`, when the children consume against `w₀`. -/
noncomputable def egmC (w₀ : M.State →ᵇ ℝ) (γ : ℝ) (s : M.State) (A : ℝ) : ℝ :=
  (M.discount * M.retSum z₀ K s) ^ (-(1 / γ))
    * powerMean (M.egmWeight z₀ K s) (-γ)
      fun ze => M.consumptionOf z₀ K w₀ (M.stateAt A ⟨ze.2, ze.1 :: s.2.node⟩)

/-- The Euler right-hand side is the return sum times the weighted mean of `c'^{-γ}`. -/
theorem eulerRhsOf_eq {γ : ℝ} (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ))
    (hR : ∀ h, 0 < M.returnAt z₀ K h) (w₀ : M.State →ᵇ ℝ) (hsl₀ : M.SlackOf z₀ K w₀)
    (s : M.State) (A : ℝ) :
    M.eulerRhsOf U z₀ K w₀ s A = M.retSum z₀ K s * ∑ ze, M.egmWeight z₀ K s ze
      * M.consumptionOf z₀ K w₀ (M.stateAt A ⟨ze.2, ze.1 :: s.2.node⟩) ^ (-γ) := by
  have hS := M.retSum_pos z₀ K hR s
  simp only [eulerRhsOf, egmWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ze _ => ?_
  rw [hdu _ (hsl₀ (M.stateAt A ⟨ze.2, ze.1 :: s.2.node⟩))]
  change M.shockProb z₀ ze (s, 0) * _ * _ = _
  field_simp

theorem eulerRhsOf_pos {γ : ℝ} (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ))
    (hR : ∀ h, 0 < M.returnAt z₀ K h) (w₀ : M.State →ᵇ ℝ) (hsl₀ : M.SlackOf z₀ K w₀)
    (s : M.State) (A : ℝ) : 0 < M.eulerRhsOf U z₀ K w₀ s A := by
  rw [M.eulerRhsOf_eq U z₀ K hdu hR w₀ hsl₀ s A]
  exact mul_pos (M.retSum_pos z₀ K hR s) (sum_rpow_pos (M.egmWeight_nonneg z₀ K hR s)
    (M.sum_egmWeight z₀ K hR s) fun ze =>
      M.consFloor_nonneg.trans_lt (hsl₀ (M.stateAt A ⟨ze.2, ze.1 :: s.2.node⟩)))

/-- The Euler right-hand side, raised to `-1/γ`, is the endogenous-gridpoint map. -/
theorem rpow_eulerRhsOf_eq_egmC {γ : ℝ} (hγ : 0 < γ)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) (hR : ∀ h, 0 < M.returnAt z₀ K h)
    (w₀ : M.State →ᵇ ℝ) (hsl₀ : M.SlackOf z₀ K w₀) (s : M.State) (A : ℝ) :
    (M.discount * M.eulerRhsOf U z₀ K w₀ s A) ^ (-(1 / γ)) = M.egmC z₀ K w₀ γ s A := by
  have hS := M.retSum_pos z₀ K hR s
  have hpm : 0 < ∑ ze, M.egmWeight z₀ K s ze
      * M.consumptionOf z₀ K w₀ (M.stateAt A ⟨ze.2, ze.1 :: s.2.node⟩) ^ (-γ) :=
    sum_rpow_pos (M.egmWeight_nonneg z₀ K hR s) (M.sum_egmWeight z₀ K hR s) fun ze =>
      M.consFloor_nonneg.trans_lt (hsl₀ (M.stateAt A ⟨ze.2, ze.1 :: s.2.node⟩))
  rw [M.eulerRhsOf_eq U z₀ K hdu hR w₀ hsl₀ s A, ← mul_assoc,
    Real.mul_rpow (mul_pos M.discount_pos hS).le hpm.le]
  simp only [egmC, powerMean]
  congr 1
  rw [show -(1 / γ) = 1 / (-γ) by field_simp]

/-- **Consumption never exceeds the endogenous-gridpoint value of the saving chosen**, unless
saving is at the cap. -/
theorem consumptionOf_le_egmC {γ : ℝ} (hγ : 0 < γ)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) (hR : ∀ h, 0 < M.returnAt z₀ K h)
    (w₀ : M.State →ᵇ ℝ) (hsl₀ : M.SlackOf z₀ K w₀) (s : M.State)
    (hsl : M.consFloor < M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s)
    (hcap : M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s < M.assetCap) :
    M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s
      ≤ M.egmC z₀ K w₀ γ s (M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s) := by
  set c := M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s
  set p := M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s
  have hc : 0 < c := M.consFloor_nonneg.trans_lt hsl
  have he := M.eulerOf_ge U z₀ K w₀ hsl₀ s hsl hcap
  rw [hdu c hsl] at he
  have hpos : 0 < M.discount * M.eulerRhsOf U z₀ K w₀ s p :=
    mul_pos M.discount_pos (M.eulerRhsOf_pos U z₀ K hdu hR w₀ hsl₀ s p)
  have hstep := Real.rpow_le_rpow_of_nonpos hpos he (show -(1 / γ) ≤ 0 by
    rw [neg_nonpos]; positivity)
  have hexp : (-γ) * (-(1 / γ)) = 1 := by field_simp
  rw [← Real.rpow_mul hc.le, hexp, Real.rpow_one] at hstep
  rw [← M.rpow_eulerRhsOf_eq_egmC U z₀ K hγ hdu hR w₀ hsl₀ s p]
  exact hstep

/-- **Above the borrowing limit, consumption is the endogenous-gridpoint value of the saving
chosen** (the Euler equation). -/
theorem consumptionOf_eq_egmC {γ : ℝ} (hγ : 0 < γ)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) (hR : ∀ h, 0 < M.returnAt z₀ K h)
    (w₀ : M.State →ᵇ ℝ) (hsl₀ : M.SlackOf z₀ K w₀) (s : M.State)
    (hsl : M.consFloor < M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s)
    (hcap : M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s < M.assetCap)
    (hpos : 0 < M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s) :
    M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s
      = M.egmC z₀ K w₀ γ s (M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s) := by
  set c := M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) s
  set p := M.policyOf z₀ K ((M.household z₀ K).bellman w₀) s
  have hc : 0 < c := M.consFloor_nonneg.trans_lt hsl
  have he1 := M.eulerOf_ge U z₀ K w₀ hsl₀ s hsl hcap
  have he2 := M.eulerOf_le U z₀ K w₀ hsl₀ s hsl hpos
  have heq : U.du c = M.discount * M.eulerRhsOf U z₀ K w₀ s p := le_antisymm he2 he1
  rw [hdu c hsl] at heq
  have hexp : (-γ) * (-(1 / γ)) = 1 := by field_simp
  rw [← M.rpow_eulerRhsOf_eq_egmC U z₀ K hγ hdu hR w₀ hsl₀ s p, ← heq, ← Real.rpow_mul hc.le,
    hexp, Real.rpow_one]

/-- **Carroll and Kimball (1996), the induction step on the tree, for CRRA.** If the children's
consumption functions against `w₀` are concave in assets, the consumption function one Bellman
step later is concave in assets at every label, provided marginal utility is `c^{-γ}` above the
floor, returns are positive, the consumption floor is slack, and the asset cap is slack. The
borrowing limit may bind. -/
theorem concaveOn_consumptionOf_bellman {γ : ℝ} (hγ : 0 < γ)
    (hdu : ∀ c, M.consFloor < c → U.du c = c ^ (-γ)) (hR : ∀ h, 0 < M.returnAt z₀ K h)
    {w₀ : M.State →ᵇ ℝ} (hw₀ : M.ConcaveSlices w₀) (hsl₀ : M.SlackOf z₀ K w₀)
    (hconc₀ : ∀ l : Label Z E,
      ConcaveOn ℝ (Icc 0 M.assetCap) fun A => M.consumptionOf z₀ K w₀ (M.stateAt A l))
    (l : Label Z E)
    (hsl : ∀ a ∈ Icc 0 M.assetCap,
      M.consFloor < M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) (M.stateAt a l))
    (hcap : ∀ a ∈ Icc 0 M.assetCap,
      M.policyOf z₀ K ((M.household z₀ K).bellman w₀) (M.stateAt a l) < M.assetCap) :
    ConcaveOn ℝ (Icc 0 M.assetCap)
      fun a => M.consumptionOf z₀ K ((M.household z₀ K).bellman w₀) (M.stateAt a l) := by
  set v := (M.household z₀ K).bellman w₀ with hv
  -- every state at label `l` has the same weights and return sum
  have hs : ∀ a, M.egmC z₀ K w₀ γ (M.stateAt a l) = M.egmC z₀ K w₀ γ (M.stateAt 0 l) :=
    fun a => rfl
  set C := M.egmC z₀ K w₀ γ (M.stateAt 0 l) with hC
  have hpos' : ∀ ze : Z × E, ∀ A ∈ Icc 0 M.assetCap,
      0 < M.consumptionOf z₀ K w₀ (M.stateAt A ⟨ze.2, ze.1 :: l.node⟩) := fun ze A _ =>
    M.consFloor_nonneg.trans_lt (hsl₀ _)
  have hk : 0 ≤ (M.discount * M.retSum z₀ K (M.stateAt 0 l)) ^ (-(1 / γ)) :=
    Real.rpow_nonneg (mul_pos M.discount_pos (M.retSum_pos z₀ K hR _)).le _
  have hCc : ConcaveOn ℝ (Icc 0 M.assetCap) C := by
    have hmean := concaveOn_powerMean_comp (convex_Icc 0 M.assetCap) (neg_neg_of_pos hγ)
      (M.egmWeight_nonneg z₀ K hR (M.stateAt 0 l)) (M.sum_egmWeight z₀ K hR (M.stateAt 0 l))
      (f := fun ze A => M.consumptionOf z₀ K w₀ (M.stateAt A ⟨ze.2, ze.1 :: l.node⟩))
      hpos' fun ze => hconc₀ ⟨ze.2, ze.1 :: l.node⟩
    refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
    have hstep := hmean.2 hx hy hθ hφ hθφ
    simp only [smul_eq_mul] at hstep ⊢
    have hnode : (M.stateAt 0 l).2.node = l.node := rfl
    simp only [hC, egmC, hnode]
    nlinarith [mul_le_mul_of_nonneg_left hstep hk]
  have hCm : MonotoneOn C (Icc 0 M.assetCap) := by
    have hmean := monotoneOn_powerMean_comp (D := Icc 0 M.assetCap) (neg_neg_of_pos hγ)
      (M.egmWeight_nonneg z₀ K hR (M.stateAt 0 l)) (M.sum_egmWeight z₀ K hR (M.stateAt 0 l))
      (f := fun ze A => M.consumptionOf z₀ K w₀ (M.stateAt A ⟨ze.2, ze.1 :: l.node⟩))
      hpos' fun ze x hx y hy hxy => M.consumptionOf_mono z₀ K hw₀ hx hy hxy _
    intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left (hmean hx hy hxy) hk
  have hM : StrictMonoOn (fun A => A + C A) (Icc 0 M.assetCap) := fun x hx y hy hxy => by
    have := hCm hx hy hxy.le
    simp only
    linarith
  refine concaveOn_of_egm_affine (α := M.wageAt z₀ K l.node * M.efficiency l.idio
      - M.returnAt z₀ K l.node * M.borrowLimit)
    (β := M.returnAt z₀ K l.node) (g := fun a => M.policyOf z₀ K v (M.stateAt a l)) hCc hM
    (fun a _ => M.mem_Icc_of_mem_feasible z₀ K (M.policyOf_mem z₀ K v _)) (fun a ha => ?_)
    (fun a ha => ?_) fun a ha hg => ?_
  · change _ = _ + (M.cash z₀ K (M.stateAt a l) - M.policyOf z₀ K v (M.stateAt a l))
    rw [M.cash_stateAt z₀ K ha l]
    ring
  · rw [← hs a]
    exact M.consumptionOf_le_egmC U z₀ K hγ hdu hR w₀ hsl₀ _ (hsl a ha) (hcap a ha)
  · rw [← hs a]
    exact M.consumptionOf_eq_egmC U z₀ K hγ hdu hR w₀ hsl₀ _ (hsl a ha) (hcap a ha) hg

end KSModel

end KrusellSmith

end LeanEconomics
