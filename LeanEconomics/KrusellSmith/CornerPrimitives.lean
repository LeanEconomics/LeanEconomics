/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CornerEquilibrium
import LeanEconomics.KrusellSmith.Sensitivity

/-!
# The corner conditions from bounds on prices

Milestone C4a of `CORNER_PLAN.md`. Suppose every gross return lies in `[Rlo, Rhi]` (`0 ≤ Rlo`) and
every wage in `[wlo, whi]`. Marginal utility is decreasing (`du_anti`) and nonnegative, so each
corner condition holds along **every** price path once it holds at its worst case:

* (Feas) `floor + g e < wlo · eff e`;
* (Emp) for savers: `u'(wlo eff e − g e) ≤ β Σ π p Rlo u'(Rhi ā + whi eff e' − g e')` — today's
  consumption at its lowest, tomorrow's at its highest;
* (Unemp) for non-savers: `β Σ π p Rhi u'(wlo eff e' − g e') ≤ u'(Rhi ā + whi eff e)`.

**`cornerConditions_of_bounds`**: then `CornerConditions`, so the corner candidate is an
equilibrium represented on `(z, K)` (`isSeqStateEquilibrium_μc`, `exists_represents_μc`).
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} {saver : E → Prop} [DecidablePred saver] {U : M.SmoothUtility}
  {Rlo Rhi wlo whi : ℝ}
  (hRlo : 0 ≤ Rlo) (hR : ∀ z K L, Rlo ≤ M.grossReturn z K L ∧ M.grossReturn z K L ≤ Rhi)
  (hw : ∀ z K L, wlo ≤ M.wage z K L ∧ M.wage z K L ≤ whi)
  (hF : ∀ e, M.consFloor + (cornerSave M saver e : ℝ) < wlo * M.efficiency e)

include hw hF in
theorem cornerFeas_of_bounds (z₀ : Z) (P : List Z → ℝ × ℝ) : CornerFeas M saver z₀ P := by
  intro h e
  have := mul_le_mul_of_nonneg_right (hw (shockAt z₀ h) (P h).1 (P h).2).1 (M.efficiency_nonneg e)
  exact (hF e).trans_le this

include hRlo hR hw hF in
theorem cornerEmp_of_bounds
    (hE : ∀ z e, saver e → U.du (wlo * M.efficiency e - cornerSave M saver e)
      ≤ M.discount * ∑ ze : Z × E, M.aggProb z ze.1 * M.idioProb z ze.1 e ze.2 * Rlo
        * U.du (Rhi * M.assetCap + whi * M.efficiency ze.2 - cornerSave M saver ze.2))
    (z₀ : Z) (P : List Z → ℝ × ℝ) : CornerEmp saver U z₀ P := by
  intro s hs
  have hFe := cornerFeas_of_bounds hw hF z₀ P
  -- today: cash is at least `wlo · eff`
  have hx : M.consFloor < wlo * M.efficiency s.2.idio - cornerSave M saver s.2.idio := by
    have := hF s.2.idio
    linarith
  have hcash : wlo * M.efficiency s.2.idio ≤ M.cash z₀ P s :=
    (mul_le_mul_of_nonneg_right (hw _ _ _).1 (M.efficiency_nonneg _)).trans
      (wage_le_cash (z₀ := z₀) (P := P) s)
  have htoday : U.du (M.cash z₀ P s - cornerPolicy M saver s)
      ≤ U.du (wlo * M.efficiency s.2.idio - cornerSave M saver s.2.idio) :=
    U.du_anti hx (by change _ ≤ M.cash z₀ P s - (cornerSave M saver s.2.idio : ℝ); linarith)
  refine htoday.trans ((hE (shockAt z₀ s.2.node) _ hs).trans ?_)
  -- tomorrow: termwise
  unfold cornerRHS
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ze _ => ?_) M.discount_pos.le
  have hp : 0 ≤ M.aggProb (shockAt z₀ s.2.node) ze.1
      * M.idioProb (shockAt z₀ s.2.node) ze.1 s.2.idio ze.2 :=
    mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _)
  change M.aggProb (shockAt z₀ s.2.node) ze.1 * M.idioProb (shockAt z₀ s.2.node) ze.1 s.2.idio ze.2
      * Rlo * U.du (Rhi * M.assetCap + whi * M.efficiency ze.2 - cornerSave M saver ze.2)
    ≤ M.aggProb (shockAt z₀ s.2.node) ze.1 * M.idioProb (shockAt z₀ s.2.node) ze.1 s.2.idio ze.2
      * M.returnAt z₀ P (ze.1 :: s.2.node)
      * U.du (M.cash z₀ P (cornerNext saver s ze) - cornerPolicy M saver (cornerNext saver s ze))
  rw [mul_assoc (_ * _) Rlo, mul_assoc (_ * _) (M.returnAt z₀ P (ze.1 :: s.2.node))]
  refine mul_le_mul_of_nonneg_left ?_ hp
  have hRn := hR (shockAt z₀ (ze.1 :: s.2.node)) (P (ze.1 :: s.2.node)).1
    (P (ze.1 :: s.2.node)).2
  have hwn := hw (shockAt z₀ (ze.1 :: s.2.node)) (P (ze.1 :: s.2.node)).1
    (P (ze.1 :: s.2.node)).2
  have hy := floor_lt_cornerCons hFe (cornerNext saver s ze)
  have hgI := (cornerSave M saver s.2.idio).2
  have hcn : M.cash z₀ P (cornerNext saver s ze)
      = M.returnAt z₀ P (ze.1 :: s.2.node) * (cornerSave M saver s.2.idio : ℝ)
        + M.wageAt z₀ P (ze.1 :: s.2.node) * M.efficiency ze.2 :=
    M.cash_clampAssets z₀ P hgI ⟨ze.2, ze.1 :: s.2.node⟩
  have hup : M.cash z₀ P (cornerNext saver s ze) - cornerPolicy M saver (cornerNext saver s ze)
      ≤ Rhi * M.assetCap + whi * M.efficiency ze.2 - cornerSave M saver ze.2 := by
    rw [hcn]
    change _ - (cornerSave M saver ze.2 : ℝ) ≤ _
    have h1 : M.returnAt z₀ P (ze.1 :: s.2.node) * (cornerSave M saver s.2.idio : ℝ)
        ≤ Rhi * M.assetCap :=
      mul_le_mul hRn.2 hgI.2 hgI.1 (hRlo.trans hRn.1 |>.trans hRn.2)
    have h2 : M.wageAt z₀ P (ze.1 :: s.2.node) * M.efficiency ze.2 ≤ whi * M.efficiency ze.2 :=
      mul_le_mul_of_nonneg_right hwn.2 (M.efficiency_nonneg _)
    linarith
  have hdu := U.du_anti hy hup
  have hdu0 := U.du_nonneg (hy.trans_le hup)
  exact mul_le_mul hRn.1 hdu hdu0 (hRlo.trans hRn.1)

include hRlo hR hw hF in
theorem cornerUnemp_of_bounds
    (hU : ∀ z e, ¬ saver e → M.discount * ∑ ze : Z × E, M.aggProb z ze.1 * M.idioProb z ze.1 e ze.2
        * Rhi * U.du (wlo * M.efficiency ze.2 - cornerSave M saver ze.2)
      ≤ U.du (Rhi * M.assetCap + whi * M.efficiency e))
    (z₀ : Z) (P : List Z → ℝ × ℝ) : CornerUnemp saver U z₀ P := by
  intro s hs
  have hFe := cornerFeas_of_bounds hw hF z₀ P
  have hg0 : (cornerSave M saver s.2.idio : ℝ) = 0 := by simp [cornerSave_val, hs]
  -- today: cash is at most `Rhi ā + whi eff`
  have hy := floor_lt_cornerCons hFe s
  have hcash : M.cash z₀ P s - cornerPolicy M saver s
      ≤ Rhi * M.assetCap + whi * M.efficiency s.2.idio := by
    change M.cash z₀ P s - (cornerSave M saver s.2.idio : ℝ) ≤ _
    rw [hg0, sub_zero]
    have hRn := hR (shockAt z₀ s.2.node) (P s.2.node).1 (P s.2.node).2
    have hwn := hw (shockAt z₀ s.2.node) (P s.2.node).1 (P s.2.node).2
    have h1 : M.returnAt z₀ P s.2.node * (s.1 : ℝ) ≤ Rhi * M.assetCap :=
      mul_le_mul hRn.2 s.1.2.2 s.1.2.1 (hRlo.trans hRn.1 |>.trans hRn.2)
    have h2 : M.wageAt z₀ P s.2.node * M.efficiency s.2.idio ≤ whi * M.efficiency s.2.idio :=
      mul_le_mul_of_nonneg_right hwn.2 (M.efficiency_nonneg _)
    change M.returnAt z₀ P s.2.node * s.1 + M.wageAt z₀ P s.2.node * M.efficiency s.2.idio ≤ _
    linarith
  have htoday := U.du_anti hy hcash
  refine le_trans ?_ ((hU (shockAt z₀ s.2.node) _ hs).trans htoday)
  unfold cornerRHS
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ze _ => ?_) M.discount_pos.le
  have hp : 0 ≤ M.aggProb (shockAt z₀ s.2.node) ze.1
      * M.idioProb (shockAt z₀ s.2.node) ze.1 s.2.idio ze.2 :=
    mul_nonneg (M.aggProb_nonneg _ _) (M.idioProb_nonneg _ _ _ _)
  change M.aggProb (shockAt z₀ s.2.node) ze.1 * M.idioProb (shockAt z₀ s.2.node) ze.1 s.2.idio ze.2
      * M.returnAt z₀ P (ze.1 :: s.2.node)
      * U.du (M.cash z₀ P (cornerNext saver s ze) - cornerPolicy M saver (cornerNext saver s ze))
    ≤ M.aggProb (shockAt z₀ s.2.node) ze.1 * M.idioProb (shockAt z₀ s.2.node) ze.1 s.2.idio ze.2
      * Rhi * U.du (wlo * M.efficiency ze.2 - cornerSave M saver ze.2)
  rw [mul_assoc (_ * _) (M.returnAt z₀ P (ze.1 :: s.2.node)), mul_assoc (_ * _) Rhi]
  refine mul_le_mul_of_nonneg_left ?_ hp
  have hRn := hR (shockAt z₀ (ze.1 :: s.2.node)) (P (ze.1 :: s.2.node)).1
    (P (ze.1 :: s.2.node)).2
  have hwn := hw (shockAt z₀ (ze.1 :: s.2.node)) (P (ze.1 :: s.2.node)).1
    (P (ze.1 :: s.2.node)).2
  have hx : M.consFloor < wlo * M.efficiency ze.2 - cornerSave M saver ze.2 := by
    have := hF ze.2
    linarith
  have hgI := (cornerSave M saver s.2.idio).2
  have hcn : M.cash z₀ P (cornerNext saver s ze)
      = M.returnAt z₀ P (ze.1 :: s.2.node) * (cornerSave M saver s.2.idio : ℝ)
        + M.wageAt z₀ P (ze.1 :: s.2.node) * M.efficiency ze.2 :=
    M.cash_clampAssets z₀ P hgI ⟨ze.2, ze.1 :: s.2.node⟩
  have hlo : wlo * M.efficiency ze.2 - cornerSave M saver ze.2
      ≤ M.cash z₀ P (cornerNext saver s ze) - cornerPolicy M saver (cornerNext saver s ze) := by
    rw [hcn, hg0, mul_zero, zero_add]
    change _ ≤ _ - (cornerSave M saver ze.2 : ℝ)
    have : wlo * M.efficiency ze.2 ≤ M.wageAt z₀ P (ze.1 :: s.2.node) * M.efficiency ze.2 :=
      mul_le_mul_of_nonneg_right hwn.1 (M.efficiency_nonneg ze.2)
    linarith
  have hdu := U.du_anti hx hlo
  have hdu0 := U.du_nonneg (hx.trans_le hlo)
  exact mul_le_mul hRn.2 hdu hdu0 (hRlo.trans hRn.1 |>.trans hRn.2)

include hRlo hR hw hF in
/-- **The corner conditions from bounds on prices**, along every history's price tree. -/
theorem cornerConditions_of_bounds (D : EmploymentDesign M.idioProb)
    (hE : ∀ z e, saver e → U.du (wlo * M.efficiency e - cornerSave M saver e)
      ≤ M.discount * ∑ ze : Z × E, M.aggProb z ze.1 * M.idioProb z ze.1 e ze.2 * Rlo
        * U.du (Rhi * M.assetCap + whi * M.efficiency ze.2 - cornerSave M saver ze.2))
    (hU : ∀ z e, ¬ saver e → M.discount * ∑ ze : Z × E, M.aggProb z ze.1 * M.idioProb z ze.1 e ze.2
        * Rhi * U.du (wlo * M.efficiency ze.2 - cornerSave M saver ze.2)
      ≤ U.du (Rhi * M.assetCap + whi * M.efficiency e)) :
    CornerConditions D saver U := fun _ω =>
  ⟨cornerFeas_of_bounds hw hF _ _, cornerEmp_of_bounds hRlo hR hw hF hE _ _,
    cornerUnemp_of_bounds hRlo hR hw hF hU _ _⟩

end KSModel

end KrusellSmith

end LeanEconomics
