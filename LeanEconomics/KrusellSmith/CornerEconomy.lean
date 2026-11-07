/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.AggregateStateIff
import LeanEconomics.KrusellSmith.EmploymentMarginals
import LeanEconomics.DynamicProgramming.PolicyEvaluation

/-!
# The corner economy: candidate, price tree, and the value of the corner policy

Milestones C0–C1 of `CORNER_PLAN.md`. A set of **savers** (`saver : E → Prop`, the employed) and
the KS employment design `D` (marginals `D.m z`, consistent under the transitions).

* **C0** `cornerSave e = ā` for savers, `0` otherwise. The candidate cross-section `cornerDist y z`
  after shocks `y` (yesterday) and `z` (today) is the law of `(cornerSave em, e)` with
  `em ∼ D.m y`, `e ∼ π(y, z, em, ·)`; `μc ω = cornerDist (ω 1) (ω 0)`.
  * `integral_cornerDist`; `capital_cornerDist` (`ā · saverMass y`); `initMass_cornerDist`
    (`D.m z`);
  * **`seqPrices_μc`**: the price tree at `ω` is `cornerTree (ω 0) (capAt μc ω)`; below the root it
    depends only on the shocks along the node and `ω 0`, so **`kSufficient_μc`**.
* **C1** for any price path `P` and the corner policy `cornerPolicy s = cornerSave (s's idio)`
  (continuous: it depends on the discrete label only):
  * `cornerValue z₀ P`, the value of following it (`policyValue`), solving its own Bellman
    equation (`cornerValue_eq`);
  * **`expectation_congr_assets`**: the expected continuation does not depend on today's assets,
    so **`cornerValue_sub_reward`**: `cornerValue s − reward(s, g)` depends only on the label.
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction
open scoped ENNReal

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E} (D : EmploymentDesign M.idioProb) (saver : E → Prop)
  [DecidablePred saver]

/-! ### C0: the candidate -/

variable (M) in
/-- **The corner saving**: the cap for savers, nothing otherwise. -/
noncomputable def cornerSave (e : E) : ↥(Icc (0 : ℝ) M.assetCap) :=
  if saver e then ⟨M.assetCap, M.assetCap_pos.le, le_rfl⟩ else ⟨0, le_rfl, M.assetCap_pos.le⟩

theorem cornerSave_val (e : E) :
    (cornerSave M saver e : ℝ) = if saver e then M.assetCap else 0 := by
  unfold cornerSave
  split_ifs <;> rfl

/-- The weight of `(em, e)` after shocks `y`, `z`. -/
noncomputable def cornerWeight (y z : Z) (p : E × E) : ℝ :=
  D.m y p.1 * M.idioProb y z p.1 p.2

theorem cornerWeight_nonneg (y z : Z) (p : E × E) : 0 ≤ cornerWeight D y z p :=
  mul_nonneg (D.m_nonneg _ _) (M.idioProb_nonneg _ _ _ _)

theorem sum_cornerWeight (y z : Z) : ∑ p, cornerWeight D y z p = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [cornerWeight, ← Finset.mul_sum, M.idioProb_sum, mul_one, D.sum_m]

variable (M) in
/-- The household after `(em, e)`. -/
noncomputable def cornerPt (p : E × E) : M.AState := (cornerSave M saver p.1, ⟨p.2⟩)

/-- **The candidate cross-section** after shocks `y` (yesterday) and `z` (today). -/
noncomputable def cornerMeasure (y z : Z) : Measure M.AState :=
  ∑ p : E × E, ENNReal.ofReal (cornerWeight D y z p) • Measure.dirac (cornerPt M saver p)

instance (y z : Z) : IsProbabilityMeasure (cornerMeasure D saver y z) := by
  constructor
  simp only [cornerMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => cornerWeight_nonneg D y z p, sum_cornerWeight,
    ENNReal.ofReal_one]

/-- The candidate as a probability measure. -/
noncomputable def cornerDist (y z : Z) : ProbabilityMeasure M.AState :=
  ⟨cornerMeasure D saver y z, inferInstance⟩

/-- **The candidate assignment** `μc ω = cornerDist (ω 1) (ω 0)`. -/
noncomputable def μc (ω : History Z) : ProbabilityMeasure M.AState :=
  cornerDist D saver (ω 1) (ω 0)

theorem integral_cornerDist (y z : Z) (f : M.AState →ᵇ ℝ) :
    ∫ x, f x ∂(cornerDist D saver y z : Measure M.AState)
      = ∑ p, cornerWeight D y z p * f (cornerPt M saver p) := by
  change ∫ x, f x ∂(cornerMeasure D saver y z) = _
  rw [cornerMeasure, integral_finsetSum_measure fun p _ =>
    (f.integrable (Measure.dirac (cornerPt M saver p))).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (cornerWeight_nonneg D y z p),
    smul_eq_mul]

/-- The mass of savers at shock `y`. -/
noncomputable def saverMass (y : Z) : ℝ := ∑ e, if saver e then D.m y e else 0

/-- **Capital of the candidate**: the cap times yesterday's mass of savers. -/
theorem capital_cornerDist (y z : Z) :
    ∫ x, M.assets x ∂(cornerDist D saver y z : Measure M.AState)
      = M.assetCap * saverMass D saver y := by
  rw [integral_cornerDist, Fintype.sum_prod_type]
  have h : ∀ em : E, ∑ e, cornerWeight D y z (em, e) * M.assets (cornerPt M saver (em, e))
      = D.m y em * (cornerSave M saver em : ℝ) := by
    intro em
    change ∑ e, D.m y em * M.idioProb y z em e * (cornerSave M saver em : ℝ) = _
    rw [← Finset.sum_mul, ← Finset.mul_sum, M.idioProb_sum, mul_one]
  simp only [h, cornerSave_val, saverMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

/-- **Employment marginal of the candidate**: today's design marginal. -/
theorem initMass_cornerDist (y z : Z) :
    M.initMass (cornerDist D saver y z : Measure M.AState) = D.m z := by
  funext e
  rw [show M.initMass (cornerDist D saver y z : Measure M.AState) e
      = ∫ x, M.idioInd e x ∂(cornerDist D saver y z : Measure M.AState) from
    (M.integral_idioInd _ e).symm, integral_cornerDist, Fintype.sum_prod_type]
  have h : ∀ em : E, ∑ e', cornerWeight D y z (em, e') * M.idioInd e (cornerPt M saver (em, e'))
      = D.m y em * M.idioProb y z em e := by
    intro em
    rw [Finset.sum_eq_single e]
    · rw [M.idioInd_of_eq (show (cornerPt M saver (em, e)).2.idio = e from rfl), mul_one]
      rfl
    · intro e' _ he'
      rw [M.idioInd_of_ne (show ¬ (cornerPt M saver (em, e')).2.idio = e from he'), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [h]
  exact D.consistent y z e

/-- Labour at shock `z` under the design. -/
noncomputable def labourD (z : Z) : ℝ := ∑ e, D.m z e * M.efficiency e

/-- **The corner price tree** from shock `z₀` and root capital `k`: below the root, capital is the
cap times the parent's mass of savers and labour is the node's design labour. -/
noncomputable def cornerTree (z₀ : Z) (k : ℝ) : List Z → ℝ × ℝ
  | [] => (k, labourD D z₀)
  | z :: g => (M.assetCap * saverMass D saver (shockAt z₀ g), labourD D z)

theorem capAt_μc (ω : History Z) :
    capAt (μc D saver) ω = M.assetCap * saverMass D saver (ω 1) :=
  capital_cornerDist D saver (ω 1) (ω 0)

/-- **The price tree of the candidate.** -/
theorem seqPrices_μc (ω : History Z) :
    M.seqPrices (μc D saver) ω = cornerTree D saver (ω 0) (capAt (μc D saver) ω) := by
  funext g
  cases g with
  | nil =>
    refine Prod.ext rfl ?_
    change ∑ e, M.initMass (cornerDist D saver (ω 1) (ω 0) : Measure M.AState) e
      * M.efficiency e = labourD D (ω 0)
    rw [initMass_cornerDist]
    rfl
  | cons z g =>
    have h1 : History.prepend (z :: g) ω 1 = shockAt (ω 0) g := by
      change History.prepend g ω 0 = _
      exact History.prepend_zero g ω
    refine Prod.ext ?_ ?_
    · change ∫ x, M.assets x ∂(cornerDist D saver (History.prepend (z :: g) ω 1)
          (History.prepend (z :: g) ω 0) : Measure M.AState) = _
      rw [capital_cornerDist, h1]
      rfl
    · change ∑ e, M.initMass (cornerDist D saver (History.prepend (z :: g) ω 1)
          (History.prepend (z :: g) ω 0) : Measure M.AState) e * M.efficiency e = _
      rw [initMass_cornerDist]
      rfl

/-- **`(z, K)` is sufficient for the candidate**: yesterday's shock enters the price tree only
through today's capital. -/
theorem kSufficient_μc : KSufficient (μc D saver) := by
  intro ω ω' h0 hk
  rw [seqPrices_μc, seqPrices_μc, h0, hk]

/-! ### C1: the value of the corner policy -/

variable (M) in
/-- **The corner policy** on household states. -/
noncomputable def cornerPolicy (s : M.State) : ℝ := (cornerSave M saver s.2.idio : ℝ)

theorem continuous_cornerPolicy : Continuous (cornerPolicy M saver) :=
  (continuous_of_discreteTopology
    (f := fun l : Label Z E => (cornerSave M saver l.idio : ℝ))).comp continuous_snd

/-- **The value of following the corner policy** along the price path `P`. -/
noncomputable def cornerValue (z₀ : Z) (P : List Z → ℝ × ℝ) : M.State →ᵇ ℝ :=
  (M.household z₀ P).policyValue (continuous_cornerPolicy saver)

theorem cornerValue_eq (z₀ : Z) (P : List Z → ℝ × ℝ) (s : M.State) :
    cornerValue saver z₀ P s
      = (M.household z₀ P).objective (cornerValue saver z₀ P) s (cornerPolicy M saver s) :=
  (M.household z₀ P).policyValue_eq _ s

/-- **The expected continuation does not depend on today's assets.** -/
theorem expectation_congr_assets (z₀ : Z) (P : List Z → ℝ × ℝ) (v : M.State →ᵇ ℝ)
    {s s' : M.State} (hs : s.2 = s'.2) (a : ℝ) :
    (M.household z₀ P).expectation v (s, a) = (M.household z₀ P).expectation v (s', a) := by
  obtain ⟨b, l⟩ := s
  obtain ⟨b', l'⟩ := s'
  change l = l' at hs
  subst hs
  rfl

/-- **The corner value is today's reward plus a function of the label alone.** -/
theorem cornerValue_sub_reward (z₀ : Z) (P : List Z → ℝ × ℝ) {s s' : M.State}
    (hs : s.2 = s'.2) :
    cornerValue saver z₀ P s - (M.household z₀ P).reward (s, cornerPolicy M saver s)
      = cornerValue saver z₀ P s' - (M.household z₀ P).reward (s', cornerPolicy M saver s') := by
  rw [cornerValue_eq, cornerValue_eq]
  have hp : cornerPolicy M saver s = cornerPolicy M saver s' := by
    simp only [cornerPolicy, hs]
  simp only [StochasticDynamicProgram.objective, hp,
    expectation_congr_assets z₀ P (cornerValue saver z₀ P) hs, add_sub_cancel_left]

end KSModel

end KrusellSmith

end LeanEconomics
