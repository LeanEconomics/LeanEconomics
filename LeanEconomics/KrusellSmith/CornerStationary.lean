/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CornerWitness
import LeanEconomics.KrusellSmith.AggregateStateStationary

/-!
# The stationary distribution on `(z, K)` of the corner economy

For the explicit corner economy of `CornerWitness.lean`, the recursive equilibrium on `(z, K)` has
a unique stationary distribution on the capital sets. No contraction is needed:

* `lawKm_witness`: on the capital sets, **next capital is the employed share of today's shock**,
  `share z`, whatever today's capital;
* `bind_witness`: hence for any law `Λ` on the capital sets, one step of the `(z, K)` kernel depends
  on `Λ` only through its shock marginal;
* `statLaw`: weight `1/4` on each `(z', share z)` — today's shock `z'` and capital from yesterday's
  shock `z`, both i.i.d. `1/2`;
* **`cornerStationary`**: `statLaw` is invariant, lives on the capital sets, and is the only
  invariant law there (an invariant law's shock marginal is `(1/2, 1/2)` because shocks are
  i.i.d.).

With `cornerWitness`: a **stationary recursive equilibrium on `(z, K)`** with heterogeneous
households and Cobb–Douglas prices.
-/

open MeasureTheory Topology Filter Set
open scoped ENNReal

namespace LeanEconomics

namespace KrusellSmith

namespace KSModel

/-- The corner candidate is continuous in the history: it depends on the two newest shocks. -/
theorem continuous_μc {Z E : Type*} [Fintype Z] [Fintype E] {M : KSModel Z E}
    (D : EmploymentDesign M.idioProb) (saver : E → Prop) [DecidablePred saver] :
    Continuous fun ξ : ShockPath Z => μc D saver ξ.toHistory := by
  have h : Continuous fun p : ShockVal Z × ShockVal Z => cornerDist D saver p.2.val p.1.val :=
    continuous_of_discreteTopology
  exact h.comp ((continuous_apply (A := fun _ : ℕ => ShockVal Z) 0).prodMk
    (continuous_apply (A := fun _ : ℕ => ShockVal Z) 1))

end KSModel

namespace CornerWitness

open KSModel

/-- The corner equilibrium. -/
noncomputable abbrev μw : History Bool → ProbabilityMeasure model.AState := μc design saver

theorem continuous_μw : Continuous fun ξ : ShockPath Bool => μw ξ.toHistory :=
  continuous_μc design saver

theorem kSufficient_μw : KSufficient μw := kSufficient_μc design saver

/-- **Next capital is the employed share of today's shock**, on the capital sets. -/
theorem lawKm_witness {z : Bool} {k : ℝ} (hk : k ∈ Kset μw z) (z' : Bool) :
    lawKm μw z k z' = share z := by
  rw [lawKm_of_mem hk]
  obtain ⟨ω, rfl, rfl⟩ := hk
  rw [lawK_eq kSufficient_μw, capAt_witness]
  rfl

theorem share_mem_Kset (z z' : Bool) : share z ∈ Kset μw z' :=
  ⟨History.cons z' (History.cons z fun _ => z), rfl, by rw [capAt_witness]; rfl⟩

theorem ofReal_half : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
  rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]

/-- The mass of today's shock `z`. -/
noncomputable def mass (Λ : Measure (ShockVal Bool × ℝ)) (z : Bool) : ℝ≥0∞ :=
  Λ (Prod.fst ⁻¹' {(⟨z⟩ : ShockVal Bool)})

theorem measurableSet_fst (z : Bool) :
    MeasurableSet (Prod.fst ⁻¹' {(⟨z⟩ : ShockVal Bool)} : Set (ShockVal Bool × ℝ)) :=
  measurable_fst (MeasurableSpace.measurableSet_top : MeasurableSet {(⟨z⟩ : ShockVal Bool)})

/-- **One step of the `(z, K)` kernel** from a law on the capital sets: it depends only on the
shock marginal. -/
theorem bind_witness (Λ : Measure (ShockVal Bool × ℝ)) [IsProbabilityMeasure Λ]
    (hK : Λ (Kgraph μw) = 1) {B : Set (ShockVal Bool × ℝ)} (hB : MeasurableSet B) :
    (Λ.bind (aggKernel μw)) B
      = ∑ z : Bool, mass Λ z
        * ∑ z' : Bool, 2⁻¹ * B.indicator 1 ((⟨z'⟩ : ShockVal Bool), share z) := by
  have hκ := measurable_aggKernel kSufficient_μw continuous_μw
  rw [Measure.bind_apply hB hκ.aemeasurable]
  have hae : ∀ᵐ s ∂Λ, s ∈ Kgraph μw :=
    (prob_compl_eq_zero_iff (measurableSet_Kgraph continuous_μw)).2 hK
  have hpt : ∀ᵐ s ∂Λ, aggKernel μw s B
      = ∑ z : Bool, (Prod.fst ⁻¹' {(⟨z⟩ : ShockVal Bool)}).indicator 1 s
        * ∑ z' : Bool, 2⁻¹ * B.indicator 1 ((⟨z'⟩ : ShockVal Bool), share z) := by
    filter_upwards [hae] with s hs
    obtain ⟨⟨b⟩, k⟩ := s
    change k ∈ Kset μw b at hs
    rw [aggKernel_apply _ hB]
    have hl : ∀ z', lawKm μw b k z' = share b := fun z' => lawKm_witness hs z'
    simp only [hl, show ∀ z z' : Bool, model.aggProb z z' = 1 / 2 from fun _ _ => rfl, ofReal_half]
    rw [Fintype.sum_bool (fun z : Bool => _ * _)]
    cases b <;> simp [Set.indicator, mem_preimage, mem_singleton_iff]
  rw [lintegral_congr_ae hpt, lintegral_finsetSum _ fun z _ =>
    ((measurable_one.indicator (measurableSet_fst z)).mul_const _)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [lintegral_mul_const _ (measurable_one.indicator (measurableSet_fst z)),
    lintegral_indicator_one (measurableSet_fst z)]
  rfl

/-- **The stationary law on `(z, K)`**: today's shock and yesterday's shock i.i.d. `1/2`, capital
the employed share of yesterday's shock. -/
noncomputable def statLaw : Measure (ShockVal Bool × ℝ) :=
  ∑ z : Bool, ∑ z' : Bool, (2⁻¹ * 2⁻¹ : ℝ≥0∞) • Measure.dirac ((⟨z'⟩ : ShockVal Bool), share z)

theorem statLaw_apply {B : Set (ShockVal Bool × ℝ)} (hB : MeasurableSet B) :
    statLaw B
      = ∑ z : Bool, 2⁻¹ * ∑ z' : Bool, 2⁻¹ * B.indicator 1 ((⟨z'⟩ : ShockVal Bool), share z) := by
  simp only [statLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hB, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem half_add_half : (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 1 := ENNReal.inv_two_add_inv_two

theorem two_mul_inv : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem two_mul_half (x : ℝ≥0∞) : 2 * (2⁻¹ * x) = x := by
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

instance : IsProbabilityMeasure statLaw := by
  constructor
  rw [statLaw_apply MeasurableSet.univ]
  simp [two_mul_inv]

theorem statLaw_Kgraph : statLaw (Kgraph μw) = 1 := by
  rw [statLaw_apply (measurableSet_Kgraph continuous_μw)]
  have h : ∀ z z' : Bool, (Kgraph μw).indicator (1 : ShockVal Bool × ℝ → ℝ≥0∞)
      ((⟨z'⟩ : ShockVal Bool), share z) = 1 := fun z z' =>
    Set.indicator_of_mem (show ((⟨z'⟩ : ShockVal Bool), share z) ∈ Kgraph μw from
      share_mem_Kset z z') _
  simp only [h, mul_one, Fintype.sum_bool, half_add_half]

theorem mass_statLaw (z : Bool) : mass statLaw z = 2⁻¹ := by
  unfold mass
  rw [statLaw_apply (measurableSet_fst z)]
  cases z <;> simp [Set.indicator, two_mul_half]

/-- **The stationary law is invariant.** -/
theorem isAggInvariant_statLaw : IsAggInvariant μw statLaw := by
  ext B hB
  rw [bind_witness statLaw statLaw_Kgraph hB, statLaw_apply hB]
  simp only [mass_statLaw]

/-- **It is the only invariant law on the capital sets.** -/
theorem eq_statLaw (Λ : Measure (ShockVal Bool × ℝ)) [IsProbabilityMeasure Λ]
    (hΛ : IsAggInvariant μw Λ) (hK : Λ (Kgraph μw) = 1) : Λ = statLaw := by
  -- the shock marginal is `(1/2, 1/2)`
  have hsum : mass Λ false + mass Λ true = 1 := by
    have hU : (Prod.fst ⁻¹' {(⟨false⟩ : ShockVal Bool)} : Set (ShockVal Bool × ℝ))
        ∪ Prod.fst ⁻¹' {(⟨true⟩ : ShockVal Bool)} = univ := by
      ext ⟨⟨b⟩, k⟩
      cases b <;> simp
    have hD : Disjoint (Prod.fst ⁻¹' {(⟨false⟩ : ShockVal Bool)} : Set (ShockVal Bool × ℝ))
        (Prod.fst ⁻¹' {(⟨true⟩ : ShockVal Bool)}) := by
      rw [Set.disjoint_left]
      rintro ⟨⟨b⟩, k⟩ h1 h2
      simp only [mem_preimage, mem_singleton_iff] at h1 h2
      rw [h1] at h2
      cases h2
    have := measure_union (μ := Λ) hD (measurableSet_fst true)
    rw [hU, measure_univ] at this
    exact this.symm
  have hmass : ∀ z, mass Λ z = 2⁻¹ := by
    intro z
    have h := bind_witness Λ hK (measurableSet_fst z)
    rw [hΛ] at h
    change mass Λ z = _ at h
    rw [h]
    cases z <;> simp [Set.indicator, ← add_mul]
    all_goals rw [add_comm, hsum, one_mul]
  ext B hB
  rw [← hΛ, bind_witness Λ hK hB, statLaw_apply hB]
  simp only [hmass]

/-- **The stationary distribution of the corner economy on `(z, K)`**: invariant for the
`(z, K)` law of motion, living on the capital sets, and unique there. -/
theorem cornerStationary :
    IsAggInvariant μw statLaw ∧ statLaw (Kgraph μw) = 1 ∧
      ∀ (Λ : Measure (ShockVal Bool × ℝ)) [IsProbabilityMeasure Λ],
        IsAggInvariant μw Λ → Λ (Kgraph μw) = 1 → Λ = statLaw :=
  ⟨isAggInvariant_statLaw, statLaw_Kgraph, fun Λ _ hΛ hK => eq_statLaw Λ hΛ hK⟩

end CornerWitness

end KrusellSmith

end LeanEconomics
