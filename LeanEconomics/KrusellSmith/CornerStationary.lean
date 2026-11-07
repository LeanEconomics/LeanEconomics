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

* `lawKm_witness`: on the capital sets, **next capital is the cap times the employed share of
  today's shock**, `capOf z`, whatever today's capital;
* `bind_witness`: hence for any law `Λ` on the capital sets, one step of the `(z, K)` kernel depends
  on `Λ` only through its shock marginal;
* `statLaw`: weight `1/2 · π(z, z')` on each `(z', capOf z)` — yesterday's shock `z` from the
  stationary law `(1/2, 1/2)` of the persistent aggregate chain, today's shock `z'` from `π(z, ·)`,
  and capital from yesterday's shock (`7/16` on the two atoms where the shock persisted, `1/16` on
  the others);
* **`cornerStationary`**: `statLaw` is invariant, lives on the capital sets, and is the only
  invariant law there (an invariant law's shock marginal is invariant for `π`, hence
  `(1/2, 1/2)`);
* **`ergodic_statLaw`**: it is ergodic.

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
    lawKm μw z k z' = capOf z := by
  rw [lawKm_of_mem hk]
  obtain ⟨ω, rfl, rfl⟩ := hk
  rw [lawK_eq kSufficient_μw, capAt_witness]
  rfl

theorem capOf_mem_Kset (z z' : Bool) : capOf z ∈ Kset μw z' :=
  ⟨History.cons z' (History.cons z fun _ => z), rfl, by rw [capAt_witness]; rfl⟩

theorem ofReal_half : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
  rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]

/-- The aggregate transition probabilities, as masses. -/
noncomputable def q (z z' : Bool) : ℝ≥0∞ := ENNReal.ofReal (piAgg z z')

theorem piAgg_nonneg (z z' : Bool) : 0 ≤ piAgg z z' := by
  cases z <;> cases z' <;> norm_num [piAgg]

theorem ofReal_aggProb (z z' : Bool) : ENNReal.ofReal (model.aggProb z z') = q z z' := rfl

theorem q_add (z : Bool) : q z true + q z false = 1 := by
  unfold q
  rw [← ENNReal.ofReal_add (piAgg_nonneg _ _) (piAgg_nonneg _ _)]
  cases z <;> norm_num [piAgg]

theorem q_add_left (z' : Bool) : q true z' + q false z' = 1 := by
  unfold q
  rw [← ENNReal.ofReal_add (piAgg_nonneg _ _) (piAgg_nonneg _ _)]
  cases z' <;> norm_num [piAgg]

theorem q_ne_zero (z z' : Bool) : q z z' ≠ 0 := by
  unfold q
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  cases z <;> cases z' <;> norm_num [piAgg]

theorem q_lt_one (z z' : Bool) : q z z' < 1 := by
  unfold q
  rw [ENNReal.ofReal_lt_one]
  cases z <;> cases z' <;> norm_num [piAgg]

theorem q_ne_top (z z' : Bool) : q z z' ≠ ⊤ := ENNReal.ofReal_ne_top

theorem toReal_q (z z' : Bool) : (q z z').toReal = piAgg z z' :=
  ENNReal.toReal_ofReal (piAgg_nonneg z z')

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
        * ∑ z' : Bool, q z z' * B.indicator 1 ((⟨z'⟩ : ShockVal Bool), capOf z) := by
  have hκ := measurable_aggKernel kSufficient_μw continuous_μw
  rw [Measure.bind_apply hB hκ.aemeasurable]
  have hae : ∀ᵐ s ∂Λ, s ∈ Kgraph μw :=
    (prob_compl_eq_zero_iff (measurableSet_Kgraph continuous_μw)).2 hK
  have hpt : ∀ᵐ s ∂Λ, aggKernel μw s B
      = ∑ z : Bool, (Prod.fst ⁻¹' {(⟨z⟩ : ShockVal Bool)}).indicator 1 s
        * ∑ z' : Bool, q z z' * B.indicator 1 ((⟨z'⟩ : ShockVal Bool), capOf z) := by
    filter_upwards [hae] with s hs
    obtain ⟨⟨b⟩, k⟩ := s
    change k ∈ Kset μw b at hs
    rw [aggKernel_apply _ hB]
    have hl : ∀ z', lawKm μw b k z' = capOf b := fun z' => lawKm_witness hs z'
    simp only [hl, ofReal_aggProb]
    rw [Fintype.sum_bool (fun z : Bool => _ * _)]
    cases b <;> simp [Set.indicator, mem_preimage, mem_singleton_iff]
  rw [lintegral_congr_ae hpt, lintegral_finsetSum _ fun z _ =>
    ((measurable_one.indicator (measurableSet_fst z)).mul_const _)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [lintegral_mul_const _ (measurable_one.indicator (measurableSet_fst z)),
    lintegral_indicator_one (measurableSet_fst z)]
  rfl

/-- **The stationary law on `(z, K)`**: yesterday's shock `z` with probability `1/2`, today's shock
`z'` with probability `π(z, z')`, capital the cap times the employed share of yesterday's shock. -/
noncomputable def statLaw : Measure (ShockVal Bool × ℝ) :=
  ∑ z : Bool, ∑ z' : Bool, (2⁻¹ * q z z' : ℝ≥0∞) • Measure.dirac ((⟨z'⟩ : ShockVal Bool), capOf z)

theorem statLaw_apply {B : Set (ShockVal Bool × ℝ)} (hB : MeasurableSet B) :
    statLaw B
      = ∑ z : Bool, 2⁻¹ * ∑ z' : Bool, q z z' * B.indicator 1 ((⟨z'⟩ : ShockVal Bool), capOf z) := by
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
  simp only [indicator_univ, Pi.one_apply, mul_one, Fintype.sum_bool, q_add, half_add_half]

theorem statLaw_Kgraph : statLaw (Kgraph μw) = 1 := by
  rw [statLaw_apply (measurableSet_Kgraph continuous_μw)]
  have h : ∀ z z' : Bool, (Kgraph μw).indicator (1 : ShockVal Bool × ℝ → ℝ≥0∞)
      ((⟨z'⟩ : ShockVal Bool), capOf z) = 1 := fun z z' =>
    Set.indicator_of_mem (show ((⟨z'⟩ : ShockVal Bool), capOf z) ∈ Kgraph μw from
      capOf_mem_Kset z z') _
  simp only [h, mul_one, Fintype.sum_bool, q_add, half_add_half]

theorem mass_statLaw (z : Bool) : mass statLaw z = 2⁻¹ := by
  unfold mass
  rw [statLaw_apply (measurableSet_fst z)]
  cases z <;> simp [Set.indicator, ← mul_add, q_add_left]

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
  -- the shock marginal is invariant for the aggregate chain
  have hrec : ∀ z, mass Λ z = mass Λ true * q true z + mass Λ false * q false z := by
    intro z
    have h := bind_witness Λ hK (measurableSet_fst z)
    rw [hΛ] at h
    change mass Λ z = _ at h
    rw [h]
    cases z <;> simp [Set.indicator]
  have hfin : ∀ z, mass Λ z ≠ ⊤ := fun z => measure_ne_top Λ _
  have hT := congrArg ENNReal.toReal (hrec true)
  have hS := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (hfin _) (q_ne_top _ _))
    (ENNReal.mul_ne_top (hfin _) (q_ne_top _ _)), ENNReal.toReal_mul, ENNReal.toReal_mul,
    toReal_q, toReal_q] at hT
  rw [ENNReal.toReal_add (hfin _) (hfin _), ENNReal.toReal_one] at hS
  norm_num [piAgg] at hT
  have hmass : ∀ z, mass Λ z = 2⁻¹ := by
    intro z
    rw [← ENNReal.ofReal_toReal (hfin z), ← ofReal_half]
    congr 1
    cases z <;> linarith
  ext B hB
  rw [← hΛ, bind_witness Λ hK hB, statLaw_apply hB]
  simp only [hmass]

/-- One step from an atom: to `(w, capOf z')` with probability `π(z', w)`. -/
theorem aggKernel_atom (z z' : Bool) {B : Set (ShockVal Bool × ℝ)} (hB : MeasurableSet B) :
    aggKernel μw ((⟨z'⟩ : ShockVal Bool), capOf z) B
      = ∑ w : Bool, q z' w * B.indicator 1 ((⟨w⟩ : ShockVal Bool), capOf z') := by
  rw [aggKernel_apply _ hB]
  have hl : ∀ w, lawKm μw z' (capOf z) w = capOf z' := fun w =>
    lawKm_witness (capOf_mem_Kset z z') w
  simp only [hl, ofReal_aggProb]

/-- **The stationary law is ergodic**: a set the `(z, K)` process does not leave has probability
`0` or `1`. -/
theorem ergodic_statLaw {B : Set (ShockVal Bool × ℝ)} (hB : MeasurableSet B)
    (hinv : ∀ᵐ s ∂statLaw, s ∈ B → aggKernel μw s B = 1) :
    statLaw B = 0 ∨ statLaw B = 1 := by
  -- the invariance holds at every atom, each of positive mass
  have hatom : ∀ z z' : Bool, ((⟨z'⟩ : ShockVal Bool), capOf z) ∈ B →
      aggKernel μw ((⟨z'⟩ : ShockVal Bool), capOf z) B = 1 := by
    intro z z' hmem
    by_contra hne
    set p : ShockVal Bool × ℝ := ((⟨z'⟩ : ShockVal Bool), capOf z)
    have h0 := ae_iff.1 hinv
    have hsub : ({p} : Set (ShockVal Bool × ℝ)) ⊆ {s | ¬ (s ∈ B → aggKernel μw s B = 1)} := by
      intro s hs
      rw [mem_singleton_iff] at hs
      subst hs
      exact fun h => hne (h hmem)
    have hle := measure_mono (μ := statLaw) hsub
    rw [h0] at hle
    have hpos : (2⁻¹ * q z z' : ℝ≥0∞) ≤ statLaw {p} := by
      rw [statLaw_apply (measurableSet_singleton p)]
      have h1 : q z z' * ({p} : Set (ShockVal Bool × ℝ)).indicator 1 p
          ≤ ∑ w' : Bool, q z w' * ({p} : Set (ShockVal Bool × ℝ)).indicator 1
            ((⟨w'⟩ : ShockVal Bool), capOf z) :=
        Finset.single_le_sum (f := fun w' : Bool => q z w'
          * ({p} : Set (ShockVal Bool × ℝ)).indicator 1 ((⟨w'⟩ : ShockVal Bool), capOf z))
          (fun _ _ => zero_le) (Finset.mem_univ z')
      have h2 := Finset.single_le_sum (f := fun w : Bool => (2⁻¹ : ℝ≥0∞)
          * ∑ w' : Bool, q w w' * ({p} : Set (ShockVal Bool × ℝ)).indicator 1
            ((⟨w'⟩ : ShockVal Bool), capOf w)) (fun _ _ => zero_le) (Finset.mem_univ z)
      rw [Set.indicator_of_mem (mem_singleton p), Pi.one_apply, mul_one] at h1
      exact (mul_le_mul_right h1 _).trans h2
    have : (2⁻¹ * q z z' : ℝ≥0∞) ≤ 0 := hpos.trans hle
    rw [nonpos_iff_eq_zero, mul_eq_zero] at this
    rcases this with h | h
    · simp at h
    · exact q_ne_zero z z' h
  -- membership spreads to both successors
  have hsucc : ∀ z z' : Bool, ((⟨z'⟩ : ShockVal Bool), capOf z) ∈ B →
      ∀ w : Bool, ((⟨w⟩ : ShockVal Bool), capOf z') ∈ B := by
    intro z z' hmem w
    have hk := hatom z z' hmem
    rw [aggKernel_atom z z' hB, Fintype.sum_bool] at hk
    by_contra hw
    have hlt : ∀ w, q z' w ≠ 1 := fun w => (q_lt_one z' w).ne
    by_cases h1 : ((⟨true⟩ : ShockVal Bool), capOf z') ∈ B <;>
      by_cases h2 : ((⟨false⟩ : ShockVal Bool), capOf z') ∈ B <;>
      cases w <;> simp_all [Set.indicator]
  by_cases hex : ∃ z z' : Bool, ((⟨z'⟩ : ShockVal Bool), capOf z) ∈ B
  · obtain ⟨z, z', hmem⟩ := hex
    have hall : ∀ w v : Bool, ((⟨v⟩ : ShockVal Bool), capOf w) ∈ B := by
      intro w v
      exact hsucc z' w (hsucc z z' hmem w) v
    right
    rw [statLaw_apply hB]
    simp only [fun w v => Set.indicator_of_mem (hall w v) (1 : ShockVal Bool × ℝ → ℝ≥0∞),
      Pi.one_apply, mul_one, Fintype.sum_bool, q_add, half_add_half]
  · left
    push Not at hex
    rw [statLaw_apply hB]
    simp only [fun w v => Set.indicator_of_notMem (hex w v) (1 : ShockVal Bool × ℝ → ℝ≥0∞),
      mul_zero, Finset.sum_const_zero]

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
