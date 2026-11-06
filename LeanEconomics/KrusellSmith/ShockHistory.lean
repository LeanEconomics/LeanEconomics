/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.MarkovEquilibrium.Ergodic
import LeanEconomics.KrusellSmith.EmploymentMarginals

/-!
# The stationary law of the shock history

Milestone SS1 of `STATIONARY_SEQUENCE_PLAN.md`. A sequence-state equilibrium is a function of the
infinite history of aggregate shocks, newest first. Each period the history is extended by a new
shock: `ξ ↦ cons z' ξ` with probability `π (ξ 0) z'` (`ShockPath.ext`). This file gives the
history a stationary law.

* `ShockPath Z = ℕ → ShockVal Z`: compact metrizable, Borel (`ShockVal Z` is `Z` with the discrete
  topology and σ-algebra).
* `ShockPath.ext`: the extension kernel; `integral_ext`, **`continuous_ext`** (Feller).
* **`ShockPath.exists_invariant_ergodic`**: an `ext`-invariant law that is ergodic — DGMM's
  Corollary 1.1 (`MarkovEquilibrium.exists_ergodic`) for the singleton correspondence `{ext ξ}`.
* `ShockPath.measure_cyl_succ_succ`, `measure_cyl_one`: for an invariant law, the probability of a
  prefix `(z₀, z₁, …)` is `π z₁ z₀` times that of `(z₁, …)` — the chain run backwards — and the
  `ξ 0`-marginal is `π`-stationary (`marginal_stationary`).
* **`ShockPath.eq_of_invariant`**: if `π` has only one stationary distribution, there is only one
  invariant law; it is then ergodic (**`ShockPath.ergodic_of_invariant`**). `π ≥ ε > 0` is enough
  (`stationary_unique_of_minor`).
-/

open MeasureTheory Topology Filter Set BoundedContinuousFunction TopologicalSpace ProbabilityTheory
open scoped ENNReal NNReal

namespace LeanEconomics

namespace KrusellSmith

/-- An aggregate shock, as a point of a discrete topological and measurable space. -/
structure ShockVal (Z : Type*) where
  /-- The shock. -/
  val : Z

namespace ShockVal

variable (Z : Type*)

instance : TopologicalSpace (ShockVal Z) := ⊥

instance : DiscreteTopology (ShockVal Z) := ⟨rfl⟩

instance : MeasurableSpace (ShockVal Z) := ⊤

instance : BorelSpace (ShockVal Z) := ⟨borel_eq_top_of_discrete.symm⟩

/-- `ShockVal Z` is `Z`. -/
def equiv : ShockVal Z ≃ Z := ⟨val, mk, fun _ => rfl, fun _ => rfl⟩

instance [Finite Z] : Finite (ShockVal Z) := Finite.of_equiv Z (equiv Z).symm

instance [Nonempty Z] : Nonempty (ShockVal Z) := ⟨⟨Classical.arbitrary Z⟩⟩

instance [Countable Z] : Countable (ShockVal Z) := Countable.of_equiv Z (equiv Z).symm

instance [Countable Z] : SecondCountableTopology (ShockVal Z) :=
  DiscreteTopology.secondCountableTopology_of_countable

end ShockVal

/-- **Shock histories**, newest first. -/
abbrev ShockPath (Z : Type*) := ℕ → ShockVal Z

namespace ShockPath

variable {Z : Type*}

/-- The history after the new shock `z`. -/
def cons (z : Z) (ξ : ShockPath Z) : ShockPath Z
  | 0 => ⟨z⟩
  | n + 1 => ξ n

/-- The history one period earlier. -/
def tail (ξ : ShockPath Z) : ShockPath Z := fun n => ξ (n + 1)

@[simp] theorem cons_zero (z : Z) (ξ : ShockPath Z) : cons z ξ 0 = ⟨z⟩ := rfl

@[simp] theorem cons_succ (z : Z) (ξ : ShockPath Z) (n : ℕ) : cons z ξ (n + 1) = ξ n := rfl

theorem continuous_cons (z : Z) : Continuous (cons z) := by
  refine continuous_pi fun n => ?_
  cases n with
  | zero => exact continuous_const
  | succ n => exact continuous_apply n

theorem measurable_cons (z : Z) : Measurable (cons z) := by
  refine measurable_pi_iff.2 fun n => ?_
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_pi_apply n

/-- The history as a `History`. -/
def toHistory (ξ : ShockPath Z) : History Z := fun n => (ξ n).val

variable [Fintype Z] (π : Z → Z → ℝ) (hπ0 : ∀ z z', 0 ≤ π z z') (hπ1 : ∀ z, ∑ z', π z z' = 1)

/-- The extension kernel as a measure. -/
noncomputable def extMeasure (ξ : ShockPath Z) : Measure (ShockPath Z) :=
  ∑ z', ENNReal.ofReal (π (ξ 0).val z') • Measure.dirac (cons z' ξ)

theorem extMeasure_apply (ξ : ShockPath Z) {A : Set (ShockPath Z)} (hA : MeasurableSet A) :
    extMeasure π ξ A = ∑ z', ENNReal.ofReal (π (ξ 0).val z') * A.indicator 1 (cons z' ξ) := by
  simp only [extMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hA, smul_eq_mul]

include hπ0 hπ1 in
theorem extMeasure_univ (ξ : ShockPath Z) : extMeasure π ξ univ = 1 := by
  rw [extMeasure_apply π ξ MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun z' _ => hπ0 _ _, hπ1, ENNReal.ofReal_one]

/-- **The extension kernel**: a new shock `z'` with probability `π (ξ 0) z'`. -/
noncomputable def ext (ξ : ShockPath Z) : ProbabilityMeasure (ShockPath Z) :=
  ⟨extMeasure π ξ, ⟨extMeasure_univ π hπ0 hπ1 ξ⟩⟩

theorem integral_ext (ξ : ShockPath Z) (f : ShockPath Z →ᵇ ℝ) :
    ∫ x, f x ∂(ext π hπ0 hπ1 ξ : Measure (ShockPath Z))
      = ∑ z', π (ξ 0).val z' * f (cons z' ξ) := by
  change ∫ x, f x ∂(extMeasure π ξ) = _
  rw [extMeasure, integral_finsetSum_measure fun z' _ =>
    (f.integrable (Measure.dirac (cons z' ξ))).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [integral_smul_measure, integral_dirac' _ _ f.continuous.stronglyMeasurable,
    ENNReal.toReal_ofReal (hπ0 _ _), smul_eq_mul]

/-- **The extension kernel is Feller.** -/
theorem continuous_ext : Continuous (ext π hπ0 hπ1) := by
  rw [continuous_iff_continuousAt]
  intro ξ
  rw [ContinuousAt, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have e : (fun ξ' => ∫ x, f x ∂(ext π hπ0 hπ1 ξ' : Measure (ShockPath Z)))
      = fun ξ' => ∑ z', π (ξ' 0).val z' * f (cons z' ξ') :=
    funext fun ξ' => integral_ext π hπ0 hπ1 ξ' f
  rw [e, integral_ext π hπ0 hπ1 ξ f]
  have hc : Continuous fun ξ' : ShockPath Z => ∑ z', π (ξ' 0).val z' * f (cons z' ξ') :=
    continuous_finsetSum _ fun z' _ =>
      ((continuous_of_discreteTopology (f := fun v : ShockVal Z => π v.val z')).comp
        (continuous_apply 0)).mul (f.continuous.comp (continuous_cons z'))
  exact hc.tendsto ξ

theorem measurable_extMeasure : Measurable (extMeasure π) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have e : (fun ξ => extMeasure π ξ A)
      = fun ξ => ∑ z', ENNReal.ofReal (π (ξ 0).val z') * A.indicator 1 (cons z' ξ) :=
    funext fun ξ => extMeasure_apply π ξ hA
  rw [e]
  refine Finset.measurable_sum _ fun z' _ => ?_
  refine Measurable.mul ?_ ((measurable_one.indicator hA).comp (measurable_cons z'))
  exact (measurable_of_countable (fun v : ShockVal Z => ENNReal.ofReal (π v.val z'))).comp
    (measurable_pi_apply 0)

/-! ### An invariant ergodic law -/

/-- `P` is **invariant**: drawing the history from `P` and extending it gives `P` again. -/
def IsInvariant (P : Measure (ShockPath Z)) : Prop :=
  P.bind (extMeasure π) = P

theorem IsInvariant.apply {P : Measure (ShockPath Z)} (hP : IsInvariant π P)
    {A : Set (ShockPath Z)} (hA : MeasurableSet A) :
    P A = ∫⁻ ξ, extMeasure π ξ A ∂P := by
  conv_lhs => rw [← hP]
  exact Measure.bind_apply hA (measurable_extMeasure π).aemeasurable

include hπ0 hπ1 in
/-- **An invariant, ergodic law of the shock history exists.** -/
theorem exists_invariant_ergodic [Nonempty Z] :
    ∃ P : ProbabilityMeasure (ShockPath Z), IsInvariant π (P : Measure (ShockPath Z)) ∧
      ∀ A, MeasurableSet A → (∀ᵐ ξ ∂(P : Measure (ShockPath Z)), ξ ∈ A → extMeasure π ξ A = 1) →
        (P : Measure (ShockPath Z)) A = 0 ∨ (P : Measure (ShockPath Z)) A = 1 := by
  set G : ShockPath Z → Set (ProbabilityMeasure (ShockPath Z)) := fun ξ => {ext π hπ0 hπ1 ξ}
  have hGr : IsClosed (MarkovEquilibrium.graphSet G) :=
    isClosed_eq continuous_snd ((continuous_ext π hπ0 hπ1).comp continuous_fst)
  have hne : ∀ ξ, (G ξ).Nonempty := fun ξ => singleton_nonempty _
  have hconv : ∀ ξ, ∀ ρ ∈ G ξ, ∀ σ ∈ G ξ, ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      MarkovEquilibrium.mix t ht ρ σ ∈ G ξ := by
    intro ξ ρ hρ σ hσ t ht
    rw [mem_singleton_iff] at hρ hσ ⊢
    subst hρ hσ
    apply ProbabilityMeasure.toMeasure_injective
    rw [MarkovEquilibrium.coe_mix, ← add_smul, ← ENNReal.ofReal_add ht.1 (sub_nonneg.2 ht.2),
      add_sub_cancel, ENNReal.ofReal_one, one_smul]
  obtain ⟨μ, T, hT, hbind, hG, herg⟩ := MarkovEquilibrium.exists_ergodic hGr hne hconv
  have hae : ∀ᵐ ξ ∂(μ : Measure (ShockPath Z)), (T ξ : Measure (ShockPath Z)) = extMeasure π ξ :=
    hG.mono fun ξ h => by
      rw [show T ξ = ext π hπ0 hπ1 ξ from h]
      rfl
  have hTm : Measurable fun ξ => (T ξ : Measure (ShockPath Z)) := measurable_subtype_coe.comp hT
  refine ⟨μ, ?_, fun A hA hinv => herg A hA ?_⟩
  · unfold IsInvariant
    conv_rhs => rw [← hbind]
    ext A hA
    rw [Measure.bind_apply hA (measurable_extMeasure π).aemeasurable,
      Measure.bind_apply hA hTm.aemeasurable]
    exact lintegral_congr_ae (hae.mono fun ξ h => (congrArg (fun m : Measure _ => m A) h).symm)
  · filter_upwards [hinv, hae] with ξ h1 h2 hξ
    rw [h2]
    exact h1 hξ

/-! ### Prefix cylinders and uniqueness -/

/-- The histories whose first `N` shocks are `w 0, …, w (N − 1)`. -/
def cyl (N : ℕ) (w : ℕ → Z) : Set (ShockPath Z) := {ξ | ∀ i < N, (ξ i).val = w i}

omit [Fintype Z] in
theorem measurableSet_cyl (N : ℕ) (w : ℕ → Z) : MeasurableSet (cyl N w) := by
  have e : cyl N w = ⋂ i ∈ Finset.range N, (fun ξ : ShockPath Z => ξ i) ⁻¹' {⟨w i⟩} := by
    ext ξ
    simp only [cyl, mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_preimage, mem_singleton_iff]
    exact forall₂_congr fun i _ => ⟨fun h => by rw [← h], fun h => by rw [h]⟩
  rw [e]
  exact Finset.measurableSet_biInter _ fun i _ =>
    measurable_pi_apply i (MeasurableSpace.measurableSet_top : MeasurableSet _)

omit [Fintype Z] in
@[simp] theorem cyl_zero (w : ℕ → Z) : cyl 0 w = (univ : Set (ShockPath Z)) := by
  ext ξ
  simp [cyl]

omit [Fintype Z] in
theorem cons_mem_cyl_succ (z : Z) (ξ : ShockPath Z) (N : ℕ) (w : ℕ → Z) :
    cons z ξ ∈ cyl (N + 1) w ↔ z = w 0 ∧ ξ ∈ cyl N (fun i => w (i + 1)) := by
  constructor
  · intro h
    refine ⟨h 0 (Nat.succ_pos N), fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)

omit [Fintype Z] in
theorem mem_cyl_succ_head {N : ℕ} {w : ℕ → Z} {ξ : ShockPath Z} (h : ξ ∈ cyl (N + 1) w) :
    (ξ 0).val = w 0 :=
  h 0 (Nat.succ_pos N)

variable {π}

/-- **The probability of a prefix, one step back**: for an invariant law,
`P (z₀, z₁, …) = ∫ π (ξ 0) z₀ 1_{(z₁, …)}`. -/
theorem IsInvariant.measure_cyl_succ {P : Measure (ShockPath Z)} (hP : IsInvariant π P) (N : ℕ)
    (w : ℕ → Z) :
    P (cyl (N + 1) w)
      = ∫⁻ ξ, ENNReal.ofReal (π (ξ 0).val (w 0)) * (cyl N fun i => w (i + 1)).indicator 1 ξ ∂P := by
  refine (hP.apply π (measurableSet_cyl _ _)).trans (lintegral_congr fun ξ => ?_)
  rw [extMeasure_apply π ξ (measurableSet_cyl _ _), Finset.sum_eq_single (w 0)]
  · congr 1
    by_cases h : ξ ∈ cyl N fun i => w (i + 1)
    · rw [indicator_of_mem h, indicator_of_mem ((cons_mem_cyl_succ _ _ _ _).2 ⟨rfl, h⟩)]
      rfl
    · rw [indicator_of_notMem h,
        indicator_of_notMem fun h' => h ((cons_mem_cyl_succ _ _ _ _).1 h').2]
  · intro z' _ hz'
    rw [indicator_of_notMem fun h' => hz' ((cons_mem_cyl_succ _ _ _ _).1 h').1, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The chain run backwards**: `P (z₀, z₁, …, z_{N+1}) = π z₁ z₀ · P (z₁, …, z_{N+1})`. -/
theorem IsInvariant.measure_cyl_succ_succ {P : Measure (ShockPath Z)} (hP : IsInvariant π P)
    (N : ℕ) (w : ℕ → Z) :
    P (cyl (N + 2) w) = ENNReal.ofReal (π (w 1) (w 0)) * P (cyl (N + 1) fun i => w (i + 1)) := by
  rw [hP.measure_cyl_succ (N + 1) w, ← lintegral_indicator_const (measurableSet_cyl _ _)]
  refine lintegral_congr fun ξ => ?_
  by_cases h : ξ ∈ cyl (N + 1) fun i => w (i + 1)
  · rw [indicator_of_mem h, indicator_of_mem h, mem_cyl_succ_head h, Pi.one_apply, mul_one]
  · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]

/-- The `ξ 0`-marginal: `P (ξ 0 = z₀) = Σ_z π z z₀ P (ξ 0 = z)`. -/
theorem IsInvariant.measure_cyl_one {P : Measure (ShockPath Z)} (hP : IsInvariant π P)
    (w : ℕ → Z) :
    P (cyl 1 w) = ∑ z, ENNReal.ofReal (π z (w 0)) * P (cyl 1 fun _ => z) := by
  rw [hP.measure_cyl_succ 0 w]
  simp only [cyl_zero, indicator_univ, Pi.one_apply, mul_one]
  have e : ∀ ξ : ShockPath Z, ENNReal.ofReal (π (ξ 0).val (w 0))
      = ∑ z, ENNReal.ofReal (π z (w 0)) * (cyl 1 fun _ => z).indicator 1 ξ := by
    intro ξ
    rw [Finset.sum_eq_single (ξ 0).val]
    · rw [indicator_of_mem (show ξ ∈ cyl 1 fun _ => (ξ 0).val from fun i hi => by
        rw [show i = 0 by omega]), Pi.one_apply, mul_one]
    · intro z _ hz
      rw [indicator_of_notMem (fun h => hz (mem_cyl_succ_head (N := 0) h).symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp_rw [e]
  rw [lintegral_finsetSum _ fun z _ =>
    (measurable_one.indicator (measurableSet_cyl _ _)).const_mul _]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_cyl _ _)),
    lintegral_indicator_one (measurableSet_cyl _ _)]

/-- The `ξ 0`-marginal of a probability law, as a real vector. -/
noncomputable def marginal (P : Measure (ShockPath Z)) (z : Z) : ℝ := (P (cyl 1 fun _ => z)).toReal

include hπ0 in
/-- **The `ξ 0`-marginal of an invariant law is `π`-stationary.** -/
theorem IsInvariant.marginal_stationary {P : Measure (ShockPath Z)} [IsProbabilityMeasure P]
    (hP : IsInvariant π P) (z' : Z) : ∑ z, marginal P z * π z z' = marginal P z' := by
  have h := hP.measure_cyl_one (fun _ => z')
  simp only [marginal]
  rw [h, ENNReal.toReal_sum fun z _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hπ0 _ _), mul_comm]

omit [Fintype Z] in
theorem marginal_nonneg (P : Measure (ShockPath Z)) (z : Z) : 0 ≤ marginal P z :=
  ENNReal.toReal_nonneg

theorem sum_marginal (P : Measure (ShockPath Z)) [IsProbabilityMeasure P] :
    ∑ z, marginal P z = 1 := by
  have hU : (⋃ z ∈ (Finset.univ : Finset Z), (cyl 1 fun _ => z : Set (ShockPath Z))) = univ := by
    ext ξ
    simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_univ, iff_true]
    exact ⟨(ξ 0).val, fun i hi => by rw [show i = 0 by omega]⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset Z) : Set Z)
      fun z => (cyl 1 fun _ => z : Set (ShockPath Z)) := by
    intro z _ z' _ hzz'
    refine Set.disjoint_left.2 fun ξ h h' => hzz' ?_
    rw [← mem_cyl_succ_head (N := 0) h, mem_cyl_succ_head (N := 0) h']
  have := measure_biUnion_finset (μ := P) hdisj fun z _ => measurableSet_cyl 1 fun _ => z
  rw [hU, measure_univ] at this
  simp only [marginal]
  rw [← ENNReal.toReal_sum fun z _ => measure_ne_top _ _, ← this, ENNReal.toReal_one]

include hπ0 in
/-- **Uniqueness of the invariant law**, when `π` has only one stationary distribution. -/
theorem eq_of_invariant [Nonempty Z]
    (huniq : ∀ q q' : Z → ℝ, (∀ z, 0 ≤ q z) → ∑ z, q z = 1 → (∀ z', ∑ z, q z * π z z' = q z') →
      (∀ z, 0 ≤ q' z) → ∑ z, q' z = 1 → (∀ z', ∑ z, q' z * π z z' = q' z') → q = q')
    {P P' : Measure (ShockPath Z)} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hP : IsInvariant π P) (hP' : IsInvariant π P') : P = P' := by
  -- equal marginals
  have hm : marginal P = marginal P' :=
    huniq _ _ (marginal_nonneg P) (sum_marginal P) (hP.marginal_stationary hπ0)
      (marginal_nonneg P') (sum_marginal P') (hP'.marginal_stationary hπ0)
  have h1 : ∀ w : ℕ → Z, P (cyl 1 w) = P' (cyl 1 w) := by
    intro w
    have e : cyl 1 w = (cyl 1 fun _ => w 0 : Set (ShockPath Z)) := by
      ext ξ
      simp only [cyl, mem_ofPred_eq]
      exact ⟨fun h i hi => by rw [h i hi, show i = 0 by omega],
        fun h i hi => by rw [h i hi, show i = 0 by omega]⟩
    rw [e, ← ENNReal.ofReal_toReal (measure_ne_top P _),
      ← ENNReal.ofReal_toReal (measure_ne_top P' _)]
    exact congrArg ENNReal.ofReal (congrFun hm (w 0))
  -- equal prefix probabilities
  have hcyl : ∀ N (w : ℕ → Z), P (cyl N w) = P' (cyl N w) := by
    intro N
    induction N with
    | zero => intro w; simp
    | succ N ih =>
      intro w
      cases N with
      | zero => exact h1 w
      | succ N =>
        rw [hP.measure_cyl_succ_succ N w, hP'.measure_cyl_succ_succ N w, ih]
  -- equal finite-dimensional laws
  have hfin : ∀ N : ℕ, P.map (Finset.range N).restrict = P'.map (Finset.range N).restrict := by
    intro N
    refine Measure.ext_of_singleton fun (x : (i : Finset.range N) → ShockVal Z) => ?_
    have hmeas : Measurable ((Finset.range N).restrict (π := fun _ : ℕ => ShockVal Z)) :=
      Finset.measurable_restrict _
    have hs : MeasurableSet ({x} : Set ((i : Finset.range N) → ShockVal Z)) :=
      measurableSet_singleton x
    rw [Measure.map_apply hmeas hs, Measure.map_apply hmeas hs]
    set w : ℕ → Z := fun i => if h : i < N then (x ⟨i, Finset.mem_range.2 h⟩).val
      else Classical.arbitrary Z
    have e : (Finset.range N).restrict (π := fun _ : ℕ => ShockVal Z) ⁻¹' {x} = cyl N w := by
      ext ξ
      simp only [mem_preimage, cyl, mem_ofPred_eq, w]
      constructor
      · intro h i hi
        rw [dite_eq_left_of_eq_true (eq_true hi), ← h]
        rfl
      · intro h
        funext ⟨i, hi⟩
        have hi' := Finset.mem_range.1 hi
        have := h i hi'
        rw [dite_eq_left_of_eq_true (eq_true hi')] at this
        change ξ i = x ⟨i, hi⟩
        exact congrArg ShockVal.mk this
    rw [e, hcyl]
  -- measurable cylinders generate the product σ-algebra
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders ?_ (by rw [measure_univ, measure_univ])
  intro A hA
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders A).1 hA
  set N := s.sup id + 1
  have hsub : s ⊆ Finset.range N := fun i hi =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hmeasN : Measurable ((Finset.range N).restrict (π := fun _ : ℕ => ShockVal Z)) :=
    Finset.measurable_restrict _
  have hr : s.restrict (π := fun _ : ℕ => ShockVal Z)
      = Finset.restrict₂ hsub ∘ (Finset.range N).restrict :=
    (Finset.restrict₂_comp_restrict hsub).symm
  have hS' : MeasurableSet (Finset.restrict₂ (π := fun _ : ℕ => ShockVal Z) hsub ⁻¹' S) :=
    Finset.measurable_restrict₂ hsub hS
  rw [cylinder, hr, preimage_comp, ← Measure.map_apply hmeasN hS',
    ← Measure.map_apply hmeasN hS', hfin N]

include hπ0 hπ1 in
/-- **The unique invariant law is ergodic.** -/
theorem ergodic_of_invariant [Nonempty Z]
    (huniq : ∀ q q' : Z → ℝ, (∀ z, 0 ≤ q z) → ∑ z, q z = 1 → (∀ z', ∑ z, q z * π z z' = q z') →
      (∀ z, 0 ≤ q' z) → ∑ z, q' z = 1 → (∀ z', ∑ z, q' z * π z z' = q' z') → q = q')
    {P : Measure (ShockPath Z)} [IsProbabilityMeasure P] (hP : IsInvariant π P)
    {A : Set (ShockPath Z)} (hA : MeasurableSet A)
    (hinv : ∀ᵐ ξ ∂P, ξ ∈ A → extMeasure π ξ A = 1) : P A = 0 ∨ P A = 1 := by
  obtain ⟨P₀, hP₀, herg⟩ := exists_invariant_ergodic π hπ0 hπ1
  have e := eq_of_invariant hπ0 huniq hP hP₀
  rw [e] at hinv ⊢
  exact herg A hA hinv

include hπ1 in
/-- `π ≥ ε > 0` gives a unique stationary distribution (Doeblin in `ℓ¹`). -/
theorem stationary_unique_of_minor {ε : ℝ} (hε : 0 < ε) (hminor : ∀ z z', ε ≤ π z z') :
    ∀ q q' : Z → ℝ, (∀ z, 0 ≤ q z) → ∑ z, q z = 1 → (∀ z', ∑ z, q z * π z z' = q z') →
      (∀ z, 0 ≤ q' z) → ∑ z, q' z = 1 → (∀ z', ∑ z, q' z * π z z' = q' z') → q = q' := by
  intro q q' _ hq1 hqs _ hq1' hqs'
  set d : Z → ℝ := fun z => q z - q' z
  have hd : ∑ z, d z = 0 := by simp only [d, Finset.sum_sub_distrib, hq1, hq1', sub_self]
  have hfix : ∀ z', ∑ z, d z * π z z' = d z' := by
    intro z'
    simp only [d, sub_mul, Finset.sum_sub_distrib, hqs, hqs']
  have hk := sum_abs_mul_le hminor hπ1 hd
  simp_rw [hfix] at hk
  by_cases hZ : IsEmpty Z
  · funext z
    exact isEmptyElim z
  rw [not_isEmpty_iff] at hZ
  have hE : 0 < (Fintype.card Z : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hc : 0 < Fintype.card Z * ε := mul_pos hE hε
  have hS : 0 ≤ ∑ z, |d z| := Finset.sum_nonneg fun z _ => abs_nonneg _
  have h0 : ∑ z, |d z| = 0 := by nlinarith
  funext z
  have := (Finset.sum_eq_zero_iff_of_nonneg fun z _ => abs_nonneg (d z)).1 h0 z (Finset.mem_univ _)
  exact sub_eq_zero.1 (abs_eq_zero.1 this)

end ShockPath

end KrusellSmith

end LeanEconomics
