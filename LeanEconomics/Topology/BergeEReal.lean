/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Topology.Berge
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Berge's maximum theorem for extended-real objectives

`LeanEconomics.Topology.Berge` proves the maximum theorem for a real-valued objective. Here
the objective may take the value `-∞`, which is what a reward like `log c` does at zero
consumption.

Allowing `-∞` is what lets a dynamic program be posed without a floor on the reward. Every
model in this library that uses a floor does so to keep the reward real-valued and bounded,
and then has to prove separately that the floor never binds. With an extended-real
objective the floor is unnecessary from the start.

## What changes, and what does not

Less than one might expect, and two of the changes make the proof *simpler*: `EReal` is a
complete lattice, so `le_sSup` and `sSup_le` carry no boundedness or nonemptiness side
conditions, unlike their conditionally-complete counterparts.

One change is forced. The real proof of upper semicontinuity picks a value strictly between
`maxValue x` and `c`, which needs the order to be densely ordered. Mathlib has no
`DenselyOrdered EReal` instance, so upper semicontinuity here goes through *attainment*
instead: the supremum over a nonempty compact set is achieved, so a strict bound at every
point of the set is a strict bound on the supremum.

## Main results

* `LeanEconomics.continuous_maxValueE` : the maximum theorem for `EReal`-valued objectives.
-/

open Set Filter Topology

namespace LeanEconomics

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y → EReal} {Γ : X → Set Y} {x : X} {c : EReal}

/-- The value of a maximisation problem whose objective may be `-∞`. No boundedness
hypothesis is needed: `EReal` is a complete lattice. -/
noncomputable def maxValueE (f : X → Y → EReal) (Γ : X → Set Y) (x : X) : EReal :=
  sSup (f x '' Γ x)

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem le_maxValueE {y : Y} (hy : y ∈ Γ x) : f x y ≤ maxValueE f Γ x := le_sSup ⟨y, hy, rfl⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem maxValueE_le (h : ∀ y ∈ Γ x, f x y ≤ c) : maxValueE f Γ x ≤ c :=
  sSup_le (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

theorem continuous_fiberE (hf : Continuous ↿f) (x : X) : Continuous (f x) :=
  hf.comp (Continuous.prodMk_right x)

/-- The engine, exactly as in the real case: a strict upper bound over the constraint set
survives into a neighbourhood of the parameter. -/
theorem eventually_forall_ltE (hf : Continuous ↿f) (hΓc : IsCompact (Γ x))
    (huhc : UpperHemicontinuousAt Γ x) (hc : ∀ y ∈ Γ x, f x y < c) :
    ∀ᶠ x' in 𝓝 x, ∀ y ∈ Γ x', f x' y < c := by
  have hW : IsOpen (↿f ⁻¹' Iio c) := isOpen_Iio.preimage hf
  have hsub : ({x} : Set X) ×ˢ Γ x ⊆ ↿f ⁻¹' Iio c := by
    rintro ⟨x', y⟩ ⟨hx', hy⟩
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact hc y hy
  obtain ⟨u, v, hu, hv, hxu, hΓv, huv⟩ := generalized_tube_lemma isCompact_singleton hΓc hW hsub
  filter_upwards [huhc.forall_isOpen v hv hΓv, hu.mem_nhds (hxu rfl)] with x' hΓ' hx'u
  intro y hy
  have hmem : (x', y) ∈ u ×ˢ v := ⟨hx'u, hΓ' hy⟩
  exact huv hmem

/-- Upper hemicontinuity of the constraint set gives upper semicontinuity of the value.
Unlike the real case this goes through attainment of the supremum, `EReal` having no
`DenselyOrdered` instance to interpolate with. -/
theorem upperSemicontinuousAt_maxValueE (hf : Continuous ↿f) (hΓne : ∀ x, (Γ x).Nonempty)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuousAt Γ x) :
    UpperSemicontinuousAt (maxValueE f Γ) x := by
  intro c hc
  have h : ∀ y ∈ Γ x, f x y < c := fun y hy => lt_of_le_of_lt (le_maxValueE hy) hc
  filter_upwards [eventually_forall_ltE hf (hΓc x) huhc h] with x' hx'
  obtain ⟨y₀, hy₀, heq⟩ :=
    (hΓc x').exists_sSup_image_eq (hΓne x') (continuous_fiberE hf x').continuousOn
  rw [maxValueE, heq]
  exact hx' y₀ hy₀

/-- Lower hemicontinuity of the constraint set gives lower semicontinuity of the value. -/
theorem lowerSemicontinuousAt_maxValueE (hf : Continuous ↿f)
    (hlhc : LowerHemicontinuousAt Γ x) : LowerSemicontinuousAt (maxValueE f Γ) x := by
  intro c hc
  obtain ⟨_, ⟨y₀, hy₀, rfl⟩, hy₀c⟩ := lt_sSup_iff.mp hc
  have hW : IsOpen (↿f ⁻¹' Ioi c) := isOpen_Ioi.preimage hf
  obtain ⟨u, v, hu, hv, hxu, hy₀v, huv⟩ := isOpen_prod_iff.mp hW x y₀ hy₀c
  filter_upwards [(lowerHemicontinuousAt_iff.mp hlhc) v hv ⟨y₀, hy₀, hy₀v⟩,
    hu.mem_nhds hxu] with x' hne hx'u
  obtain ⟨y, hyΓ, hyv⟩ := hne
  have hmem : (x', y) ∈ u ×ˢ v := ⟨hx'u, hyv⟩
  exact lt_of_lt_of_le (huv hmem) (le_maxValueE hyΓ)

/-- **Berge's maximum theorem for an extended-real objective.** -/
theorem continuousAt_maxValueE (hf : Continuous ↿f) (hΓne : ∀ x, (Γ x).Nonempty)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuousAt Γ x)
    (hlhc : LowerHemicontinuousAt Γ x) : ContinuousAt (maxValueE f Γ) x := by
  rw [ContinuousAt, tendsto_order]
  exact ⟨lowerSemicontinuousAt_maxValueE hf hlhc,
    upperSemicontinuousAt_maxValueE hf hΓne hΓc huhc⟩

theorem continuous_maxValueE (hf : Continuous ↿f) (hΓne : ∀ x, (Γ x).Nonempty)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuous Γ) (hlhc : LowerHemicontinuous Γ) :
    Continuous (maxValueE f Γ) :=
  continuous_iff_continuousAt.mpr fun x =>
    continuousAt_maxValueE hf hΓne hΓc (huhc x) (hlhc x)

/-- At a maximiser the objective equals the value, exactly as in the real case. -/
theorem maxValueE_eq (hf : Continuous ↿f) (hΓne : (Γ x).Nonempty) (hΓc : IsCompact (Γ x)) :
    ∃ y ∈ Γ x, maxValueE f Γ x = f x y := by
  obtain ⟨y₀, hy₀, heq⟩ := hΓc.exists_sSup_image_eq hΓne (continuous_fiberE hf x).continuousOn
  exact ⟨y₀, hy₀, heq⟩

end LeanEconomics
