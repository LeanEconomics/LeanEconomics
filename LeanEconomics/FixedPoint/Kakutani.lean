/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.FixedPoint.Schauder

/-!
# Kakutani's fixed-point theorem in normed spaces

Kakutani (1941) proved that an upper hemicontinuous correspondence with nonempty convex values
from a simplex into itself has a fixed point; Bohnenblust and Karlin (1950) and Glicksberg (1952)
extended it beyond finite dimensions. This module proves the theorem for a nonempty compact convex
subset `K` of any real normed space, with the hypothesis in its closed-graph form: `F x` nonempty
and convex and inside `K` for `x ∈ K`, and the graph of `F` over `K` closed. It includes the
finite-dimensional theorem as the case `FiniteDimensional ℝ E`.

The proof reduces to Schauder's theorem `schauder` by approximate continuous selections (Cellina):

* `exists_approx_fixedPoint`: for every `ε > 0` there is `x ∈ K` lying in the convex hull of the
  values of `F` at points of `K` within `ε` of `x`. Take a finite `ε`-net `{cᵢ} ⊆ K`, a point
  `yᵢ ∈ F cᵢ`, the tent weights `wᵢ(x) = max(0, ε − ‖x − cᵢ‖)`, and the continuous map
  `g x = Σ wᵢ(x) yᵢ / Σ wᵢ(x)` of `K` into itself; a Schauder fixed point of `g` is the point.
* `exists_uhc`: a closed graph into a compact set makes `F` upper hemicontinuous, in the form
  `F x' ⊆ thickening δ (F a)` for `x'` near `a`.
* `kakutani`: approximate fixed points at `ε = 1/(n+1)` have a limit `a ∈ K`; for each `δ > 0`
  they eventually lie in the convex set `thickening δ (F a)`, so `a` lies in every
  `cthickening δ (F a)`, hence in the closed set `F a`.
-/

namespace LeanEconomics.FixedPoint

open Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The graph of a correspondence `F` over a set `K`. -/
def graphOn {α : Type*} (K : Set α) (F : α → Set α) : Set (α × α) := {p | p.1 ∈ K ∧ p.2 ∈ F p.1}

/-- The tent weight of the point `x` at the centre `c` with radius `ε`. -/
noncomputable def tent (ε : ℝ) (c x : E) : ℝ := max 0 (ε - ‖x - c‖)

omit [NormedSpace ℝ E] in
theorem tent_nonneg (ε : ℝ) (c x : E) : 0 ≤ tent ε c x := le_max_left _ _

omit [NormedSpace ℝ E] in
theorem tent_pos_iff {ε : ℝ} {c x : E} : 0 < tent ε c x ↔ dist x c < ε := by
  rw [tent, lt_max_iff, dist_eq_norm, sub_pos]
  exact ⟨fun h => h.resolve_left (lt_irrefl 0), Or.inr⟩

omit [NormedSpace ℝ E] in
theorem continuous_tent (ε : ℝ) (c : E) : Continuous (tent ε c) :=
  continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)

omit [NormedSpace ℝ E] in
/-- The values of a correspondence with a closed graph over `K` are closed at points of `K`. -/
theorem isClosed_apply_of_isClosed_graphOn {K : Set E} {F : E → Set E}
    (hgraph : IsClosed (graphOn K F)) {a : E} (ha : a ∈ K) : IsClosed (F a) := by
  have h : F a = (fun y => (a, y)) ⁻¹' graphOn K F := by
    ext y
    simp [graphOn, ha]
  rw [h]
  exact hgraph.preimage (continuous_const.prodMk continuous_id)

/-- **Approximate fixed points.** For every `ε > 0` some `x ∈ K` lies in the convex hull of the
values of `F` at points of `K` within `ε` of `x`. -/
theorem exists_approx_fixedPoint {K : Set E} {F : E → Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hFne : ∀ x ∈ K, (F x).Nonempty)
    (hFK : ∀ x ∈ K, F x ⊆ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ K, x ∈ convexHull ℝ (⋃ x' ∈ K ∩ ball x ε, F x') := by
  classical
  obtain ⟨t, htK, htf, hcover⟩ := hK.finite_cover_balls hε
  set T := htf.toFinset with hT
  choose! y hy using hFne
  set g : E → E := fun x => T.centerMass (fun c => tent ε c x) y with hg
  have hsum : ∀ x ∈ K, 0 < ∑ c ∈ T, tent ε c x := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcover hx)
    exact Finset.sum_pos' (fun c _ => tent_nonneg ε c x)
      ⟨c, htf.mem_toFinset.2 hc, tent_pos_iff.2 (mem_ball.1 hxc)⟩
  have hgmem : ∀ x ∈ K, g x ∈ convexHull ℝ (⋃ x' ∈ K ∩ ball x ε, F x') := by
    intro x hx
    have hfil : ∑ c ∈ T with tent ε c x ≠ 0, tent ε c x = ∑ c ∈ T, tent ε c x :=
      Finset.sum_filter_ne_zero T
    change T.centerMass (fun c => tent ε c x) y ∈ _
    rw [← Finset.centerMass_filter_ne_zero y]
    refine Finset.centerMass_mem_convexHull _ (fun c _ => tent_nonneg ε c x)
      (hfil ▸ hsum x hx) ?_
    intro c hc
    obtain ⟨hcT, hpos⟩ := Finset.mem_filter.1 hc
    have hcK : c ∈ K := htK (htf.mem_toFinset.1 hcT)
    refine mem_iUnion₂.2 ⟨c, ⟨hcK, ?_⟩, hy c hcK⟩
    rw [mem_ball, dist_comm]
    exact tent_pos_iff.1 (lt_of_le_of_ne (tent_nonneg ε c x) (Ne.symm hpos))
  have hgK : MapsTo g K K := fun x hx =>
    convexHull_min (iUnion₂_subset fun x' hx' => hFK x' hx'.1) hconv (hgmem x hx)
  have hgc : ContinuousOn g K := by
    have hs : ContinuousOn (fun x => ∑ c ∈ T, tent ε c x) K :=
      (continuous_finsetSum T fun c _ => continuous_tent ε c).continuousOn
    have hv : ContinuousOn (fun x => ∑ c ∈ T, tent ε c x • y c) K :=
      (continuous_finsetSum T fun c _ => (continuous_tent ε c).smul continuous_const).continuousOn
    exact (hs.inv₀ fun x hx => (hsum x hx).ne').smul hv
  obtain ⟨x, hx, hfx⟩ := schauder hK hconv hne hgc hgK
  have h := hgmem x hx
  rw [hfx] at h
  exact ⟨x, hx, h⟩

omit [NormedSpace ℝ E] in
/-- **A closed graph into a compact set is upper hemicontinuous**: for every `δ > 0`, the values
of `F` at points of `K` near `a` lie in the `δ`-thickening of `F a`. -/
theorem exists_uhc {K : Set E} {F : E → Set E} (hK : IsCompact K) (hFK : ∀ x ∈ K, F x ⊆ K)
    (hgraph : IsClosed (graphOn K F)) {a : E} (hFa : (F a).Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ x' ∈ K, dist x' a < η → F x' ⊆ thickening δ (F a) := by
  by_contra hcon
  have hseq : ∀ n : ℕ, ∃ x' ∈ K, dist x' a < 1 / ((n : ℝ) + 1) ∧
      ∃ y ∈ F x', δ ≤ infDist y (F a) := by
    intro n
    by_contra hn
    refine hcon ⟨1 / ((n : ℝ) + 1), by positivity, fun x' hx' hd y hy => ?_⟩
    rw [mem_thickening_iff_infDist_lt hFa]
    by_contra hy'
    exact hn ⟨x', hx', hd, y, hy, not_lt.1 hy'⟩
  choose x' hx'K hx'd y hyF hyd using hseq
  obtain ⟨b, -, φ, hφ, hlim⟩ := hK.tendsto_subseq fun n => hFK _ (hx'K n) (hyF n)
  have hxlim : Tendsto (x' ∘ φ) atTop (𝓝 a) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg)
      (fun n => (hx'd (φ n)).le) ?_)
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hgr : (a, b) ∈ graphOn K F :=
    hgraph.mem_of_tendsto (hxlim.prodMk_nhds hlim)
      (Eventually.of_forall fun n => ⟨hx'K (φ n), hyF (φ n)⟩)
  have h1 : δ ≤ infDist b (F a) :=
    ge_of_tendsto (((continuous_infDist_pt (F a)).tendsto b).comp hlim)
      (Eventually.of_forall fun n => hyd (φ n))
  rw [infDist_zero_of_mem hgr.2] at h1
  linarith

/-- **Kakutani's fixed-point theorem** (Kakutani 1941; Bohnenblust–Karlin 1950; Glicksberg 1952).
Let `K` be a nonempty compact convex subset of a real normed space and `F` a correspondence with
nonempty convex values in `K` at points of `K` and a closed graph over `K`. Then `F` has a fixed
point: some `x ∈ K` with `x ∈ F x`. -/
theorem kakutani {K : Set E} {F : E → Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hFne : ∀ x ∈ K, (F x).Nonempty) (hFconv : ∀ x ∈ K, Convex ℝ (F x))
    (hFK : ∀ x ∈ K, F x ⊆ K) (hgraph : IsClosed (graphOn K F)) : ∃ x ∈ K, x ∈ F x := by
  have happ : ∀ n : ℕ, ∃ x ∈ K,
      x ∈ convexHull ℝ (⋃ x' ∈ K ∩ ball x (1 / ((n : ℝ) + 1)), F x') :=
    fun n => exists_approx_fixedPoint hK hconv hne hFne hFK (by positivity)
  choose x hxK hxhull using happ
  obtain ⟨a, haK, φ, hφ, hlim⟩ := hK.tendsto_subseq hxK
  refine ⟨a, haK, ?_⟩
  rw [← (isClosed_apply_of_isClosed_graphOn hgraph haK).closure_eq,
    closure_eq_iInter_cthickening]
  refine mem_iInter₂.2 fun δ hδ => ?_
  obtain ⟨η, hη, huhc⟩ := exists_uhc hK hFK hgraph (hFne a haK) hδ
  have h1 : ∀ᶠ n in atTop, dist ((x ∘ φ) n) a < η / 2 :=
    Metric.tendsto_nhds.1 hlim (η / 2) (half_pos hη)
  have h2 : ∀ᶠ n in atTop, 1 / ((φ n : ℝ) + 1) < η / 2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).eventually
      (gt_mem_nhds (half_pos hη))
  have hev : ∀ᶠ n in atTop, (x ∘ φ) n ∈ thickening δ (F a) := by
    filter_upwards [h1, h2] with n hn1 hn2
    refine convexHull_min ?_ ((hFconv a haK).thickening δ) (hxhull (φ n))
    refine iUnion₂_subset fun x' hx' => huhc x' hx'.1 ?_
    calc dist x' a ≤ dist x' (x (φ n)) + dist (x (φ n)) a := dist_triangle _ _ _
      _ < η / 2 + η / 2 := add_lt_add ((mem_ball.1 hx'.2).trans hn2) hn1
      _ = η := add_halves η
  exact closure_thickening_subset_cthickening δ _ (mem_closure_of_tendsto hlim hev)

/-- **Kakutani's theorem in `ℝⁿ`**, the form in which it is usually quoted. -/
theorem kakutani_euclidean {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hFne : ∀ x ∈ K, (F x).Nonempty)
    (hFconv : ∀ x ∈ K, Convex ℝ (F x)) (hFK : ∀ x ∈ K, F x ⊆ K)
    (hgraph : IsClosed (graphOn K F)) : ∃ x ∈ K, x ∈ F x :=
  kakutani hK hconv hne hFne hFconv hFK hgraph

end LeanEconomics.FixedPoint
