/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.FixedPoint.Kakutani
import LeanEconomics.FixedPoint.SchauderTychonoff

/-!
# The Fan–Glicksberg fixed-point theorem

Fan (1952) and Glicksberg (1952) extended Kakutani's theorem to locally convex spaces: a
correspondence on a nonempty compact convex subset `K` of a locally convex Hausdorff topological
vector space, with nonempty convex values in `K` and a closed graph over `K`, has a fixed point.
This is the theorem the existence proofs for economies with a continuum of agents apply on spaces
of measures with the weak topology. The module proves it from the Schauder–Tychonoff theorem
`schauderTychonoff`, following the proof of `kakutani` with convex neighbourhoods of zero in
place of balls.

* `exists_approx_fixedPoint_convexNhds`: for every convex neighbourhood `U` of zero some `x ∈ K`
  lies in the convex hull of the values of `F` at points `c ∈ K` with `c − x ∈ U`. The weights
  `μ_c(x) = max(0, 1 − p (c − x))`, with `p` the gauge of `U`, on a finite cover of `K` and a
  point `y_c ∈ F c` for each centre give a continuous self-map `x ↦ Σ μ_c(x) y_c / Σ μ_c(x)` of
  `K`, and a Schauder–Tychonoff fixed point of it is the point.
* `exists_uhc_nhds`: a closed graph into a compact set is upper hemicontinuous, in the form: for
  every neighbourhood `W` of zero, `F c ⊆ F a + W` for `c ∈ K` with `c − a` in some neighbourhood
  of zero. The pairs `(c, y)` of the graph with `y ∉ F a + interior W` form a compact set whose
  projection is closed and misses `a`.
* `fanGlicksberg`: if no point of `K` were fixed, each `a ∈ K` would have a convex neighbourhood
  `V_a` of zero such that no `x` with `x − a ∈ V_a` lies in the convex hull of the values at
  points `c ∈ K` with `c − x ∈ V_a` (upper hemicontinuity at `a` puts that hull inside the convex
  set `F a + W`, which a small `W` keeps away from `a` because `F a` is closed). Finitely many of
  the sets `{x | x − a ∈ V_a}` cover `K`, and an approximate fixed point for the intersection of
  their `V_a` contradicts this.
-/

namespace LeanEconomics.FixedPoint

open Set Filter Topology Pointwise

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **Approximate fixed points in a locally convex space.** For every convex neighbourhood `U` of
zero some `x ∈ K` lies in the convex hull of the values of `F` at points `c ∈ K` with
`c − x ∈ U`. -/
theorem exists_approx_fixedPoint_convexNhds [LocallyConvexSpace ℝ E] [T2Space E] {K : Set E}
    {F : E → Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hFne : ∀ x ∈ K, (F x).Nonempty) (hFK : ∀ x ∈ K, F x ⊆ K) {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) (hUc : Convex ℝ U) :
    ∃ x ∈ K, x ∈ convexHull ℝ (⋃ c ∈ {c | c ∈ K ∧ c - x ∈ U}, F c) := by
  classical
  set p : E → ℝ := gauge U with hpdef
  have hp : Continuous p := continuous_gauge hUc hU
  have hpU : ∀ v, p v < 1 → v ∈ U := by
    intro v hv
    have hint : v ∈ interior U := by
      rw [← setOfPred_gauge_lt_one_eq_interior hUc hU]
      exact hv
    exact interior_subset hint
  obtain ⟨T, hTK, hcov⟩ := hK.elim_nhds_subcover (fun c => {z | p (c - z) < 1}) fun c _ => by
    refine IsOpen.mem_nhds (isOpen_lt (hp.comp (continuous_const.sub continuous_id))
      continuous_const) ?_
    change p (c - c) < 1
    rw [sub_self, hpdef, gauge_zero]
    exact one_pos
  choose! y hy using hFne
  set μ : E → E → ℝ := fun c z => max 0 (1 - p (c - z)) with hμ
  have hμ0 : ∀ c z, 0 ≤ μ c z := fun c z => le_max_left _ _
  have hμc : ∀ c, Continuous (μ c) := fun c =>
    continuous_const.max (continuous_const.sub (hp.comp (continuous_const.sub continuous_id)))
  have hμU : ∀ c z, 0 < μ c z → c - z ∈ U := by
    intro c z hcz
    rcases lt_max_iff.1 hcz with h | h
    · exact absurd h (lt_irrefl 0)
    · exact hpU _ (by linarith)
  set g : E → E := fun x => T.centerMass (fun c => μ c x) y with hg
  have hsum : ∀ x ∈ K, 0 < ∑ c ∈ T, μ c x := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcov hx)
    exact Finset.sum_pos' (fun c _ => hμ0 c x) ⟨c, hc, lt_max_of_lt_right (by simpa using hxc)⟩
  have hgmem : ∀ x ∈ K, g x ∈ convexHull ℝ (⋃ c ∈ {c | c ∈ K ∧ c - x ∈ U}, F c) := by
    intro x hx
    have hfil : ∑ c ∈ T with μ c x ≠ 0, μ c x = ∑ c ∈ T, μ c x :=
      Finset.sum_filter_ne_zero T
    change T.centerMass (fun c => μ c x) y ∈ _
    rw [← Finset.centerMass_filter_ne_zero y]
    refine Finset.centerMass_mem_convexHull _ (fun c _ => hμ0 c x) (hfil ▸ hsum x hx) ?_
    intro c hc
    obtain ⟨hcT, hpos⟩ := Finset.mem_filter.1 hc
    have hcK : c ∈ K := hTK c hcT
    exact mem_iUnion₂.2 ⟨c, ⟨hcK, hμU c x (lt_of_le_of_ne (hμ0 c x) (Ne.symm hpos))⟩,
      hy c hcK⟩
  have hgK : MapsTo g K K := fun x hx =>
    convexHull_min (iUnion₂_subset fun c hc => hFK c hc.1) hconv (hgmem x hx)
  have hgc : ContinuousOn g K := by
    have hs : ContinuousOn (fun x => ∑ c ∈ T, μ c x) K :=
      (continuous_finsetSum T fun c _ => hμc c).continuousOn
    have hv : ContinuousOn (fun x => ∑ c ∈ T, μ c x • y c) K :=
      (continuous_finsetSum T fun c _ => (hμc c).smul continuous_const).continuousOn
    exact (hs.inv₀ fun x hx => (hsum x hx).ne').smul hv
  obtain ⟨x, hx, hfx⟩ := schauderTychonoff hK hconv hne hgc hgK
  have h := hgmem x hx
  rw [hfx] at h
  exact ⟨x, hx, h⟩

omit [Module ℝ E] [ContinuousSMul ℝ E] in
/-- **A closed graph into a compact set is upper hemicontinuous**, neighbourhood form: for every
neighbourhood `W` of zero, the values of `F` at points `c ∈ K` with `c − a` in some neighbourhood
of zero lie in `F a + W`. -/
theorem exists_uhc_nhds [T2Space E] {K : Set E} {F : E → Set E} (hK : IsCompact K)
    (hFK : ∀ x ∈ K, F x ⊆ K) (hgraph : IsClosed (graphOn K F)) (a : E) {W : Set E}
    (hW : W ∈ 𝓝 (0 : E)) : ∃ N ∈ 𝓝 (0 : E), ∀ c ∈ K, c - a ∈ N → F c ⊆ F a + W := by
  have hW0 : (0 : E) ∈ interior W := mem_interior_iff_mem_nhds.2 hW
  have hO : IsOpen (F a + interior W) := isOpen_interior.add_left
  set B : Set (E × E) := graphOn K F ∩ (Prod.snd ⁻¹' (F a + interior W))ᶜ with hB
  have hBc : IsCompact B :=
    (hK.prod hK).of_isClosed_subset (hgraph.inter (hO.preimage continuous_snd).isClosed_compl)
      fun q hq => ⟨hq.1.1, hFK _ hq.1.1 hq.1.2⟩
  have hP : IsClosed (Prod.fst '' B) := (hBc.image continuous_fst).isClosed
  have haP : a ∉ Prod.fst '' B := by
    rintro ⟨q, ⟨hqG, hqO⟩, hqa⟩
    exact hqO ⟨q.2, hqa ▸ hqG.2, 0, hW0, add_zero _⟩
  have hN : (fun n => a + n) ⁻¹' (Prod.fst '' B)ᶜ ∈ 𝓝 (0 : E) := by
    refine (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds ?_
    change (Prod.fst '' B)ᶜ ∈ 𝓝 (a + 0)
    rw [add_zero]
    exact hP.isOpen_compl.mem_nhds haP
  refine ⟨_, hN, fun c hc hca y hy => ?_⟩
  have hc' : c ∉ Prod.fst '' B := by
    have h : a + (c - a) ∈ (Prod.fst '' B)ᶜ := hca
    rwa [add_sub_cancel] at h
  by_contra hyW
  exact hc' ⟨(c, y), ⟨⟨hc, hy⟩, fun h => hyW (add_subset_add_left interior_subset h)⟩, rfl⟩

/-- **Fan–Glicksberg fixed-point theorem** (Fan 1952; Glicksberg 1952). Let `K` be a nonempty
compact convex subset of a real locally convex Hausdorff topological vector space and `F` a
correspondence with nonempty convex values in `K` at points of `K` and a closed graph over `K`.
Then `F` has a fixed point: some `x ∈ K` with `x ∈ F x`. -/
theorem fanGlicksberg [LocallyConvexSpace ℝ E] [T2Space E] {K : Set E} {F : E → Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) (hFne : ∀ x ∈ K, (F x).Nonempty)
    (hFconv : ∀ x ∈ K, Convex ℝ (F x)) (hFK : ∀ x ∈ K, F x ⊆ K)
    (hgraph : IsClosed (graphOn K F)) : ∃ x ∈ K, x ∈ F x := by
  classical
  by_contra hcon
  have hno : ∀ a ∈ K, a ∉ F a := fun a ha h => hcon ⟨a, ha, h⟩
  -- at each point of `K`, a convex neighbourhood of zero that rules out approximate fixed points
  have key : ∀ a ∈ K, ∃ V ∈ 𝓝 (0 : E), Convex ℝ V ∧ ∀ x, x - a ∈ V →
      x ∉ convexHull ℝ (⋃ c ∈ {c | c ∈ K ∧ c - x ∈ V}, F c) := by
    intro a ha
    have hFa : IsClosed (F a) := by
      have h : F a = (fun y => (a, y)) ⁻¹' graphOn K F := by
        ext y
        simp [graphOn, ha]
      rw [h]
      exact hgraph.preimage (continuous_const.prodMk continuous_id)
    have hW0 : (fun w => a - w) ⁻¹' (F a)ᶜ ∈ 𝓝 (0 : E) := by
      refine (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds ?_
      change (F a)ᶜ ∈ 𝓝 (a - 0)
      rw [sub_zero]
      exact hFa.isOpen_compl.mem_nhds (hno a ha)
    obtain ⟨W1, hW1, hW1half⟩ := exists_nhds_zero_half hW0
    obtain ⟨W, ⟨hWn, hWc⟩, hWsub⟩ := (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.1 hW1
    obtain ⟨N, hN, hNuhc⟩ := exists_uhc_nhds hK hFK hgraph a hWn
    obtain ⟨N1, hN1, hN1half⟩ := exists_nhds_zero_half hN
    have hnegW : -W ∈ 𝓝 (0 : E) := neg_mem_nhds_zero E hWn
    obtain ⟨V, ⟨hVn, hVc⟩, hVsub⟩ :=
      (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.1 (inter_mem hN1 hnegW)
    refine ⟨V, hVn, hVc, fun x hxa hx => ?_⟩
    have hsub : convexHull ℝ (⋃ c ∈ {c | c ∈ K ∧ c - x ∈ V}, F c) ⊆ F a + W := by
      refine convexHull_min (iUnion₂_subset fun c hc => hNuhc c hc.1 ?_)
        ((hFconv a ha).add hWc)
      have hca : c - a = (c - x) + (x - a) := by abel
      rw [hca]
      exact hN1half _ (hVsub hc.2).1 _ (hVsub hxa).1
    obtain ⟨y, hy, w, hw, hyw⟩ := hsub hx
    have hax : a - x ∈ W := by
      have h : x - a ∈ -W := (hVsub hxa).2
      rwa [Set.mem_neg, neg_sub] at h
    have hmem : a - (w + (a - x)) ∈ (F a)ᶜ := hW1half _ (hWsub hw) _ (hWsub hax)
    have hya : a - (w + (a - x)) = y := by
      rw [← hyw, sub_add_eq_sub_sub, sub_sub_sub_cancel_left, add_sub_cancel_right]
    rw [hya] at hmem
    exact hmem hy
  choose! V hV hVc hVprop using key
  -- finitely many of the neighbourhoods cover `K`
  obtain ⟨T, hTK, hcov⟩ := hK.elim_nhds_subcover (fun a => {x | x - a ∈ V a}) fun a ha => by
    refine (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds ?_
    change V a ∈ 𝓝 (a - a)
    rw [sub_self]
    exact hV a ha
  set U : Set E := ⋂ a ∈ T, V a with hUdef
  have hU : U ∈ 𝓝 (0 : E) := (Filter.biInter_finset_mem T).2 fun a ha => hV a (hTK a ha)
  have hUc : Convex ℝ U := convex_iInter₂ fun a ha => hVc a (hTK a ha)
  obtain ⟨x, hxK, hxhull⟩ :=
    exists_approx_fixedPoint_convexNhds hK hconv hne hFne hFK hU hUc
  obtain ⟨a, haT, hxa⟩ := mem_iUnion₂.1 (hcov hxK)
  refine hVprop a (hTK a haT) x hxa (convexHull_mono ?_ hxhull)
  exact iUnion₂_mono' fun c hc =>
    ⟨c, ⟨hc.1, mem_iInter₂.1 hc.2 a haT⟩, subset_rfl⟩

end LeanEconomics.FixedPoint
