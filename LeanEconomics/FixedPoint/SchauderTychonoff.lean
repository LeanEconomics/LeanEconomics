/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.FixedPoint.Brouwer
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# The Schauder–Tychonoff fixed-point theorem

Tychonoff (1935) extended Schauder's theorem from normed spaces to locally convex spaces: a
continuous self-map of a nonempty compact convex subset `K` of a locally convex Hausdorff
topological vector space has a fixed point. This is the form used on spaces of measures with the
weak topology, which are not normable. The module proves it from the Brouwer theorem `brouwer`,
with gauges of convex neighbourhoods of zero in place of the norm of `schauder`.

* `exists_approx_fixedPoint_nhds`: in any real topological vector space, for every convex
  neighbourhood `U` of zero there is `x ∈ K` with `x − f x ∈ U`. Cover `K` by finitely many sets
  `{z | p (yᵢ − z) < 1}` with `yᵢ ∈ K`, where `p` is the gauge of `U` (continuous because `U` is a
  convex neighbourhood of zero). The weights `μᵢ(z) = max(0, 1 − p (yᵢ − z))` normalise to a
  continuous map from `K` into the standard simplex of `ℝ^{yᵢ}`, and composing with
  `λ ↦ Σ λᵢ yᵢ` and `f` gives a continuous self-map of the simplex. A Brouwer fixed point `λ`
  gives `x = Σ λᵢ yᵢ ∈ K` with `x − f x = Σ λᵢ (yᵢ − f x)`, a convex combination of points
  `yᵢ − f x` with `p (yᵢ − f x) < 1`, which lie in `U`.
* `schauderTychonoff`: in a locally convex Hausdorff space the closed sets
  `{x ∈ K | x − f x ∈ closure U}` have the finite intersection property (a finite intersection of
  convex neighbourhoods of zero is one), so by compactness some `x ∈ K` has `x − f x` in the
  closure of every convex neighbourhood of zero. Closed neighbourhoods of zero form a basis and
  convex ones lie inside each of them, so `x − f x = 0`.
* `schauderTychonoff_subtype`: the same for `f : K → K`.

The simplex is written out as a set rather than through Mathlib's `stdSimplex`, which is
deprecated in the pinned Mathlib.
-/

namespace LeanEconomics.FixedPoint

open Set Filter Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **Approximate fixed points in a topological vector space.** A map `f` continuous on a
nonempty compact convex subset `K` of a real topological vector space, with `f(K) ⊆ K`, has for
every convex neighbourhood `U` of zero a point `x ∈ K` with `x − f x ∈ U`. -/
theorem exists_approx_fixedPoint_nhds {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) {f : E → E} (hf : ContinuousOn f K) (hmaps : MapsTo f K K) {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) (hUc : Convex ℝ U) : ∃ x ∈ K, x - f x ∈ U := by
  classical
  set p : E → ℝ := gauge U with hpdef
  have hp : Continuous p := continuous_gauge hUc hU
  have hpU : ∀ v, p v < 1 → v ∈ U := by
    intro v hv
    have hint : v ∈ interior U := by
      rw [← setOfPred_gauge_lt_one_eq_interior hUc hU]
      exact hv
    exact interior_subset hint
  -- a finite cover of `K` by gauge balls centred in `K`
  obtain ⟨s, hsK, hcov⟩ := hK.elim_nhds_subcover (fun y => {z | p (y - z) < 1}) fun y _ => by
    refine IsOpen.mem_nhds (isOpen_lt (hp.comp (continuous_const.sub continuous_id))
      continuous_const) ?_
    change p (y - y) < 1
    rw [sub_self, hpdef, gauge_zero]
    exact one_pos
  -- the weights
  set μ : E → E → ℝ := fun y z => max 0 (1 - p (y - z)) with hμ
  have hμ0 : ∀ y z, 0 ≤ μ y z := fun y z => le_max_left _ _
  have hμc : ∀ y, Continuous (μ y) := fun y =>
    continuous_const.max (continuous_const.sub (hp.comp (continuous_const.sub continuous_id)))
  have hμU : ∀ y z, 0 < μ y z → y - z ∈ U := by
    intro y z hyz
    rcases lt_max_iff.1 hyz with h | h
    · exact absurd h (lt_irrefl 0)
    · exact hpU _ (by linarith)
  have hsum : ∀ z ∈ K, 0 < ∑ i : s, μ i z := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 (hcov hz)
    refine Finset.sum_pos' (fun i _ => hμ0 i z) ⟨⟨y, hy⟩, Finset.mem_univ _, ?_⟩
    exact lt_max_of_lt_right (by simpa using hzy)
  -- the simplex on the cover and the maps through it
  set S : Set (s → ℝ) := {l | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1} with hS
  set L : (s → ℝ) → E := fun l => ∑ i : s, l i • (i : E) with hL
  have hLc : Continuous L :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hLK : MapsTo L S K := fun l hl =>
    hconv.sum_mem (fun i _ => hl.1 i) hl.2 fun i _ => hsK i i.2
  set w : E → (s → ℝ) := fun z i => μ i z / ∑ j : s, μ j z with hw
  have hwc : ContinuousOn w K := by
    refine continuousOn_pi.2 fun i => ?_
    exact (hμc i).continuousOn.div
      (continuous_finsetSum Finset.univ fun (j : s) _ => hμc (j : E)).continuousOn
      fun z hz => (hsum z hz).ne'
  have hwS : MapsTo w K S := by
    intro z hz
    refine ⟨fun i => div_nonneg (hμ0 i z) (hsum z hz).le, ?_⟩
    simp only [hw]
    rw [← Finset.sum_div, div_self (hsum z hz).ne']
  have hSc : IsCompact S := by
    refine IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ : s => (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))) ?_ ?_
    · rw [hS, ofPred_and, ofPred_forall]
      refine IsClosed.inter (isClosed_iInter fun i => isClosed_le continuous_const
        (continuous_apply i)) (isClosed_eq ?_ continuous_const)
      exact continuous_finsetSum _ fun i _ => continuous_apply i
    · intro l hl i _
      refine ⟨hl.1 i, ?_⟩
      rw [← hl.2]
      exact Finset.single_le_sum (fun j _ => hl.1 j) (Finset.mem_univ i)
  have hSconv : Convex ℝ S := by
    intro l hl m hm a b ha hb hab
    refine ⟨fun i => add_nonneg (mul_nonneg ha (hl.1 i)) (mul_nonneg hb (hm.1 i)), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hl.2, hm.2, mul_one, hab]
  obtain ⟨z0, hz0⟩ := hne
  have hSne : S.Nonempty := ⟨w z0, hwS hz0⟩
  set h : (s → ℝ) → (s → ℝ) := fun l => w (f (L l)) with hh
  have hhc : ContinuousOn h S :=
    hwc.comp (hf.comp hLc.continuousOn hLK) fun l hl => hmaps (hLK hl)
  have hhm : MapsTo h S S := fun l hl => hwS (hmaps (hLK hl))
  obtain ⟨l, hl, hfix⟩ := brouwer hSc hSconv hSne hhc hhm
  -- the fixed point of the simplex map is an approximate fixed point of `f`
  set z := f (L l) with hz
  refine ⟨L l, hLK hl, ?_⟩
  have hpos : ∀ i, 0 < l i → (i : E) - z ∈ U := by
    intro i hi
    have hwi : 0 < w z i := by
      have := congrFun hfix i
      simp only [hh] at this
      rw [← hz] at this
      rw [this]
      exact hi
    exact hμU _ _ ((div_pos_iff_of_pos_right (hsum z (hmaps (hLK hl)))).1 hwi)
  have hdiff : L l - z = ∑ i : s, l i • ((i : E) - z) := by
    simp only [hL, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hl.2, one_smul]
  have h0U : (0 : E) ∈ U := mem_of_mem_nhds hU
  have hterm : ∀ i : s, l i • ((i : E) - z) = l i • (if 0 < l i then (i : E) - z else 0) := by
    intro i
    split_ifs with hi
    · rfl
    · rw [le_antisymm (not_lt.1 hi) (hl.1 i), zero_smul, zero_smul]
  rw [hdiff, Finset.sum_congr rfl fun i _ => hterm i]
  refine hUc.sum_mem (fun i _ => hl.1 i) hl.2 fun i _ => ?_
  split_ifs with hi
  · exact hpos i hi
  · exact h0U

/-- **Schauder–Tychonoff fixed-point theorem.** A map continuous on a nonempty compact convex
subset `K` of a real locally convex Hausdorff topological vector space and mapping `K` into
itself has a fixed point in `K`. -/
theorem schauderTychonoff [LocallyConvexSpace ℝ E] [T2Space E] {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) {f : E → E} (hf : ContinuousOn f K)
    (hmaps : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  classical
  set ι := {U : Set E // U ∈ 𝓝 (0 : E) ∧ Convex ℝ U}
  set t : ι → Set E := fun U => K ∩ (fun x => x - f x) ⁻¹' closure U.1 with ht
  have htc : ∀ U, IsClosed (t U) := fun U =>
    (continuousOn_id.sub hf).preimage_isClosed_of_isClosed hK.isClosed isClosed_closure
  have hst : ∀ u : Finset ι, (K ∩ ⋂ U ∈ u, t U).Nonempty := by
    intro u
    set W : Set E := ⋂ U ∈ u, U.1 with hW
    have hWn : W ∈ 𝓝 (0 : E) := (Filter.biInter_finset_mem u).2 fun U _ => U.2.1
    have hWc : Convex ℝ W := convex_iInter₂ fun U _ => U.2.2
    obtain ⟨x, hx, hxW⟩ := exists_approx_fixedPoint_nhds hK hconv hne hf hmaps hWn hWc
    refine ⟨x, hx, mem_iInter₂.2 fun U hU => ⟨hx, ?_⟩⟩
    exact subset_closure (mem_iInter₂.1 hxW U hU)
  obtain ⟨x, hx, hxt⟩ := hK.inter_iInter_nonempty t htc hst
  refine ⟨x, hx, ?_⟩
  by_contra hne'
  have hv : x - f x ≠ 0 := sub_ne_zero.2 (Ne.symm hne')
  have hcompl : ({x - f x}ᶜ : Set E) ∈ 𝓝 (0 : E) :=
    isOpen_compl_singleton.mem_nhds (Ne.symm hv)
  obtain ⟨C, ⟨hCn, hCcl⟩, hCsub⟩ := (closed_nhds_basis (0 : E)).mem_iff.1 hcompl
  obtain ⟨U, ⟨hUn, hUc⟩, hUC⟩ := (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.1 hCn
  have hxU := (mem_iInter.1 hxt ⟨U, hUn, hUc⟩).2
  exact hCsub (closure_minimal hUC hCcl hxU) rfl

/-- **Schauder–Tychonoff fixed-point theorem, subtype form.** A continuous self-map of a
nonempty compact convex subset `K` of a real locally convex Hausdorff topological vector space
has a fixed point. -/
theorem schauderTychonoff_subtype [LocallyConvexSpace ℝ E] [T2Space E] {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) {f : K → K}
    (hf : Continuous f) : ∃ x : K, f x = x := by
  classical
  set F : E → E := fun x => if h : x ∈ K then (f ⟨x, h⟩ : E) else x with hFdef
  have hFK : ∀ x : K, F x = f x := fun x => by simp [hFdef, x.2]
  have hFc : ContinuousOn F K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : K.domRestrict F = fun x : K => (f x : E) := funext hFK
    rw [this]
    exact continuous_subtype_val.comp hf
  have hFm : MapsTo F K K := fun x hx => by
    rw [hFK ⟨x, hx⟩]
    exact (f _).2
  obtain ⟨x, hx, hFx⟩ := schauderTychonoff hK hconv hne hFc hFm
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [← hFK ⟨x, hx⟩]
  exact hFx

end LeanEconomics.FixedPoint
