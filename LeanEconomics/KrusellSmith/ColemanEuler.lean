/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# The one-period Euler root

Milestone CO1 of `COLEMAN_PLAN.md`: the building block of the Coleman operator, as pure real
analysis.

A household with cash `y` chooses saving `s ∈ [0, ā]`, `s < y`; marginal utility `u'` is strictly
decreasing on `(0, ∞)`; the continuation `B(s)` — discounted expected return times next period's
marginal utility — is antitone in `s`. **The Euler root** (`IsEulerRoot`) is the KKT point:
`u'(y − s) ≤ B(s)` if `s > 0`, `u'(y − s) ≥ B(s)` if `s < ā`.

* **`eulerRoot_cons_le`**: consumption `y − s` rises with cash and when the continuation falls;
* **`eulerRoot_saving_le`**: saving rises with cash;
* **`eulerRoot_unique`**: the root is unique;
* **`exists_eulerRoot`**: it exists, for continuous `u'` with the Inada condition at zero and a
  continuous continuation: a corner, or the intermediate value theorem.
-/

open Set Filter Topology

namespace LeanEconomics

namespace KrusellSmith

namespace Coleman

/-- **The Euler root**: saving `s` at cash `y`, against the continuation `B`, with the corners at
`0` and the cap `ā`. -/
def IsEulerRoot (du B : ℝ → ℝ) (cap y s : ℝ) : Prop :=
  0 ≤ s ∧ s ≤ cap ∧ s < y ∧ (0 < s → du (y - s) ≤ B s) ∧ (s < cap → B s ≤ du (y - s))

variable {du B B' : ℝ → ℝ} {cap : ℝ}

/-- **Consumption rises with cash and when the continuation falls.** -/
theorem eulerRoot_cons_le (hdu : StrictAntiOn du (Ioi 0)) (hB : AntitoneOn B (Icc 0 cap))
    (hBB : ∀ s ∈ Icc 0 cap, B' s ≤ B s) {y y' s s' : ℝ} (hyy : y ≤ y')
    (h : IsEulerRoot du B cap y s) (h' : IsEulerRoot du B' cap y' s') :
    y - s ≤ y' - s' := by
  obtain ⟨hs0, hscap, hsy, -, hs2⟩ := h
  obtain ⟨hs0', hscap', hsy', hs1', -⟩ := h'
  by_contra hlt
  rw [not_le] at hlt
  have hss : s < s' := by linarith
  have h1 := hs1' (by linarith)
  have h2 := hs2 (by linarith)
  have h3 : du (y - s) < du (y' - s') :=
    hdu (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith)) hlt
  have h4 : B s' ≤ B s := hB ⟨hs0, hscap⟩ ⟨by linarith, hscap'⟩ hss.le
  have h5 := hBB s' ⟨by linarith, hscap'⟩
  linarith

/-- **Saving rises with cash.** -/
theorem eulerRoot_saving_le (hdu : StrictAntiOn du (Ioi 0)) (hB : AntitoneOn B (Icc 0 cap))
    {y y' s s' : ℝ} (hyy : y ≤ y') (h : IsEulerRoot du B cap y s)
    (h' : IsEulerRoot du B cap y' s') : s ≤ s' := by
  obtain ⟨hs0, hscap, hsy, hs1, -⟩ := h
  obtain ⟨hs0', hscap', hsy', -, hs2'⟩ := h'
  by_contra hlt
  rw [not_le] at hlt
  have h1 := hs1 (by linarith)
  have h2 := hs2' (by linarith)
  have h3 : du (y' - s') < du (y - s) :=
    hdu (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith)) (by linarith)
  have h4 : B s ≤ B s' := hB ⟨hs0', hscap'⟩ ⟨hs0, hscap⟩ hlt.le
  linarith

/-- **The Euler root is unique.** -/
theorem eulerRoot_unique (hdu : StrictAntiOn du (Ioi 0)) (hB : AntitoneOn B (Icc 0 cap))
    {y s s' : ℝ} (h : IsEulerRoot du B cap y s) (h' : IsEulerRoot du B cap y s') : s = s' :=
  le_antisymm (eulerRoot_saving_le hdu hB le_rfl h h') (eulerRoot_saving_le hdu hB le_rfl h' h)

/-- **The Euler root exists**: for `u'` continuous on `(0, ∞)` with `u'(c) → ∞` as `c → 0⁺`, and a
continuous continuation, at every positive cash. -/
theorem exists_eulerRoot (hduc : ContinuousOn du (Ioi 0)) (hinada : Tendsto du (𝓝[>] 0) atTop)
    (hBc : ContinuousOn B (Icc 0 cap)) (hcap : 0 < cap) {y : ℝ} (hy : 0 < y) :
    ∃ s, IsEulerRoot du B cap y s := by
  -- the corner at zero
  by_cases h0 : B 0 ≤ du y
  · exact ⟨0, le_rfl, hcap.le, hy, fun h => absurd h (lt_irrefl 0), fun _ => by rwa [sub_zero]⟩
  push Not at h0
  -- the corner at the cap
  by_cases hc : cap < y ∧ du (y - cap) ≤ B cap
  · exact ⟨cap, hcap.le, le_rfl, hc.1, fun _ => hc.2, fun h => absurd h (lt_irrefl _)⟩
  -- an interior point where the Euler gap is nonnegative
  have hm : ∃ m, 0 < m ∧ m ≤ cap ∧ m < y ∧ B m ≤ du (y - m) := by
    by_cases hcy : cap < y
    · have : ¬ du (y - cap) ≤ B cap := fun h => hc ⟨hcy, h⟩
      exact ⟨cap, hcap, le_rfl, hcy, (lt_of_not_ge this).le⟩
    · push Not at hcy
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hBc
      have hev := hinada.eventually (eventually_ge_atTop C)
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
      set d := min u y / 2 with hd
      have hd0 : 0 < d := by rw [hd]; exact half_pos (lt_min hu hy)
      have hdu' : d < u := by rw [hd]; linarith [min_le_left u y, lt_min hu hy]
      have hdy : d < y := by rw [hd]; linarith [min_le_right u y, lt_min hu hy]
      refine ⟨y - d, by linarith, by linarith, by linarith, ?_⟩
      have h1 : C ≤ du (y - (y - d)) := by
        rw [sub_sub_cancel]
        exact hsub ⟨hd0, hdu'⟩
      have h2 := hC (y - d) ⟨by linarith, by linarith⟩
      rw [Real.norm_eq_abs] at h2
      linarith [le_abs_self (B (y - d))]
  obtain ⟨m, hm0, hmcap, hmy, hmB⟩ := hm
  -- the intermediate value theorem on `[0, m]`
  have hcont : ContinuousOn (fun s => du (y - s) - B s) (Icc 0 m) := by
    refine ContinuousOn.sub ?_ (hBc.mono fun s hs => ⟨hs.1, hs.2.trans hmcap⟩)
    refine hduc.comp (continuousOn_const.sub continuousOn_id) fun s hs => ?_
    exact mem_Ioi.2 (by linarith [hs.2])
  have hivt := intermediate_value_Icc hm0.le hcont
  have h0mem : (0 : ℝ) ∈ Icc (du (y - 0) - B 0) (du (y - m) - B m) :=
    ⟨by rw [sub_zero]; linarith, by linarith⟩
  obtain ⟨s, hs, hroot⟩ := hivt h0mem
  have hr : du (y - s) - B s = 0 := hroot
  exact ⟨s, hs.1, hs.2.trans hmcap, by linarith [hs.2], fun _ => by linarith, fun _ => by linarith⟩

end Coleman

end KrusellSmith

end LeanEconomics
