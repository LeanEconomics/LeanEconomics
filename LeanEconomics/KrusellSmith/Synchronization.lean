/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.InfiniteHistory

/-!
# Synchronization on infinite histories (Lee's saddle-path theorems)

Milestone LS1 of `LEE_MATCHING_PLAN.md`: the abstract results of Lee (2026 WP), *Dancing on the
Saddles*, Theorems 1 and 2, on infinite histories of shocks.

A family of maps `Γ z z' : X → X` on a metric space moves the aggregate state from a date with
shock `z` to the next, when the new shock is `z'`. An assignment `Φ : History Z → X` is
**consistent** (`Consistent`) if `Φ ω = Γ (ω 1) (ω 0) (Φ (tail ω))` at every history: the state
today is yesterday's, moved by the last shock. `run T ω x` starts at `x`, `T` periods back along
`ω`, and moves forward to today.

`UniformContraction`: every `Γ z z'` maps the set `U` into itself and contracts distances on it
by the factor `c < 1`, and `U` has diameter at most `D` (Lee's Definition 7). Then:

* `Consistent.dist_le_of_agree`: **suffix synchronization** (Lee Thm 2(ii)): a consistent
  assignment with values in `U`, at two histories agreeing over the shocks `ω 0, …, ω T`, gives
  states within `c ^ T * D`;
* `Consistent.dist_run_le`: **the starting state washes out**: the state today is within
  `c ^ T * D` of the state reached from any start in `U`, `T` periods back;
* `Consistent.eq`: **at most one** consistent assignment with values in `U`;
* `exists_consistent`: **existence** (Lee Thm 2(i)), as the backward limit, on a complete space
  with `U` closed and nonempty.

`injOn_orbit_of_strictMono`, `injOn_orbit_of_strictAnti` (Lee Thm 1): a coordinate strictly
monotone along an orbit and converging to its value at the limit indexes the orbit and its limit.
-/

open Set Filter Topology

namespace LeanEconomics

namespace KrusellSmith

namespace History

variable {Z : Type*}

/-- The history `T` periods earlier. -/
def drop (T : ℕ) (ω : History Z) : History Z := fun n => ω (n + T)

@[simp] theorem drop_zero (ω : History Z) : drop 0 ω = ω := rfl

theorem drop_succ (T : ℕ) (ω : History Z) : drop (T + 1) ω = drop T (tail ω) := rfl

end History

section Synchronization

variable {Z X : Type*} [MetricSpace X] (Γ : Z → Z → X → X)

/-- Start at `x`, `T` periods back along `ω`, and move forward to today. -/
def run : ℕ → History Z → X → X
  | 0, _, x => x
  | T + 1, ω, x => Γ (ω 1) (ω 0) (run T (History.tail ω) x)

omit [MetricSpace X] in
theorem run_add (k : ℕ) : ∀ (T : ℕ) (ω : History Z) (x : X),
    run Γ (T + k) ω x = run Γ T ω (run Γ k (History.drop T ω) x)
  | 0, ω, x => by rw [Nat.zero_add]; rfl
  | T + 1, ω, x => by
    rw [Nat.add_right_comm]
    change Γ (ω 1) (ω 0) (run Γ (T + k) (History.tail ω) x)
      = Γ (ω 1) (ω 0) (run Γ T (History.tail ω) (run Γ k (History.drop (T + 1) ω) x))
    rw [run_add k T (History.tail ω) x, History.drop_succ]

/-- **A consistent assignment**: the state today is yesterday's, moved by the last shock. -/
def Consistent (Φ : History Z → X) : Prop :=
  ∀ ω, Φ ω = Γ (ω 1) (ω 0) (Φ (History.tail ω))

variable {Γ}

omit [MetricSpace X] in
theorem consistent_iff_cons {Φ : History Z → X} :
    Consistent Γ Φ ↔ ∀ z' ω, Φ (History.cons z' ω) = Γ (ω 0) z' (Φ ω) := by
  constructor
  · intro h z' ω
    exact h (History.cons z' ω)
  · intro h ω
    have := h (ω 0) (History.tail ω)
    rwa [History.cons_head_tail] at this

omit [MetricSpace X] in
/-- A consistent assignment is today's end of the run from its own value `T` periods back. -/
theorem Consistent.eq_run {Φ : History Z → X} (hΦ : Consistent Γ Φ) :
    ∀ (T : ℕ) (ω : History Z), Φ ω = run Γ T ω (Φ (History.drop T ω))
  | 0, _ => rfl
  | T + 1, ω => by
    rw [hΦ ω, Consistent.eq_run hΦ T (History.tail ω), History.drop_succ]
    rfl

/-- **A uniform contraction** (Lee, Definition 7): the maps send `U` into itself and contract on
it by the factor `c ∈ [0, 1)`, and `U` has diameter at most `D`. -/
structure UniformContraction (Γ : Z → Z → X → X) (U : Set X) (c D : ℝ) : Prop where
  mapsTo : ∀ z z', MapsTo (Γ z z') U U
  dist_le : ∀ z z', ∀ x ∈ U, ∀ y ∈ U, dist (Γ z z' x) (Γ z z' y) ≤ c * dist x y
  rate_nonneg : 0 ≤ c
  rate_lt_one : c < 1
  diam : ∀ x ∈ U, ∀ y ∈ U, dist x y ≤ D

variable {U : Set X} {c D : ℝ}

theorem UniformContraction.run_mem (hΓ : UniformContraction Γ U c D) :
    ∀ (T : ℕ) (ω : History Z) {x : X}, x ∈ U → run Γ T ω x ∈ U
  | 0, _, _, hx => hx
  | T + 1, ω, _, hx => hΓ.mapsTo _ _ (hΓ.run_mem T (History.tail ω) hx)

/-- Two runs over histories agreeing over the shocks `ω 0, …, ω T`, from any starts in `U`, end
within `c ^ T * D`. -/
theorem UniformContraction.dist_run_le (hΓ : UniformContraction Γ U c D) :
    ∀ (T : ℕ) {ω ω' : History Z}, (∀ n ≤ T, ω n = ω' n) → ∀ {x y : X}, x ∈ U → y ∈ U →
      dist (run Γ T ω x) (run Γ T ω' y) ≤ c ^ T * D
  | 0, _, _, _, _, _, hx, hy => by rw [pow_zero, one_mul]; exact hΓ.diam _ hx _ hy
  | T + 1, ω, ω', hag, x, y, hx, hy => by
    have h0 : ω 0 = ω' 0 := hag 0 (Nat.zero_le _)
    have h1 : ω 1 = ω' 1 := hag 1 (by omega)
    have htail : ∀ n ≤ T, History.tail ω n = History.tail ω' n :=
      fun n hn => hag (n + 1) (by omega)
    change dist (Γ (ω 1) (ω 0) (run Γ T (History.tail ω) x))
      (Γ (ω' 1) (ω' 0) (run Γ T (History.tail ω') y)) ≤ _
    rw [h0, h1]
    calc _ ≤ c * dist (run Γ T (History.tail ω) x) (run Γ T (History.tail ω') y) :=
          hΓ.dist_le _ _ _ (hΓ.run_mem T _ hx) _ (hΓ.run_mem T _ hy)
      _ ≤ c * (c ^ T * D) := mul_le_mul_of_nonneg_left (hΓ.dist_run_le T htail hx hy)
          hΓ.rate_nonneg
      _ = c ^ (T + 1) * D := by ring

/-- **Suffix synchronization** (Lee, Theorem 2(ii)): a consistent assignment with values in `U`
gives states within `c ^ T * D` at two histories agreeing over the shocks `ω 0, …, ω T`. -/
theorem Consistent.dist_le_of_agree {Φ : History Z → X} (hΦ : Consistent Γ Φ)
    (hU : ∀ ω, Φ ω ∈ U) (hΓ : UniformContraction Γ U c D) (T : ℕ) {ω ω' : History Z}
    (hag : ∀ n ≤ T, ω n = ω' n) : dist (Φ ω) (Φ ω') ≤ c ^ T * D := by
  rw [hΦ.eq_run T ω, hΦ.eq_run T ω']
  exact hΓ.dist_run_le T hag (hU _) (hU _)

/-- **The starting state washes out** (Lee, Theorem 2(i)): today's state is within `c ^ T * D` of
the state reached from any start in `U`, `T` periods back. -/
theorem Consistent.dist_run_le {Φ : History Z → X} (hΦ : Consistent Γ Φ)
    (hU : ∀ ω, Φ ω ∈ U) (hΓ : UniformContraction Γ U c D) (T : ℕ) (ω : History Z) {x : X}
    (hx : x ∈ U) : dist (Φ ω) (run Γ T ω x) ≤ c ^ T * D := by
  rw [hΦ.eq_run T ω]
  exact hΓ.dist_run_le T (fun _ _ => rfl) (hU _) hx

theorem UniformContraction.tendsto_bound (hΓ : UniformContraction Γ U c D) :
    Tendsto (fun T : ℕ => c ^ T * D) atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hΓ.rate_nonneg hΓ.rate_lt_one).mul_const D
  rwa [zero_mul] at this

/-- **At most one consistent assignment** with values in `U`. -/
theorem Consistent.eq {Φ Ψ : History Z → X} (hΦ : Consistent Γ Φ) (hΨ : Consistent Γ Ψ)
    (hΦU : ∀ ω, Φ ω ∈ U) (hΨU : ∀ ω, Ψ ω ∈ U) (hΓ : UniformContraction Γ U c D) : Φ = Ψ := by
  funext ω
  have hle : ∀ T : ℕ, dist (Φ ω) (Ψ ω) ≤ c ^ T * D := by
    intro T
    rw [hΦ.eq_run T ω, hΨ.eq_run T ω]
    exact hΓ.dist_run_le T (fun _ _ => rfl) (hΦU _) (hΨU _)
  have h0 : dist (Φ ω) (Ψ ω) ≤ 0 :=
    ge_of_tendsto hΓ.tendsto_bound (Eventually.of_forall hle)
  exact dist_le_zero.1 h0

/-- **Existence of the consistent assignment** (Lee, Theorem 2(i)): the backward limit of runs
from any start in `U`. -/
theorem exists_consistent [CompleteSpace X] (hΓ : UniformContraction Γ U c D) (hcl : IsClosed U)
    (hne : U.Nonempty) : ∃ Φ : History Z → X, Consistent Γ Φ ∧ ∀ ω, Φ ω ∈ U := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hcauchy : ∀ ω : History Z, CauchySeq fun T => run Γ T ω x₀ := by
    intro ω
    refine cauchySeq_of_le_geometric c D hΓ.rate_lt_one fun T => ?_
    rw [run_add Γ 1 T ω x₀, mul_comm]
    exact hΓ.dist_run_le T (fun _ _ => rfl) hx₀ (hΓ.run_mem 1 _ hx₀)
  have hlim : ∀ ω : History Z, ∃ L, Tendsto (fun T => run Γ T ω x₀) atTop (𝓝 L) :=
    fun ω => cauchySeq_tendsto_of_complete (hcauchy ω)
  choose L hL using hlim
  have hLU : ∀ ω, L ω ∈ U := fun ω =>
    hcl.mem_of_tendsto (hL ω) (Eventually.of_forall fun T => hΓ.run_mem T ω hx₀)
  refine ⟨L, fun ω => ?_, hLU⟩
  have hshift : Tendsto (fun T => run Γ (T + 1) ω x₀) atTop (𝓝 (L ω)) :=
    (hL ω).comp (tendsto_add_atTop_nat 1)
  have hmove : Tendsto (fun T => run Γ (T + 1) ω x₀) atTop
      (𝓝 (Γ (ω 1) (ω 0) (L (History.tail ω)))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hd := (tendsto_iff_dist_tendsto_zero.1 (hL (History.tail ω))).const_mul c
    rw [mul_zero] at hd
    refine squeeze_zero (fun _ => dist_nonneg) (fun T => ?_) hd
    exact hΓ.dist_le _ _ _ (hΓ.run_mem T _ hx₀) _ (hLU _)
  exact tendsto_nhds_unique hshift hmove

end Synchronization

/-! ### A monotone coordinate indexes an orbit (Lee, Theorem 1) -/

section Coordinate

variable {Y : Type*} {Φ : ℕ → Y} {Φcs : Y} {e : Y → ℝ}

/-- **A strictly increasing coordinate indexes the orbit and its limit.** -/
theorem injOn_orbit_of_strictMono (hmono : StrictMono (e ∘ Φ))
    (hlim : Tendsto (e ∘ Φ) atTop (𝓝 (e Φcs))) : InjOn e (range Φ ∪ {Φcs}) := by
  have hlt : ∀ t, e (Φ t) < e Φcs := fun t =>
    (hmono (Nat.lt_succ_self t)).trans_le (hmono.monotone.ge_of_tendsto hlim (t + 1))
  rintro x (⟨s, rfl⟩ | hx) y (⟨t, rfl⟩ | hy) hxy
  · rw [hmono.injective hxy]
  · rw [mem_singleton_iff] at hy
    subst hy
    exact absurd hxy (hlt s).ne
  · rw [mem_singleton_iff] at hx
    subst hx
    exact absurd hxy.symm (hlt t).ne
  · rw [mem_singleton_iff] at hx hy
    rw [hx, hy]

/-- **A strictly decreasing coordinate indexes the orbit and its limit.** -/
theorem injOn_orbit_of_strictAnti (hanti : StrictAnti (e ∘ Φ))
    (hlim : Tendsto (e ∘ Φ) atTop (𝓝 (e Φcs))) : InjOn e (range Φ ∪ {Φcs}) := by
  have hgt : ∀ t, e Φcs < e (Φ t) := fun t =>
    (hanti.antitone.le_of_tendsto hlim (t + 1)).trans_lt (hanti (Nat.lt_succ_self t))
  rintro x (⟨s, rfl⟩ | hx) y (⟨t, rfl⟩ | hy) hxy
  · rw [hanti.injective hxy]
  · rw [mem_singleton_iff] at hy
    subst hy
    exact absurd hxy (hgt s).ne'
  · rw [mem_singleton_iff] at hx
    subst hx
    exact absurd hxy.symm (hgt t).ne'
  · rw [mem_singleton_iff] at hx hy
    rw [hx, hy]

end Coordinate

end KrusellSmith

end LeanEconomics
