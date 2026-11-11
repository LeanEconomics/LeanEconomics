/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.HomotheticCRRA
import Mathlib.Order.FixedPoints
import Mathlib.Topology.Order.IntermediateValue

/-!
# Existence of the saving-rate function of the homothetic CRRA economy

`HomotheticCRRA.lean` reduces the homothetic economy with CRRA utility to the **rate equation**

    ℓ(s(z, K)) = Σ_{z'} μ(z, z') g(z', K')^{1−γ} (1 − s(z', K'))^{−γ},   K' = s(z, K) g(z, K) K,

with `ℓ(s) = (1 − s)^{−γ} s^γ` and `μ = β π m`. Here it is solved for `0 < γ < 1`, on an interval
`[lo, hi]` of capital levels, by a Coleman-type monotone operator on saving rates.

**Data** (`RateData`): `g` positive, continuous and nonincreasing in capital on `[lo, hi]`,
resources `g K` nondecreasing, and bounds `0 < s̲ ≤ s̄ < 1` on the rate that are self-confirming
(`low`, `high`) and keep capital in the interval (`inv_lo`, `inv_hi`).

**The lattice** (`Pol`): rates `s(z, K) ∈ [s̲, s̄]`, nonincreasing in capital, with saving
`s g K` nondecreasing in capital. Members are continuous (`continuous_pol`), and infima are
pointwise, so `Pol` is a complete lattice.

**The operator** (`T`). Against `s`, the right-hand side `Φ` is nonincreasing in next period's
capital (`Phi_anti`: with `γ < 1` a higher `K'` lowers `g^{1−γ}` and lowers next period's rate), so
the equation `ℓ(σ) = Φ(σ g K)` has exactly one root `σ ∈ [s̲, s̄]` (`exists_root`, `root_compare`).
The root is nonincreasing in capital, saving is nondecreasing, and the root rises with `s`.

**`exists_rate`**: Tarski gives a fixed point, a solution of the rate equation on `[lo, hi]`.
**`HomotheticEconomy.exists_isRateFunction`** and
**`HomotheticEconomy.exists_recursiveEquilibriumCRRA`**: so the homothetic CRRA economy has a
sequential equilibrium recursive on `(z, K)`, with uninsured idiosyncratic risk.
-/

open Set Filter Topology

namespace LeanEconomics

namespace KrusellSmith

/-- A function whose increments are dominated by those of a continuous function is continuous. -/
theorem continuous_of_abs_sub_le {X : Type*} [TopologicalSpace X] {f y : X → ℝ} {C : ℝ}
    (hy : Continuous y) (h : ∀ a b, |f a - f b| ≤ C * |y a - y b|) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun b => ?_
  have h0 : Tendsto (fun a => C * |y a - y b|) (𝓝 b) (𝓝 0) := by
    have := ((hy.tendsto b).sub_const (y b)).abs.const_mul C
    simpa using this
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun a => dist_nonneg) (fun a => ?_) h0)
  rw [Real.dist_eq]
  exact h a b

/-- The data of the rate equation. -/
structure RateData (Z : Type*) [Fintype Z] where
  μ : Z → Z → ℝ
  μ_nonneg : ∀ z z', 0 ≤ μ z z'
  γ : ℝ
  γ_pos : 0 < γ
  γ_lt : γ < 1
  lo : ℝ
  hi : ℝ
  lo_pos : 0 < lo
  lo_le : lo ≤ hi
  g : Z → ℝ → ℝ
  g_pos : ∀ z, ∀ k ∈ Icc lo hi, 0 < g z k
  g_anti : ∀ z, AntitoneOn (g z) (Icc lo hi)
  g_cont : ∀ z, ContinuousOn (g z) (Icc lo hi)
  y_mono : ∀ z, MonotoneOn (fun k => g z k * k) (Icc lo hi)
  sl : ℝ
  su : ℝ
  sl_pos : 0 < sl
  sl_le : sl ≤ su
  su_lt : su < 1
  low : ∀ z, sl ^ γ ≤ ∑ z', μ z z' * g z' hi ^ (1 - γ)
  high : ∀ z, ∑ z', μ z z' * g z' lo ^ (1 - γ) ≤ su ^ γ
  inv_lo : ∀ z, lo ≤ sl * (g z lo * lo)
  inv_hi : ∀ z, su * (g z hi * hi) ≤ hi

namespace RateData

variable {Z : Type*} [Fintype Z] (D : RateData Z)

/-- Capital levels. -/
abbrev Box := ↥(Icc D.lo D.hi)

/-- Resources. -/
def y (z : Z) (k : ℝ) : ℝ := D.g z k * k

theorem lo_mem : D.lo ∈ Icc D.lo D.hi := ⟨le_rfl, D.lo_le⟩

theorem hi_mem : D.hi ∈ Icc D.lo D.hi := ⟨D.lo_le, le_rfl⟩

theorem y_pos (z : Z) {k : ℝ} (hk : k ∈ Icc D.lo D.hi) : 0 < D.y z k :=
  mul_pos (D.g_pos z k hk) (D.lo_pos.trans_le hk.1)

theorem y_le (z : Z) {a b : ℝ} (ha : a ∈ Icc D.lo D.hi) (hb : b ∈ Icc D.lo D.hi) (hab : a ≤ b) :
    D.y z a ≤ D.y z b := D.y_mono z ha hb hab

/-- Saving at a rate in `[s̲, s̄]` keeps capital in the interval. -/
theorem saving_mem (z : Z) {k : ℝ} (hk : k ∈ Icc D.lo D.hi) {σ : ℝ} (hσ : σ ∈ Icc D.sl D.su) :
    σ * D.y z k ∈ Icc D.lo D.hi := by
  have h1 := D.y_le z D.lo_mem hk hk.1
  have h2 := D.y_le z hk D.hi_mem hk.2
  have h3 := D.y_pos z D.lo_mem
  have h4 := D.y_pos z hk
  constructor
  · calc D.lo ≤ D.sl * D.y z D.lo := D.inv_lo z
      _ ≤ σ * D.y z k := mul_le_mul hσ.1 h1 h3.le (D.sl_pos.le.trans hσ.1)
  · calc σ * D.y z k ≤ D.su * D.y z D.hi :=
          mul_le_mul hσ.2 h2 h4.le (D.sl_pos.le.trans D.sl_le)
      _ ≤ D.hi := D.inv_hi z

/-- The left-hand side of the rate equation. -/
noncomputable def ell (σ : ℝ) : ℝ := (1 - σ) ^ (-D.γ) * σ ^ D.γ

theorem ell_strictMonoOn : StrictMonoOn D.ell (Icc D.sl D.su) := by
  intro a ha b hb hab
  have ha0 : 0 < a := D.sl_pos.trans_le ha.1
  have hb1 : 0 < 1 - b := by linarith [hb.2, D.su_lt]
  have h1 : (1 - a) ^ (-D.γ) < (1 - b) ^ (-D.γ) :=
    Real.rpow_lt_rpow_of_neg hb1 (by linarith) (by linarith [D.γ_pos])
  have h2 : a ^ D.γ < b ^ D.γ := Real.rpow_lt_rpow ha0.le hab D.γ_pos
  exact mul_lt_mul'' h1 h2 (Real.rpow_nonneg (by linarith [ha.2, D.su_lt]) _)
    (Real.rpow_nonneg ha0.le _)

theorem continuousOn_ell : ContinuousOn D.ell (Icc D.sl D.su) := by
  refine ContinuousOn.mul ((continuousOn_const.sub continuousOn_id).rpow_const fun x hx =>
    Or.inl (ne_of_gt (show (0 : ℝ) < 1 - x by linarith [hx.2, D.su_lt])))
    (continuousOn_id.rpow_const fun x _ => Or.inr D.γ_pos.le)

/-- **The policy constraints**: rates in `[s̲, s̄]`, nonincreasing in capital, with saving
nondecreasing in capital. -/
def InC (s : Z → D.Box → ℝ) : Prop :=
  (∀ z k, s z k ∈ Icc D.sl D.su) ∧ (∀ z (a b : D.Box), (a : ℝ) ≤ b → s z b ≤ s z a) ∧
    (∀ z (a b : D.Box), (a : ℝ) ≤ b → s z a * D.y z a ≤ s z b * D.y z b)

/-- **The lattice of rate policies.** -/
def Pol := {s : Z → D.Box → ℝ // D.InC s}

instance : PartialOrder D.Pol := Subtype.partialOrder _

/-- The highest rate is a policy (the top). -/
theorem inC_top : D.InC fun _ _ => D.su :=
  ⟨fun _ _ => ⟨D.sl_le, le_rfl⟩, fun _ _ _ _ => le_rfl, fun z a b hab =>
    mul_le_mul_of_nonneg_left (D.y_le z a.2 b.2 hab) (D.sl_pos.le.trans D.sl_le)⟩

open Classical in
/-- Pointwise infima (the highest rate for the empty set). -/
noncomputable instance : InfSet D.Pol where
  sInf S := if hS : S.Nonempty then
      ⟨fun z k => sInf ((fun c : D.Pol => c.1 z k) '' S), by
        have hb : ∀ z k, BddBelow ((fun c : D.Pol => c.1 z k) '' S) := fun z k =>
          ⟨D.sl, by rintro _ ⟨c, -, rfl⟩; exact (c.2.1 z k).1⟩
        have hne : ∀ z k, ((fun c : D.Pol => c.1 z k) '' S).Nonempty := fun z k => hS.image _
        obtain ⟨c₀, hc₀⟩ := hS
        refine ⟨fun z k => ⟨le_csInf (hne z k) ?_, ?_⟩, fun z a b hab => ?_,
          fun z a b hab => ?_⟩
        · rintro _ ⟨c, -, rfl⟩; exact (c.2.1 z k).1
        · exact (csInf_le (hb z k) ⟨c₀, hc₀, rfl⟩).trans (c₀.2.1 z k).2
        · refine le_csInf (hne z a) ?_
          rintro _ ⟨c, hc, rfl⟩
          exact (csInf_le (hb z b) ⟨c, hc, rfl⟩).trans (c.2.2.1 z a b hab)
        · have hyb := D.y_pos z b.2
          have hya := D.y_pos z a.2
          have : sInf ((fun c : D.Pol => c.1 z a) '' S) * D.y z a / D.y z b
              ≤ sInf ((fun c : D.Pol => c.1 z b) '' S) := by
            refine le_csInf (hne z b) ?_
            rintro _ ⟨c, hc, rfl⟩
            have h1 := csInf_le (hb z a) ⟨c, hc, rfl⟩
            have h2 := c.2.2.2 z a b hab
            rw [div_le_iff₀ hyb]
            simp only at h1 ⊢
            nlinarith
          rwa [div_le_iff₀ hyb] at this⟩
    else ⟨fun _ _ => D.su, D.inC_top⟩

open Classical in
theorem isGLB_sInf (S : Set D.Pol) : IsGLB S (sInf S) := by
  by_cases hS : S.Nonempty
  · have hval : ∀ z k, (sInf S : D.Pol).1 z k = sInf ((fun c : D.Pol => c.1 z k) '' S) :=
      fun z k => by
        change (if hS : S.Nonempty then _ else _ : D.Pol).1 z k = _
        simp only [hS, ↓reduceDIte]
    have hb : ∀ z k, BddBelow ((fun c : D.Pol => c.1 z k) '' S) := fun z k =>
      ⟨D.sl, by rintro _ ⟨c, -, rfl⟩; exact (c.2.1 z k).1⟩
    refine ⟨fun c hc z k => ?_, fun d hd z k => ?_⟩
    · rw [hval]
      exact csInf_le (hb z k) ⟨c, hc, rfl⟩
    · change d.1 z k ≤ (sInf S : D.Pol).1 z k
      rw [hval]
      refine le_csInf (hS.image _) ?_
      rintro _ ⟨c, hc, rfl⟩
      exact hd hc z k
  · have hval : (sInf S : D.Pol).1 = fun _ (_ : D.Box) => D.su := by
      change (if hS : S.Nonempty then _ else _ : D.Pol).1 = _
      simp only [hS, ↓reduceDIte]
    refine ⟨fun c hc => absurd ⟨c, hc⟩ hS, fun d _ z k => ?_⟩
    change d.1 z k ≤ (sInf S : D.Pol).1 z k
    rw [hval]
    exact (d.2.1 z k).2

noncomputable instance : CompleteLattice D.Pol := completeLatticeOfInf _ D.isGLB_sInf

/-- **Policies are continuous**: the two monotonicities bound the increments of the rate by those
of resources. -/
theorem continuous_pol (s : D.Pol) (z : Z) : Continuous (s.1 z) := by
  have hc : 0 < D.y z D.lo := D.y_pos z D.lo_mem
  have hycont : Continuous fun k : D.Box => D.y z k :=
    (continuousOn_iff_continuous_domRestrict.1 (D.g_cont z)).mul continuous_subtype_val
  have key : ∀ a b : D.Box, (a : ℝ) ≤ b → s.1 z a - s.1 z b ≤ (D.y z b - D.y z a) / D.y z D.lo := by
    intro a b hab
    have h1 := s.2.2.1 z a b hab
    have h2 := s.2.2.2 z a b hab
    have h3 := D.y_le z a.2 b.2 hab
    have h4 := D.y_le z D.lo_mem a.2 a.2.1
    have h5 : s.1 z b ≤ 1 := (s.2.1 z b).2.trans D.su_lt.le
    rw [le_div_iff₀ hc]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h4),
      mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 h3)]
  refine continuous_of_abs_sub_le (C := 1 / D.y z D.lo) hycont fun a b => ?_
  rw [one_div, inv_mul_eq_div]
  rcases le_total (a : ℝ) b with hab | hba
  · have h1 := s.2.2.1 z a b hab
    have h3 := D.y_le z a.2 b.2 hab
    rw [abs_of_nonneg (sub_nonneg.2 h1), abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h3)]
    exact key a b hab
  · have h1 := s.2.2.1 z b a hba
    have h3 := D.y_le z b.2 a.2 hba
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (sub_nonneg.2 h3)]
    exact key b a hba

/-- A policy extended to all capital levels through the clamp. -/
noncomputable def ext (s : D.Pol) (z : Z) (x : ℝ) : ℝ := s.1 z (projIcc D.lo D.hi D.lo_le x)

theorem ext_of_mem (s : D.Pol) (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) :
    D.ext s z x = s.1 z ⟨x, hx⟩ := by
  rw [ext, projIcc_of_mem _ hx]

theorem ext_mem (s : D.Pol) (z : Z) (x : ℝ) : D.ext s z x ∈ Icc D.sl D.su := s.2.1 z _

theorem continuous_ext (s : D.Pol) (z : Z) : Continuous (D.ext s z) :=
  (D.continuous_pol s z).comp continuous_projIcc

theorem ext_anti (s : D.Pol) (z : Z) {a b : ℝ} (ha : a ∈ Icc D.lo D.hi) (hb : b ∈ Icc D.lo D.hi)
    (hab : a ≤ b) : D.ext s z b ≤ D.ext s z a := by
  rw [D.ext_of_mem s z ha, D.ext_of_mem s z hb]
  exact s.2.2.1 z ⟨a, ha⟩ ⟨b, hb⟩ hab

/-- The right-hand side of the rate equation at next period's capital `x`. -/
noncomputable def Phi (s : D.Pol) (z : Z) (x : ℝ) : ℝ :=
  ∑ z', D.μ z z' * D.g z' x ^ (1 - D.γ) * (1 - D.ext s z' x) ^ (-D.γ)

theorem one_sub_ext_pos (s : D.Pol) (z : Z) (x : ℝ) : 0 < 1 - D.ext s z x := by
  linarith [(D.ext_mem s z x).2, D.su_lt]

/-- **`Φ` is nonincreasing in next period's capital.** -/
theorem Phi_anti (s : D.Pol) (z : Z) {a b : ℝ} (ha : a ∈ Icc D.lo D.hi)
    (hb : b ∈ Icc D.lo D.hi) (hab : a ≤ b) : D.Phi s z b ≤ D.Phi s z a := by
  refine Finset.sum_le_sum fun z' _ => ?_
  have h1 : D.g z' b ^ (1 - D.γ) ≤ D.g z' a ^ (1 - D.γ) :=
    Real.rpow_le_rpow (D.g_pos z' b hb).le (D.g_anti z' ha hb hab) (by linarith [D.γ_lt])
  have h2 : (1 - D.ext s z' b) ^ (-D.γ) ≤ (1 - D.ext s z' a) ^ (-D.γ) :=
    Real.rpow_le_rpow_of_nonpos (D.one_sub_ext_pos s z' a)
      (by linarith [D.ext_anti s z' ha hb hab]) (by linarith [D.γ_pos])
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (D.μ_nonneg z z')) h2
    (Real.rpow_nonneg (D.one_sub_ext_pos s z' b).le _)
    (mul_nonneg (D.μ_nonneg z z') (Real.rpow_nonneg (D.g_pos z' a ha).le _))

/-- `Φ` rises with the policy. -/
theorem Phi_mono {s t : D.Pol} (hst : s ≤ t) (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) :
    D.Phi s z x ≤ D.Phi t z x := by
  refine Finset.sum_le_sum fun z' _ => ?_
  have h2 : (1 - D.ext s z' x) ^ (-D.γ) ≤ (1 - D.ext t z' x) ^ (-D.γ) :=
    Real.rpow_le_rpow_of_nonpos (D.one_sub_ext_pos t z' x)
      (by have := hst z' (projIcc D.lo D.hi D.lo_le x); simp only [ext]; linarith)
      (by linarith [D.γ_pos])
  exact mul_le_mul_of_nonneg_left h2
    (mul_nonneg (D.μ_nonneg z z') (Real.rpow_nonneg (D.g_pos z' x hx).le _))

theorem ell_sl_le_Phi (s : D.Pol) (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) :
    D.ell D.sl ≤ D.Phi s z x := by
  have hpos : 0 ≤ (1 - D.sl) ^ (-D.γ) :=
    Real.rpow_nonneg (by linarith [D.sl_le, D.su_lt]) _
  calc D.ell D.sl ≤ (1 - D.sl) ^ (-D.γ) * ∑ z', D.μ z z' * D.g z' D.hi ^ (1 - D.γ) :=
        mul_le_mul_of_nonneg_left (D.low z) hpos
    _ = ∑ z', D.μ z z' * D.g z' D.hi ^ (1 - D.γ) * (1 - D.sl) ^ (-D.γ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z' _ => by ring
    _ ≤ D.Phi s z x := by
        refine Finset.sum_le_sum fun z' _ => ?_
        have h1 : D.g z' D.hi ^ (1 - D.γ) ≤ D.g z' x ^ (1 - D.γ) :=
          Real.rpow_le_rpow (D.g_pos z' _ D.hi_mem).le (D.g_anti z' hx D.hi_mem hx.2)
            (by linarith [D.γ_lt])
        have h2 : (1 - D.sl) ^ (-D.γ) ≤ (1 - D.ext s z' x) ^ (-D.γ) :=
          Real.rpow_le_rpow_of_nonpos (D.one_sub_ext_pos s z' x)
            (by linarith [(D.ext_mem s z' x).1]) (by linarith [D.γ_pos])
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (D.μ_nonneg z z')) h2 hpos
          (mul_nonneg (D.μ_nonneg z z') (Real.rpow_nonneg (D.g_pos z' x hx).le _))

theorem Phi_le_ell_su (s : D.Pol) (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) :
    D.Phi s z x ≤ D.ell D.su := by
  have h1su : 0 < 1 - D.su := by linarith [D.su_lt]
  have hpos : 0 ≤ (1 - D.su) ^ (-D.γ) := Real.rpow_nonneg h1su.le _
  calc D.Phi s z x ≤ ∑ z', D.μ z z' * D.g z' D.lo ^ (1 - D.γ) * (1 - D.su) ^ (-D.γ) := by
        refine Finset.sum_le_sum fun z' _ => ?_
        have h1 : D.g z' x ^ (1 - D.γ) ≤ D.g z' D.lo ^ (1 - D.γ) :=
          Real.rpow_le_rpow (D.g_pos z' x hx).le (D.g_anti z' D.lo_mem hx hx.1)
            (by linarith [D.γ_lt])
        have h2 : (1 - D.ext s z' x) ^ (-D.γ) ≤ (1 - D.su) ^ (-D.γ) :=
          Real.rpow_le_rpow_of_nonpos h1su (by linarith [(D.ext_mem s z' x).2])
            (by linarith [D.γ_pos])
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (D.μ_nonneg z z')) h2
          (Real.rpow_nonneg (D.one_sub_ext_pos s z' x).le _)
          (mul_nonneg (D.μ_nonneg z z') (Real.rpow_nonneg (D.g_pos z' _ D.lo_mem).le _))
    _ = (1 - D.su) ^ (-D.γ) * ∑ z', D.μ z z' * D.g z' D.lo ^ (1 - D.γ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z' _ => by ring
    _ ≤ D.ell D.su := mul_le_mul_of_nonneg_left (D.high z) hpos

theorem continuousOn_Phi (s : D.Pol) (z : Z) {k : ℝ} (hk : k ∈ Icc D.lo D.hi) :
    ContinuousOn (fun σ => D.Phi s z (σ * D.y z k)) (Icc D.sl D.su) := by
  have hmaps : MapsTo (fun σ : ℝ => σ * D.y z k) (Icc D.sl D.su) (Icc D.lo D.hi) :=
    fun σ hσ => D.saving_mem z hk hσ
  have hlin : ContinuousOn (fun σ : ℝ => σ * D.y z k) (Icc D.sl D.su) :=
    (continuous_id.mul continuous_const).continuousOn
  refine continuousOn_finsetSum _ fun z' _ => ContinuousOn.mul (ContinuousOn.mul
    continuousOn_const (((D.g_cont z').comp hlin hmaps).rpow_const fun σ _ =>
      Or.inr (by linarith [D.γ_lt]))) ?_
  refine ContinuousOn.rpow_const ((continuous_const.sub ((D.continuous_ext s z').comp
    (continuous_id.mul continuous_const))).continuousOn) fun σ _ =>
      Or.inl (D.one_sub_ext_pos s z' _).ne'

/-- **The rate equation has a root** in `[s̲, s̄]`, against every policy. -/
theorem exists_root (s : D.Pol) (z : Z) (k : D.Box) :
    ∃ σ ∈ Icc D.sl D.su, D.ell σ = D.Phi s z (σ * D.y z k) := by
  have hcont : ContinuousOn (fun σ => D.ell σ - D.Phi s z (σ * D.y z k)) (Icc D.sl D.su) :=
    D.continuousOn_ell.sub (D.continuousOn_Phi s z k.2)
  have h0 : (0 : ℝ) ∈ Icc (D.ell D.sl - D.Phi s z (D.sl * D.y z k))
      (D.ell D.su - D.Phi s z (D.su * D.y z k)) :=
    ⟨sub_nonpos.2 (D.ell_sl_le_Phi s z (D.saving_mem z k.2 ⟨le_rfl, D.sl_le⟩)),
      sub_nonneg.2 (D.Phi_le_ell_su s z (D.saving_mem z k.2 ⟨D.sl_le, le_rfl⟩))⟩
  obtain ⟨σ, hσ, hσ0⟩ := intermediate_value_Icc D.sl_le hcont h0
  exact ⟨σ, hσ, sub_eq_zero.1 hσ0⟩

/-- The root of the rate equation against `s` at `(z, k)`. -/
noncomputable def root (s : D.Pol) (z : Z) (k : D.Box) : ℝ := (D.exists_root s z k).choose

theorem root_mem (s : D.Pol) (z : Z) (k : D.Box) : D.root s z k ∈ Icc D.sl D.su :=
  (D.exists_root s z k).choose_spec.1

theorem root_spec (s : D.Pol) (z : Z) (k : D.Box) :
    D.ell (D.root s z k) = D.Phi s z (D.root s z k * D.y z k) :=
  (D.exists_root s z k).choose_spec.2

/-- **Comparison of roots**: more capital, or a lower policy, lowers the root. -/
theorem root_compare {s t : D.Pol} (hst : s ≤ t) (z : Z) {a b : D.Box} (hab : (a : ℝ) ≤ b) :
    D.root s z b ≤ D.root t z a := by
  by_contra hlt
  push Not at hlt
  have ha := D.root_mem t z a
  have hb := D.root_mem s z b
  have hya := D.y_pos z a.2
  have hyab := D.y_le z a.2 b.2 hab
  have hle : D.root t z a * D.y z a ≤ D.root s z b * D.y z b :=
    mul_le_mul hlt.le hyab hya.le (D.sl_pos.le.trans hb.1)
  have h1 := D.Phi_anti s z (D.saving_mem z a.2 ha) (D.saving_mem z b.2 hb) hle
  have h2 := D.Phi_mono hst z (D.saving_mem z a.2 ha)
  have h3 := D.ell_strictMonoOn ha hb hlt
  rw [D.root_spec t z a, D.root_spec s z b] at h3
  linarith

/-- **Saving at the root is nondecreasing in capital.** -/
theorem root_saving_le (s : D.Pol) (z : Z) {a b : D.Box} (hab : (a : ℝ) ≤ b) :
    D.root s z a * D.y z a ≤ D.root s z b * D.y z b := by
  by_contra hlt
  push Not at hlt
  have ha := D.root_mem s z a
  have hb := D.root_mem s z b
  have hya := D.y_pos z a.2
  have hyab := D.y_le z a.2 b.2 hab
  have h1 := D.Phi_anti s z (D.saving_mem z b.2 hb) (D.saving_mem z a.2 ha) hlt.le
  rw [← D.root_spec s z a, ← D.root_spec s z b] at h1
  have h2 : D.root s z a ≤ D.root s z b := by
    by_contra h
    push Not at h
    exact absurd (D.ell_strictMonoOn hb ha h) (not_lt.2 h1)
  have h3 : D.root s z a * D.y z a ≤ D.root s z b * D.y z b :=
    mul_le_mul h2 hyab hya.le (D.sl_pos.le.trans hb.1)
  linarith

/-- **The operator**: the root of the rate equation against the policy. -/
noncomputable def T : D.Pol →o D.Pol where
  toFun s := ⟨fun z k => D.root s z k, fun z k => D.root_mem s z k,
    fun z _ _ hab => D.root_compare le_rfl z hab, fun z _ _ hab => D.root_saving_le s z hab⟩
  monotone' _ _ hst z _ := D.root_compare hst z le_rfl

/-- **The rate equation has a solution** on `[lo, hi]`. -/
theorem exists_rate : ∃ s : D.Pol, ∀ (z : Z) (k : D.Box),
    D.ell (s.1 z k) = D.Phi s z (s.1 z k * D.y z k) := by
  refine ⟨OrderHom.gfp D.T, fun z k => ?_⟩
  have hfix : D.T (OrderHom.gfp D.T) = OrderHom.gfp D.T := OrderHom.map_gfp D.T
  have hval : (OrderHom.gfp D.T).1 z k = D.root (OrderHom.gfp D.T) z k := by
    conv_lhs => rw [← hfix]
    rfl
  rw [hval]
  exact D.root_spec _ z k

end RateData

/-! ### The homothetic CRRA economy -/

namespace HomotheticEconomy

variable {Z E : Type*} [Fintype Z] [Fintype E] (M : HomotheticEconomy Z E)

/-- **A saving-rate function exists**: `0 < γ < 1`, resources per unit of capital positive,
continuous and nonincreasing on `[lo, hi]`, total resources nondecreasing, and bounds
`0 < s̲ ≤ s̄ < 1` on the rate that confirm themselves and keep capital in `[lo, hi]`. -/
theorem exists_isRateFunction {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {m : Z → Z → ℝ}
    (hm0 : ∀ z z', 0 ≤ m z z')
    (hm : ∀ z z' e, ∑ e', M.idioProb z z' e e' * M.shock e' ^ (1 - γ) = m z z')
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hganti : ∀ z, AntitoneOn (M.resources z) (Icc lo hi))
    (hgcont : ∀ z, ContinuousOn (M.resources z) (Icc lo hi))
    (hymono : ∀ z, MonotoneOn (fun k => M.resources z k * k) (Icc lo hi))
    {sl su : ℝ} (hsl : 0 < sl) (hslsu : sl ≤ su) (hsu : su < 1)
    (hlow : ∀ z, sl ^ γ
      ≤ ∑ z', M.discount * M.aggProb z z' * m z z' * M.resources z' hi ^ (1 - γ))
    (hhigh : ∀ z, ∑ z', M.discount * M.aggProb z z' * m z z' * M.resources z' lo ^ (1 - γ)
      ≤ su ^ γ)
    (hinvlo : ∀ z, lo ≤ sl * (M.resources z lo * lo))
    (hinvhi : ∀ z, su * (M.resources z hi * hi) ≤ hi) :
    ∃ σ : Z → ℝ → ℝ, M.IsRateFunction γ m (Icc lo hi) σ su := by
  let D : RateData Z :=
    { μ := fun z z' => M.discount * M.aggProb z z' * m z z'
      μ_nonneg := fun z z' =>
        mul_nonneg (mul_nonneg M.discount_pos.le (M.aggProb_nonneg z z')) (hm0 z z')
      γ := γ
      γ_pos := hγ0
      γ_lt := hγ1
      lo := lo
      hi := hi
      lo_pos := hlo
      lo_le := hlohi
      g := M.resources
      g_pos := fun z k hk => M.resources_pos z k (hlo.trans_le hk.1)
      g_anti := hganti
      g_cont := hgcont
      y_mono := hymono
      sl := sl
      su := su
      sl_pos := hsl
      sl_le := hslsu
      su_lt := hsu
      low := hlow
      high := hhigh
      inv_lo := hinvlo
      inv_hi := hinvhi }
  obtain ⟨s, hs⟩ := D.exists_rate
  refine ⟨fun z k => D.ext s z k, ?_⟩
  have hsav : ∀ z, ∀ k ∈ Icc lo hi, D.ext s z k * M.resources z k * k ∈ Icc lo hi := by
    intro z k hk
    rw [mul_assoc]
    exact D.saving_mem z hk (D.ext_mem s z k)
  refine ⟨fun k hk => hlo.trans_le hk.1, fun z k _ => hsl.trans_le (D.ext_mem s z k).1,
    fun z k _ => (D.ext_mem s z k).2, hsu, hsav, hm, fun z k hk => ?_⟩
  have h := hs z ⟨k, hk⟩
  rw [← D.ext_of_mem s z hk] at h
  have hx : D.ext s z k * M.resources z k * k = D.ext s z k * D.y z k := mul_assoc _ _ _
  rw [hx]
  change _ = D.ell (D.ext s z k)
  rw [h, RateData.Phi, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z' _ => by ring

/-- **The homothetic CRRA economy has a sequential equilibrium recursive on `(z, K)`**, with
uninsured idiosyncratic risk, from every initial shock and every initial distribution of positive
wealth levels with mean in `[lo, hi]`. -/
theorem exists_recursiveEquilibriumCRRA {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {m : Z → Z → ℝ}
    (hm0 : ∀ z z', 0 ≤ m z z')
    (hm : ∀ z z' e, ∑ e', M.idioProb z z' e e' * M.shock e' ^ (1 - γ) = m z z')
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hganti : ∀ z, AntitoneOn (M.resources z) (Icc lo hi))
    (hgcont : ∀ z, ContinuousOn (M.resources z) (Icc lo hi))
    (hymono : ∀ z, MonotoneOn (fun k => M.resources z k * k) (Icc lo hi))
    {sl su : ℝ} (hsl : 0 < sl) (hslsu : sl ≤ su) (hsu : su < 1)
    (hlow : ∀ z, sl ^ γ
      ≤ ∑ z', M.discount * M.aggProb z z' * m z z' * M.resources z' hi ^ (1 - γ))
    (hhigh : ∀ z, ∑ z', M.discount * M.aggProb z z' * m z z' * M.resources z' lo ^ (1 - γ)
      ≤ su ^ γ)
    (hinvlo : ∀ z, lo ≤ sl * (M.resources z lo * lo))
    (hinvhi : ∀ z, su * (M.resources z hi * hi) ≤ hi) :
    ∃ σ : Z → ℝ → ℝ, ∀ {ι : Type} [Fintype ι] (z₀ : Z) (ν w : ι → ℝ) (t : ι → E),
      (∀ i, 0 < w i) → ∑ i, ν i * w i ∈ Icc lo hi →
        M.IsSequentialEquilibriumCRRA γ z₀ ν w t (M.ratePath σ z₀ (∑ i, ν i * w i)) := by
  obtain ⟨σ, F⟩ := M.exists_isRateFunction hγ0 hγ1 hm0 hm hlo hlohi hganti hgcont hymono hsl
    hslsu hsu hlow hhigh hinvlo hinvhi
  exact ⟨σ, fun z₀ ν w t hw hk => F.isSequentialEquilibriumCRRA_ratePath z₀ hγ0 ν w t hw hk⟩

end HomotheticEconomy

end KrusellSmith

end LeanEconomics
