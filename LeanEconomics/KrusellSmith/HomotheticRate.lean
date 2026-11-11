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

    (1 − s)^{−γ} s^γ = Σ_{z'} μ(z, z') g(z', K')^{1−γ} (1 − s(z', K'))^{−γ},   K' = s g(z, K) K,

with `μ = β π m`. Here it is solved for **every `γ > 0`**, on an interval `[lo, hi]` of capital
levels, by a Coleman operator on consumption levels. In levels, with resources `y = g K` and
consumption `c = (1 − s) y`, the equation is the Euler equation

    c(z, K)^{−γ} = Σ_{z'} μ(z, z') g(z', K') c(z', K')^{−γ},   K' = y(z, K) − c(z, K),

whose right-hand side is nonincreasing in `K'` whenever consumption is nondecreasing in capital,
for every `γ`. (In rates the right-hand side is monotone in `K'` only for `γ < 1`.)

**Data** (`RateData`): `g` positive, continuous and nonincreasing in capital on `[lo, hi]`,
resources `g K` nondecreasing, and bounds `0 < s̲ ≤ s̄ < 1` on the saving rate that confirm
themselves (`low`, `high`) and keep capital in the interval (`inv_lo`, `inv_hi`).

**The lattice** (`Pol`): consumption with `(1 − s̄) y ≤ c ≤ (1 − s̲) y`, consumption and saving
`y − c` both nondecreasing in capital. Members are continuous (`continuous_pol`), infima are
pointwise, so `Pol` is a complete lattice.

**The operator** (`T`). Against `c`, the Euler equation at `(z, K)` has exactly one saving rate
`σ ∈ [s̲, s̄]` solving it (`exists_root`; uniqueness and the comparative statics are
`root_saving_le`, `root_cons_le`), and `T c = (1 − σ) y`.

**`exists_rate`**: Tarski gives a fixed point, a solution of the rate equation on `[lo, hi]`.
**`HomotheticEconomy.exists_isRateFunction`** and
**`HomotheticEconomy.exists_recursiveEquilibriumCRRA`**: so the homothetic CRRA economy has a
sequential equilibrium recursive on `(z, K)`, with uninsured idiosyncratic risk, for every
`γ > 0`.
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

theorem mul_rpow_neg_self {γ g t x : ℝ} (hg : 0 < g) (ht : 0 < t) (hx : 0 < x) :
    g * (t * (g * x)) ^ (-γ) = g ^ (1 - γ) * (t * x) ^ (-γ) := by
  rw [show t * (g * x) = g * (t * x) by ring, Real.mul_rpow hg.le (mul_pos ht hx).le,
    ← mul_assoc, show (1 : ℝ) - γ = 1 + -γ by ring, Real.rpow_add hg, Real.rpow_one]

theorem rpow_mul_rpow_neg_cancel {γ t w : ℝ} (ht : 0 < t) (hw : 0 < w) :
    t ^ γ * (t * w) ^ (-γ) = w ^ (-γ) := by
  have h1 : t ^ γ * t ^ (-γ) = 1 := by
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]
  rw [Real.mul_rpow ht.le hw.le]
  linear_combination w ^ (-γ) * h1

/-- The data of the rate equation. -/
structure RateData (Z : Type*) [Fintype Z] where
  μ : Z → Z → ℝ
  μ_nonneg : ∀ z z', 0 ≤ μ z z'
  γ : ℝ
  γ_pos : 0 < γ
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
  low : ∀ z, ∀ x ∈ Icc lo hi, sl ^ γ ≤ ∑ z', μ z z' * g z' x ^ (1 - γ)
  high : ∀ z, ∀ x ∈ Icc lo hi, ∑ z', μ z z' * g z' x ^ (1 - γ) ≤ su ^ γ
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

theorem su_pos : 0 < D.su := D.sl_pos.trans_le D.sl_le

theorem sl_lt : D.sl < 1 := D.sl_le.trans_lt D.su_lt

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
  · calc σ * D.y z k ≤ D.su * D.y z D.hi := mul_le_mul hσ.2 h2 h4.le D.su_pos.le
      _ ≤ D.hi := D.inv_hi z

/-- **The policy constraints**: consumption between the shares `1 − s̄` and `1 − s̲` of resources,
consumption and saving nondecreasing in capital. -/
def InC (c : Z → D.Box → ℝ) : Prop :=
  (∀ z (k : D.Box), (1 - D.su) * D.y z k ≤ c z k) ∧
    (∀ z (k : D.Box), c z k ≤ (1 - D.sl) * D.y z k) ∧
    (∀ z (a b : D.Box), (a : ℝ) ≤ b → c z a ≤ c z b) ∧
    (∀ z (a b : D.Box), (a : ℝ) ≤ b → c z b - c z a ≤ D.y z b - D.y z a)

/-- **The lattice of consumption policies.** -/
def Pol := {c : Z → D.Box → ℝ // D.InC c}

instance : PartialOrder D.Pol := Subtype.partialOrder _

/-- Consuming the largest share is a policy (the top). -/
theorem inC_top : D.InC fun z k => (1 - D.sl) * D.y z k := by
  have h1 : 0 ≤ 1 - D.sl := by linarith [D.sl_lt]
  refine ⟨fun z k => mul_le_mul_of_nonneg_right (by linarith [D.sl_le]) (D.y_pos z k.2).le,
    fun _ _ => le_rfl, fun z a b hab => mul_le_mul_of_nonneg_left (D.y_le z a.2 b.2 hab) h1,
    fun z a b hab => ?_⟩
  have := D.y_le z a.2 b.2 hab
  nlinarith [D.sl_pos]

open Classical in
/-- Pointwise infima (the top for the empty set). -/
noncomputable instance : InfSet D.Pol where
  sInf S := if hS : S.Nonempty then
      ⟨fun z k => sInf ((fun c : D.Pol => c.1 z k) '' S), by
        have hb : ∀ z k, BddBelow ((fun c : D.Pol => c.1 z k) '' S) := fun z k =>
          ⟨(1 - D.su) * D.y z k, by rintro _ ⟨c, -, rfl⟩; exact c.2.1 z k⟩
        have hne : ∀ z k, ((fun c : D.Pol => c.1 z k) '' S).Nonempty := fun z k => hS.image _
        obtain ⟨c₀, hc₀⟩ := hS
        refine ⟨fun z k => le_csInf (hne z k) ?_, fun z k => ?_, fun z a b hab => ?_,
          fun z a b hab => ?_⟩
        · rintro _ ⟨c, -, rfl⟩; exact c.2.1 z k
        · exact (csInf_le (hb z k) ⟨c₀, hc₀, rfl⟩).trans (c₀.2.2.1 z k)
        · refine le_csInf (hne z b) ?_
          rintro _ ⟨c, hc, rfl⟩
          exact (csInf_le (hb z a) ⟨c, hc, rfl⟩).trans (c.2.2.2.1 z a b hab)
        · have : sInf ((fun c : D.Pol => c.1 z b) '' S) - (D.y z b - D.y z a)
              ≤ sInf ((fun c : D.Pol => c.1 z a) '' S) := by
            refine le_csInf (hne z a) ?_
            rintro _ ⟨c, hc, rfl⟩
            have h1 := csInf_le (hb z b) ⟨c, hc, rfl⟩
            have h2 := c.2.2.2.2 z a b hab
            simp only at h1 ⊢
            linarith
          linarith⟩
    else ⟨fun z k => (1 - D.sl) * D.y z k, D.inC_top⟩

open Classical in
theorem isGLB_sInf (S : Set D.Pol) : IsGLB S (sInf S) := by
  by_cases hS : S.Nonempty
  · have hval : ∀ z k, (sInf S : D.Pol).1 z k = sInf ((fun c : D.Pol => c.1 z k) '' S) :=
      fun z k => by
        change (if hS : S.Nonempty then _ else _ : D.Pol).1 z k = _
        simp only [hS, ↓reduceDIte]
    have hb : ∀ z k, BddBelow ((fun c : D.Pol => c.1 z k) '' S) := fun z k =>
      ⟨(1 - D.su) * D.y z k, by rintro _ ⟨c, -, rfl⟩; exact c.2.1 z k⟩
    refine ⟨fun c hc z k => ?_, fun d hd z k => ?_⟩
    · rw [hval]
      exact csInf_le (hb z k) ⟨c, hc, rfl⟩
    · change d.1 z k ≤ (sInf S : D.Pol).1 z k
      rw [hval]
      refine le_csInf (hS.image _) ?_
      rintro _ ⟨c, hc, rfl⟩
      exact hd hc z k
  · have hval : (sInf S : D.Pol).1 = fun z (k : D.Box) => (1 - D.sl) * D.y z k := by
      change (if hS : S.Nonempty then _ else _ : D.Pol).1 = _
      simp only [hS, ↓reduceDIte]
    refine ⟨fun c hc => absurd ⟨c, hc⟩ hS, fun d _ z k => ?_⟩
    change d.1 z k ≤ (sInf S : D.Pol).1 z k
    rw [hval]
    exact d.2.2.1 z k

noncomputable instance : CompleteLattice D.Pol := completeLatticeOfInf _ D.isGLB_sInf

/-- **Policies are continuous**: the increments of consumption are at most those of resources. -/
theorem continuous_pol (c : D.Pol) (z : Z) : Continuous (c.1 z) := by
  have hycont : Continuous fun k : D.Box => D.y z k :=
    (continuousOn_iff_continuous_domRestrict.1 (D.g_cont z)).mul continuous_subtype_val
  refine continuous_of_abs_sub_le (C := 1) hycont fun a b => ?_
  rw [one_mul]
  rcases le_total (a : ℝ) b with hab | hba
  · have h1 := c.2.2.2.1 z a b hab
    have h2 := c.2.2.2.2 z a b hab
    have h3 := D.y_le z a.2 b.2 hab
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h1), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 h3)]
    exact h2
  · have h1 := c.2.2.2.1 z b a hba
    have h2 := c.2.2.2.2 z b a hba
    have h3 := D.y_le z b.2 a.2 hba
    rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (sub_nonneg.2 h3)]
    exact h2

/-- A policy extended to all capital levels through the clamp. -/
noncomputable def ext (c : D.Pol) (z : Z) (x : ℝ) : ℝ := c.1 z (projIcc D.lo D.hi D.lo_le x)

theorem ext_of_mem (c : D.Pol) (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) :
    D.ext c z x = c.1 z ⟨x, hx⟩ := by
  rw [ext, projIcc_of_mem _ hx]

theorem continuous_ext (c : D.Pol) (z : Z) : Continuous (D.ext c z) :=
  (D.continuous_pol c z).comp continuous_projIcc

theorem ext_ge (c : D.Pol) (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) :
    (1 - D.su) * D.y z x ≤ D.ext c z x := by
  rw [D.ext_of_mem c z hx]
  exact c.2.1 z ⟨x, hx⟩

theorem ext_le (c : D.Pol) (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) :
    D.ext c z x ≤ (1 - D.sl) * D.y z x := by
  rw [D.ext_of_mem c z hx]
  exact c.2.2.1 z ⟨x, hx⟩

theorem ext_pos (c : D.Pol) (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) : 0 < D.ext c z x :=
  (mul_pos (by linarith [D.su_lt]) (D.y_pos z hx)).trans_le (D.ext_ge c z hx)

theorem ext_mono (c : D.Pol) (z : Z) {a b : ℝ} (ha : a ∈ Icc D.lo D.hi) (hb : b ∈ Icc D.lo D.hi)
    (hab : a ≤ b) : D.ext c z a ≤ D.ext c z b := by
  rw [D.ext_of_mem c z ha, D.ext_of_mem c z hb]
  exact c.2.2.2.1 z ⟨a, ha⟩ ⟨b, hb⟩ hab

/-- The right-hand side of the Euler equation at next period's capital `x`. -/
noncomputable def Psi (c : D.Pol) (z : Z) (x : ℝ) : ℝ :=
  ∑ z', D.μ z z' * D.g z' x * D.ext c z' x ^ (-D.γ)

/-- **`Ψ` is nonincreasing in next period's capital**, for every `γ > 0`. -/
theorem Psi_anti (c : D.Pol) (z : Z) {a b : ℝ} (ha : a ∈ Icc D.lo D.hi)
    (hb : b ∈ Icc D.lo D.hi) (hab : a ≤ b) : D.Psi c z b ≤ D.Psi c z a := by
  refine Finset.sum_le_sum fun z' _ => ?_
  have h1 : D.g z' b ≤ D.g z' a := D.g_anti z' ha hb hab
  have h2 : D.ext c z' b ^ (-D.γ) ≤ D.ext c z' a ^ (-D.γ) :=
    Real.rpow_le_rpow_of_nonpos (D.ext_pos c z' ha) (D.ext_mono c z' ha hb hab)
      (by linarith [D.γ_pos])
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (D.μ_nonneg z z')) h2
    (Real.rpow_nonneg (D.ext_pos c z' hb).le _)
    (mul_nonneg (D.μ_nonneg z z') (D.g_pos z' a ha).le)

/-- `Ψ` falls as the policy rises. -/
theorem Psi_le_of_le {c d : D.Pol} (hcd : c ≤ d) (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) :
    D.Psi d z x ≤ D.Psi c z x := by
  refine Finset.sum_le_sum fun z' _ => ?_
  have h2 : D.ext d z' x ^ (-D.γ) ≤ D.ext c z' x ^ (-D.γ) :=
    Real.rpow_le_rpow_of_nonpos (D.ext_pos c z' hx) (hcd z' _) (by linarith [D.γ_pos])
  exact mul_le_mul_of_nonneg_left h2 (mul_nonneg (D.μ_nonneg z z') (D.g_pos z' x hx).le)

/-- The sum in the rate bounds. -/
noncomputable def moment (z : Z) (x : ℝ) : ℝ := ∑ z', D.μ z z' * D.g z' x ^ (1 - D.γ)

theorem Psi_ge (c : D.Pol) (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) :
    D.moment z x * ((1 - D.sl) * x) ^ (-D.γ) ≤ D.Psi c z x := by
  have hx0 : 0 < x := D.lo_pos.trans_le hx.1
  have h1 : 0 < 1 - D.sl := by linarith [D.sl_lt]
  rw [moment, Finset.sum_mul]
  refine Finset.sum_le_sum fun z' _ => ?_
  have hg := D.g_pos z' x hx
  have h2 : ((1 - D.sl) * (D.g z' x * x)) ^ (-D.γ) ≤ D.ext c z' x ^ (-D.γ) :=
    Real.rpow_le_rpow_of_nonpos (D.ext_pos c z' hx) (D.ext_le c z' hx) (by linarith [D.γ_pos])
  have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (D.μ_nonneg z z') hg.le)
  rw [mul_assoc, mul_rpow_neg_self hg h1 hx0, ← mul_assoc] at h3
  exact h3

theorem Psi_le (c : D.Pol) (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) :
    D.Psi c z x ≤ D.moment z x * ((1 - D.su) * x) ^ (-D.γ) := by
  have hx0 : 0 < x := D.lo_pos.trans_le hx.1
  have h1 : 0 < 1 - D.su := by linarith [D.su_lt]
  rw [moment, Finset.sum_mul]
  refine Finset.sum_le_sum fun z' _ => ?_
  have hg := D.g_pos z' x hx
  have h2 : D.ext c z' x ^ (-D.γ) ≤ ((1 - D.su) * (D.g z' x * x)) ^ (-D.γ) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos h1 (mul_pos hg hx0)) (D.ext_ge c z' hx)
      (by linarith [D.γ_pos])
  have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (D.μ_nonneg z z') hg.le)
  rw [mul_assoc (D.μ z z') (D.g z' x) (((1 - D.su) * (D.g z' x * x)) ^ (-D.γ)),
    mul_rpow_neg_self hg h1 hx0, ← mul_assoc] at h3
  exact h3

theorem continuousOn_Psi (c : D.Pol) (z : Z) {k : ℝ} (hk : k ∈ Icc D.lo D.hi) :
    ContinuousOn (fun σ => D.Psi c z (σ * D.y z k)) (Icc D.sl D.su) := by
  have hmaps : MapsTo (fun σ : ℝ => σ * D.y z k) (Icc D.sl D.su) (Icc D.lo D.hi) :=
    fun σ hσ => D.saving_mem z hk hσ
  have hlin : ContinuousOn (fun σ : ℝ => σ * D.y z k) (Icc D.sl D.su) :=
    (continuous_id.mul continuous_const).continuousOn
  refine continuousOn_finsetSum _ fun z' _ => ContinuousOn.mul (ContinuousOn.mul
    continuousOn_const ((D.g_cont z').comp hlin hmaps)) ?_
  exact ContinuousOn.rpow_const (((D.continuous_ext c z').comp
    (continuous_id.mul continuous_const)).continuousOn) fun σ hσ =>
      Or.inl (D.ext_pos c z' (hmaps hσ)).ne'

/-- **The Euler equation has a root**: a saving rate in `[s̲, s̄]`, against every policy. -/
theorem exists_root (c : D.Pol) (z : Z) (k : D.Box) :
    ∃ σ ∈ Icc D.sl D.su, ((1 - σ) * D.y z k) ^ (-D.γ) = D.Psi c z (σ * D.y z k) := by
  have hY := D.y_pos z k.2
  have hL : ContinuousOn (fun σ : ℝ => ((1 - σ) * D.y z k) ^ (-D.γ)) (Icc D.sl D.su) :=
    ContinuousOn.rpow_const ((continuous_const.sub continuous_id).mul
      continuous_const).continuousOn fun σ hσ =>
        Or.inl (mul_pos (show (0 : ℝ) < 1 - σ by linarith [hσ.2, D.su_lt]) hY).ne'
  have hcont : ContinuousOn
      (fun σ => ((1 - σ) * D.y z k) ^ (-D.γ) - D.Psi c z (σ * D.y z k)) (Icc D.sl D.su) :=
    hL.sub (D.continuousOn_Psi c z k.2)
  have hlo := D.saving_mem z k.2 (σ := D.sl) ⟨le_rfl, D.sl_le⟩
  have hhi := D.saving_mem z k.2 (σ := D.su) ⟨D.sl_le, le_rfl⟩
  have h1sl : 0 < 1 - D.sl := by linarith [D.sl_lt]
  have h1su : 0 < 1 - D.su := by linarith [D.su_lt]
  have e1 : D.sl ^ D.γ * ((1 - D.sl) * (D.sl * D.y z k)) ^ (-D.γ)
      = ((1 - D.sl) * D.y z k) ^ (-D.γ) := by
    rw [show (1 - D.sl) * (D.sl * D.y z k) = D.sl * ((1 - D.sl) * D.y z k) by ring]
    exact rpow_mul_rpow_neg_cancel D.sl_pos (mul_pos h1sl hY)
  have e2 : D.su ^ D.γ * ((1 - D.su) * (D.su * D.y z k)) ^ (-D.γ)
      = ((1 - D.su) * D.y z k) ^ (-D.γ) := by
    rw [show (1 - D.su) * (D.su * D.y z k) = D.su * ((1 - D.su) * D.y z k) by ring]
    exact rpow_mul_rpow_neg_cancel D.su_pos (mul_pos h1su hY)
  have hneg : ((1 - D.sl) * D.y z k) ^ (-D.γ) ≤ D.Psi c z (D.sl * D.y z k) := by
    rw [← e1]
    exact (mul_le_mul_of_nonneg_right (D.low z _ hlo) (Real.rpow_nonneg
      (mul_pos h1sl (mul_pos D.sl_pos hY)).le _)).trans (D.Psi_ge c z hlo)
  have hpos : D.Psi c z (D.su * D.y z k) ≤ ((1 - D.su) * D.y z k) ^ (-D.γ) := by
    rw [← e2]
    exact (D.Psi_le c z hhi).trans (mul_le_mul_of_nonneg_right (D.high z _ hhi)
      (Real.rpow_nonneg (mul_pos h1su (mul_pos D.su_pos hY)).le _))
  have h0 : (0 : ℝ) ∈ Icc (((1 - D.sl) * D.y z k) ^ (-D.γ) - D.Psi c z (D.sl * D.y z k))
      (((1 - D.su) * D.y z k) ^ (-D.γ) - D.Psi c z (D.su * D.y z k)) :=
    ⟨sub_nonpos.2 hneg, sub_nonneg.2 hpos⟩
  obtain ⟨σ, hσ, hσ0⟩ := intermediate_value_Icc D.sl_le hcont h0
  exact ⟨σ, hσ, sub_eq_zero.1 hσ0⟩

/-- The saving rate solving the Euler equation against `c` at `(z, k)`. -/
noncomputable def root (c : D.Pol) (z : Z) (k : D.Box) : ℝ := (D.exists_root c z k).choose

theorem root_mem (c : D.Pol) (z : Z) (k : D.Box) : D.root c z k ∈ Icc D.sl D.su :=
  (D.exists_root c z k).choose_spec.1

theorem root_spec (c : D.Pol) (z : Z) (k : D.Box) :
    ((1 - D.root c z k) * D.y z k) ^ (-D.γ) = D.Psi c z (D.root c z k * D.y z k) :=
  (D.exists_root c z k).choose_spec.2

theorem cons_pos (c : D.Pol) (z : Z) (k : D.Box) : 0 < (1 - D.root c z k) * D.y z k :=
  mul_pos (by linarith [(D.root_mem c z k).2, D.su_lt]) (D.y_pos z k.2)

/-- Marginal utility orders consumption. -/
theorem le_of_rpow_neg_le {x w : ℝ} (hx : 0 < x)
    (h : x ^ (-D.γ) ≤ w ^ (-D.γ)) : w ≤ x := by
  by_contra hlt
  push Not at hlt
  exact absurd (Real.rpow_lt_rpow_of_neg hx hlt (by linarith [D.γ_pos])) (not_lt.2 h)

/-- **Saving at the root is nondecreasing in capital.** -/
theorem root_saving_le (c : D.Pol) (z : Z) {a b : D.Box} (hab : (a : ℝ) ≤ b) :
    D.root c z a * D.y z a ≤ D.root c z b * D.y z b := by
  by_contra hlt
  push Not at hlt
  have hyab := D.y_le z a.2 b.2 hab
  have h1 := D.Psi_anti c z (D.saving_mem z b.2 (D.root_mem c z b))
    (D.saving_mem z a.2 (D.root_mem c z a)) hlt.le
  rw [← D.root_spec c z a, ← D.root_spec c z b] at h1
  have h2 := D.le_of_rpow_neg_le (D.cons_pos c z a) h1
  linarith

/-- **Consumption at the root is nondecreasing in capital and in the policy.** -/
theorem root_cons_le {c d : D.Pol} (hcd : c ≤ d) (z : Z) {a b : D.Box} (hab : (a : ℝ) ≤ b) :
    (1 - D.root c z a) * D.y z a ≤ (1 - D.root d z b) * D.y z b := by
  by_contra hlt
  push Not at hlt
  have hyab := D.y_le z a.2 b.2 hab
  have hma := D.saving_mem z a.2 (D.root_mem c z a)
  have hmb := D.saving_mem z b.2 (D.root_mem d z b)
  have h1 : ((1 - D.root c z a) * D.y z a) ^ (-D.γ) < ((1 - D.root d z b) * D.y z b) ^ (-D.γ) :=
    Real.rpow_lt_rpow_of_neg (D.cons_pos d z b) hlt (by linarith [D.γ_pos])
  rw [D.root_spec c z a, D.root_spec d z b] at h1
  have h2 : D.root d z b * D.y z b < D.root c z a * D.y z a := by
    by_contra hge
    push Not at hge
    have h3 := D.Psi_anti d z hma hmb hge
    have h4 := D.Psi_le_of_le hcd z hma
    linarith
  linarith

/-- **The operator**: consumption at the root of the Euler equation against the policy. -/
noncomputable def T : D.Pol →o D.Pol where
  toFun c := ⟨fun z k => (1 - D.root c z k) * D.y z k,
    fun z k => mul_le_mul_of_nonneg_right (by linarith [(D.root_mem c z k).2]) (D.y_pos z k.2).le,
    fun z k => mul_le_mul_of_nonneg_right (by linarith [(D.root_mem c z k).1]) (D.y_pos z k.2).le,
    fun z _ _ hab => D.root_cons_le le_rfl z hab, fun z a b hab => by
      have := D.root_saving_le c z hab
      linarith⟩
  monotone' _ _ hcd z _ := D.root_cons_le hcd z le_rfl

/-- **The fixed point**: a consumption policy solving the Euler equation on `[lo, hi]`. -/
noncomputable def fixed : D.Pol := OrderHom.gfp D.T

/-- The saving rate of the fixed point. -/
noncomputable def rate (z : Z) (x : ℝ) : ℝ :=
  D.root D.fixed z (projIcc D.lo D.hi D.lo_le x)

theorem rate_mem (z : Z) (x : ℝ) : D.rate z x ∈ Icc D.sl D.su := D.root_mem _ _ _

theorem fixed_apply (z : Z) (k : D.Box) :
    D.fixed.1 z k = (1 - D.root D.fixed z k) * D.y z k := by
  have hfix : D.T D.fixed = D.fixed := OrderHom.map_gfp D.T
  conv_lhs => rw [← hfix]
  rfl

theorem ext_fixed (z : Z) {x : ℝ} (hx : x ∈ Icc D.lo D.hi) :
    D.ext D.fixed z x = (1 - D.rate z x) * D.y z x := by
  rw [D.ext_of_mem _ z hx, D.fixed_apply, rate, projIcc_of_mem _ hx]

/-- **The rate equation has a solution** on `[lo, hi]`, for every `γ > 0`. -/
theorem exists_rate {z : Z} {k : ℝ} (hk : k ∈ Icc D.lo D.hi) :
    ∑ z', D.μ z z' * D.g z' (D.rate z k * D.y z k) ^ (1 - D.γ)
        * (1 - D.rate z' (D.rate z k * D.y z k)) ^ (-D.γ)
      = (1 - D.rate z k) ^ (-D.γ) * D.rate z k ^ D.γ := by
  set σ := D.rate z k with hσ
  have hσm := D.rate_mem z k
  have hY := D.y_pos z hk
  have hx := D.saving_mem z hk hσm
  have hx0 : 0 < σ * D.y z k := D.lo_pos.trans_le hx.1
  have hspec := D.root_spec D.fixed z ⟨k, hk⟩
  have hr : D.root D.fixed z ⟨k, hk⟩ = σ := by rw [hσ, rate, projIcc_of_mem _ hk]
  rw [hr] at hspec
  -- the right-hand side of the Euler equation, in rates
  have hPsi : D.Psi D.fixed z (σ * D.y z k)
      = (∑ z', D.μ z z' * D.g z' (σ * D.y z k) ^ (1 - D.γ)
          * (1 - D.rate z' (σ * D.y z k)) ^ (-D.γ)) * (σ * D.y z k) ^ (-D.γ) := by
    rw [Psi, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z' _ => ?_
    have hg := D.g_pos z' _ hx
    have h1 : 0 < 1 - D.rate z' (σ * D.y z k) := by
      linarith [(D.rate_mem z' (σ * D.y z k)).2, D.su_lt]
    have hext : D.ext D.fixed z' (σ * D.y z k)
        = (1 - D.rate z' (σ * D.y z k)) * (D.g z' (σ * D.y z k) * (σ * D.y z k)) :=
      D.ext_fixed z' hx
    rw [hext, mul_assoc (D.μ z z'), mul_rpow_neg_self hg h1 hx0, Real.mul_rpow h1.le hx0.le]
    ring
  have hfold := rpow_rate_fold (γ := D.γ) (D.sl_pos.trans_le hσm.1)
    (hσm.2.trans_lt D.su_lt) hY
  have hne : (σ * D.y z k) ^ (-D.γ) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
  refine mul_right_cancel₀ hne ?_
  rw [← hPsi, ← hspec, hfold]

end RateData

/-! ### The homothetic CRRA economy -/

namespace HomotheticEconomy

variable {Z E : Type*} [Fintype Z] [Fintype E] (M : HomotheticEconomy Z E)

/-- **A saving-rate function exists**, for every `γ > 0`: resources per unit of capital positive,
continuous and nonincreasing on `[lo, hi]`, total resources nondecreasing, and bounds
`0 < s̲ ≤ s̄ < 1` on the rate that confirm themselves and keep capital in `[lo, hi]`. -/
theorem exists_isRateFunction {γ : ℝ} (hγ0 : 0 < γ) {m : Z → Z → ℝ}
    (hm0 : ∀ z z', 0 ≤ m z z')
    (hm : ∀ z z' e, ∑ e', M.idioProb z z' e e' * M.shock e' ^ (1 - γ) = m z z')
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hganti : ∀ z, AntitoneOn (M.resources z) (Icc lo hi))
    (hgcont : ∀ z, ContinuousOn (M.resources z) (Icc lo hi))
    (hymono : ∀ z, MonotoneOn (fun k => M.resources z k * k) (Icc lo hi))
    {sl su : ℝ} (hsl : 0 < sl) (hslsu : sl ≤ su) (hsu : su < 1)
    (hlow : ∀ z, ∀ x ∈ Icc lo hi, sl ^ γ
      ≤ ∑ z', M.discount * M.aggProb z z' * m z z' * M.resources z' x ^ (1 - γ))
    (hhigh : ∀ z, ∀ x ∈ Icc lo hi,
      ∑ z', M.discount * M.aggProb z z' * m z z' * M.resources z' x ^ (1 - γ) ≤ su ^ γ)
    (hinvlo : ∀ z, lo ≤ sl * (M.resources z lo * lo))
    (hinvhi : ∀ z, su * (M.resources z hi * hi) ≤ hi) :
    ∃ σ : Z → ℝ → ℝ, M.IsRateFunction γ m (Icc lo hi) σ su := by
  let D : RateData Z :=
    { μ := fun z z' => M.discount * M.aggProb z z' * m z z'
      μ_nonneg := fun z z' =>
        mul_nonneg (mul_nonneg M.discount_pos.le (M.aggProb_nonneg z z')) (hm0 z z')
      γ := γ
      γ_pos := hγ0
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
  refine ⟨D.rate, ?_⟩
  have hsav : ∀ z, ∀ k ∈ Icc lo hi, D.rate z k * M.resources z k * k ∈ Icc lo hi := by
    intro z k hk
    rw [mul_assoc]
    exact D.saving_mem z hk (D.rate_mem z k)
  refine ⟨fun k hk => hlo.trans_le hk.1, fun z k _ => hsl.trans_le (D.rate_mem z k).1,
    fun z k _ => (D.rate_mem z k).2, hsu, hsav, hm, fun z k hk => ?_⟩
  have h := D.exists_rate (z := z) hk
  have hx : D.rate z k * M.resources z k * k = D.rate z k * D.y z k := mul_assoc _ _ _
  rw [hx, ← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z' _ => by
    change _ = M.discount * M.aggProb z z' * m z z' * _ * _
    ring

/-- **The homothetic CRRA economy has a sequential equilibrium recursive on `(z, K)`**, with
uninsured idiosyncratic risk, for every `γ > 0`, from every initial shock and every initial
distribution of positive wealth levels with mean in `[lo, hi]`. -/
theorem exists_recursiveEquilibriumCRRA {γ : ℝ} (hγ0 : 0 < γ) {m : Z → Z → ℝ}
    (hm0 : ∀ z z', 0 ≤ m z z')
    (hm : ∀ z z' e, ∑ e', M.idioProb z z' e e' * M.shock e' ^ (1 - γ) = m z z')
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hganti : ∀ z, AntitoneOn (M.resources z) (Icc lo hi))
    (hgcont : ∀ z, ContinuousOn (M.resources z) (Icc lo hi))
    (hymono : ∀ z, MonotoneOn (fun k => M.resources z k * k) (Icc lo hi))
    {sl su : ℝ} (hsl : 0 < sl) (hslsu : sl ≤ su) (hsu : su < 1)
    (hlow : ∀ z, ∀ x ∈ Icc lo hi, sl ^ γ
      ≤ ∑ z', M.discount * M.aggProb z z' * m z z' * M.resources z' x ^ (1 - γ))
    (hhigh : ∀ z, ∀ x ∈ Icc lo hi,
      ∑ z', M.discount * M.aggProb z z' * m z z' * M.resources z' x ^ (1 - γ) ≤ su ^ γ)
    (hinvlo : ∀ z, lo ≤ sl * (M.resources z lo * lo))
    (hinvhi : ∀ z, su * (M.resources z hi * hi) ≤ hi) :
    ∃ σ : Z → ℝ → ℝ, ∀ {ι : Type} [Fintype ι] (z₀ : Z) (ν w : ι → ℝ) (t : ι → E),
      (∀ i, 0 < w i) → ∑ i, ν i * w i ∈ Icc lo hi →
        M.IsSequentialEquilibriumCRRA γ z₀ ν w t (M.ratePath σ z₀ (∑ i, ν i * w i)) := by
  obtain ⟨σ, F⟩ := M.exists_isRateFunction hγ0 hm0 hm hlo hlohi hganti hgcont hymono hsl
    hslsu hsu hlow hhigh hinvlo hinvhi
  exact ⟨σ, fun z₀ ν w t hw hk => F.isSequentialEquilibriumCRRA_ratePath z₀ hγ0 ν w t hw hk⟩

end HomotheticEconomy

end KrusellSmith

end LeanEconomics
