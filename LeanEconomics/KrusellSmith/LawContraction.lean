/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Contraction
import LeanEconomics.KrusellSmith.SequenceStateSynchronization

/-!
# The law of motion contracts when prices respond weakly to capital

Milestone LS4 of `LEE_MATCHING_PLAN.md`: Lee's uniform contraction (Definition 7) derived from
primitives, in the class of Track A (`Contraction.lean`, `κ < 1`).

**The distance.** `DistLE d ν ν'`: every bounded continuous test function that is `L`-Lipschitz
in assets (with any values across idiosyncratic states) integrates against `ν` and `ν'` to within
`L d` — the Wasserstein distance in assets, with households compared only within their
idiosyncratic state. Indicators of idiosyncratic states are `0`-Lipschitz, so `DistLE d ν ν'`
forces **the same idiosyncratic marginals** (`DistLE.initMass_eq`), hence the same labour path:
only capital feeds back into prices. Conversely the same marginals give `DistLE (2 assetCap)`
(`distLE_of_initMass_eq`), and `DistLE 0` gives `ν = ν'` (`DistLE.eq_of_zero`, Stone–Weierstrass:
the asset-Lipschitz functions are a point-separating subalgebra).

**The contraction** (`ContractionHyp.distLE_lawOfMotion`). Under Track A's hypotheses with
`κ < 1`, if `DistLE d ν ν'` then tomorrow's distributions satisfy `DistLE (r d)`, where

  `r = R̄ + G / (1 − κ)`,   `G = ℓ C + A / m`

(`lawRate`, `policyGain`). The steps: the two equilibrium capital paths are within
`d / (1 − κ)` in Track A's weighted norm (`eqPath_gap`); so the saving policies today differ by at
most `G d / (1 − κ)` (`recursivePolicy_gap`); and pushing forward moves the distance by the saving
slope `R̄` plus that policy gap. `r < 1` needs `R̄ < 1` — automatic in the `κ < 1` class with
Cobb–Douglas prices, where the capital share is tiny and `R ≈ 1 − δ` — and `G` small.

**Sequence state.** For a sequence-state equilibrium whose idiosyncratic marginals depend only on
today's aggregate shock (as in Krusell–Smith's design of the employment process):

* `IsSeqStateEquilibrium.distLE_of_agree`: **fading memory**, `DistLE (r ^ T · 2 assetCap)`
  between histories that agree over their last `T + 1` shocks;
* `IsSeqStateEquilibrium.distLE_run`: **burn-in** from any start with the right marginal;
* `IsSeqStateEquilibrium.seqPolicy_gap_of_agree`, `seqCapital_gap_of_agree`: **an explicit
  error bound for matched expectations** — saving differs by at most
  `G r ^ T 2 assetCap / (1 − κ)`;
* `IsSeqStateEquilibrium.eq_of_lawRate_lt_one`: **uniqueness** of the sequence-state equilibrium
  with given marginals when `r < 1`.
-/

open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable {M : KSModel Z E}

/-! ### The asset-Lipschitz distance -/

/-- **`ν` and `ν'` are within `d`**: every bounded continuous function that is `L`-Lipschitz in
assets integrates to within `L d`. -/
def DistLE (d : ℝ) (ν ν' : Measure M.AState) : Prop :=
  ∀ L, 0 ≤ L → ∀ f : M.AState →ᵇ ℝ, AssetLip L f →
    |∫ x, f x ∂ν - ∫ x, f x ∂ν'| ≤ L * d

theorem DistLE.nonneg {d : ℝ} {ν ν' : Measure M.AState} (hd : DistLE d ν ν') : 0 ≤ d := by
  have := hd 1 zero_le_one M.assets assetLip_assets
  rw [one_mul] at this
  exact (abs_nonneg _).trans this

theorem assetLip_idioInd (e : E) : AssetLip 0 (M.idioInd e) := by
  intro a b i
  by_cases hi : i.idio = e
  · rw [M.idioInd_of_eq (x := (a, i)) hi, M.idioInd_of_eq (x := (b, i)) hi]
    simp
  · rw [M.idioInd_of_ne (x := (a, i)) hi, M.idioInd_of_ne (x := (b, i)) hi]
    simp

/-- **Within any distance, the idiosyncratic marginals agree.** -/
theorem DistLE.initMass_eq {d : ℝ} {ν ν' : Measure M.AState} [IsFiniteMeasure ν]
    [IsFiniteMeasure ν'] (hd : DistLE d ν ν') : M.initMass ν = M.initMass ν' := by
  funext e
  have := hd 0 le_rfl (M.idioInd e) (assetLip_idioInd e)
  rw [zero_mul, integral_idioInd, integral_idioInd] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- **The same idiosyncratic marginals: within `2 assetCap`.** -/
theorem distLE_of_initMass_eq {ν ν' : Measure M.AState} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (h : M.initMass ν = M.initMass ν') :
    DistLE (2 * M.assetCap) ν ν' := by
  intro L hL f hf
  let a₀ : ↥(Icc (0 : ℝ) M.assetCap) := ⟨0, le_rfl, M.assetCap_pos.le⟩
  let g : M.AState →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => f (a₀, x.2), f.continuous.comp (continuous_const.prodMk continuous_snd)⟩
  have hg : (g : M.AState → ℝ) = fun x => ∑ e, f (a₀, ⟨e⟩) * M.idioInd e x := by
    funext x
    exact M.eq_sum_idioInd (fun e => f (a₀, ⟨e⟩)) x
  have hgi : ∀ (μ : Measure M.AState) [IsFiniteMeasure μ],
      ∫ x, g x ∂μ = ∑ e, f (a₀, ⟨e⟩) * M.initMass μ e := by
    intro μ _
    rw [hg, integral_finsetSum _ fun e _ => ((M.idioInd e).integrable μ).const_mul _]
    exact Finset.sum_congr rfl fun e _ => by rw [integral_const_mul, integral_idioInd]; rfl
  have hfg : ∀ x : M.AState, ‖f x - g x‖ ≤ L * M.assetCap := by
    intro x
    rw [Real.norm_eq_abs]
    change |f (x.1, x.2) - f (a₀, x.2)| ≤ _
    refine (hf x.1 a₀ x.2).trans (mul_le_mul_of_nonneg_left ?_ hL)
    have := x.1.2
    change |(x.1 : ℝ) - 0| ≤ _
    rw [sub_zero, abs_of_nonneg this.1]
    exact this.2
  have hb : ∀ (μ : Measure M.AState) [IsProbabilityMeasure μ],
      |∫ x, (f x - g x) ∂μ| ≤ L * M.assetCap := by
    intro μ _
    have := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hfg)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  have e1 : ∀ (μ : Measure M.AState) [IsProbabilityMeasure μ],
      ∫ x, f x ∂μ = ∫ x, (f x - g x) ∂μ + ∑ e, f (a₀, ⟨e⟩) * M.initMass μ e := by
    intro μ _
    rw [integral_sub (f.integrable μ) (g.integrable μ), hgi μ]
    ring
  rw [e1 ν, e1 ν', h]
  have h1 := hb ν
  have h2 := hb ν'
  calc _ = |∫ x, (f x - g x) ∂ν - ∫ x, (f x - g x) ∂ν'| := by ring_nf
    _ ≤ |∫ x, (f x - g x) ∂ν| + |∫ x, (f x - g x) ∂ν'| := abs_sub _ _
    _ ≤ L * M.assetCap + L * M.assetCap := add_le_add h1 h2
    _ = L * (2 * M.assetCap) := by ring

variable (M) in
/-- **Bounded continuous functions Lipschitz in assets**, a subalgebra. -/
noncomputable def assetLipSubalgebra : StarSubalgebra ℝ (M.AState →ᵇ ℝ) where
  carrier := {f | ∃ L, 0 ≤ L ∧ AssetLip L f}
  mul_mem' := by
    rintro f g ⟨L, hL, hf⟩ ⟨L', hL', hg⟩
    refine ⟨‖f‖ * L' + ‖g‖ * L, add_nonneg (mul_nonneg (norm_nonneg _) hL')
      (mul_nonneg (norm_nonneg _) hL), fun a b i => ?_⟩
    change |f (a, i) * g (a, i) - f (b, i) * g (b, i)| ≤ _
    have e : f (a, i) * g (a, i) - f (b, i) * g (b, i)
        = f (a, i) * (g (a, i) - g (b, i)) + g (b, i) * (f (a, i) - f (b, i)) := by ring
    rw [e]
    have h1 : |f (a, i)| ≤ ‖f‖ := by
      rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
    have h2 : |g (b, i)| ≤ ‖g‖ := by
      rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm _
    have hd := abs_nonneg ((a : ℝ) - b)
    calc _ ≤ |f (a, i)| * |g (a, i) - g (b, i)| + |g (b, i)| * |f (a, i) - f (b, i)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ ‖f‖ * (L' * |(a : ℝ) - b|) + ‖g‖ * (L * |(a : ℝ) - b|) :=
          add_le_add (mul_le_mul h1 (hg a b i) (abs_nonneg _) (norm_nonneg _))
            (mul_le_mul h2 (hf a b i) (abs_nonneg _) (norm_nonneg _))
      _ = (‖f‖ * L' + ‖g‖ * L) * |(a : ℝ) - b| := by ring
  add_mem' := by
    rintro f g ⟨L, hL, hf⟩ ⟨L', hL', hg⟩
    refine ⟨L + L', add_nonneg hL hL', fun a b i => ?_⟩
    change |(f (a, i) + g (a, i)) - (f (b, i) + g (b, i))| ≤ _
    have e : (f (a, i) + g (a, i)) - (f (b, i) + g (b, i))
        = (f (a, i) - f (b, i)) + (g (a, i) - g (b, i)) := by ring
    rw [e, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hf a b i) (hg a b i))
  algebraMap_mem' := by
    intro r
    refine ⟨0, le_rfl, fun a b i => ?_⟩
    change |r - r| ≤ _
    simp
  star_mem' := by
    intro f hf
    have : star f = f := by
      ext x
      simp
    rw [this]
    exact hf

theorem assetLipSubalgebra_separatesPoints :
    ((M.assetLipSubalgebra).map (toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  have mem : ∀ f : M.AState →ᵇ ℝ, f ∈ M.assetLipSubalgebra →
      (f : M.AState → ℝ) ∈ ((fun g : C(M.AState, ℝ) => (g : M.AState → ℝ)) ''
        (((M.assetLipSubalgebra).map (toContinuousMapStarₐ ℝ)) : Set C(M.AState, ℝ))) :=
    fun f hf => ⟨toContinuousMapStarₐ ℝ f, ⟨f, hf, rfl⟩, rfl⟩
  by_cases ha : x.1 = y.1
  · have hi : x.2.idio ≠ y.2.idio := by
      intro he
      apply hxy
      rcases x with ⟨a, ⟨i⟩⟩
      rcases y with ⟨b, ⟨j⟩⟩
      simp only at ha he
      rw [ha, he]
    refine ⟨_, mem (M.idioInd x.2.idio) ⟨0, le_rfl, assetLip_idioInd _⟩, ?_⟩
    rw [M.idioInd_of_eq rfl, M.idioInd_of_ne (Ne.symm hi)]
    exact one_ne_zero
  · refine ⟨_, mem M.assets ⟨1, zero_le_one, assetLip_assets⟩, ?_⟩
    change (x.1 : ℝ) ≠ y.1
    exact fun h => ha (Subtype.ext h)

/-- **Asset-Lipschitz functions separate finite measures.** -/
theorem eq_of_forall_assetLip {ν ν' : Measure M.AState} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h : ∀ L, 0 ≤ L → ∀ f : M.AState →ᵇ ℝ, AssetLip L f → ∫ x, f x ∂ν = ∫ x, f x ∂ν') :
    ν = ν' :=
  ext_of_forall_mem_subalgebra_integral_eq_of_polish assetLipSubalgebra_separatesPoints
    fun g ⟨L, hL, hg⟩ => h L hL g hg

/-- **Distance zero is equality.** -/
theorem DistLE.eq_of_zero {ν ν' : Measure M.AState} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (hd : DistLE 0 ν ν') : ν = ν' :=
  eq_of_forall_assetLip fun L hL f hf => by
    have := hd L hL f hf
    rw [mul_zero] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-! ### Distributions down the tree from two roots -/

/-- The distribution gap down the tree from a gap `d₀` at the root. -/
def gapFrom (θ d₀ : ℝ) (P : List Z → ℝ) : List Z → ℝ
  | [] => d₀
  | _ :: h => θ * gapFrom θ d₀ P h + P h

variable (z₀ : Z)

/-- **Distributions from two roots drift apart by at most the gap from the root distance.** -/
theorem integral_nodeDist_sub_le_of_distLE (μ₀ μ₁ : Measure M.AState) [IsProbabilityMeasure μ₀]
    [IsProbabilityMeasure μ₁] (K K' : List Z → ℝ × ℝ) (P : List Z → ℝ)
    (hP : ∀ h (x : M.AState),
      |M.policy z₀ K (x.1, ⟨x.2.idio, h⟩) - M.policy z₀ K' (x.1, ⟨x.2.idio, h⟩)| ≤ P h)
    {d₀ : ℝ} (h0 : DistLE d₀ μ₀ μ₁) :
    ∀ (h : List Z) {L : ℝ}, 0 ≤ L → ∀ {f : M.AState →ᵇ ℝ}, AssetLip L f →
      |∫ x, f x ∂(M.nodeDist z₀ μ₀ K h) - ∫ x, f x ∂(M.nodeDist z₀ μ₁ K' h)|
        ≤ L * gapFrom M.returnBound d₀ P h
  | [], L, hL, f, hf => h0 L hL f hf
  | z' :: h, L, hL, f, hf => by
    have := M.isProbabilityMeasure_nodeDist z₀ μ₀ K h
    have := M.isProbabilityMeasure_nodeDist z₀ μ₁ K' h
    have hR0 : 0 ≤ M.returnBound :=
      (M.grossReturn_nonneg z₀ 0 0).trans (M.grossReturn_le z₀ 0 0)
    have hd : ∫ x, f x ∂(M.nodeDist z₀ μ₀ K (z' :: h))
        = ∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K h) :=
      M.integral_pushNode z₀ K h z' _ f
    have hd' : ∫ x, f x ∂(M.nodeDist z₀ μ₁ K' (z' :: h))
        = ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₁ K' h) :=
      M.integral_pushNode z₀ K' h z' _ f
    rw [hd, hd']
    -- same integrand, different distributions
    have h1 := integral_nodeDist_sub_le_of_distLE μ₀ μ₁ K K' P hP h0 h (mul_nonneg hR0 hL)
      (M.assetLip_expectedNext z₀ K h z' hL hf)
    -- same distribution, different integrands
    have h2 : |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₁ K' h)
        - ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₁ K' h)| ≤ L * P h := by
      rw [← integral_sub ((M.expectedNext z₀ K h z' f).integrable _)
        ((M.expectedNext z₀ K' h z' f).integrable _)]
      have := norm_integral_le_of_norm_le_const (μ := M.nodeDist z₀ μ₁ K' h)
        (f := fun x => M.expectedNext z₀ K h z' f x - M.expectedNext z₀ K' h z' f x)
        (C := L * P h) (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          exact (M.abs_expectedNext_sub_le z₀ K K' h z' hf x).trans
            (mul_le_mul_of_nonneg_left (hP h x) hL))
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    calc |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K h)
          - ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₁ K' h)|
        ≤ |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₀ K h)
            - ∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₁ K' h)|
          + |∫ x, M.expectedNext z₀ K h z' f x ∂(M.nodeDist z₀ μ₁ K' h)
            - ∫ x, M.expectedNext z₀ K' h z' f x ∂(M.nodeDist z₀ μ₁ K' h)| :=
          abs_sub_le _ _ _
      _ ≤ M.returnBound * L * gapFrom M.returnBound d₀ P h + L * P h := add_le_add h1 h2
      _ = L * gapFrom M.returnBound d₀ P (z' :: h) := by simp only [gapFrom]; ring

/-! ### The contraction -/

namespace ContractionHyp

variable (H : M.ContractionHyp)
include H

/-- **The gain of today's saving in the distance between distributions** (per unit of the
capital-path gap). -/
noncomputable def policyGain : ℝ := H.ℓ * M.cashScale + H.A / H.m

/-- **The contraction rate of the law of motion.** -/
noncomputable def lawRate : ℝ := M.returnBound + H.policyGain / (1 - H.κ)

theorem policyGain_nonneg : 0 ≤ H.policyGain :=
  add_nonneg (mul_nonneg H.ℓ_nonneg M.cashScale_nonneg) (div_nonneg H.A_nonneg H.m_pos.le)

theorem lawRate_nonneg [Nonempty Z] (hκ : H.κ < 1) : 0 ≤ H.lawRate :=
  add_nonneg M.returnBound_nonneg (div_nonneg H.policyGain_nonneg (sub_pos.2 hκ).le)

theorem weighted_gapFrom [Nonempty Z] {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ∀ h : List Z, H.lam ^ h.length * gapFrom M.returnBound d
        (fun h : List Z => c / H.lam ^ h.length) h
      ≤ d + H.lam * c / (1 - H.lam * M.returnBound)
  | [] => by
    simp only [gapFrom, List.length_nil, pow_zero, one_mul]
    have := div_nonneg (mul_nonneg H.lam_pos.le hc) (sub_nonneg.2 H.lam_return_lt.le)
    linarith
  | z :: h => by
    have ih := weighted_gapFrom hc hd h
    set G := H.lam * c / (1 - H.lam * M.returnBound)
    have hG : G * (1 - H.lam * M.returnBound) = H.lam * c :=
      div_mul_cancel₀ _ (ne_of_gt (sub_pos.2 H.lam_return_lt))
    have hne : H.lam ^ h.length ≠ 0 := (pow_pos H.lam_pos _).ne'
    have e : H.lam ^ (z :: h).length * gapFrom M.returnBound d
          (fun h : List Z => c / H.lam ^ h.length) (z :: h)
        = H.lam * M.returnBound * (H.lam ^ h.length * gapFrom M.returnBound d
          (fun h : List Z => c / H.lam ^ h.length) h) + H.lam * c := by
      simp only [gapFrom, List.length_cons, pow_succ]
      field_simp
    rw [e]
    have hlr : 0 ≤ H.lam * M.returnBound := mul_nonneg H.lam_pos.le M.returnBound_nonneg
    have h1 := mul_le_mul_of_nonneg_left ih hlr
    have h2 : H.lam * M.returnBound * d ≤ d :=
      mul_le_of_le_one_left hd H.lam_return_lt.le
    have h3 : H.lam * M.returnBound * (d + G) = H.lam * M.returnBound * d
        + H.lam * M.returnBound * G := by ring
    have h4 : H.lam * M.returnBound * G + H.lam * c = G := by linarith [hG]
    linarith

variable {z : Z} {ν ν' : ProbabilityMeasure M.AState} {d : ℝ}

/-- **The equilibrium capital paths from two distributions** are within `d / (1 − κ)` in the
weighted norm. -/
theorem eqPath_gap (hκ : H.κ < 1) (hd : DistLE d (ν : Measure M.AState) ν') (h : List Z) :
    H.lam ^ h.length * |M.eqPath z ν h - M.eqPath z ν' h| ≤ d / (1 - H.κ) := by
  have : Nonempty Z := ⟨z⟩
  have hm := hd.initMass_eq
  have hd0 := hd.nonneg
  have h1κ : 0 < 1 - H.κ := sub_pos.2 hκ
  set K := M.eqPath z ν
  set K' := M.eqPath z ν'
  set m₀ := M.initMass (ν : Measure M.AState)
  have eK : ∀ h, K h = ∫ x, M.assets x
      ∂(M.nodeDist z (ν : Measure M.AState) (M.pricePath z m₀ K) h) :=
    fun h => M.eqPath_spec z ν h
  have eK' : ∀ h, K' h = ∫ x, M.assets x
      ∂(M.nodeDist z (ν' : Measure M.AState) (M.pricePath z m₀ K') h) := by
    intro h
    rw [show m₀ = M.initMass (ν' : Measure M.AState) from hm]
    exact M.eqPath_spec z ν' h
  -- one step: a weighted bound `b` gives `d + κ b`
  have step : ∀ b, 0 ≤ b → (∀ h : List Z, H.lam ^ h.length * |K h - K' h| ≤ b) →
      ∀ h : List Z, H.lam ^ h.length * |K h - K' h| ≤ d + H.κ * b := by
    intro b hb0 hb h
    set c := H.policyGain * b
    have hc : 0 ≤ c := mul_nonneg H.policyGain_nonneg hb0
    have hP : ∀ h (x : M.AState),
        |M.policy z (M.pricePath z m₀ K) (x.1, ⟨x.2.idio, h⟩)
          - M.policy z (M.pricePath z m₀ K') (x.1, ⟨x.2.idio, h⟩)|
          ≤ (fun h : List Z => c / H.lam ^ h.length) h := by
      intro h x
      rw [le_div_iff₀ (pow_pos H.lam_pos _), mul_comm]
      exact H.weighted_policy_gap z m₀ K K' hb0 hb (x.1, ⟨x.2.idio, h⟩)
    have hi := M.integral_nodeDist_sub_le_of_distLE z (ν : Measure M.AState) ν' _ _ _ hP hd h
      zero_le_one assetLip_assets
    rw [← eK, ← eK', one_mul] at hi
    calc _ ≤ H.lam ^ h.length * gapFrom M.returnBound d
          (fun h : List Z => c / H.lam ^ h.length) h :=
          mul_le_mul_of_nonneg_left hi (pow_nonneg H.lam_pos.le _)
      _ ≤ d + H.lam * c / (1 - H.lam * M.returnBound) := H.weighted_gapFrom hc hd0 h
      _ = d + H.κ * b := by simp only [c, κ, policyGain]; ring
  -- iterate from the bound `assetCap`
  have hb : ∀ h, |K h - K' h| ≤ M.assetCap := by
    intro h
    have h1 := M.meanCapital_mem z (ν : Measure M.AState) (M.pricePath z m₀ K) h
    have h2 := M.meanCapital_mem z (ν' : Measure M.AState) (M.pricePath z m₀ K') h
    have e1 : K h = M.meanCapital z (ν : Measure M.AState) (M.pricePath z m₀ K) h := eK h
    have e2 : K' h = M.meanCapital z (ν' : Measure M.AState) (M.pricePath z m₀ K') h := eK' h
    rw [← e1] at h1
    rw [← e2] at h2
    exact abs_sub_le_iff.2 ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩
  have hcap : 0 ≤ M.assetCap := M.assetCap_pos.le
  have hiter : ∀ n : ℕ, ∀ h : List Z,
      H.lam ^ h.length * |K h - K' h| ≤ d / (1 - H.κ) + H.κ ^ n * M.assetCap := by
    intro n
    induction n with
    | zero =>
      intro h
      rw [pow_zero, one_mul]
      have := div_nonneg hd0 h1κ.le
      calc _ ≤ 1 * |K h - K' h| :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ H.lam_pos.le H.lam_le_one) (abs_nonneg _)
        _ ≤ M.assetCap := by rw [one_mul]; exact hb h
        _ ≤ _ := by linarith
    | succ n ih =>
      intro h
      have hb0 : 0 ≤ d / (1 - H.κ) + H.κ ^ n * M.assetCap :=
        add_nonneg (div_nonneg hd0 h1κ.le) (mul_nonneg (pow_nonneg H.κ_nonneg n) hcap)
      have := step _ hb0 ih h
      have e : d + H.κ * (d / (1 - H.κ) + H.κ ^ n * M.assetCap)
          = d / (1 - H.κ) + H.κ ^ (n + 1) * M.assetCap := by
        field_simp
        ring
      rwa [e] at this
  have hlim : Tendsto (fun n : ℕ => d / (1 - H.κ) + H.κ ^ n * M.assetCap) atTop
      (𝓝 (d / (1 - H.κ) + 0 * M.assetCap)) :=
    tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one H.κ_nonneg hκ).mul tendsto_const_nhds)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim fun n => hiter n h

/-- **Today's saving policies from two distributions** differ by at most `G d / (1 − κ)`. -/
theorem recursivePolicy_gap (hκ : H.κ < 1) (hd : DistLE d (ν : Measure M.AState) ν')
    (x : M.AState) :
    |M.recursivePolicy z ν x - M.recursivePolicy z ν' x| ≤ H.policyGain * (d / (1 - H.κ)) := by
  have : Nonempty Z := ⟨z⟩
  have hm := hd.initMass_eq
  have hη0 : 0 ≤ d / (1 - H.κ) := div_nonneg hd.nonneg (sub_pos.2 hκ).le
  have := H.weighted_policy_gap z (M.initMass (ν : Measure M.AState)) (M.eqPath z ν)
    (M.eqPath z ν') hη0 (fun h => H.eqPath_gap hκ hd h) (x.1, ⟨x.2.idio, []⟩)
  simp only [List.length_nil, pow_zero, one_mul] at this
  unfold recursivePolicy
  rw [← hm]
  exact this

/-- **The law of motion contracts at the rate `r = R̄ + G / (1 − κ)`.** -/
theorem distLE_lawOfMotion (hκ : H.κ < 1) (hd : DistLE d (ν : Measure M.AState) ν') (z' : Z) :
    DistLE (H.lawRate * d) (M.lawOfMotion z ν z' : Measure M.AState) (M.lawOfMotion z ν' z') := by
  have : Nonempty Z := ⟨z⟩
  have hm := hd.initMass_eq
  have hη0 : 0 ≤ d / (1 - H.κ) := div_nonneg hd.nonneg (sub_pos.2 hκ).le
  set m₀ := M.initMass (ν : Measure M.AState)
  set c := H.policyGain * (d / (1 - H.κ))
  have hP : ∀ h (x : M.AState),
      |M.policy z (M.pricePath z m₀ (M.eqPath z ν)) (x.1, ⟨x.2.idio, h⟩)
        - M.policy z (M.pricePath z m₀ (M.eqPath z ν')) (x.1, ⟨x.2.idio, h⟩)|
        ≤ (fun h : List Z => c / H.lam ^ h.length) h := by
    intro h x
    rw [le_div_iff₀ (pow_pos H.lam_pos _), mul_comm]
    exact H.weighted_policy_gap z m₀ _ _ hη0 (fun h => H.eqPath_gap hκ hd h) (x.1, ⟨x.2.idio, h⟩)
  intro L hL f hf
  have hi := M.integral_nodeDist_sub_le_of_distLE z (ν : Measure M.AState) ν' _ _ _ hP hd [z']
    hL hf
  change |∫ x, f x ∂(M.nodeDist z (ν : Measure M.AState) (M.pricePath z m₀ (M.eqPath z ν)) [z'])
      - ∫ x, f x ∂(M.nodeDist z (ν' : Measure M.AState)
        (M.pricePath z (M.initMass (ν' : Measure M.AState)) (M.eqPath z ν')) [z'])| ≤ _
  rw [← hm]
  refine hi.trans (le_of_eq ?_)
  simp only [gapFrom, List.length_nil, pow_zero, div_one, c, lawRate]
  ring

end ContractionHyp

/-! ### Fading memory, burn-in, matching and uniqueness on the sequence state -/

namespace IsSeqStateEquilibrium

variable (H : M.ContractionHyp) (hκ : H.κ < 1) {μ : History Z → ProbabilityMeasure M.AState}
  (hμ : M.IsSeqStateEquilibrium μ)
include H hκ hμ

/-- Under the contraction hypotheses, tomorrow's distribution is the law of motion of today's. -/
theorem eq_lawOfMotion_tail (ω : History Z) :
    μ ω = M.lawOfMotion (ω 1) (μ (History.tail ω)) (ω 0) := by
  have := hμ.eq_lawOfMotion (H.uniqueSequentialEquilibrium hκ) (History.tail ω) (ω 0)
  rwa [History.cons_head_tail] at this

/-- **Fading memory**: histories agreeing over their last `T + 1` shocks carry distributions
within `r ^ T · 2 assetCap`, when idiosyncratic marginals depend only on today's shock. -/
theorem distLE_of_agree
    (hm : ∀ ω ω' : History Z, ω 0 = ω' 0 →
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ ω' : Measure M.AState)) :
    ∀ (T : ℕ) (ω ω' : History Z), (∀ n ≤ T, ω n = ω' n) →
      DistLE (H.lawRate ^ T * (2 * M.assetCap)) (μ ω : Measure M.AState) (μ ω') := by
  intro T
  induction T with
  | zero =>
    intro ω ω' hag
    rw [pow_zero, one_mul]
    exact distLE_of_initMass_eq (hm ω ω' (hag 0 le_rfl))
  | succ T ih =>
    intro ω ω' hag
    have ih' := ih (History.tail ω) (History.tail ω') fun n hn => hag (n + 1) (by omega)
    rw [hμ.eq_lawOfMotion_tail H hκ ω, hμ.eq_lawOfMotion_tail H hκ ω', hag 0 (by omega),
      hag 1 (by omega)]
    have e : H.lawRate ^ (T + 1) * (2 * M.assetCap)
        = H.lawRate * (H.lawRate ^ T * (2 * M.assetCap)) := by ring
    rw [e]
    exact H.distLE_lawOfMotion hκ ih' (ω' 0)

/-- **Burn-in**: the distribution today is within `r ^ T · 2 assetCap` of the one reached by
starting from any `ν` with the right idiosyncratic marginal, `T` periods back, and running the
law of motion along the realized shocks. -/
theorem distLE_run :
    ∀ (T : ℕ) (ω : History Z) (ν : ProbabilityMeasure M.AState),
      M.initMass (ν : Measure M.AState) = M.initMass (μ (History.drop T ω) : Measure M.AState) →
      DistLE (H.lawRate ^ T * (2 * M.assetCap)) (μ ω : Measure M.AState)
        ((run M.lawMap T ω ν : ProbabilityMeasure M.AState) : Measure M.AState) := by
  intro T
  induction T with
  | zero =>
    intro ω ν hν
    rw [pow_zero, one_mul]
    exact distLE_of_initMass_eq hν.symm
  | succ T ih =>
    intro ω ν hν
    have ih' := ih (History.tail ω) ν hν
    rw [hμ.eq_lawOfMotion_tail H hκ ω]
    have e : H.lawRate ^ (T + 1) * (2 * M.assetCap)
        = H.lawRate * (H.lawRate ^ T * (2 * M.assetCap)) := by ring
    rw [e]
    exact H.distLE_lawOfMotion hκ ih' (ω 0)

/-- **Matched expectations, saving**: at histories agreeing over their last `T + 1` shocks,
saving differs by at most `G r ^ T 2 assetCap / (1 − κ)` at every household state. -/
theorem seqPolicy_gap_of_agree
    (hm : ∀ ω ω' : History Z, ω 0 = ω' 0 →
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ ω' : Measure M.AState))
    (T : ℕ) {ω ω' : History Z} (hag : ∀ n ≤ T, ω n = ω' n)
    (a : ↥(Icc (0 : ℝ) M.assetCap)) (e : E) :
    |(M.seqPolicy μ ω a e : ℝ) - M.seqPolicy μ ω' a e|
      ≤ H.policyGain * (H.lawRate ^ T * (2 * M.assetCap) / (1 - H.κ)) := by
  have hU := H.uniqueSequentialEquilibrium hκ
  rw [hμ.seqPolicy_eq_recursivePolicy hU ω a e, hμ.seqPolicy_eq_recursivePolicy hU ω' a e,
    hag 0 (Nat.zero_le T)]
  exact H.recursivePolicy_gap hκ (hμ.distLE_of_agree H hκ hm T ω ω' hag) (a, ⟨e⟩)

/-- **Matched expectations, capital**: at histories agreeing over their last `T + 1` shocks,
capital at every future node `g` differs by at most `r ^ T 2 assetCap / ((1 − κ) λ^{|g|})`. -/
theorem seqCapital_gap_of_agree
    (hm : ∀ ω ω' : History Z, ω 0 = ω' 0 →
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ ω' : Measure M.AState))
    (T : ℕ) {ω ω' : History Z} (hag : ∀ n ≤ T, ω n = ω' n) (g : List Z) :
    H.lam ^ g.length * |M.seqCapital μ ω g - M.seqCapital μ ω' g|
      ≤ H.lawRate ^ T * (2 * M.assetCap) / (1 - H.κ) := by
  have hU := H.uniqueSequentialEquilibrium hκ
  rw [hμ.seqCapital_eq_eqPath hU ω, hμ.seqCapital_eq_eqPath hU ω', hag 0 (Nat.zero_le T)]
  exact H.eqPath_gap hκ (hμ.distLE_of_agree H hκ hm T ω ω' hag) g

/-- **Uniqueness**: when `r < 1`, two sequence-state equilibria with the same idiosyncratic
marginals at every history are equal. -/
theorem eq_of_lawRate_lt_one (hr : H.lawRate < 1) {μ' : History Z → ProbabilityMeasure M.AState}
    (hμ' : M.IsSeqStateEquilibrium μ')
    (hm : ∀ ω : History Z,
      M.initMass (μ ω : Measure M.AState) = M.initMass (μ' ω : Measure M.AState)) :
    μ = μ' := by
  have hT : ∀ (T : ℕ) (ω : History Z),
      DistLE (H.lawRate ^ T * (2 * M.assetCap)) (μ ω : Measure M.AState) (μ' ω) := by
    intro T
    induction T with
    | zero =>
      intro ω
      rw [pow_zero, one_mul]
      exact distLE_of_initMass_eq (hm ω)
    | succ T ih =>
      intro ω
      rw [hμ.eq_lawOfMotion_tail H hκ ω, hμ'.eq_lawOfMotion_tail H hκ ω]
      have e : H.lawRate ^ (T + 1) * (2 * M.assetCap)
          = H.lawRate * (H.lawRate ^ T * (2 * M.assetCap)) := by ring
      rw [e]
      exact H.distLE_lawOfMotion hκ (ih (History.tail ω)) (ω 0)
  funext ω
  have : Nonempty Z := ⟨ω 0⟩
  apply ProbabilityMeasure.toMeasure_injective
  refine eq_of_forall_assetLip fun L hL f hf => ?_
  have hlim : Tendsto (fun T : ℕ => L * (H.lawRate ^ T * (2 * M.assetCap))) atTop
      (𝓝 (L * (0 * (2 * M.assetCap)))) :=
    tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (H.lawRate_nonneg hκ) hr).mul tendsto_const_nhds)
  rw [zero_mul, mul_zero] at hlim
  have h0 := ge_of_tendsto' hlim fun T => hT T ω L hL f hf
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

end IsSeqStateEquilibrium

end KSModel

end KrusellSmith

end LeanEconomics
