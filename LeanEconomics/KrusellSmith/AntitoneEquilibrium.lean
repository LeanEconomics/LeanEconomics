/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.GreatestEquilibrium

/-!
# Uniqueness from an order-reversing equilibrium map

Milestone B1 of the bracket plan (`EXISTENCE_EXTENSIONS_PLAN.md`, item 6). With Cobb–Douglas prices
capital only redistributes cash (`CobbDouglasRedistribution.lean`), so the equilibrium map cannot
preserve order; the candidate structure is that it **reverses** it.

**The bracket** (abstract, any complete lattice). For an antitone `f`, the square `f ∘ f` is
monotone (`sq`); Tarski gives its least and greatest fixed points `lo ≤ hi`;

* `f` swaps them: `f lo = hi`, `f hi = lo` (`map_lfp_sq`, `map_gfp_sq`);
* every fixed point of `f` lies between them (`lfp_sq_le`, `le_gfp_sq`);
* if `lo = hi`, `f` has exactly one fixed point (`eq_of_lfp_eq_gfp`, `isFixedPt_of_lfp_eq_gfp`).

**Concavity closes the bracket** (`eq_of_concave`, paths `ι → ℝ`): if a monotone `g` fixes
`lo ≤ hi`, `lo ≥ t₀ hi` for some `t₀ > 0`, and `g` is concave at the top in Krasnosel'skii's sense —
for every `t ∈ (0, 1)` some `φ > t` has `φ hi ≤ g (t hi)` — then `lo = hi`. Take the largest `t`
with `t hi ≤ lo`; concavity pushes it up unless it is `1`. No Lipschitz bound is used.

**Krusell–Smith** (`eqFn`, `EqMapAntitone`, `SqConcaveAtTop`): if the equilibrium map from every
`(z, μ)` reverses order, and its square is concave at the top of the bracket with the bottom a
positive fraction of the top, then **sequential equilibrium is unique**
(`uniqueSequentialEquilibrium_of_antitone`) and a recursive equilibrium on the minimal state
exists (`isRecursive_of_antitone`). The two hypotheses are milestones B2 and B3: open.
-/

open Set MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

/-! ### The bracket of an order-reversing map -/

namespace AntitoneBracket

variable {α : Type*} [CompleteLattice α] {f : α → α} (hf : Antitone f)

/-- The square of an antitone map, as a monotone map. -/
def sq : α →o α := ⟨f ∘ f, fun _ _ h => hf (hf h)⟩

theorem sq_apply (a : α) : sq hf a = f (f a) := rfl

theorem isFixedPt_sq_map {a : α} (ha : sq hf a = a) : sq hf (f a) = f a := by
  change f (f (f a)) = f a
  rw [show f (f a) = a from ha]

/-- `f` maps the least fixed point of its square to the greatest. -/
theorem map_lfp_sq : f (OrderHom.lfp (sq hf)) = OrderHom.gfp (sq hf) := by
  set lo := OrderHom.lfp (sq hf)
  set hi := OrderHom.gfp (sq hf)
  have hlo : sq hf lo = lo := OrderHom.map_lfp _
  have hhi : sq hf hi = hi := OrderHom.map_gfp _
  refine le_antisymm (OrderHom.le_gfp _ (isFixedPt_sq_map hf hlo).ge) ?_
  have h1 : lo ≤ f hi := OrderHom.lfp_le _ (isFixedPt_sq_map hf hhi).le
  have h2 := hf h1
  change hi ≤ f lo
  calc hi = f (f hi) := hhi.symm
    _ ≤ f lo := h2

/-- `f` maps the greatest fixed point of its square to the least. -/
theorem map_gfp_sq : f (OrderHom.gfp (sq hf)) = OrderHom.lfp (sq hf) := by
  rw [← map_lfp_sq hf]
  exact OrderHom.map_lfp (sq hf)

theorem lfp_sq_le {x : α} (hx : f x = x) : OrderHom.lfp (sq hf) ≤ x :=
  OrderHom.lfp_le _ (by rw [sq_apply, hx, hx])

theorem le_gfp_sq {x : α} (hx : f x = x) : x ≤ OrderHom.gfp (sq hf) :=
  OrderHom.le_gfp _ (by rw [sq_apply, hx, hx])

/-- **If the bracket closes, `f` has exactly one fixed point.** -/
theorem eq_of_lfp_eq_gfp (heq : OrderHom.lfp (sq hf) = OrderHom.gfp (sq hf)) {x : α}
    (hx : f x = x) : x = OrderHom.lfp (sq hf) :=
  le_antisymm (heq ▸ le_gfp_sq hf hx) (lfp_sq_le hf hx)

theorem isFixedPt_of_lfp_eq_gfp (heq : OrderHom.lfp (sq hf) = OrderHom.gfp (sq hf)) :
    f (OrderHom.lfp (sq hf)) = OrderHom.lfp (sq hf) := by
  rw [map_lfp_sq hf, heq]

end AntitoneBracket

/-! ### Concavity closes the bracket -/

/-- **Krasnosel'skii's argument**: a monotone map fixing `lo ≤ hi`, with `lo` at least a positive
fraction of `hi ≥ 0`, and concave at the top (`φ hi ≤ g (t hi)` for some `φ > t`, every
`t ∈ (0, 1)`), has `lo = hi`. -/
theorem eq_of_concave {ι : Type*} {g : (ι → ℝ) → (ι → ℝ)} {lo hi : ι → ℝ}
    (hglo : g lo = lo) (hle : lo ≤ hi) (h0 : 0 ≤ hi)
    (hmono : ∀ t ∈ Icc (0 : ℝ) 1, t • hi ≤ lo → g (t • hi) ≤ g lo)
    (hpos : ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ • hi ≤ lo)
    (hconc : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ φ : ℝ, t < φ ∧ φ • hi ≤ g (t • hi)) : lo = hi := by
  obtain ⟨t₀, ht₀, ht₀le⟩ := hpos
  set S : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ t • hi ≤ lo} with hS
  have hh0 : ∀ i, (0 : ℝ) ≤ hi i := fun i => h0 i
  have hlo0 : ∀ i, (0 : ℝ) ≤ lo i := fun i => by
    have : t₀ * hi i ≤ lo i := ht₀le i
    exact (mul_nonneg ht₀.le (hh0 i)).trans this
  have hmin : min t₀ 1 ∈ S := by
    refine ⟨⟨le_min ht₀.le zero_le_one, min_le_right _ _⟩, fun i => ?_⟩
    have h1 : t₀ * hi i ≤ lo i := ht₀le i
    have h2 := mul_le_mul_of_nonneg_right (min_le_left t₀ 1) (hh0 i)
    change min t₀ 1 * hi i ≤ lo i
    linarith
  have hbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  set ts := sSup S with hts
  have hts1 : ts ≤ 1 := csSup_le ⟨_, hmin⟩ fun t ht => ht.1.2
  have hts0 : 0 < ts := lt_of_lt_of_le (lt_min ht₀ one_pos) (le_csSup hbdd hmin)
  -- the supremum is attained
  have hmem : ts • hi ≤ lo := fun i => by
    change ts * hi i ≤ lo i
    rcases (hh0 i).lt_or_eq with hpos' | hzero
    · have : ts ≤ lo i / hi i := csSup_le ⟨_, hmin⟩ fun t ht => by
        have : t * hi i ≤ lo i := ht.2 i
        rw [le_div_iff₀ hpos']
        exact this
      rwa [le_div_iff₀ hpos'] at this
    · rw [← hzero, mul_zero]
      exact hlo0 i
  -- concavity pushes it to one
  have hts_eq : ts = 1 := by
    by_contra hne
    have hlt : ts < 1 := lt_of_le_of_ne hts1 hne
    obtain ⟨φ, hφ, hφle⟩ := hconc ts ⟨hts0, hlt⟩
    have hup : φ • hi ≤ lo :=
      hφle.trans ((hmono ts ⟨hts0.le, hts1⟩ hmem).trans hglo.le)
    have hin : min φ 1 ∈ S := by
      refine ⟨⟨le_min (hts0.le.trans hφ.le) zero_le_one, min_le_right _ _⟩, fun i => ?_⟩
      have h1 : φ * hi i ≤ lo i := hup i
      have h2 := mul_le_mul_of_nonneg_right (min_le_left φ 1) (hh0 i)
      change min φ 1 * hi i ≤ lo i
      linarith
    have := le_csSup hbdd hin
    have : ts < min φ 1 := lt_min hφ hlt
    linarith
  refine le_antisymm hle fun i => ?_
  have := hmem i
  rw [hts_eq, one_smul] at this
  exact this

/-! ### The Krusell–Smith equilibrium map -/

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **The equilibrium map** on capital paths in `[0, ā]`: a path to the mean-capital path it
induces. Its fixed points are the sequential equilibria. -/
noncomputable def eqFn (z : Z) (μ : ProbabilityMeasure M.AState) (K : M.CapPath) : M.CapPath :=
  fun h => ⟨M.meanCapital z (μ : Measure M.AState)
      (M.pricePath z (M.initMass (μ : Measure M.AState)) fun g => (K g : ℝ)) h,
    M.meanCapital_mem z _ _ h⟩

/-- **The equilibrium map reverses order** (milestone B2, open). -/
def EqMapAntitone : Prop := ∀ (z : Z) (μ : ProbabilityMeasure M.AState), Antitone (M.eqFn z μ)

variable {M}

/-- The top and bottom of the bracket, as real paths. -/
noncomputable def bracketHi (hA : M.EqMapAntitone) (z : Z) (μ : ProbabilityMeasure M.AState) :
    List Z → ℝ :=
  fun h => (OrderHom.gfp (AntitoneBracket.sq (hA z μ)) h : ℝ)

noncomputable def bracketLo (hA : M.EqMapAntitone) (z : Z) (μ : ProbabilityMeasure M.AState) :
    List Z → ℝ :=
  fun h => (OrderHom.lfp (AntitoneBracket.sq (hA z μ)) h : ℝ)

/-- A real path clamped into `[0, ā]`. -/
noncomputable def toCap (K : List Z → ℝ) : M.CapPath :=
  fun h => projIcc 0 M.assetCap M.assetCap_pos.le (K h)

/-- The square of the equilibrium map, on real paths. -/
noncomputable def sqReal (hA : M.EqMapAntitone) (z : Z) (μ : ProbabilityMeasure M.AState)
    (K : List Z → ℝ) : List Z → ℝ :=
  fun h => (AntitoneBracket.sq (hA z μ) (toCap K) h : ℝ)

variable (M) in
/-- **The square is concave at the top of the bracket, whose bottom is a positive fraction of its
top** (milestone B3, open). -/
def SqConcaveAtTop (hA : M.EqMapAntitone) : Prop :=
  ∀ (z : Z) (μ : ProbabilityMeasure M.AState),
    (∃ t₀ : ℝ, 0 < t₀ ∧ t₀ • bracketHi hA z μ ≤ bracketLo hA z μ) ∧
    ∀ t ∈ Ioo (0 : ℝ) 1, ∃ φ : ℝ, t < φ ∧
      φ • bracketHi hA z μ ≤ sqReal hA z μ (t • bracketHi hA z μ)

theorem toCap_val (K : M.CapPath) : toCap (M := M) (fun h => (K h : ℝ)) = K :=
  funext fun h => projIcc_val _ (K h)

/-- **The bracket closes** under concavity at the top. -/
theorem lfp_eq_gfp (hA : M.EqMapAntitone) (hC : M.SqConcaveAtTop hA) (z : Z)
    (μ : ProbabilityMeasure M.AState) :
    OrderHom.lfp (AntitoneBracket.sq (hA z μ)) = OrderHom.gfp (AntitoneBracket.sq (hA z μ)) := by
  set lo := OrderHom.lfp (AntitoneBracket.sq (hA z μ))
  set hi := OrderHom.gfp (AntitoneBracket.sq (hA z μ))
  have hcap : toCap (M := M) (bracketLo hA z μ) = lo := toCap_val lo
  have hloR : sqReal hA z μ (bracketLo hA z μ) = bracketLo hA z μ := by
    funext h
    simp only [sqReal]
    rw [hcap, OrderHom.map_lfp]
    rfl
  have hle : bracketLo hA z μ ≤ bracketHi hA z μ := fun h =>
    (OrderHom.lfp_le_gfp (AntitoneBracket.sq (hA z μ))) h
  have h0 : 0 ≤ bracketHi hA z μ := fun h => (hi h).2.1
  have hmono : ∀ t ∈ Icc (0 : ℝ) 1, t • bracketHi hA z μ ≤ bracketLo hA z μ →
      sqReal hA z μ (t • bracketHi hA z μ) ≤ sqReal hA z μ (bracketLo hA z μ) := by
    intro t _ ht h
    simp only [sqReal]
    refine (AntitoneBracket.sq (hA z μ)).monotone (fun g => ?_) h
    simp only [toCap, bracketLo]
    exact monotone_projIcc _ (ht g)
  have heq := eq_of_concave hloR hle h0 hmono (hC z μ).1 (hC z μ).2
  funext h
  exact Subtype.ext (congrFun heq h)

/-- **Uniqueness of sequential equilibrium from an order-reversing equilibrium map whose square is
concave at the top of the bracket.** -/
theorem uniqueSequentialEquilibrium_of_antitone (hA : M.EqMapAntitone) (hC : M.SqConcaveAtTop hA) :
    M.UniqueSequentialEquilibrium := by
  intro z μ K K' hK hK'
  have key : ∀ {K : List Z → ℝ} (hK : M.IsSequentialEquilibrium z (μ : Measure M.AState) K),
      (fun h => (⟨K h, M.equilibrium_mem_pi z μ hK h (mem_univ h)⟩ : ↥(Icc (0 : ℝ) M.assetCap)))
        = OrderHom.lfp (AntitoneBracket.sq (hA z μ)) := by
    intro K hK
    refine AntitoneBracket.eq_of_lfp_eq_gfp (hA z μ) (lfp_eq_gfp hA hC z μ) ?_
    funext h
    exact Subtype.ext (hK h).symm
  funext h
  exact congrArg Subtype.val (congrFun ((key hK).trans (key hK').symm) h)

/-- **A recursive equilibrium on the minimal state `(z, μ)`** for an order-reversing equilibrium
map whose square is concave at the top of the bracket. -/
theorem isRecursive_of_antitone (hA : M.EqMapAntitone) (hC : M.SqConcaveAtTop hA) (z : Z)
    (μ : ProbabilityMeasure M.AState) (h : List Z) :
    M.eqPath z μ h = ∫ x, M.assets x ∂(M.nodeProb z μ h : Measure M.AState) ∧
      (∀ x : M.AState,
        M.policy z (M.pricePath z (M.initMass (μ : Measure M.AState)) (M.eqPath z μ))
            (x.1, ⟨x.2.idio, h⟩)
          = M.recursivePolicy (shockAt z h) (M.nodeProb z μ h) x) ∧
      ∀ z' : Z, M.nodeProb z μ (z' :: h) = M.lawOfMotion (shockAt z h) (M.nodeProb z μ h) z' :=
  M.isRecursive (uniqueSequentialEquilibrium_of_antitone hA hC) z μ h

end KSModel

end KrusellSmith

end LeanEconomics
