/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ConsistentSelection
import LeanEconomics.KrusellSmith.StochasticOrder

/-!
# The greatest sequential equilibrium is a consistent selection

Milestone MR3 of `MINIMAL_STATE_PLAN.md`: a recursive equilibrium on the minimal state `(z, μ)`
**without uniqueness of sequential equilibrium**, when savings rise with aggregate capital.

**Hypothesis** (`SavingMonotone`): along a pointwise higher path of capital (the same labour),
every household saves weakly more.

* `eqMap hH z μ`: the equilibrium map (capital path ↦ mean-saving path) as a monotone map of the
  complete lattice `List Z → [0, assetCap]` (`meanCapital_le`, MR2).
* `greatest hH z μ`: its greatest fixed point (Knaster–Tarski, `OrderHom.gfp`), a sequential
  equilibrium (`greatest_spec`) above every other (`le_greatest`).
* `greatest_shift`, **consistency**: the continuation of the greatest equilibrium below `[z']` is
  the greatest equilibrium from the child's state. One way, the continuation is an equilibrium.
  The other way, splice the child's greatest equilibrium into the parent's (`splice`): saving at
  the root rises, so the child's distribution dominates (`nodeDist_dominates`) and mean capital
  below rises (`meanCapital_le`); the spliced path is a post-fixed point, hence below the greatest
  fixed point.
* **`SavingMonotone.consistentSelection`** and **`SavingMonotone.isRecursive`**: a recursive
  equilibrium on the minimal state (MR1).

`SavingMonotone` fails with Cobb–Douglas prices (see the plan); it is aimed at economies with
complementarities, where the return rises with aggregate capital.
-/

open Set MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E)

/-- **Savings rise with aggregate capital**: along a pointwise higher path of capital, with the
same labour, every household saves weakly more. -/
def SavingMonotone : Prop :=
  ∀ (z : Z) (m₀ : E → ℝ) (K K' : List Z → ℝ), (∀ h, K h ≤ K' h) →
    ∀ s, M.policy z (M.pricePath z m₀ K) s ≤ M.policy z (M.pricePath z m₀ K') s

instance assetCap_fact : Fact ((0 : ℝ) ≤ M.assetCap) := ⟨M.assetCap_pos.le⟩

/-- Capital paths with values in `[0, assetCap]`: a complete lattice. -/
abbrev CapPath := List Z → ↥(Icc (0 : ℝ) M.assetCap)

variable {M}

/-- **The equilibrium map** as a monotone map of capital paths. -/
noncomputable def eqMap (hH : M.SavingMonotone) (z : Z) (μ : ProbabilityMeasure M.AState) :
    M.CapPath →o M.CapPath where
  toFun K h := ⟨M.meanCapital z (μ : Measure M.AState)
      (M.pricePath z (M.initMass (μ : Measure M.AState)) fun g => (K g : ℝ)) h,
    M.meanCapital_mem z _ _ h⟩
  monotone' _ _ hKL h :=
    M.meanCapital_le z (hH z _ _ _ fun g => hKL g) (AssetDominates.refl _) h

/-- **The greatest sequential equilibrium** from `(z, μ)`. -/
noncomputable def greatest (hH : M.SavingMonotone) (z : Z) (μ : ProbabilityMeasure M.AState) :
    List Z → ℝ :=
  fun h => (OrderHom.gfp (eqMap hH z μ) h : ℝ)

variable (hH : M.SavingMonotone)

theorem greatest_spec (z : Z) (μ : ProbabilityMeasure M.AState) :
    M.IsSequentialEquilibrium z (μ : Measure M.AState) (greatest hH z μ) := fun h =>
  (congrArg Subtype.val (congrFun (OrderHom.map_gfp (eqMap hH z μ)) h)).symm

/-- A path in `[0, assetCap]` below the mean-saving path it induces lies below the greatest
equilibrium. -/
theorem le_greatest_of_post (z : Z) (μ : ProbabilityMeasure M.AState) {K : List Z → ℝ}
    (hK : ∀ h, K h ∈ Icc 0 M.assetCap)
    (hpost : ∀ h, K h ≤ M.meanCapital z (μ : Measure M.AState)
      (M.pricePath z (M.initMass (μ : Measure M.AState)) K) h) (h : List Z) :
    K h ≤ greatest hH z μ h := by
  have hle : (fun g => (⟨K g, hK g⟩ : ↥(Icc (0 : ℝ) M.assetCap)))
      ≤ eqMap hH z μ (fun g => ⟨K g, hK g⟩) := fun g => hpost g
  exact OrderHom.le_gfp _ hle h

/-- **The greatest equilibrium is above every sequential equilibrium.** -/
theorem le_greatest (z : Z) (μ : ProbabilityMeasure M.AState) {K : List Z → ℝ}
    (hK : M.IsSequentialEquilibrium z (μ : Measure M.AState) K) (h : List Z) :
    K h ≤ greatest hH z μ h :=
  le_greatest_of_post hH z μ (fun g => M.equilibrium_mem_pi z μ hK g (mem_univ g))
    (fun g => (hK g).le) h

/-! ### Splicing a continuation below a child -/

open Classical in
/-- `K₁` with the subtree below `[z']` replaced by `K₂`. -/
noncomputable def splice (K₁ : List Z → ℝ) (z' : Z) (K₂ : List Z → ℝ) : List Z → ℝ :=
  fun h => if h.getLast? = some z' then K₂ h.dropLast else K₁ h

omit [Fintype Z] [Fintype E] in
theorem splice_append (K₁ : List Z → ℝ) (z' : Z) (K₂ : List Z → ℝ) (g : List Z) :
    splice K₁ z' K₂ (g ++ [z']) = K₂ g := by
  simp [splice]

omit [Fintype Z] [Fintype E] in
theorem shiftPath_splice (K₁ : List Z → ℝ) (z' : Z) (K₂ : List Z → ℝ) :
    shiftPath (splice K₁ z' K₂) [z'] = K₂ :=
  funext fun g => splice_append K₁ z' K₂ g

/-- **Consistency of the greatest equilibrium**: its continuation below `[z']` is the greatest
equilibrium from the child's shock and distribution. -/
theorem greatest_shift (z : Z) (μ : ProbabilityMeasure M.AState) (z' : Z) :
    shiftPath (greatest hH z μ) [z'] =
      greatest hH z' ⟨M.nodeDist z (μ : Measure M.AState)
        (M.pricePath z (M.initMass (μ : Measure M.AState)) (greatest hH z μ)) [z'],
        M.isProbabilityMeasure_nodeDist z _ _ [z']⟩ := by
  set Kb := greatest hH z μ with hKb
  set μ' : ProbabilityMeasure M.AState := ⟨M.nodeDist z (μ : Measure M.AState)
    (M.pricePath z (M.initMass (μ : Measure M.AState)) Kb) [z'],
    M.isProbabilityMeasure_nodeDist z _ _ [z']⟩ with hμ'
  set K' := greatest hH z' μ' with hK'
  -- the continuation is an equilibrium from the child's state
  have hcont : M.IsSequentialEquilibrium z' (μ' : Measure M.AState) (shiftPath Kb [z']) :=
    (greatest_spec hH z μ).continuation M z (μ : Measure M.AState) [z']
  have h1 : ∀ g, shiftPath Kb [z'] g ≤ K' g := le_greatest hH z' μ' hcont
  -- the spliced path
  set K'' := splice Kb z' K' with hK''
  have hmemK' : ∀ g, K' g ∈ Icc 0 M.assetCap := fun g =>
    M.equilibrium_mem_pi z' μ' (greatest_spec hH z' μ') g (mem_univ g)
  have hmemKb : ∀ g, Kb g ∈ Icc 0 M.assetCap := fun g =>
    M.equilibrium_mem_pi z μ (greatest_spec hH z μ) g (mem_univ g)
  have hmem'' : ∀ h, K'' h ∈ Icc 0 M.assetCap := by
    intro h
    simp only [hK'', splice]
    split_ifs
    · exact hmemK' _
    · exact hmemKb _
  have hle : ∀ h, Kb h ≤ K'' h := by
    intro h
    by_cases hh : h.getLast? = some z'
    · obtain ⟨g, rfl⟩ := List.getLast?_eq_some_iff.1 hh
      rw [hK'', splice_append]
      exact h1 g
    · simp [hK'', splice, hh]
  have hpol := hH z (M.initMass (μ : Measure M.AState)) Kb K'' hle
  have hpost : ∀ h, K'' h ≤ M.meanCapital z (μ : Measure M.AState)
      (M.pricePath z (M.initMass (μ : Measure M.AState)) K'') h := by
    intro h
    by_cases hh : h.getLast? = some z'
    · obtain ⟨g, rfl⟩ := List.getLast?_eq_some_iff.1 hh
      rw [hK'', splice_append]
      set P'' := M.pricePath z (M.initMass (μ : Measure M.AState)) K''
      set ν'' := M.nodeDist z (μ : Measure M.AState) P'' [z']
      have := M.isProbabilityMeasure_nodeDist z (μ : Measure M.AState) P'' [z']
      have hdom : M.AssetDominates (μ' : Measure M.AState) ν'' :=
        nodeDist_dominates z hpol (AssetDominates.refl _) [z']
      have hmass : M.initMass ν'' = M.initMass (μ' : Measure M.AState) := by
        rw [M.initMass_nodeDist z (μ : Measure M.AState) P'' [z']]
        exact (M.initMass_nodeDist z (μ : Measure M.AState) _ [z']).symm
      have hshift : M.meanCapital z (μ : Measure M.AState) P'' (g ++ [z'])
          = M.meanCapital z' ν'' (M.pricePath z' (M.initMass (μ' : Measure M.AState)) K') g := by
        rw [← M.meanCapital_shift z P'' [z'] (μ : Measure M.AState) g]
        change M.meanCapital z' ν'' (shiftPath P'' [z']) g = _
        rw [← M.pricePath_shift z (μ : Measure M.AState) K'' [z'], hK'', shiftPath_splice]
        change M.meanCapital z' ν''
          (M.pricePath z' (M.initMass ν'') K') g = _
        rw [hmass]
      rw [hshift]
      calc K' g = M.meanCapital z' (μ' : Measure M.AState)
            (M.pricePath z' (M.initMass (μ' : Measure M.AState)) K') g :=
            greatest_spec hH z' μ' g
        _ ≤ M.meanCapital z' ν'' (M.pricePath z' (M.initMass (μ' : Measure M.AState)) K') g :=
            M.meanCapital_le z' (fun s => le_rfl) hdom g
    · have hoff : K'' h = Kb h := by simp [hK'', splice, hh]
      rw [hoff]
      calc Kb h = M.meanCapital z (μ : Measure M.AState)
            (M.pricePath z (M.initMass (μ : Measure M.AState)) Kb) h := greatest_spec hH z μ h
        _ ≤ _ := M.meanCapital_le z hpol (AssetDominates.refl _) h
  funext g
  refine le_antisymm (h1 g) ?_
  have := le_greatest_of_post hH z μ hmem'' hpost (g ++ [z'])
  rw [hK'', splice_append] at this
  exact this

/-- **Under `SavingMonotone`, the greatest equilibrium is a consistent selection.** -/
noncomputable def SavingMonotone.consistentSelection : M.ConsistentSelection where
  sel := greatest hH
  sel_spec := greatest_spec hH
  sel_shift := greatest_shift hH

/-- **A recursive equilibrium on the minimal state without uniqueness**: when savings rise with
aggregate capital, along the greatest sequential equilibrium from any `(z, μ)`, at every node
`h` with state `(z_h, μ_h)`, capital is mean assets of `μ_h`, households save by the recursive
policy at `(z_h, μ_h)`, and the distribution at every child is the law of motion at
`(z_h, μ_h)`. -/
theorem SavingMonotone.isRecursive (z : Z) (μ : ProbabilityMeasure M.AState) (h : List Z) :
    let S := hH.consistentSelection
    S.sel z μ h = ∫ x, M.assets x ∂(S.nodeProb z μ h : Measure M.AState) ∧
      (∀ x : M.AState, M.policy z (S.prices z μ) (x.1, ⟨x.2.idio, h⟩)
          = S.recursivePolicy (shockAt z h) (S.nodeProb z μ h) x) ∧
      ∀ z' : Z, S.nodeProb z μ (z' :: h) = S.lawOfMotion (shockAt z h) (S.nodeProb z μ h) z' :=
  hH.consistentSelection.isRecursive z μ h

end KSModel

end KrusellSmith

end LeanEconomics
