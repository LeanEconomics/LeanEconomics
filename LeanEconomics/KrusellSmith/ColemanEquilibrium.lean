/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ColemanSufficiency
import LeanEconomics.KrusellSmith.RepAgentExpMap

/-!
# The Coleman fixed point is a sequential equilibrium

Milestone CO4d of `COLEMAN_PLAN.md`: the representative-agent CRRA, Cobb–Douglas economy with one
idiosyncratic state and `β R̄ ≤ 1`.

* **`colemanPlan`**: from capital `k` at shock `z`, the plan "hold the Coleman capital path" in
  the household problem at the prices that path implies (`colemanPrices`). Its consumption is the
  Coleman fixed point (`colemanPlan_cons`), at least the floor `m = w̲ L`, which lies above the
  CRRA model's consumption floor (`consFloor_lt_m`).
* **`colemanPlan_euler`**: the plan satisfies the household's Euler conditions with the corners —
  the expected marginal value of the household is the Coleman continuation (`nextMU_eq`).
* **`policy_eq_saving`**: by Euler sufficiency (`policy_eq_of_euler`), the household's optimal
  saving at the root is the Coleman saving.
* **`isSequentialEquilibrium_capPath`**: from every point mass, the Coleman capital path is a
  sequential equilibrium. The point mass stays a point mass (`nodeDist_dirac`); shifted to any node,
  the price path is the Coleman path from that node (`Data.capPath_append`), so the household
  saves the Coleman saving there, and its assets follow the path.
-/

open Set Filter Topology MeasureTheory
open LeanEconomics.StochasticDynamicProgram

namespace LeanEconomics

namespace KrusellSmith

namespace Coleman

/-- The capital path from a node continues as the capital path started at that node. -/
theorem Data.capPath_append {Z : Type*} [Fintype Z] (D : Data Z) (c : D.Pol) (z₀ : Z)
    (k₀ : D.Box) : ∀ g h : List Z,
    D.capPath c z₀ k₀ (g ++ h) = D.capPath c (shockAt z₀ h) (D.capPath c z₀ k₀ h) g
  | [], _ => rfl
  | _ :: g, h => by
    change D.savingBox c ((g ++ h).headD z₀) (D.capPath c z₀ k₀ (g ++ h))
      = D.savingBox c (g.headD (shockAt z₀ h)) (D.capPath c (shockAt z₀ h) (D.capPath c z₀ k₀ h) g)
    rw [Data.capPath_append D c z₀ k₀ g h]
    congr 1
    exact (shockAt_append z₀ g h).symm

variable {Z E : Type*} [Fintype Z] [Fintype E] [Unique E] (V : KSEnvironment Z E)
  (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ)
  (hLbox : T.clampLab (V.efficiency default) = V.efficiency default)
  (hβR : V.discount * T.returnBound ≤ 1)

local notation "𝒟" => crraData V T hγ hLbox hβR
local notation "𝒸" => OrderHom.gfp (Data.T (crraData V T hγ hLbox hβR))
local notation "𝕄" => crraModel V T hγ

/-- The price path of the Coleman capital path from `(z, k)`: capital on the path, labour the
efficiency. -/
noncomputable def colemanPrices (z : Z) (k : (𝒟).Box) : List Z → ℝ × ℝ :=
  fun g => (((𝒟).capPath 𝒸 z k g : ℝ), V.efficiency default)

/-- The household's root state at capital `k`. -/
noncomputable def rootOf (k : (𝒟).Box) : (𝕄).State :=
  (⟨k.1, k.2⟩, ⟨default, []⟩)

/-- The CRRA model's consumption floor lies below the Coleman floor `m`. -/
theorem consFloor_lt_m : (𝕄).consFloor < (𝒟).m := by
  have h1 : crraFloorLevel V T hγ ≤ T.wageLo * V.effLo / 4 := min_le_right _ _
  have h2 : T.wageLo * V.effLo ≤ T.wageLo * V.efficiency default :=
    mul_le_mul_of_nonneg_left (V.effLo_le default) T.wageLo_pos.le
  have h3 := crraFloorLevel_pos V T hγ
  have h4 := mul_pos T.wageLo_pos V.effLo_pos
  change crraFloorLevel V T hγ / 2 < T.wageLo * V.efficiency default
  linarith

/-- Cash at a state holding the Coleman capital of its node is the Coleman cash there. -/
theorem cash_eq (z : Z) (k : (𝒟).Box) (s : (𝕄).State)
    (hs : (s.1 : ℝ) = (𝒟).capPath 𝒸 z k s.2.node) :
    (𝕄).cash z (colemanPrices V T hγ hLbox hβR z k) s
      = (𝒟).y (shockAt z s.2.node) ((𝒟).capPath 𝒸 z k s.2.node) := by
  simp only [KSModel.cash, KSModel.returnAt, KSModel.wageAt, colemanPrices]
  rw [hs, Unique.eq_default s.2.idio]
  change T.grossReturn _ _ _ * _ + T.wage _ _ _ * V.efficiency default
    - T.grossReturn _ _ _ * 0 = _
  rw [mul_zero, sub_zero]
  rfl

/-- **The Coleman plan**: hold the Coleman capital of the node. -/
noncomputable def colemanPlan (z : Z) (k : (𝒟).Box) :
    ((𝕄).household z (colemanPrices V T hγ hLbox hβR z k)).Plan (rootOf V T hγ hLbox hβR k) where
  state n h := (⟨((𝒟).capPath 𝒸 z k (KSModel.labelOf ⟨default, []⟩ n h).node : ℝ),
    ((𝒟).capPath 𝒸 z k (KSModel.labelOf ⟨default, []⟩ n h).node).2⟩,
    KSModel.labelOf ⟨default, []⟩ n h)
  action n h := (𝒟).saving 𝒸 (shockAt z (KSModel.labelOf ⟨default, []⟩ n h).node)
    ((𝒟).capPath 𝒸 z k (KSModel.labelOf ⟨default, []⟩ n h).node)
  state_zero _ := rfl
  action_mem n h := by
    set g := (KSModel.labelOf (⟨default, []⟩ : Label Z E) n h).node
    obtain ⟨hs0, hscap, -, -, -⟩ := (𝒟).saving_spec 𝒸 (shockAt z g) ((𝒟).capPath 𝒸 z k g)
    have hc := cash_eq V T hγ hLbox hβR z k (⟨((𝒟).capPath 𝒸 z k g : ℝ),
      ((𝒟).capPath 𝒸 z k g).2⟩, KSModel.labelOf ⟨default, []⟩ n h) rfl
    have hgfp := (𝒟).gfp_cons (shockAt z g) ((𝒟).capPath 𝒸 z k g)
    have hm := (𝒸).2.1 (shockAt z g) ((𝒟).capPath 𝒸 z k g)
    have hfl := consFloor_lt_m V T hγ hLbox hβR
    refine ⟨hs0, le_min hscap ?_⟩
    change _ ≤ (𝕄).cash z (colemanPrices V T hγ hLbox hβR z k) _ - (𝕄).consFloor
    rw [hc]
    linarith
  state_succ n h ze := by
    refine Prod.ext (Subtype.ext ?_) ?_
    · change ((𝒟).capPath 𝒸 z k (KSModel.labelOf ⟨default, []⟩ (n + 1) (Fin.snoc h ze)).node : ℝ)
        = ((𝕄).clampAssets ((𝒟).saving 𝒸 (shockAt z (KSModel.labelOf ⟨default, []⟩ n h).node)
          ((𝒟).capPath 𝒸 z k (KSModel.labelOf ⟨default, []⟩ n h).node)) : ℝ)
      rw [KSModel.labelOf_snoc, (𝕄).clampAssets_of_mem
        ⟨((𝒟).saving_spec _ _ _).1, ((𝒟).saving_spec _ _ _).2.1⟩]
      rfl
    · exact KSModel.labelOf_snoc _ n h ze

/-- **Consumption along the Coleman plan is the Coleman fixed point.** -/
theorem colemanPlan_cons (z : Z) (k : (𝒟).Box) (n : ℕ) (h : Fin n → Z × E) :
    KSModel.planCons z (colemanPrices V T hγ hLbox hβR z k) (colemanPlan V T hγ hLbox hβR z k) n h
      = (𝒸).1 (shockAt z (KSModel.labelOf ⟨default, []⟩ n h).node)
        ((𝒟).capPath 𝒸 z k (KSModel.labelOf ⟨default, []⟩ n h).node) := by
  rw [KSModel.planCons, (𝒟).gfp_cons]
  rw [cash_eq V T hγ hLbox hβR z k _ rfl]
  rfl

/-- **The household's expected marginal value is the Coleman continuation.** -/
theorem nextMU_eq (z : Z) (k : (𝒟).Box) (n : ℕ) (h : Fin n → Z × E) :
    V.discount * KSModel.nextMU z (colemanPrices V T hγ hLbox hβR z k)
        (crraSmoothUtility V T hγ) (colemanPlan V T hγ hLbox hβR z k) n h
      = (𝒟).cont 𝒸 (shockAt z (KSModel.labelOf ⟨default, []⟩ n h).node)
        ((colemanPlan V T hγ hLbox hβR z k).action n h) := by
  set g := (KSModel.labelOf (⟨default, []⟩ : Label Z E) n h).node with hg
  set s := (colemanPlan V T hγ hLbox hβR z k).action n h with hs
  have hsmem : s ∈ Icc 0 (𝒟).cap :=
    ⟨((𝒟).saving_spec 𝒸 (shockAt z g) ((𝒟).capPath 𝒸 z k g)).1,
      ((𝒟).saving_spec 𝒸 (shockAt z g) ((𝒟).capPath 𝒸 z k g)).2.1⟩
  rw [KSModel.nextMU, Data.cont, Fintype.sum_prod_type]
  change V.discount * _ = V.discount * _
  congr 1
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [Fintype.sum_unique]
  have hidio : ∀ e, V.idioProb (shockAt z g) z' e default = 1 := fun e => by
    have := V.idioProb_sum (shockAt z g) z' e
    rwa [Fintype.sum_unique] at this
  have hcons := colemanPlan_cons V T hγ hLbox hβR z k (n + 1) (Fin.snoc h (z', default))
  rw [KSModel.labelOf_snoc] at hcons
  rw [hcons]
  have hext : (𝒟).ext 𝒸 z' s = (𝒸).1 z' ((𝒟).capPath 𝒸 z k (z' :: g)) := by
    rw [Data.ext, projIcc_of_mem _ hsmem]
    rfl
  rw [hext]
  change V.aggProb (shockAt z g) z'
      * V.idioProb (shockAt z g) z' (KSModel.labelOf (⟨default, []⟩ : Label Z E) n h).idio default
      * (T.grossReturn (shockAt z (z' :: g)) ((𝒟).capPath 𝒸 z k (z' :: g)) (V.efficiency default)
        * ((𝒸).1 (shockAt z (z' :: g)) ((𝒟).capPath 𝒸 z k (z' :: g))) ^ (-γ))
    = V.aggProb (shockAt z g) z' * T.grossReturn z' s (V.efficiency default)
      * ((𝒸).1 z' ((𝒟).capPath 𝒸 z k (z' :: g))) ^ (-γ)
  rw [hidio]
  change V.aggProb (shockAt z g) z' * 1
      * (T.grossReturn z' s (V.efficiency default)
        * ((𝒸).1 z' ((𝒟).capPath 𝒸 z k (z' :: g))) ^ (-γ)) = _
  ring

/-- **The Coleman plan satisfies the household's Euler conditions with the corners.** -/
theorem colemanPlan_euler (z : Z) (k : (𝒟).Box) :
    KSModel.PlanEuler z (colemanPrices V T hγ hLbox hβR z k) (crraSmoothUtility V T hγ)
      (colemanPlan V T hγ hLbox hβR z k) := by
  intro n h
  set g := (KSModel.labelOf (⟨default, []⟩ : Label Z E) n h).node with hg
  have hroot := (𝒟).saving_spec 𝒸 (shockAt z g) ((𝒟).capPath 𝒸 z k g)
  obtain ⟨-, -, -, h1, h2⟩ := hroot
  have hcons := colemanPlan_cons V T hγ hLbox hβR z k n h
  have hgfp := (𝒟).gfp_cons (shockAt z g) ((𝒟).capPath 𝒸 z k g)
  have hm := (𝒸).2.1 (shockAt z g) ((𝒟).capPath 𝒸 z k g)
  have hfl := consFloor_lt_m V T hγ hLbox hβR
  have hmu := nextMU_eq V T hγ hLbox hβR z k n h
  have hdisc : (𝕄).discount = V.discount := rfl
  have hdu : ∀ c, (crraSmoothUtility V T hγ).du c = (𝒟).du c := fun _ => rfl
  refine ⟨by rw [hcons]; linarith, fun ha => ?_, fun ha => ?_⟩
  · rw [hdisc, hmu, hdu, hcons, hgfp]
    exact h1 ha
  · rw [hdisc, hmu, hdu, hcons, hgfp]
    exact h2 ha

/-- **The household saves the Coleman saving**: at the prices of the Coleman path from `(z, k)`,
the household's optimal saving at capital `k` is the Coleman saving. -/
theorem policy_eq_saving (z : Z) (k : (𝒟).Box) :
    (𝕄).policy z (colemanPrices V T hγ hLbox hβR z k) (rootOf V T hγ hLbox hβR k)
      = (𝒟).saving 𝒸 z k := by
  have hD : ∀ n h, (crraSmoothUtility V T hγ).du (KSModel.planCons z
      (colemanPrices V T hγ hLbox hβR z k) (colemanPlan V T hγ hLbox hβR z k) n h)
      ≤ (𝒟).m ^ (-γ) := by
    intro n h
    rw [colemanPlan_cons]
    exact Real.rpow_le_rpow_of_nonpos (𝒟).m_pos ((𝒸).2.1 _ _) (by linarith)
  exact KSModel.policy_eq_of_euler z _ _ rfl (colemanPlan_euler V T hγ hLbox hβR z k) hD
    Fin.elim0

/-- The household at a point mass on the tree: the point mass is pushed along its saving. -/
noncomputable def repNode (z₀ : Z) (x₀ : (𝕄).AState) (Q : List Z → ℝ × ℝ) : List Z → (𝕄).AState
  | [] => x₀
  | _ :: h => (𝕄).nextA z₀ Q h default (repNode z₀ x₀ Q h)

/-- **From a point mass the distributions on the tree are point masses.** -/
theorem nodeDist_dirac (z₀ : Z) (x₀ : (𝕄).AState) (Q : List Z → ℝ × ℝ) :
    ∀ h, (𝕄).nodeDist z₀ (Measure.dirac x₀) Q h = Measure.dirac (repNode V T hγ z₀ x₀ Q h)
  | [] => rfl
  | z' :: h => by
    change (𝕄).pushNode z₀ Q h z' ((𝕄).nodeDist z₀ (Measure.dirac x₀) Q h) = _
    rw [nodeDist_dirac z₀ x₀ Q h, KSModel.pushNode_dirac]
    rfl

/-- **The Coleman capital path is a sequential equilibrium from every point mass**: the
representative-agent CRRA, Cobb–Douglas economy with one idiosyncratic state, labour inside its
box and `β R̄ ≤ 1`, for every capital share. -/
theorem isSequentialEquilibrium_capPath (z₀ : Z) (x₀ : (𝕄).AState) :
    (𝕄).IsSequentialEquilibrium z₀ (Measure.dirac x₀)
      (fun h => ((𝒟).capPath 𝒸 z₀ ⟨x₀.1.1, x₀.1.2⟩ h : ℝ)) := by
  set k₀ : (𝒟).Box := ⟨x₀.1.1, x₀.1.2⟩
  set K : List Z → ℝ := fun h => ((𝒟).capPath 𝒸 z₀ k₀ h : ℝ) with hK
  set m₀ := (𝕄).initMass (Measure.dirac x₀)
  have hQ : (𝕄).pricePath z₀ m₀ K = colemanPrices V T hγ hLbox hβR z₀ k₀ := by
    funext g
    simp only [KSModel.pricePath, colemanPrices, m₀, (𝕄).labour_unique]
    rfl
  -- the household's assets follow the Coleman path
  have hpath : ∀ h, ((repNode V T hγ z₀ x₀ (colemanPrices V T hγ hLbox hβR z₀ k₀) h).1 : ℝ)
      = (𝒟).capPath 𝒸 z₀ k₀ h := by
    intro h
    induction h with
    | nil => rfl
    | cons z' h ih =>
      set x := repNode V T hγ z₀ x₀ (colemanPrices V T hγ hLbox hβR z₀ k₀) h
      have hshift : shiftPath (colemanPrices V T hγ hLbox hβR z₀ k₀) h
          = colemanPrices V T hγ hLbox hβR (shockAt z₀ h) ((𝒟).capPath 𝒸 z₀ k₀ h) := by
        funext g
        simp only [shiftPath_apply, colemanPrices, Data.capPath_append 𝒟 𝒸 z₀ k₀ g h]
      have hx1 : x.1 = ⟨((𝒟).capPath 𝒸 z₀ k₀ h : ℝ), ((𝒟).capPath 𝒸 z₀ k₀ h).2⟩ :=
        Subtype.ext ih
      have hval : ((repNode V T hγ z₀ x₀ (colemanPrices V T hγ hLbox hβR z₀ k₀) (z' :: h)).1 : ℝ)
          = (𝕄).policy (shockAt z₀ h) (shiftPath (colemanPrices V T hγ hLbox hβR z₀ k₀) h)
            (x.1, ⟨default, []⟩) := by
        rw [(𝕄).policy_shift z₀ (colemanPrices V T hγ hLbox hβR z₀ k₀) h]
        change (((𝕄).clampAssets ((𝕄).policy z₀ (colemanPrices V T hγ hLbox hβR z₀ k₀)
          (x.1, ⟨x.2.idio, h⟩)) : ℝ)) = _
        rw [(𝕄).clampAssets_of_mem ((𝕄).policy_mem_Icc z₀ _ _), Unique.eq_default x.2.idio]
        rfl
      rw [hval, hshift, hx1]
      exact policy_eq_saving V T hγ hLbox hβR (shockAt z₀ h) ((𝒟).capPath 𝒸 z₀ k₀ h)
  intro h
  rw [KSModel.meanCapital, hQ, nodeDist_dirac, integral_dirac]
  exact (hpath h).symm

end Coleman

end KrusellSmith

end LeanEconomics
