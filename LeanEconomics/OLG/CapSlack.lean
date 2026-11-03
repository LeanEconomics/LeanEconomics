/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.IntervalEuler

/-!
# The cap is slack through a finite life, from impatience against the cap

Several results of the life cycle are stated under the hypothesis that the artefactual asset
cap is slack at every stage. For a household patient at the rate --- `βR > 1`, which a
life-cycle equilibrium rate above the rate of time preference is --- that is false for long
enough horizons: the infinite-horizon household accumulates without bound and reaches any cap.
But a life is finite, and what is needed is slack at the stages of that life only.

`stagePolicy_lt_cap_of_impatience` gives it: if at every stage `k < K`

  `y_max + r·cap  <  κ_k (y_min + R·cap) / Þ`,

then the cap is slack at every stage `k ≤ K` on the whole capped interval. The proof is by
induction on the stage. Should a household at stage `k+1` be at the cap, its Euler equation above
the floor (it could always save less) puts `u'(m - cap) ≤ βR E u'(c_k(cap, ·))`, and the
propensity floor at stage `k` --- available on the regions where the cap is slack, which by
the induction hypothesis are the whole interval up to stage `k` --- makes tomorrow's consumption
at the cap at least `κ_k (y_min + R·cap)`. Rearranged, `m - cap ≥ κ_k (y_min + R·cap)/Þ`, and
`m ≤ y_max + R·cap`, against the hypothesis.

The file also supplies what the hypothesis needs at a calibration: `stageMPC` is antitone in
the stage (`stageMPC_succ_le`), and it is bounded below from a rational upper bound on `Þ`
through the geometric sum of `mpcSum` (`stageMPC_ge_of_patience_le`); and it restates
concavity of stage consumption for stages `k ≤ K` from slack up to `K` only
(`concaveOn_stageConsumption_le`), which is what the enclosure certificate uses.
-/

open Set

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- Slack at every stage up to `K`, on the whole capped interval. -/
def SlackUpTo (K : ℕ) : Prop :=
  ∀ j ≤ K, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, P.stagePolicy j (a, z) < assetCap

/-- The whole interval up to stage `K` and nothing beyond: a reachable family whenever the cap is
slack up to `K`. -/
def truncRegions (K : ℕ) (hslack : P.SlackUpTo K) : P.StageRegions where
  region := fun j => if j ≤ K then Icc (0 : ℝ) assetCap else ∅
  subset := fun j => by
    by_cases hj : j ≤ K
    · simp [hj]
    · simp [hj]
  maps := fun k a ha z => by
    by_cases hk : k + 1 ≤ K
    · have hk' : k ≤ K := by omega
      simp only [hk, ite_true] at ha
      simp only [hk', ite_true]
      exact P.stagePolicy_mem_region _ _
    · simp [hk] at ha
  slack := fun k a ha z => by
    by_cases hk : k ≤ K
    · simp only [hk, ite_true] at ha
      exact hslack k hk a ha z
    · simp [hk] at ha

theorem truncRegions_region_of_le (K : ℕ) (hslack : P.SlackUpTo K) {j : ℕ} (hj : j ≤ K) :
    (P.truncRegions K hslack).region j = Icc (0 : ℝ) assetCap := by
  simp [truncRegions, hj]

/-- **Carroll–Kimball for stages up to `K`, from slack up to `K`.** -/
theorem concaveOn_stageConsumption_le {γ : ℝ} (hpc : P.PositiveConsumptionAll) (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ) (K : ℕ) (hslack : P.SlackUpTo K) :
    ∀ k ≤ K, ∀ z : Z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap) (P.stageConsumption k z) := by
  intro k
  induction k with
  | zero => intro _ z; exact P.concaveOn_consumptionFnOf_zero z
  | succ k ih =>
    intro hk z
    have hk' : k ≤ K := by omega
    have hnext : ∀ a ∈ Icc (0 : ℝ) assetCap,
        P.policyOf (P.toExtended.bellman (P.stageValue k)) (a, z) < P.maxSaving (a, z) := by
      intro a ha
      rw [← P.stageValue_succ]
      exact P.policyOf_lt_maxSaving hpc (P.concaveSlices_stageValue (k + 1)) ha
        (hslack (k + 1) hk a ha z)
    show ConcaveOn ℝ _ (P.consumptionFnOf (P.stageValue (k + 1)) z)
    rw [P.stageValue_succ]
    exact P.concaveOn_consumptionFnOf_bellman hγ0 hβ hu z
      (fun z' A hA => hpc _ (P.concaveSlices_stageValue k) z' A hA) (fun z' => ih hk' z')
      (fun z' x hx y hy hxy => P.consumptionFnOf_mono (P.concaveSlices_stageValue k) hx hy hxy)
      (fun a ha => hpc _ (P.concaveSlices_bellman (P.concaveSlices_stageValue k)) z a ha) hnext
      fun A hA z' => P.policyOf_lt_maxSaving hpc (P.concaveSlices_stageValue k) hA
        (hslack k hk' A hA z')

/-! ### The propensity is antitone in the stage, and bounded below -/

/-- `κ_{k+1} ≤ κ_k`: the propensity to consume falls as the horizon lengthens. -/
theorem stageMPC_succ_le {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (k : ℕ) :
    P.stageMPC γ (k + 1) ≤ P.stageMPC γ k := by
  have hκ := P.stageMPC_pos hγ0 hβ k
  have hT := P.patience_pos' hγ0 hβ
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hmin := P.minMPC_le_stageMPC hγ0 hβ k
  have hmin' : 1 - P.patience γ / (1 + P.interest) ≤ P.stageMPC γ k := hmin
  rw [stageMPC_succ, div_le_iff₀ (by positivity)]
  have h1 : 1 + P.interest ≤ P.patience γ + P.stageMPC γ k * (1 + P.interest) := by
    have h := mul_le_mul_of_nonneg_right (sub_le_iff_le_add.1 hmin') hR.le
    have hdiv : P.patience γ / (1 + P.interest) * (1 + P.interest) = P.patience γ :=
      div_mul_cancel₀ _ hR.ne'
    nlinarith [h, hdiv]
  nlinarith [mul_le_mul_of_nonneg_left h1 hκ.le]

theorem stageMPC_antitone {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) {j k : ℕ}
    (hjk : j ≤ k) : P.stageMPC γ k ≤ P.stageMPC γ j := by
  induction k with
  | zero =>
    have : j = 0 := Nat.le_zero.1 hjk
    subst this; exact le_rfl
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact le_trans (P.stageMPC_succ_le hγ0 hβ k) (ih (by omega))
    · have : j = k + 1 := by omega
      subst this; exact le_rfl

/-- `Þ ≤ t` from `βR ≤ t^γ`. -/
theorem patience_le_of_le_rpow {γ t : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (ht : 0 < t)
    (h : (P.discount : ℝ) * (1 + P.interest) ≤ t ^ γ) : P.patience γ ≤ t := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR : (0 : ℝ) ≤ (P.discount : ℝ) * (1 + P.interest) := by positivity
  calc P.patience γ = ((P.discount : ℝ) * (1 + P.interest)) ^ (1 / γ) := rfl
    _ ≤ (t ^ γ) ^ (1 / γ) := Real.rpow_le_rpow hβR h (by positivity)
    _ = t := by rw [← Real.rpow_mul ht.le, mul_one_div_cancel hγ0.ne', Real.rpow_one]

/-- **A lower bound on `κ_K` from an upper bound on `Þ`**, through the geometric sum. -/
theorem stageMPC_ge_of_patience_le {γ t : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (ht : P.patience γ ≤ t) (K : ℕ) :
    1 / ∑ i ∈ Finset.range (K + 1), (t / (1 + P.interest)) ^ i ≤ P.stageMPC γ K := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hT := P.patience_pos' hγ0 hβ
  have hq : 0 ≤ P.patience γ / (1 + P.interest) := by positivity
  have hle : P.mpcSum γ K ≤ ∑ i ∈ Finset.range (K + 1), (t / (1 + P.interest)) ^ i := by
    unfold mpcSum
    refine Finset.sum_le_sum fun i _ => ?_
    exact pow_le_pow_left₀ hq (div_le_div_of_nonneg_right ht hR.le) i
  have hSpos : 0 < P.mpcSum γ K := by
    unfold mpcSum
    exact Finset.sum_pos (fun i _ => pow_pos (by positivity) i)
      ⟨0, Finset.mem_range.2 (Nat.succ_pos K)⟩
  have hκ := P.stageMPC_mul_mpcSum hγ0 hβ K
  have hκeq : P.stageMPC γ K = 1 / P.mpcSum γ K := by
    field_simp; linarith [hκ]
  rw [hκeq]
  exact one_div_le_one_div_of_le hSpos hle

/-! ### Slack at every stage of a finite life -/

/-- **The cap is slack up to `K` if the household is impatient against the cap at every stage
below `K`.** -/
theorem stagePolicy_lt_cap_of_impatience {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (hd : P.Unbounded) (hcap : 0 < assetCap) (K : ℕ)
    (hcond : ∀ k < K, P.maxIncome + P.interest * assetCap
      < P.stageMPC γ k * (P.minIncome + (1 + P.interest) * assetCap) / P.patience γ) :
    P.SlackUpTo K := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hT := P.patience_pos' hγ0 hβ
  have hβR : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hTpow : (P.patience γ) ^ γ = (P.discount : ℝ) * (1 + P.interest) := by
    rw [patience, ← Real.rpow_mul hβR.le, one_div_mul_cancel hγ0.ne', Real.rpow_one]
  -- the induction carries slack at every stage up to k
  have main : ∀ k, k ≤ K → P.SlackUpTo k := by
    intro k
    induction k with
    | zero =>
      intro _ j hj a ha z
      have : j = 0 := by omega
      subst this
      rw [P.stagePolicy_zero ha z]; exact hcap
    | succ k ih =>
      intro hk j hj a ha z
      have hk' : k ≤ K := by omega
      have ihk := ih hk'
      rcases Nat.lt_or_ge j (k + 1) with hjlt | hjge
      · exact ihk j (by omega) a ha z
      have hj' : j = k + 1 := by omega
      subst hj'
      by_contra hcon
      push Not at hcon
      set g := P.stagePolicy (k + 1) (a, z) with hg
      have hgmem : g ∈ Icc (0 : ℝ) assetCap := P.stagePolicy_mem_region _ _
      have hgeq : g = assetCap := le_antisymm hgmem.2 hcon
      have hgpos : 0 < g := by rw [hgeq]; exact hcap
      -- Euler above the floor at the cap
      have hslackg : ∀ z', P.stagePolicy k (g, z') < P.maxSaving (g, z') := fun z' =>
        P.policyOf_lt_maxSaving_of_pos (P.stageConsumption_pos hd k z' hgmem)
          (ihk k le_rfl g hgmem z')
      have heul := P.stage_euler_ge hu hd k z ha hgpos hslackg
      -- tomorrow's consumption at the cap is at least `κ_k (y_min + R cap)`
      set L := P.stageMPC γ k * (P.minIncome + (1 + P.interest) * assetCap) with hL
      have hκ := P.stageMPC_pos hγ0 hβ k
      have hLpos : 0 < L := by
        have := P.minIncome_pos
        positivity
      have hlow : ∀ z', L ≤ P.stageConsumption k z' g := by
        intro z'
        have hreg : g ∈ (P.truncRegions k ihk).region k := by
          rw [P.truncRegions_region_of_le k ihk le_rfl]; exact hgmem
        have h := P.stageMPC_mul_le_stageConsumption_on hγ0 hu hβ hd (P.truncRegions k ihk)
          k z' hreg
        rw [P.resources_eq_of_mem hgmem z', hgeq] at h
        have hy := P.minIncome_le z'
        have h' : P.stageMPC γ k * (P.minIncome + (1 + P.interest) * assetCap)
            ≤ P.stageMPC γ k * (P.income z' + (1 + P.interest) * assetCap) :=
          mul_le_mul_of_nonneg_left (add_le_add hy le_rfl) hκ.le
        rw [hL, hgeq]
        exact le_trans h' h
      have h2 : P.eulerSum γ z (fun z' => P.stageConsumption k z' g)
          ≤ P.eulerSum γ z (fun _ => L) :=
        P.eulerSum_anti hγ0 z (fun _ => hLpos) hlow
      have h3 : P.eulerSum γ z (fun _ => L) = (L / P.patience γ) ^ (-γ) := by
        unfold eulerSum
        rw [← Finset.sum_mul, P.transitionMatrix_sum z, one_mul, Real.div_rpow hLpos.le hT.le,
          Real.rpow_neg hT.le, hTpow]
        field_simp
      have h4 : (P.stageConsumption (k + 1) z a) ^ (-γ) ≤ (L / P.patience γ) ^ (-γ) := by
        rw [← h3]
        refine le_trans ?_ h2
        unfold eulerSum
        exact heul
      have hc : 0 < P.stageConsumption (k + 1) z a := P.stageConsumption_pos hd _ z ha
      have h5 : L / P.patience γ ≤ P.stageConsumption (k + 1) z a :=
        le_of_rpow_neg_le hc (by positivity) hγ0 h4
      -- but consumption at the cap is at most `y_max + r cap`
      have h6 : P.stageConsumption (k + 1) z a ≤ P.maxIncome + P.interest * assetCap := by
        rw [P.stageConsumption_eq, P.resources_eq_of_mem ha z, ← hg, hgeq]
        have := P.le_maxIncome z
        nlinarith [ha.2, hR]
      have h7 := hcond k (by omega)
      rw [← hL] at h7
      linarith
  exact main K le_rfl

end IncomeFluctuation

end LeanEconomics
