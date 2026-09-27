/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.EnclStage
import LeanEconomics.OLG.Increment
import Mathlib.Algebra.Field.GeomSum

/-!
# The enclosure certificate: from the checker's verdict to the increment bound

Everything the certificate `enclCheckOf R1 R2 = true` asserts is turned into the hypotheses of
`olgCapital_sub_ge_of_failure` for the seven-state economy `olg7` at `4%` against its copy at
`4.6%`: the stage enclosures (`EnclStage`), cap slack from impatience (`CapSlack`), the reach
regions, the failure bounds `V`, the Lipschitz constants `G`, and the accumulated bound against
the fall in the firm's demand. The conclusion is the pairwise single-crossing inequality
`D(r₂) - D(r₁) < S(r₂) - S(r₁)` between the two rates.
-/

open Set

namespace LeanEconomics.EnclCert

open IncomeFluctuation

/-! ### Small facts about `val` and the checker's combinators -/

theorem val_le_val_iff {m n : ℕ} : val m ≤ val n ↔ m ≤ n := by
  unfold val
  rw [div_le_div_iff_of_pos_right D_pos]
  exact Nat.cast_le

theorem val_sub_ge (a b : ℕ) : val a - val b ≤ val (a - b) := by
  unfold val
  rcases le_or_gt b a with h | h
  · rw [Nat.cast_sub h, sub_div]
  · have : a - b = 0 := by omega
    rw [this, Nat.cast_zero, zero_div]
    have := D_pos
    have hab : (a : ℝ) ≤ b := by exact_mod_cast h.le
    have : (a : ℝ) / D ≤ (b : ℝ) / D := div_le_div_of_nonneg_right hab this.le
    linarith

theorem le_max7 (f : ℕ → ℕ) : ∀ n < 7, f n ≤ max7 f := by
  intro n hn
  unfold max7
  interval_cases n <;> omega

theorem le_maxRange (f : ℕ → ℕ) : ∀ n i, i < n → f i ≤ maxRange f n := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    simp only [maxRange]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact le_trans (ih i h) (le_max_left _ _)
    · subst h; exact le_max_right _ _

theorem sumRange_cast (f : ℕ → ℚ) :
    ∀ n, ((sumRange f n : ℚ) : ℝ) = ∑ k ∈ Finset.range n, (f k : ℝ) := by
  intro n
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, Finset.sum_range_succ, Rat.cast_add, ih]

theorem geomSum_cast (q : ℚ) :
    ∀ n, ((geomSum q n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (q : ℝ) ^ i := by
  intro n
  induction n with
  | zero => simp [geomSum]
  | succ n ih => rw [geomSum, Finset.sum_range_succ, Rat.cast_add, ih, Rat.cast_pow]

theorem slopeUp_cast (Rb : ℕ × ℕ) (kap : ℚ) : ∀ k, ((slopeUp Rb kap k : ℚ) : ℝ)
    = (if k = 0 then 1 else 1 + (slopeUp Rb kap (k - 1) : ℝ) * (1 - (kap : ℝ)) * rate Rb) := by
  intro k
  cases k with
  | zero => simp [slopeUp]
  | succ k => simp [slopeUp, rate]

theorem nuSum_cast (f : ℕ → ℚ) :
    ((nuSum f : ℚ) : ℝ) = ∑ z : Fin 7, (nuQ z : ℝ) * (f z : ℝ) := by
  unfold nuSum
  rw [sumRange_cast, show nz = 7 from rfl,
    ← Fin.sum_univ_eq_sum_range (fun n => ((((nuN n).1 : ℚ) / (nuN n).2 * f n : ℚ) : ℝ)) 7]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [nuQ]
  push_cast
  ring

/-- Every asset level below the cap lies in some grid interval. -/
theorem exists_bracket (hg : gridOK () = true) {x : ℝ} (hx0 : 0 ≤ x) (hxC : x < val CAP) :
    ∃ i, i + 1 < NA ∧ val grid[i]! ≤ x ∧ x ≤ val grid[i+1]! := by
  obtain ⟨h0, htop, _⟩ := gridOK_facts hg
  have hNA : 2 ≤ NA := by
    by_contra hlt
    have : NA - 1 = 0 := by omega
    rw [this, h0] at htop
    exact absurd htop (by norm_num [CAP, D])
  have key : ∀ n i, i + n = NA - 1 → val grid[i]! ≤ x →
      ∃ j, j + 1 < NA ∧ val grid[j]! ≤ x ∧ x ≤ val grid[j+1]! := by
    intro n
    induction n with
    | zero =>
      intro i hi hix
      have : i = NA - 1 := by omega
      rw [this, htop] at hix
      exact absurd hxC (not_lt.mpr hix)
    | succ n ih =>
      intro i hi hix
      rcases le_or_gt x (val grid[i+1]!) with hle | hlt
      · exact ⟨i, by omega, hix, hle⟩
      · exact ih (i + 1) (by omega) hlt.le
  exact key (NA - 1) 0 (by omega) (by rw [h0, val_zero]; exact hx0)

/-! ### The two economies -/

/-- The higher-rate copy of `olg7`, at `4.6%`. -/
noncomputable def olg7hi : IncomeFluctuation (Fin 7) 0 2000 :=
  olg7.withRate (23 / 500) olg7_rateOK_high

theorem olg7hi_unbounded : olg7hi.Unbounded := olg7_unbounded

theorem matches_low : Matches olg7 R1 where
  rate := by norm_num [rate, R1]
  income := fun z => rfl
  trans := fun z z' => rfl
  disc := by norm_num
  u := rfl
  unb := olg7_unbounded

theorem matches_high : Matches olg7hi R2 where
  rate := by simp only [olg7hi, withRate_interest]; norm_num [rate, R2]
  income := fun z => rfl
  trans := fun z z' => rfl
  disc := by simp only [olg7hi, withRate_discount]; norm_num
  u := rfl
  unb := olg7hi_unbounded

theorem olg7hi_transitionMatrix : olg7hi.transitionMatrix = olg7.transitionMatrix := rfl

/-! ### Cap slack from impatience, numerically -/

/-- Slack up to stage `59` from a bound `t` on patience and a floor `kap` on the propensity. -/
theorem slackUpTo_of_numeric {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ}
    (hM : Matches P R) {t : ℝ} (ht0 : 0 < t) (htp : (24 / 25 : ℝ) * rate R ≤ t ^ (3 : ℝ))
    {kap : ℝ} (hk : kap ≤ 1 / ∑ i ∈ Finset.range (59 + 1), (t / rate R) ^ i)
    (hnum : P.maxIncome + P.interest * 2000 < kap * (P.minIncome + rate R * 2000) / t) :
    P.SlackUpTo 59 := by
  have hγ : (0 : ℝ) < 3 := by norm_num
  have hβ := hM.disc_pos
  have hÞ : P.patience 3 ≤ t :=
    P.patience_le_of_le_rpow hγ hβ ht0 (by rw [hM.disc, hM.rate]; exact htp)
  have hÞ0 : 0 < P.patience 3 := P.patience_pos' hγ hβ
  have hκ : ∀ k < 59, kap ≤ P.stageMPC 3 k := by
    intro k hk'
    refine le_trans hk (le_trans ?_ (P.stageMPC_antitone hγ hβ hk'.le))
    have h59 := P.stageMPC_ge_of_patience_le hγ hβ hÞ 59
    rw [hM.rate] at h59
    exact h59
  refine P.stagePolicy_lt_cap_of_impatience hγ hM.u hβ hM.unb (by norm_num) 59 ?_
  intro k hk'
  have hX : 0 ≤ P.minIncome + (1 + P.interest) * 2000 := by
    have := P.minIncome_pos
    have : 0 < 1 + P.interest := P.interest_gt_neg_one
    positivity
  calc P.maxIncome + P.interest * 2000
      < kap * (P.minIncome + rate R * 2000) / t := hnum
    _ = kap * (P.minIncome + (1 + P.interest) * 2000) / t := by rw [hM.rate]
    _ ≤ P.stageMPC 3 k * (P.minIncome + (1 + P.interest) * 2000) / t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hκ k hk') hX) ht0.le
    _ ≤ P.stageMPC 3 k * (P.minIncome + (1 + P.interest) * 2000) / P.patience 3 :=
        div_le_div_of_nonneg_left (mul_nonneg (P.stageMPC_pos hγ hβ k).le hX) hÞ0 hÞ

theorem slack_low : olg7.SlackUpTo 59 := by
  refine slackUpTo_of_numeric matches_low (t := 100139 / 100000) (by norm_num) ?_
    (kap := 1 / ∑ i ∈ Finset.range (59 + 1), ((100139 / 100000 : ℝ) / rate R1) ^ i) le_rfl ?_
  · rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num [rate, R1]
  · refine lt_of_lt_of_le
      (b := (413 / 10000 : ℝ) * (olg7.minIncome + rate R1 * 2000) / (100139 / 100000)) ?_ ?_
    · simp only [olg7_maxIncome, olg7_minIncome, olg7_interest]; norm_num [rate, R1]
    · refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_) (by norm_num)
      · rw [geom_sum_eq (by norm_num [rate, R1]) (59 + 1)]; norm_num [rate, R1]
      · simp only [olg7_minIncome]; norm_num [rate, R1]

theorem slack_high : olg7hi.SlackUpTo 59 := by
  refine slackUpTo_of_numeric matches_high (t := 100139 / 100000) (by norm_num) ?_
    (kap := 1 / ∑ i ∈ Finset.range (59 + 1), ((100139 / 100000 : ℝ) / rate R2) ^ i) le_rfl ?_
  · rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num [rate, R2]
  · refine lt_of_lt_of_le
      (b := (459 / 10000 : ℝ) * (olg7hi.minIncome + rate R2 * 2000) / (100139 / 100000)) ?_ ?_
    · simp only [olg7hi, withRate_maxIncome, withRate_minIncome, withRate_interest,
        olg7_maxIncome, olg7_minIncome]; norm_num [rate, R2]
    · refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_) (by norm_num)
      · rw [geom_sum_eq (by norm_num [rate, R2]) (59 + 1)]; norm_num [rate, R2]
      · simp only [olg7hi, withRate_minIncome, olg7_minIncome]; norm_num [rate, R2]

/-! ### The Lipschitz constants -/

theorem cohortSlope_nonneg {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ} (hM : Matches P R) :
    ∀ k, 0 ≤ P.cohortSlope 3 k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [cohortSlope_succ]
    have h1 := P.stageMPC_le_one (γ := 3) (by norm_num) hM.disc_pos (k + 1)
    have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
    have := mul_nonneg (mul_nonneg ih (sub_nonneg.mpr h1)) hR.le
    linarith

/-- `cohortSlope ≤ slopeUp` up to stage `59`, given the propensity floor. -/
theorem cohortSlope_le_slopeUp {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ}
    (hM : Matches P R) {kap : ℚ} (hκ : ∀ k ≤ 59, (kap : ℝ) ≤ P.stageMPC 3 k) :
    ∀ k ≤ 59, P.cohortSlope 3 k ≤ ((slopeUp R kap k : ℚ) : ℝ) := by
  intro k
  induction k with
  | zero => intro _; simp [slopeUp]
  | succ k ih =>
    intro hk
    rw [cohortSlope_succ, slopeUp_cast, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, ← hM.rate]
    have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
    have h1 : 1 - P.stageMPC 3 (k + 1) ≤ 1 - (kap : ℝ) := by linarith [hκ (k + 1) hk]
    have h2 : 0 ≤ 1 - P.stageMPC 3 (k + 1) := by
      linarith [P.stageMPC_le_one (γ := 3) (by norm_num) hM.disc_pos (k + 1)]
    have h3 := ih (by omega)
    have h4 := cohortSlope_nonneg hM k
    have := mul_le_mul h3 h1 h2 (by linarith [h3, h4])
    have := mul_le_mul_of_nonneg_right this hR.le
    linarith

theorem kapLo_le_stageMPC_high : ∀ k ≤ 59, ((kapLoOf R2 : ℚ) : ℝ) ≤ olg7hi.stageMPC 3 k := by
  intro k hk
  have hγ : (0 : ℝ) < 3 := by norm_num
  have hβ := matches_high.disc_pos
  have hÞ : olg7hi.patience 3 ≤ (tUp : ℝ) := by
    refine olg7hi.patience_le_of_le_rpow hγ hβ (by norm_num [tUp]) ?_
    rw [matches_high.disc, matches_high.rate, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num [rate, R2, tUp]
  refine le_trans ?_ (olg7hi.stageMPC_antitone hγ hβ hk)
  have := olg7hi.stageMPC_ge_of_patience_le hγ hβ hÞ 59
  rw [matches_high.rate] at this
  refine le_trans (le_of_eq ?_) this
  unfold kapLoOf
  rw [Rat.cast_div, Rat.cast_one, geomSum_cast,
    show Finset.range J = Finset.range (59 + 1) from rfl]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [rate, R2]
  push_cast
  ring

/-! ### The regions of the lower-rate economy -/

/-- The joint reach the checker uses. -/
def reachR (arr1 arr2 : Array Stage) (j : ℕ) : ℕ := max (reachOf R1 arr1 j) (reachOf R2 arr2 j)

theorem J_eq : J = 60 := rfl

/-- The reach regions: at stage `k` a cohort is `J - 1 - k` periods old. -/
noncomputable def encRegions (arr1 : Array Stage) (hg : gridOK () = true)
    (henc : ∀ k < J, StageEnc olg7 k arr1[k]!)
    (hreach : ∀ j < J, reachOf R1 arr1 j < CAP) (hsl : olg7.SlackUpTo 59) :
    olg7.StageRegions where
  region k := if k ≤ 59 then Icc (0 : ℝ) (val (reachOf R1 arr1 (J - 1 - k))) else ∅
  subset k := by
    have hJ := J_eq
    by_cases hk : k ≤ 59
    · simp only [hk, ite_true]
      intro a ha
      refine ⟨ha.1, le_trans ha.2 ?_⟩
      rw [← val_CAP]
      exact val_le_val (hreach _ (by omega)).le
    · simp [hk]
  maps k a ha z := by
    have hJ := J_eq
    by_cases hk : k + 1 ≤ 59
    · have hk' : k ≤ 59 := by omega
      simp only [hk, ite_true] at ha
      simp only [hk', ite_true]
      set j := J - 1 - (k + 1) with hj
      have hj1 : J - 1 - k = j + 1 := by omega
      have hjk : J - 1 - j = k + 1 := by omega
      have hr : reachOf R1 arr1 j < CAP := hreach j (by omega)
      have hrI : val (reachOf R1 arr1 j) ∈ Icc (0 : ℝ) 2000 := val_mem _ hr.le
      have haI : a ∈ Icc (0 : ℝ) 2000 := ⟨ha.1, le_trans ha.2 hrI.2⟩
      refine ⟨(olg7.stagePolicy_mem_region _ _).1, ?_⟩
      rw [hj1, reachOf, hjk]
      have h1 := olg7.stagePolicy_mono (k + 1) (z := z) haI hrI ha.2
      have h2 : olg7.stagePolicy (k + 1) (val (reachOf R1 arr1 j), z)
          ≤ val (mUp R1 z (reachOf R1 arr1 j))
            - val (encLo R1 arr1[k+1]! z (reachOf R1 arr1 j)) := by
        have hc := olg7.stageConsumption_eq (k + 1) z (val (reachOf R1 arr1 j))
        have hm : olg7.resources (val (reachOf R1 arr1 j), z)
            ≤ val (mUp R1 z (reachOf R1 arr1 j)) := by
          rw [resources_val olg7 R1 matches_low.rate matches_low.income z _ hr.le]
          exact le_mUp R1 matches_low.den z _
        have hl := encLo_sound olg7 R1 matches_low.rate matches_low.income
          hg (k + 1) arr1[k+1]! (stageConsumption_monotoneOn olg7 (k + 1))
          (stageConsumption_concaveOn matches_low (k + 1) (fun j hj => hsl j (by omega)))
          (stageConsumption_nonneg_on olg7 olg7_unbounded (k + 1)) (henc (k + 1) (by omega)) z
          _ hr.le
        linarith
      refine le_trans h1 (le_trans h2 (le_trans (val_sub_ge _ _) ?_))
      exact val_le_val (le_max7 (fun w => mUp R1 w (reachOf R1 arr1 j)
        - encLo R1 arr1[k+1]! w (reachOf R1 arr1 j)) z z.2)
    · simp [hk] at ha
  slack k a ha z := by
    have hJ := J_eq
    by_cases hk : k ≤ 59
    · simp only [hk, ite_true] at ha
      refine hsl k hk a ⟨ha.1, le_trans ha.2 ?_⟩ z
      rw [← val_CAP]
      exact val_le_val (hreach _ (by omega)).le
    · simp [hk] at ha

/-! ### The failure bounds -/

/-- The certificate's failure bound at stage `k`, for `1 ≤ k ≤ 59`, at the joint reach of the
cohort that is `J - 1 - k` periods old. -/
noncomputable def failV (arr1 arr2 : Array Stage) (k : ℕ) (z : Fin 7) : ℝ :=
  if 1 ≤ k ∧ k ≤ 59 then
    val (failBound R1 R2 arr1[k]! arr2[k]! (reachR arr1 arr2 (J - 1 - k)) z)
  else 0

theorem failV_nonneg (arr1 arr2 : Array Stage) (k : ℕ) (z : Fin 7) : 0 ≤ failV arr1 arr2 k z := by
  unfold failV
  split_ifs
  · exact val_nonneg _
  · exact le_rfl

theorem drOf_val : ((drOf R1 R2).1 : ℝ) / (drOf R1 R2).2 = rate R2 - rate R1 := by
  norm_num [drOf, R1, R2, rate]

/-- **The failure bound is sound** on the reach regions: the lower-rate economy saves more than
the higher-rate one by at most `V`. -/
theorem failV_sound (arr1 arr2 : Array Stage) (hg : gridOK () = true)
    (henc1 : ∀ k < J, StageEnc olg7 k arr1[k]!) (henc2 : ∀ k < J, StageEnc olg7hi k arr2[k]!)
    (hreach : ∀ j < J, reachOf R1 arr1 j < CAP) (hsl : olg7.SlackUpTo 59) :
    ∀ k : ℕ, ∀ a ∈ (encRegions arr1 hg henc1 hreach hsl).region (k + 1), ∀ z : Fin 7,
      olg7.stagePolicy (k + 1) (a, z) - olg7hi.stagePolicy (k + 1) (a, z)
        ≤ failV arr1 arr2 (k + 1) z := by
  intro k a ha z
  have hJ := J_eq
  by_cases hk : k + 1 ≤ 59
  · simp only [encRegions, hk, ite_true] at ha
    unfold failV
    rw [if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ 59 from ⟨by omega, hk⟩)]
    set j := J - 1 - (k + 1) with hj
    have hr1 : reachOf R1 arr1 j < CAP := hreach j (by omega)
    have hrj : reachOf R1 arr1 j ≤ reachR arr1 arr2 j := le_max_left _ _
    have haC : a < val CAP := lt_of_le_of_lt ha.2 (val_lt_val hr1)
    obtain ⟨i, hi1, hgi, hgi1⟩ := exists_bracket hg ha.1 haC
    have hgiC : grid[i]! ≤ CAP := grid_le_CAP hg i (by omega)
    have hgi1C : grid[i+1]! ≤ CAP := grid_le_CAP hg _ hi1
    have haI : a ∈ Icc (0 : ℝ) 2000 := ⟨ha.1, le_trans ha.2 (val_mem _ hr1.le).2⟩
    have hgr : grid[i]! ≤ reachR arr1 arr2 j :=
      le_trans (val_le_val_iff.mp (le_trans hgi ha.2)) hrj
    have hc2 : olg7hi.stageConsumption (k + 1) z a ≤ val (at2 arr2[k+1]!.hi z (i + 1)) :=
      le_trans (olg7hi.stageConsumption_mono (k + 1) haI (val_mem _ hgi1C) hgi1)
        ((henc2 (k + 1) (by omega)).hi z (i + 1) hi1)
    have hc1 : val (at2 arr1[k+1]!.lo z i) ≤ olg7.stageConsumption (k + 1) z a :=
      le_trans ((henc1 (k + 1) (by omega)).lo z i (by omega))
        (olg7.stageConsumption_mono (k + 1) (val_mem _ hgiC) haI hgi)
    have hq : val (grid[i]! * (drOf R1 R2).1 / (drOf R1 R2).2) ≤ (rate R2 - rate R1) * a := by
      rw [← drOf_val]
      have h1 := natDiv_le_real (grid[i]! * (drOf R1 R2).1) (drOf R1 R2).2
      rw [Nat.cast_mul] at h1
      have hdr : (0 : ℝ) ≤ ((drOf R1 R2).1 : ℝ) / (drOf R1 R2).2 :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have h2 : val grid[i]! ≤ a := hgi
      unfold val at h2 ⊢
      calc ((grid[i]! * (drOf R1 R2).1 / (drOf R1 R2).2 : ℕ) : ℝ) / D
          ≤ ((grid[i]! : ℝ) * (drOf R1 R2).1 / (drOf R1 R2).2) / D :=
            div_le_div_of_nonneg_right h1 D_pos.le
        _ = ((drOf R1 R2).1 : ℝ) / (drOf R1 R2).2 * ((grid[i]! : ℝ) / D) := by ring
        _ ≤ ((drOf R1 R2).1 : ℝ) / (drOf R1 R2).2 * a := mul_le_mul_of_nonneg_left h2 hdr
    have hp1 : olg7.stagePolicy (k + 1) (a, z)
        = (yQ z : ℝ) + rate R1 * a - olg7.stageConsumption (k + 1) z a := by
      rw [olg7.stageConsumption_eq, olg7.resources_eq_of_mem haI z, matches_low.rate,
        matches_low.income]
      ring
    have hp2 : olg7hi.stagePolicy (k + 1) (a, z)
        = (yQ z : ℝ) + rate R2 * a - olg7hi.stageConsumption (k + 1) z a := by
      rw [olg7hi.stageConsumption_eq, olg7hi.resources_eq_of_mem haI z, matches_high.rate,
        matches_high.income]
      ring
    have hdiff : olg7.stagePolicy (k + 1) (a, z) - olg7hi.stagePolicy (k + 1) (a, z)
        ≤ val (at2 arr2[k+1]!.hi z (i + 1)) - val (at2 arr1[k+1]!.lo z i)
          - val (grid[i]! * (drOf R1 R2).1 / (drOf R1 R2).2) := by
      rw [hp1, hp2]
      linarith
    calc olg7.stagePolicy (k + 1) (a, z) - olg7hi.stagePolicy (k + 1) (a, z)
        ≤ val (at2 arr2[k+1]!.hi z (i + 1)) - val (at2 arr1[k+1]!.lo z i)
          - val (grid[i]! * (drOf R1 R2).1 / (drOf R1 R2).2) := hdiff
      _ ≤ val (at2 arr2[k+1]!.hi z (i + 1) - at2 arr1[k+1]!.lo z i)
          - val (grid[i]! * (drOf R1 R2).1 / (drOf R1 R2).2) := by
            linarith [val_sub_ge (at2 arr2[k+1]!.hi z (i + 1)) (at2 arr1[k+1]!.lo z i)]
      _ ≤ val (at2 arr2[k+1]!.hi z (i + 1) - at2 arr1[k+1]!.lo z i
          - grid[i]! * (drOf R1 R2).1 / (drOf R1 R2).2) := val_sub_ge _ _
      _ ≤ val (failBound R1 R2 arr1[k+1]! arr2[k+1]! (reachR arr1 arr2 j) z) := by
            apply val_le_val
            unfold failBound
            have := le_maxRange (fun i => if grid[i]! ≤ reachR arr1 arr2 j then
              at2 arr2[k+1]!.hi z (i + 1) - at2 arr1[k+1]!.lo z i
                - grid[i]! * (drOf R1 R2).1 / (drOf R1 R2).2 else 0) (NA - 1) i (by omega)
            simp only [if_pos hgr] at this
            exact this
  · simp [encRegions, hk] at ha

/-! ### The Lipschitz hypothesis at the higher rate -/

theorem kapLo_le_one : ((kapLoOf R2 : ℚ) : ℝ) ≤ 1 := by
  have := kapLo_le_stageMPC_high 0 (by norm_num)
  simpa [stageMPC] using this

theorem slopeUp_nonneg : ∀ k, 0 ≤ ((slopeUp R2 (kapLoOf R2) k : ℚ) : ℝ) := by
  intro k
  induction k with
  | zero => simp [slopeUp]
  | succ k ih =>
    rw [slopeUp_cast, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
    have h1 : (0 : ℝ) ≤ 1 - (kapLoOf R2 : ℝ) := by linarith [kapLo_le_one]
    have h2 : (0 : ℝ) ≤ rate R2 := by unfold rate; positivity
    have := mul_nonneg (mul_nonneg ih h1) h2
    linarith

theorem lip_high (hsl : olg7hi.SlackUpTo 59) :
    ∀ k < 59, ∀ (z : Fin 7) (a₁ a₂ : ℝ), a₁ ∈ Icc (0 : ℝ) 2000 → a₂ ∈ Icc (0 : ℝ) 2000 →
      a₁ ≤ a₂ → olg7hi.cohortAssets k (a₂, z) - olg7hi.cohortAssets k (a₁, z)
        ≤ ((slopeUp R2 (kapLoOf R2) k : ℚ) : ℝ) * (a₂ - a₁) := by
  intro k hk z a₁ a₂ h1 h2 h12
  have hs := olg7hi.cohortAssets_sub_le_cohortSlope (γ := 3) (by norm_num) matches_high.u
    matches_high.disc_pos olg7hi_unbounded k
    (fun j hj b hb w => policy_lt_maxSaving olg7hi olg7hi_unbounded j
      (fun c hc v => hsl j (by omega) c hc v) b hb w) z a₁ a₂ h1 h2 h12
  exact le_trans hs (mul_le_mul_of_nonneg_right
    (cohortSlope_le_slopeUp matches_high kapLo_le_stageMPC_high k hk.le) (by linarith))

/-! ### The invariant law, the accumulated bound and the budget -/

/-- The invariant law as reals. -/
noncomputable def nuR (z : Fin 7) : ℝ := (nuQ z : ℝ)

theorem nuR_nonneg (z : Fin 7) : 0 ≤ nuR z := by unfold nuR; exact_mod_cast nuQ_nonneg z

theorem nuR_invariant : ∀ z' : Fin 7, ∑ z, nuR z * olg7.transitionMatrix z z' = nuR z' := by
  intro z'
  simp only [nuR, olg7_transitionMatrix]
  exact_mod_cast nuQ_invariant z'

theorem accumulated_cast (arr1 arr2 : Array Stage) :
    ((accumulated R1 R2 arr1 arr2 (reachR arr1 arr2) : ℚ) : ℝ)
      = (∑ k ∈ Finset.range 59, ((slopeUp R2 (kapLoOf R2) k : ℚ) : ℝ)
          * ∑ z : Fin 7, nuR z * failV arr1 arr2 (k + 1) z) / (((59 : ℕ) : ℝ) + 1) := by
  have hJ := J_eq
  unfold accumulated
  rw [show J - 1 = 59 from rfl, Rat.cast_div, sumRange_cast]
  rw [show ((J : ℚ) : ℝ) = ((59 : ℕ) : ℝ) + 1 by norm_num [J]]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < 59 := Finset.mem_range.mp hk
  rw [Rat.cast_mul, nuSum_cast]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold nuR failV
  rw [if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ 59 from ⟨by omega, by omega⟩),
    show J - 1 - (k + 1) = J - 2 - k by omega]
  unfold val
  push_cast
  rfl

/-- The firm's capital demand in wage units, `α / ((1 - α)(r + δ))` at `α = 9/25`, `δ = 2/25`. -/
noncomputable def olgDemand (r : ℝ) : ℝ := (9 / 25) / ((1 - 9 / 25) * (r + 2 / 25))

theorem budget_cast : ((budgetOf R1 R2 : ℚ) : ℝ) = olgDemand (1 / 25) - olgDemand (23 / 500) := by
  simp only [budgetOf, R1, R2, olgDemand]
  push_cast
  norm_num

/-! ### The verdict, unpacked -/

theorem enclCheck_unpack (h : enclCheckOf R1 R2 = true) :
    gridOK () = true ∧ checkAllStages R1 (runStages R1) = true
      ∧ checkAllStages R2 (runStages R2) = true
      ∧ (∀ j < J, reachR (runStages R1) (runStages R2) j < CAP)
      ∧ accumulated R1 R2 (runStages R1) (runStages R2) (reachR (runStages R1) (runStages R2))
          < budgetOf R1 R2 := by
  simp only [enclCheckOf, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hg, h1⟩, h2⟩, hr⟩, _⟩, hacc⟩ := h
  exact ⟨hg, h1, h2, hr, hacc⟩

/-- **The pairwise single-crossing inequality at `4%` and `4.6%`**, from the checker's verdict:
capital supply rises between the two rates by more than demand falls, so the two rates are not
both stationary equilibria. -/
theorem increment_of_enclCheck (h : enclCheckOf R1 R2 = true) :
    olgDemand (23 / 500) - olgDemand (1 / 25)
      < olg7hi.olgCapital 59 nuR - olg7.olgCapital 59 nuR := by
  obtain ⟨hg, h1, h2, hr, hacc⟩ := enclCheck_unpack h
  have henc1 := checkAllStages_sound matches_low hg slack_low (runStages R1) h1
  have henc2 := checkAllStages_sound matches_high hg slack_high (runStages R2) h2
  have hreach1 : ∀ j < J, reachOf R1 (runStages R1) j < CAP :=
    fun j hj => lt_of_le_of_lt (le_max_left _ _) (hr j hj)
  have hV := failV_sound (runStages R1) (runStages R2) hg henc1 henc2 hreach1 slack_low
  have h0 : (0 : ℝ) ∈ (encRegions (runStages R1) hg henc1 hreach1 slack_low).region 59 := by
    simp only [encRegions, le_refl, ite_true]
    exact ⟨le_rfl, val_nonneg _⟩
  have hmain := olg7.olgCapital_sub_ge_of_failure (Q := olg7hi) olg7hi_transitionMatrix
    (encRegions (runStages R1) hg henc1 hreach1 slack_low)
    (G := fun k => ((slopeUp R2 (kapLoOf R2) k : ℚ) : ℝ)) slopeUp_nonneg 59 (lip_high slack_high)
    (failV_nonneg (runStages R1) (runStages R2)) hV h0 nuR_nonneg nuR_invariant
  rw [← accumulated_cast] at hmain
  have hbud : ((accumulated R1 R2 (runStages R1) (runStages R2)
      (reachR (runStages R1) (runStages R2)) : ℚ) : ℝ) < ((budgetOf R1 R2 : ℚ) : ℝ) := by
    exact_mod_cast hacc
  rw [budget_cast] at hbud
  exact OLG.lt_of_increment_bound hmain hbud

end LeanEconomics.EnclCert
