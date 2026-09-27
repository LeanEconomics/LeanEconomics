/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.EnclBridge

/-!
# The enclosure certificate: stage soundness

Each stored stage enclosure is re-verified by `checkStage`; here every check is shown to imply
the real inequality it was designed for, so that `checkAllStages` gives `StageEnc` at every
stage. The interval Euler step (`IntervalEuler`) supplies the economics; the bridge lemmas
supply the rounding.
-/

open Set

namespace LeanEconomics.EnclCert

open IncomeFluctuation

/-! ### The stage step -/

/-- The economy `P` carries the certificate's data at gross rate `R`. -/
structure Matches (P : IncomeFluctuation (Fin 7) 0 2000) (R : ℕ × ℕ) : Prop where
  rate : 1 + P.interest = rate R
  income : ∀ z, P.income z = (yQ z : ℝ)
  trans : ∀ z z', P.transitionMatrix z z' = (piQ z z' : ℝ)
  disc : (P.discount : ℝ) = 24 / 25
  u : P.u = crraUtility 3
  unb : P.Unbounded

theorem Matches.den {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ} (hM : Matches P R) :
    0 < R.2 := rate_pos_den P R hM.rate

theorem Matches.disc_pos {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ}
    (hM : Matches P R) : 0 < (P.discount : ℝ) := by rw [hM.disc]; norm_num

/-- Cap slack gives slack against `maxSaving`, consumption being positive. -/
theorem policy_lt_maxSaving (P : IncomeFluctuation (Fin 7) 0 2000) (hd : P.Unbounded) (j : ℕ)
    (hsl : ∀ a ∈ Icc (0 : ℝ) 2000, ∀ z : Fin 7, P.stagePolicy j (a, z) < 2000) :
    ∀ a ∈ Icc (0 : ℝ) 2000, ∀ z : Fin 7, P.stagePolicy j (a, z) < P.maxSaving (a, z) := by
  intro a ha z
  have hc := P.stageConsumption_pos hd j z ha
  rw [stageConsumption_eq] at hc
  unfold maxSaving
  exact lt_of_lt_of_le (lt_min (hsl a ha z) (by linarith)) (le_max_right _ _)

theorem stageConsumption_monotoneOn (P : IncomeFluctuation (Fin 7) 0 2000) (k : ℕ) (z : Fin 7) :
    MonotoneOn (P.stageConsumption k z) (Icc (0 : ℝ) 2000) :=
  fun _ ha _ hb hab => P.stageConsumption_mono k ha hb hab

theorem stageConsumption_nonneg_on (P : IncomeFluctuation (Fin 7) 0 2000) (hd : P.Unbounded)
    (k : ℕ) (z : Fin 7) : ∀ a ∈ Icc (0 : ℝ) 2000, 0 ≤ P.stageConsumption k z a :=
  fun _ ha => (P.stageConsumption_pos hd k z ha).le

theorem stageConsumption_concaveOn {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ}
    (hM : Matches P R) (k : ℕ) (hsl : P.SlackUpTo k) (z : Fin 7) :
    ConcaveOn ℝ (Icc (0 : ℝ) 2000) (P.stageConsumption k z) :=
  P.concaveOn_stageConsumption_le (P.positiveConsumptionAll_of_unbounded hM.unb) (by norm_num)
    hM.disc_pos hM.u k hsl k le_rfl z

theorem pos7_sound {xs : ℕ → ℕ} (h : pos7 xs = true) : ∀ i : Fin 7, 0 < xs i := by
  unfold pos7 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  intro i
  fin_cases i <;> assumption

/-- **The lower certification is sound.** -/
theorem certL_sound {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ} (hM : Matches P R)
    (hg : gridOK () = true) (k : ℕ) (hsl : P.SlackUpTo k) (S : Stage) (henc : StageEnc P k S)
    (z : Fin 7) (i : ℕ) (hi : i < NA) (n : ℕ) (h : certL R S z i n = true) :
    val n ≤ P.stageConsumption (k + 1) z (val grid[i]!) := by
  have hR2 := hM.den
  have hC : grid[i]! ≤ CAP := grid_le_CAP hg i hi
  have haI := val_mem _ hC
  simp only [certL] at h
  split_ifs at h with hnm
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hnm h
    obtain ⟨hn0, hnm⟩ := hnm
    obtain ⟨⟨hapC, hpos⟩, htest⟩ := h
    have hpos' := pos7_sound hpos
    have hres := resources_val P R hM.rate hM.income z _ hC
    have hm : val (mDn R z grid[i]!) ≤ P.resources (val grid[i]!, z) := by
      rw [hres]; exact mDn_le R hR2 z _
    have hcLm : val n ≤ P.resources (val grid[i]!, z) := le_trans (val_le_val hnm) hm
    have hapv : val (mDn R z grid[i]! - n) = val (mDn R z grid[i]!) - val n := by
      unfold val; rw [Nat.cast_sub hnm, sub_div]
    rcases le_or_gt (P.resources (val grid[i]!, z) - val n) 2000 with hle | hgt
    · refine P.le_stageConsumption_of_cert (γ := 3) (by norm_num) hM.u hM.unb k z haI ?_
        (val_pos hn0) hcLm (ℓ := fun z' => val (encLo R S z' (mDn R z grid[i]! - n)))
        (fun z' => val_pos (hpos' z')) ?_ ?_
      · intro z'
        exact policy_lt_maxSaving P hM.unb k (fun a ha w => hsl k le_rfl a ha w) _
          (P.stagePolicy_mem_region _ _) z'
      · intro z'
        have h1 := encLo_sound P R hM.rate hM.income hg k S (stageConsumption_monotoneOn P k)
          (stageConsumption_concaveOn hM k hsl) (stageConsumption_nonneg_on P hM.unb k) henc z'
          _ hapC
        refine le_trans h1 (P.stageConsumption_mono k (val_mem _ hapC) ⟨?_, hle⟩ ?_)
        · linarith [val_nonneg (mDn R z grid[i]! - n), hapv]
        · rw [hapv]; linarith
      · exact eulerSum_le_of_test P hM.trans hM.disc R hR2 hM.rate z hn0
          (fun z' => encLo R S z' (mDn R z grid[i]! - n)) hpos' htest
    · rw [stageConsumption_eq]
      have := (P.stagePolicy_mem_region (k + 1) (val grid[i]!, z)).2
      linarith

/-- **The upper certification is sound.** -/
theorem certH_sound {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ} (hM : Matches P R)
    (hg : gridOK () = true) (k : ℕ) (hsl : P.SlackUpTo (k + 1)) (S : Stage)
    (henc : StageEnc P k S) (z : Fin 7) (i : ℕ) (hi : i < NA) (n : ℕ)
    (h : certH R S z i n = true) :
    P.stageConsumption (k + 1) z (val grid[i]!) ≤ val n := by
  have hR2 := hM.den
  have hC : grid[i]! ≤ CAP := grid_le_CAP hg i hi
  have haI := val_mem _ hC
  have hres := resources_val P R hM.rate hM.income z _ hC
  have hm : P.resources (val grid[i]!, z) ≤ val (mUp R z grid[i]!) := by
    rw [hres]; exact le_mUp R hR2 z _
  have hcr := P.stageConsumption_le_resources (k + 1) z (val grid[i]!)
  simp only [certH] at h
  split_ifs at h with hmn hn0
  · exact le_trans hcr (le_trans hm (val_le_val hmn))
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hapC, hpos⟩, htest⟩ := h
    have hpos' := pos7_sound hpos
    have hn0' : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp at hn0
      · exact h0
    have hnm : n ≤ mUp R z grid[i]! := by omega
    have hapv : val (mUp R z grid[i]! - n) = val (mUp R z grid[i]!) - val n := by
      unfold val; rw [Nat.cast_sub hnm, sub_div]
    rcases le_or_gt (val n) (P.resources (val grid[i]!, z)) with hle | hgt
    · have hsl' : P.SlackUpTo k := fun j hj => hsl j (Nat.le_succ_of_le hj)
      refine P.stageConsumption_le_of_cert (γ := 3) (by norm_num) hM.u hM.unb k z haI ?_
        (val_pos hn0') hle ?_ (h := fun z' => val (encHi R S z' (mUp R z grid[i]! - n))) ?_ ?_
      · exact policy_lt_maxSaving P hM.unb (k + 1) (fun a ha w => hsl (k + 1) le_rfl a ha w) _
          haI z
      · have := val_le_val hapC
        rw [val_CAP] at this
        rw [hapv] at this
        linarith
      · intro z'
        have h1 := encHi_sound P R hM.rate hM.income hg k S (stageConsumption_monotoneOn P k)
          (stageConsumption_concaveOn hM k hsl') henc z' _ hapC
        refine le_trans (P.stageConsumption_mono k ⟨by linarith, ?_⟩ (val_mem _ hapC) ?_) h1
        · have := val_le_val hapC
          rw [val_CAP] at this
          rw [hapv] at this
          linarith
        · rw [hapv]; linarith
      · exact le_eulerSum_of_test P hM.trans hM.disc R hR2 hM.rate z hn0'
          (fun z' => encHi R S z' (mUp R z grid[i]! - n)) hpos' htest
    · exact le_trans hcr hgt.le

/-- **The corner test is sound**: below the tested asset level all cash on hand is consumed. -/
theorem cornerTest_sound {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ} (hM : Matches P R)
    (hg : gridOK () = true) (k : ℕ) (hsl : P.SlackUpTo k) (S : Stage) (henc : StageEnc P k S)
    (z : Fin 7) (a' : ℕ) (h : cornerTest R S z a' = true) :
    ∀ a, a ≤ CAP → a ≤ a' → P.stageConsumption (k + 1) z (val a) = P.resources (val a, z) := by
  intro a haC haa
  have hR2 := hM.den
  have haI := val_mem _ haC
  simp only [cornerTest, Bool.and_eq_true] at h
  obtain ⟨hpos, htest⟩ := h
  have hpos' := pos7_sound hpos
  have hy : (0 : ℝ) < (yQ z : ℝ) := by
    have := yQ_min z
    have h' : ((19264 / 72101 : ℚ) : ℝ) ≤ (yQ z : ℝ) := Rat.cast_le.mpr this
    have h'' : ((19264 / 72101 : ℚ) : ℝ) = (19264 : ℝ) / 72101 := by norm_num
    rw [h''] at h'
    linarith
  have hrate : 0 ≤ rate R := by unfold rate; positivity
  have hmU : P.resources (val a, z) ≤ val (mUp R z a') := by
    rw [resources_val P R hM.rate hM.income z a haC]
    refine le_trans ?_ (le_mUp R hR2 z a')
    have := mul_le_mul_of_nonneg_left (val_le_val haa) hrate
    linarith
  have hrpos : 0 < P.resources (val a, z) := by
    rw [resources_val P R hM.rate hM.income z a haC]
    have := mul_nonneg hrate (val_nonneg a)
    linarith
  have hmUpos : 0 < mUp R z a' := by
    rcases Nat.eq_zero_or_pos (mUp R z a') with h0 | h0
    · rw [h0, val_zero] at hmU; linarith
    · exact h0
  refine P.stageConsumption_eq_resources_of_cert (γ := 3) (by norm_num) hM.u hM.unb k z haI ?_
    (ℓ := fun z' => val (encLo R S z' 0)) (fun z' => val_pos (hpos' z')) ?_ ?_
  · intro z'
    exact policy_lt_maxSaving P hM.unb k (fun b hb w => hsl k le_rfl b hb w) _
      (P.stagePolicy_mem_region _ _) z'
  · intro z'
    have h1 := encLo_sound P R hM.rate hM.income hg k S (stageConsumption_monotoneOn P k)
      (stageConsumption_concaveOn hM k hsl) (stageConsumption_nonneg_on P hM.unb k) henc z'
      0 (Nat.zero_le _)
    rwa [val_zero] at h1
  · have h1 := eulerSum_le_of_test P hM.trans hM.disc R hR2 hM.rate z hmUpos
      (fun z' => encLo R S z' 0) hpos' htest
    have h2 : (val (mUp R z a')) ^ (-(3 : ℝ)) ≤ (P.resources (val a, z)) ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hrpos hmU (by norm_num)
    exact le_trans h1 h2

/-- **One checked stage step carries the enclosure forward.** -/
theorem checkStage_sound {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ} (hM : Matches P R)
    (hg : gridOK () = true) (k : ℕ) (hsl : P.SlackUpTo (k + 1)) (prev next : Stage)
    (hprev : StageEnc P k prev) (h : checkStage R prev next = true) :
    StageEnc P (k + 1) next := by
  have hsl' : P.SlackUpTo k := fun j hj => hsl j (Nat.le_succ_of_le hj)
  unfold checkStage at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq] at h
  refine ⟨fun z i hi => ?_, fun z i hi => ?_, fun z a haC hlt => ?_⟩
  · exact certL_sound hM hg k hsl' prev hprev z i hi _ ((h z z.2).2 i hi).1
  · exact certH_sound hM hg k hsl prev hprev z i hi _ ((h z z.2).2 i hi).2
  · rcases (h z z.2).1 with h0 | hct
    · omega
    · exact cornerTest_sound hM hg k hsl' prev hprev z _ hct a haC (by omega)

/-- **The terminal check gives the stage-`0` enclosure.** -/
theorem checkTerminal_sound {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ}
    (hM : Matches P R) (hg : gridOK () = true) (S : Stage) (h : checkTerminal R S = true) :
    StageEnc P 0 S := by
  have hR2 := hM.den
  unfold checkTerminal at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨fun z i hi => ?_, fun z i hi => ?_, fun z a haC _ => ?_⟩
  · have hC := grid_le_CAP hg i hi
    rw [P.stageConsumption_zero (val_mem _ hC) z, resources_val P R hM.rate hM.income z _ hC]
    exact le_trans (val_le_val (h z z.2 i hi).1) (mDn_le R hR2 z _)
  · have hC := grid_le_CAP hg i hi
    rw [P.stageConsumption_zero (val_mem _ hC) z, resources_val P R hM.rate hM.income z _ hC]
    exact le_trans (le_mUp R hR2 z _) (val_le_val (h z z.2 i hi).2)
  · exact P.stageConsumption_zero (val_mem _ haC) z

/-- **Every checked stage is enclosed.** -/
theorem checkAllStages_sound {P : IncomeFluctuation (Fin 7) 0 2000} {R : ℕ × ℕ}
    (hM : Matches P R) (hg : gridOK () = true) (hsl : P.SlackUpTo (J - 1)) (arr : Array Stage)
    (h : checkAllStages R arr = true) : ∀ k < J, StageEnc P k arr[k]! := by
  unfold checkAllStages at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨_, hterm⟩, hstep⟩ := h
  intro k
  induction k with
  | zero => intro _; exact checkTerminal_sound hM hg _ hterm
  | succ k ih =>
    intro hk
    have hsl' : P.SlackUpTo (k + 1) := fun j hj => hsl j (by omega)
    exact checkStage_sound hM hg k hsl' _ _ (ih (by omega)) (hstep k (by omega))

end LeanEconomics.EnclCert
