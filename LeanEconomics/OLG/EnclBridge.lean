/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EnclCert.Check
import LeanEconomics.Models.OLG7Witness
import LeanEconomics.OLG.IntervalEuler
import LeanEconomics.OLG.CapSlack
import LeanEconomics.OLG.IncrementCohort

/-!
# From the certificate's arithmetic to the life-cycle economy

`EnclCert.Check` computes with naturals over `D`. This file says what each of its tests means
for the economy `olg7` at the two rates, and assembles the stage induction: if `checkAllStages`
holds then the stored naturals enclose the stage consumption functions at every grid point.

## Data

The certificate's tables are the witness's rationals cleared of denominators
(`piNum_div`, `yN_div`, `nuN_div`).

## Rounding

`mDn`/`mUp` bracket cash on hand (`mDn_le`, `le_mUp`); `ceilDiv` rounds up (`le_ceilDiv_mul`).

## The Euler test

`eulerTest_low` and `eulerTest_high` read the two rounded tests as the exact inequalities
`βR ∑ π (c/x)^γ ≤ 1` and `≥ 1`, which are the hypotheses of `le_stageConsumption_of_cert` and
`stageConsumption_le_of_cert` in marginal-utility form (`eulerSum_le_of_test`,
`le_eulerSum_of_test`).
-/

open Set

namespace LeanEconomics.EnclCert

open IncomeFluctuation

/-- The real number a natural over `D` stands for. -/
noncomputable def val (n : ℕ) : ℝ := (n : ℝ) / D

theorem D_pos : (0 : ℝ) < D := by norm_num [D]

theorem val_nonneg (n : ℕ) : 0 ≤ val n := by unfold val; positivity

theorem val_zero : val 0 = 0 := by unfold val; simp

theorem val_le_val {m n : ℕ} (h : m ≤ n) : val m ≤ val n := by
  unfold val; exact div_le_div_of_nonneg_right (by exact_mod_cast h) D_pos.le

/-! ### Data -/

theorem piNum_div (z z' : Fin 7) : (piNum z z' : ℝ) / piDen = (piQ z z' : ℝ) := by
  simp [piQ]

theorem yN_div (z : Fin 7) : ((yN z).1 : ℝ) / (yN z).2 = (yQ z : ℝ) := by
  simp [yQ]

theorem nuN_div (z : Fin 7) : ((nuN z).1 : ℝ) / (nuN z).2 = (nuQ z : ℝ) := by
  simp [nuQ]

theorem yN_pos (z : Fin 7) : 0 < (yN z).1 ∧ 0 < (yN z).2 := by
  fin_cases z <;> decide

/-! ### Rounding -/

theorem ceilDiv_mul_ge {a b : ℕ} (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  have h := Nat.lt_div_mul_add (a := a + b - 1) hb
  omega

theorem le_ceilDiv_real {a b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ (ceilDiv a b : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast ceilDiv_mul_ge hb

theorem natDiv_le_real (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

/-- The gross rate `R = R.1 / R.2` as a real. -/
noncomputable def rate (R : ℕ × ℕ) : ℝ := (R.1 : ℝ) / R.2

/-- `mDn` is below cash on hand at `a/D` in state `z`. -/
theorem mDn_le (R : ℕ × ℕ) (hR : 0 < R.2) (z : Fin 7) (a : ℕ) :
    val (mDn R z a) ≤ (yQ z : ℝ) + rate R * val a := by
  unfold mDn val rate
  obtain ⟨hyn, hyd⟩ := yN_pos z
  rw [← yN_div z]
  have hD := D_pos
  have hyd' : (0 : ℝ) < (yN z).2 := by exact_mod_cast hyd
  have hR' : (0 : ℝ) < R.2 := by exact_mod_cast hR
  calc (((((yN z).1 * D * R.2 + R.1 * a * (yN z).2) / ((yN z).2 * R.2) : ℕ)) : ℝ) / D
      ≤ ((((yN z).1 * D * R.2 + R.1 * a * (yN z).2 : ℕ) : ℝ) / (((yN z).2 * R.2 : ℕ) : ℝ)) / D :=
        div_le_div_of_nonneg_right (natDiv_le_real _ _) hD.le
    _ = ((yN z).1 : ℝ) / (yN z).2 + (R.1 : ℝ) / R.2 * ((a : ℝ) / D) := by
        push_cast; field_simp

/-- `mUp` is above cash on hand at `a/D` in state `z`. -/
theorem le_mUp (R : ℕ × ℕ) (hR : 0 < R.2) (z : Fin 7) (a : ℕ) :
    (yQ z : ℝ) + rate R * val a ≤ val (mUp R z a) := by
  unfold mUp val rate
  obtain ⟨hyn, hyd⟩ := yN_pos z
  rw [← yN_div z]
  have hD := D_pos
  have hyd' : (0 : ℝ) < (yN z).2 := by exact_mod_cast hyd
  have hR' : (0 : ℝ) < R.2 := by exact_mod_cast hR
  calc ((yN z).1 : ℝ) / (yN z).2 + (R.1 : ℝ) / R.2 * ((a : ℝ) / D)
      = ((((yN z).1 * D * R.2 + R.1 * a * (yN z).2 : ℕ) : ℝ) / (((yN z).2 * R.2 : ℕ) : ℝ)) / D := by
        push_cast; field_simp
    _ ≤ ((ceilDiv ((yN z).1 * D * R.2 + R.1 * a * (yN z).2) ((yN z).2 * R.2) : ℕ) : ℝ) / D :=
        div_le_div_of_nonneg_right (le_ceilDiv_real (by positivity)) hD.le

/-! ### The Euler test -/

theorem sum7_cast (f : ℕ → ℕ) : ((sum7 f : ℕ) : ℝ) = ∑ i : Fin 7, (f i : ℝ) := by
  simp only [sum7, Fin.sum_univ_seven, Nat.cast_add]
  rfl

theorem piNum_nonneg (z i : ℕ) : (0 : ℝ) ≤ (piNum z i : ℝ) := by positivity

theorem SCALE_pos : (0 : ℝ) < SCALE := by norm_num [SCALE]
theorem piDen_pos : (0 : ℝ) < piDen := by norm_num [piDen]

/-- **The lower Euler test read exactly**: `βR ∑ π (c/x)^3 ≤ 1`. -/
theorem eulerTest_low (R : ℕ × ℕ) (hR : 0 < R.2) (z : Fin 7) (c : ℕ) (xs : ℕ → ℕ)
    (hpos : ∀ i : Fin 7, 0 < xs i) (h : eulerTest R z c xs true = true) :
    (24 / 25 : ℝ) * rate R * ∑ i : Fin 7, (piQ z i : ℝ) * ((c : ℝ) / xs i) ^ 3 ≤ 1 := by
  have hD := SCALE_pos
  have hP := piDen_pos
  have hR' : (0 : ℝ) < R.2 := by exact_mod_cast hR
  simp only [eulerTest, beta, gam, decide_eq_true_eq, ite_true] at h
  -- the tested inequality, cast to the reals
  have hcast : (24 : ℝ) * R.1 * (sum7 fun i => piNum z i * ceilDiv (c ^ 3 * SCALE) (xs i ^ 3) : ℕ)
      ≤ 25 * R.2 * piDen * SCALE := by exact_mod_cast h
  rw [sum7_cast] at hcast
  push_cast at hcast
  -- each rounded ratio bounds the exact one
  have hterm : ∀ i : Fin 7, (piNum z i : ℝ) * ((c : ℝ) ^ 3 * SCALE / (xs i : ℝ) ^ 3)
      ≤ (piNum z i : ℝ) * (ceilDiv (c ^ 3 * SCALE) (xs i ^ 3) : ℝ) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (piNum_nonneg _ _)
    have := le_ceilDiv_real (a := c ^ 3 * SCALE) (b := xs i ^ 3) (pow_pos (hpos i) 3)
    push_cast at this
    exact this
  have hsum : ∑ i : Fin 7, (piNum z i : ℝ) * ((c : ℝ) ^ 3 * SCALE / (xs i : ℝ) ^ 3)
      ≤ ∑ i : Fin 7, (piNum z i : ℝ) * (ceilDiv (c ^ 3 * SCALE) (xs i ^ 3) : ℝ) :=
    Finset.sum_le_sum fun i _ => hterm i
  -- assemble
  have key : (24 : ℝ) * R.1 * ∑ i : Fin 7, (piNum z i : ℝ) * ((c : ℝ) ^ 3 * SCALE / (xs i : ℝ) ^ 3)
      ≤ 25 * R.2 * piDen * SCALE := by
    calc (24 : ℝ) * R.1 * ∑ i : Fin 7, (piNum z i : ℝ) * ((c : ℝ) ^ 3 * SCALE / (xs i : ℝ) ^ 3)
        ≤ (24 : ℝ) * R.1
          * ∑ i : Fin 7, (piNum z i : ℝ) * (ceilDiv (c ^ 3 * SCALE) (xs i ^ 3) : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ _ := hcast
  -- divide through
  have hK : (0 : ℝ) < 25 * R.2 * piDen * SCALE := by positivity
  have hrew : (24 / 25 : ℝ) * rate R * (∑ i : Fin 7, (piQ z i : ℝ) * ((c : ℝ) / xs i) ^ 3)
        * (25 * R.2 * piDen * SCALE)
      = (24 : ℝ) * R.1 * ∑ i : Fin 7, (piNum z i : ℝ) * ((c : ℝ) ^ 3 * SCALE / (xs i : ℝ) ^ 3) := by
    unfold rate
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← piNum_div z i]
    all_goals
      have hx : (0 : ℝ) < xs i := by exact_mod_cast hpos i
      field_simp
  have h1 : (24 / 25 : ℝ) * rate R * (∑ i : Fin 7, (piQ z i : ℝ) * ((c : ℝ) / xs i) ^ 3)
        * (25 * R.2 * piDen * SCALE) ≤ 1 * (25 * R.2 * piDen * SCALE) := by
    rw [hrew, one_mul]; exact key
  exact le_of_mul_le_mul_right h1 hK

/-- **The upper Euler test read exactly**: `βR ∑ π (c/x)^3 ≥ 1`. -/
theorem eulerTest_high (R : ℕ × ℕ) (hR : 0 < R.2) (z : Fin 7) (c : ℕ) (xs : ℕ → ℕ)
    (hpos : ∀ i : Fin 7, 0 < xs i) (h : eulerTest R z c xs false = true) :
    1 ≤ (24 / 25 : ℝ) * rate R * ∑ i : Fin 7, (piQ z i : ℝ) * ((c : ℝ) / xs i) ^ 3 := by
  have hD := SCALE_pos
  have hP := piDen_pos
  have hR' : (0 : ℝ) < R.2 := by exact_mod_cast hR
  simp only [eulerTest, beta, gam, decide_eq_true_eq, ite_false, Bool.false_eq_true] at h
  have hcast : (25 : ℝ) * R.2 * piDen * SCALE
      ≤ 24 * R.1 * (sum7 fun i => piNum z i * ((c ^ 3 * SCALE) / (xs i ^ 3)) : ℕ) := by
    exact_mod_cast h
  rw [sum7_cast] at hcast
  push_cast at hcast
  have hterm : ∀ i : Fin 7, (piNum z i : ℝ) * (((c ^ 3 * SCALE) / (xs i ^ 3) : ℕ) : ℝ)
      ≤ (piNum z i : ℝ) * ((c : ℝ) ^ 3 * SCALE / (xs i : ℝ) ^ 3) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (piNum_nonneg _ _)
    have := natDiv_le_real (c ^ 3 * SCALE) (xs i ^ 3)
    push_cast at this
    exact this
  have hsum : ∑ i : Fin 7, (piNum z i : ℝ) * (((c ^ 3 * SCALE) / (xs i ^ 3) : ℕ) : ℝ)
      ≤ ∑ i : Fin 7, (piNum z i : ℝ) * ((c : ℝ) ^ 3 * SCALE / (xs i : ℝ) ^ 3) :=
    Finset.sum_le_sum fun i _ => hterm i
  have key : (25 : ℝ) * R.2 * piDen * SCALE
      ≤ (24 : ℝ) * R.1 * ∑ i : Fin 7, (piNum z i : ℝ) * ((c : ℝ) ^ 3 * SCALE / (xs i : ℝ) ^ 3) := by
    calc (25 : ℝ) * R.2 * piDen * SCALE
        ≤ 24 * R.1 * ∑ i : Fin 7, (piNum z i : ℝ) * (((c ^ 3 * SCALE) / (xs i ^ 3) : ℕ) : ℝ) :=
          hcast
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  have hK : (0 : ℝ) < 25 * R.2 * piDen * SCALE := by positivity
  have hrew : (24 / 25 : ℝ) * rate R * (∑ i : Fin 7, (piQ z i : ℝ) * ((c : ℝ) / xs i) ^ 3)
        * (25 * R.2 * piDen * SCALE)
      = (24 : ℝ) * R.1 * ∑ i : Fin 7, (piNum z i : ℝ) * ((c : ℝ) ^ 3 * SCALE / (xs i : ℝ) ^ 3) := by
    unfold rate
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← piNum_div z i]
    all_goals
      have hx : (0 : ℝ) < xs i := by exact_mod_cast hpos i
      field_simp
  have h1 : 1 * (25 * R.2 * piDen * SCALE)
      ≤ (24 / 25 : ℝ) * rate R * (∑ i : Fin 7, (piQ z i : ℝ) * ((c : ℝ) / xs i) ^ 3)
        * (25 * R.2 * piDen * SCALE) := by
    rw [hrew, one_mul]; exact key
  exact le_of_mul_le_mul_right h1 hK

/-! ### The tests as the hypotheses of the interval Euler step -/

/-- `x ^ (-3) = (x ^ 3)⁻¹`. -/
theorem rpow_neg_three {x : ℝ} (hx : 0 < x) : x ^ (-(3 : ℝ)) = (x ^ 3)⁻¹ := by
  rw [Real.rpow_neg hx.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The Euler sum of an economy with the certificate's data. -/
theorem eulerSum_eq {assetCap : ℝ} (P : IncomeFluctuation (Fin 7) 0 assetCap)
    (hπ : ∀ z z', P.transitionMatrix z z' = (piQ z z' : ℝ)) (hβ : (P.discount : ℝ) = 24 / 25)
    (z : Fin 7) (x : Fin 7 → ℝ) :
    P.eulerSum 3 z x
      = (24 / 25 : ℝ) * (1 + P.interest) * ∑ z', (piQ z z' : ℝ) * (x z') ^ (-(3 : ℝ)) := by
  unfold eulerSum
  rw [hβ, mul_assoc]
  congr 2
  exact Finset.sum_congr rfl fun z' _ => by rw [hπ]

theorem val_pos {n : ℕ} (hn : 0 < n) : 0 < val n := by
  unfold val; have := D_pos; positivity

/-- **The lower test gives the hypothesis of `le_stageConsumption_of_cert`.** -/
theorem eulerSum_le_of_test {assetCap : ℝ} (P : IncomeFluctuation (Fin 7) 0 assetCap)
    (hπ : ∀ z z', P.transitionMatrix z z' = (piQ z z' : ℝ)) (hβ : (P.discount : ℝ) = 24 / 25)
    (R : ℕ × ℕ) (hR2 : 0 < R.2) (hR : 1 + P.interest = rate R) (z : Fin 7) {n : ℕ} (hn : 0 < n)
    (xs : ℕ → ℕ) (hpos : ∀ i : Fin 7, 0 < xs i) (h : eulerTest R z n xs true = true) :
    P.eulerSum 3 z (fun z' => val (xs z')) ≤ (val n) ^ (-(3 : ℝ)) := by
  have hE := eulerTest_low R hR2 z n xs hpos h
  rw [eulerSum_eq P hπ hβ, hR, rpow_neg_three (val_pos hn)]
  have hn3 : (0 : ℝ) < (val n) ^ 3 := pow_pos (val_pos hn) 3
  have key : (24 / 25 : ℝ) * rate R * (∑ z', (piQ z z' : ℝ) * (val (xs z')) ^ (-(3 : ℝ)))
      * (val n) ^ 3 ≤ 1 := by
    refine le_of_eq_of_le ?_ hE
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z' _ => ?_
    have hx := val_pos (hpos z')
    rw [rpow_neg_three hx]
    unfold val
    have hD := D_pos
    have hxn : (0 : ℝ) < (xs z' : ℝ) := by exact_mod_cast hpos z'
    field_simp
  calc (24 / 25 : ℝ) * rate R * ∑ z', (piQ z z' : ℝ) * (val (xs z')) ^ (-(3 : ℝ))
      = ((24 / 25 : ℝ) * rate R * (∑ z', (piQ z z' : ℝ) * (val (xs z')) ^ (-(3 : ℝ)))
          * (val n) ^ 3) / (val n) ^ 3 := (mul_div_cancel_right₀ _ hn3.ne').symm
    _ ≤ 1 / (val n) ^ 3 := div_le_div_of_nonneg_right key hn3.le
    _ = ((val n) ^ 3)⁻¹ := one_div _

/-- **The upper test gives the hypothesis of `stageConsumption_le_of_cert`.** -/
theorem le_eulerSum_of_test {assetCap : ℝ} (P : IncomeFluctuation (Fin 7) 0 assetCap)
    (hπ : ∀ z z', P.transitionMatrix z z' = (piQ z z' : ℝ)) (hβ : (P.discount : ℝ) = 24 / 25)
    (R : ℕ × ℕ) (hR2 : 0 < R.2) (hR : 1 + P.interest = rate R) (z : Fin 7) {n : ℕ} (hn : 0 < n)
    (xs : ℕ → ℕ) (hpos : ∀ i : Fin 7, 0 < xs i) (h : eulerTest R z n xs false = true) :
    (val n) ^ (-(3 : ℝ)) ≤ P.eulerSum 3 z (fun z' => val (xs z')) := by
  have hE := eulerTest_high R hR2 z n xs hpos h
  rw [eulerSum_eq P hπ hβ, hR, rpow_neg_three (val_pos hn)]
  have hn3 : (0 : ℝ) < (val n) ^ 3 := pow_pos (val_pos hn) 3
  have key : 1 ≤ (24 / 25 : ℝ) * rate R * (∑ z', (piQ z z' : ℝ) * (val (xs z')) ^ (-(3 : ℝ)))
      * (val n) ^ 3 := by
    refine le_of_le_of_eq hE ?_
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z' _ => ?_
    have hx := val_pos (hpos z')
    rw [rpow_neg_three hx]
    unfold val
    have hD := D_pos
    have hxn : (0 : ℝ) < (xs z' : ℝ) := by exact_mod_cast hpos z'
    field_simp
  calc ((val n) ^ 3)⁻¹ = 1 / (val n) ^ 3 := (one_div _).symm
    _ ≤ ((24 / 25 : ℝ) * rate R * (∑ z', (piQ z z' : ℝ) * (val (xs z')) ^ (-(3 : ℝ)))
          * (val n) ^ 3) / (val n) ^ 3 := div_le_div_of_nonneg_right key hn3.le
    _ = _ := mul_div_cancel_right₀ _ hn3.ne'

/-! ### The grid -/

theorem CAP_pos : 0 < CAP := by norm_num [CAP, D]

theorem val_CAP : val CAP = 2000 := by
  unfold val CAP D; norm_num

theorem gridOK_facts (h : gridOK () = true) :
    grid[0]! = 0 ∧ grid[NA - 1]! = CAP ∧ ∀ i, i + 1 < NA → grid[i]! < grid[i+1]! := by
  unfold gridOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨h0, htop⟩, hs⟩ := h
  exact ⟨h0, htop, fun i hi => hs i (by omega)⟩

theorem grid_mono_of_ok (h : gridOK () = true) :
    ∀ i j, i ≤ j → j < NA → grid[i]! ≤ grid[j]! := by
  obtain ⟨_, _, hs⟩ := gridOK_facts h
  intro i j hij hj
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact le_rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact le_trans (ih (by omega) (by omega)) (hs j hj).le
    · have : i = j + 1 := by omega
      subst this; exact le_rfl

theorem grid_le_CAP (h : gridOK () = true) : ∀ i, i < NA → grid[i]! ≤ CAP := by
  obtain ⟨_, htop, _⟩ := gridOK_facts h
  intro i hi
  rw [← htop]
  exact grid_mono_of_ok h i (NA - 1) (by omega) (by omega)

theorem grid_nonneg_val (i : ℕ) : 0 ≤ val grid[i]! := val_nonneg _

/-! ### A stage enclosure, as a proposition about the economy -/

/-- The naturals stored for stage `k` enclose stage consumption at every grid point, and below
the corner threshold consumption is cash on hand. -/
structure StageEnc (P : IncomeFluctuation (Fin 7) 0 2000) (k : ℕ) (S : Stage) : Prop where
  lo : ∀ z : Fin 7, ∀ i, i < NA → val (at2 S.lo z i) ≤ P.stageConsumption k z (val grid[i]!)
  hi : ∀ z : Fin 7, ∀ i, i < NA → P.stageConsumption k z (val grid[i]!) ≤ val (at2 S.hi z i)
  corner : ∀ z : Fin 7, ∀ a, a ≤ CAP → a < S.corner[(z : ℕ)]! →
    P.stageConsumption k z (val a) = P.resources (val a, z)

/-- Cash on hand at `val a` in the certificate's data. -/
theorem resources_val (P : IncomeFluctuation (Fin 7) 0 2000) (R : ℕ × ℕ)
    (hR : 1 + P.interest = rate R) (hinc : ∀ z, P.income z = (yQ z : ℝ)) (z : Fin 7) (a : ℕ)
    (ha : a ≤ CAP) : P.resources (val a, z) = (yQ z : ℝ) + rate R * val a := by
  have hmem : val a ∈ Icc (0 : ℝ) 2000 := ⟨val_nonneg a, by rw [← val_CAP]; exact val_le_val ha⟩
  rw [P.resources_eq_of_mem hmem z, hinc, hR]

/-- `val a ∈ [0, 2000]` for `a ≤ CAP`. -/
theorem val_mem (a : ℕ) (ha : a ≤ CAP) : val a ∈ Icc (0 : ℝ) 2000 :=
  ⟨val_nonneg a, by rw [← val_CAP]; exact val_le_val ha⟩

/-- The chord of two lower bounds, computed in naturals with a floored division, is below the
real chord. -/
theorem chord_nat_le {a0 a1 ap l0 l1 : ℕ} (h01 : a0 < a1) (h0 : a0 ≤ ap) (hl : l0 ≤ l1) :
    val (l0 + (ap - a0) * (l1 - l0) / (a1 - a0))
      ≤ val l0 + (val ap - val a0) * (val l1 - val l0) / (val a1 - val a0) := by
  unfold val
  have hD := D_pos
  have hd : (0 : ℝ) < (a1 : ℝ) - a0 := by
    rw [sub_pos]; exact_mod_cast h01
  have hq : (((ap - a0) * (l1 - l0) / (a1 - a0) : ℕ) : ℝ)
      ≤ ((ap : ℝ) - a0) * ((l1 : ℝ) - l0) / ((a1 : ℝ) - a0) := by
    have := natDiv_le_real ((ap - a0) * (l1 - l0)) (a1 - a0)
    rw [Nat.cast_mul, Nat.cast_sub h0, Nat.cast_sub hl, Nat.cast_sub h01.le] at this
    exact this
  have hrhs : (l0 : ℝ) / D + ((ap : ℝ) / D - a0 / D) * ((l1 : ℝ) / D - l0 / D)
        / ((a1 : ℝ) / D - a0 / D)
      = ((l0 : ℝ) + ((ap : ℝ) - a0) * ((l1 : ℝ) - l0) / ((a1 : ℝ) - a0)) / D := by
    field_simp
  rw [hrhs, Nat.cast_add]
  exact div_le_div_of_nonneg_right (by linarith [hq]) hD.le

/-- The real chord through two points, in the form `le_of_chord` produces. -/
theorem chord_form {a0 a1 x l0 l1 : ℝ} (h : a0 < a1) :
    ((a1 - x) * l0 + (x - a0) * l1) / (a1 - a0) = l0 + (x - a0) * (l1 - l0) / (a1 - a0) := by
  have : a1 - a0 ≠ 0 := by linarith
  field_simp
  ring

theorem val_lt_val {m n : ℕ} (h : m < n) : val m < val n := by
  unfold val; exact div_lt_div_of_pos_right (by exact_mod_cast h) D_pos

/-- **`chordNat` is a lower bound** for a concave nondecreasing function bracketed at the ends. -/
theorem chordNat_sound {f : ℝ → ℝ} (hconc : ConcaveOn ℝ (Icc (0 : ℝ) 2000) f)
    (hmono : MonotoneOn f (Icc (0 : ℝ) 2000)) (hnn : ∀ a ∈ Icc (0 : ℝ) 2000, 0 ≤ f a)
    {a0 a1 ap l0 l1 : ℕ} (ha0 : a0 ≤ CAP) (ha1 : a1 ≤ CAP) (hap : ap ≤ a1)
    (hl0 : val l0 ≤ f (val a0)) (hl1 : val l1 ≤ f (val a1)) :
    val (chordNat a0 a1 ap l0 l1) ≤ f (val ap) := by
  have hapC : ap ≤ CAP := le_trans hap ha1
  unfold chordNat
  split_ifs with hin hll
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
    obtain ⟨h01, h0ap⟩ := hin
    have hchord := le_of_chord hconc (val_mem a0 ha0) (val_mem a1 ha1) (val_lt_val h01)
      (val_le_val h0ap) (val_le_val hap) hl0 hl1
    rw [chord_form (val_lt_val h01)] at hchord
    exact le_trans (chord_nat_le h01 h0ap hll) hchord
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
    obtain ⟨_, h0ap⟩ := hin
    calc val (min l0 l1) ≤ val l0 := val_le_val (min_le_left _ _)
      _ ≤ f (val a0) := hl0
      _ ≤ f (val ap) := hmono (val_mem a0 ha0) (val_mem ap hapC) (val_le_val h0ap)
  · rw [val_zero]; exact hnn _ (val_mem ap hapC)

/-- **`encLoAt` is a lower bound on stage consumption** on a bracketing interval. -/
theorem encLoAt_sound (P : IncomeFluctuation (Fin 7) 0 2000) (R : ℕ × ℕ) (hR2 : 0 < R.2)
    (hR : 1 + P.interest = rate R) (hinc : ∀ z, P.income z = (yQ z : ℝ)) (hg : gridOK () = true)
    (k : ℕ) (S : Stage) (hmono : ∀ z, MonotoneOn (P.stageConsumption k z) (Icc (0 : ℝ) 2000))
    (hconc : ∀ z, ConcaveOn ℝ (Icc (0 : ℝ) 2000) (P.stageConsumption k z))
    (hnn : ∀ z, ∀ a ∈ Icc (0 : ℝ) 2000, 0 ≤ P.stageConsumption k z a)
    (henc : StageEnc P k S) (z : Fin 7) (ap i : ℕ) (hap : ap ≤ CAP) :
    val (encLoAt R S z ap i) ≤ P.stageConsumption k z (val ap) := by
  unfold encLoAt
  split_ifs with hbr hk
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hbr hk
    obtain ⟨⟨⟨hi1, _⟩, hgi1⟩, _⟩ := hbr
    have hcor : S.corner[(z : ℕ)]! - 1 < S.corner[(z : ℕ)]! := by omega
    have hl0 : val (mDn R z (S.corner[(z : ℕ)]! - 1))
        ≤ P.stageConsumption k z (val (S.corner[(z : ℕ)]! - 1)) := by
      rw [henc.corner z _ (by omega) hcor, resources_val P R hR hinc z _ (by omega)]
      exact mDn_le R hR2 z _
    exact chordNat_sound (hconc z) (hmono z) (hnn z) (by omega) (grid_le_CAP hg _ hi1) hgi1 hl0
      (henc.lo z (i + 1) hi1)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hbr
    obtain ⟨⟨⟨hi1, _⟩, hgi1⟩, _⟩ := hbr
    exact chordNat_sound (hconc z) (hmono z) (hnn z) (grid_le_CAP hg i (by omega))
      (grid_le_CAP hg _ hi1) hgi1 (henc.lo z i (by omega)) (henc.lo z (i + 1) hi1)
  · rw [val_zero]; exact hnn z _ (val_mem ap hap)

theorem rate_pos_den (P : IncomeFluctuation (Fin 7) 0 2000) (R : ℕ × ℕ)
    (hR : 1 + P.interest = rate R) : 0 < R.2 := by
  by_contra hR0
  have h0 : R.2 = 0 := by omega
  have h1 : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  rw [hR] at h1; unfold rate at h1; rw [h0] at h1; simp at h1

/-- **`encLo` is a lower bound on stage consumption.** -/
theorem encLo_sound (P : IncomeFluctuation (Fin 7) 0 2000) (R : ℕ × ℕ)
    (hR : 1 + P.interest = rate R) (hinc : ∀ z, P.income z = (yQ z : ℝ)) (hg : gridOK () = true)
    (k : ℕ) (S : Stage) (hmono : ∀ z, MonotoneOn (P.stageConsumption k z) (Icc (0 : ℝ) 2000))
    (hconc : ∀ z, ConcaveOn ℝ (Icc (0 : ℝ) 2000) (P.stageConsumption k z))
    (hnn : ∀ z, ∀ a ∈ Icc (0 : ℝ) 2000, 0 ≤ P.stageConsumption k z a)
    (henc : StageEnc P k S) (z : Fin 7) (ap : ℕ) (hap : ap ≤ CAP) :
    val (encLo R S z ap) ≤ P.stageConsumption k z (val ap) := by
  have hR2 := rate_pos_den P R hR
  unfold encLo
  split_ifs with hcor hcap
  · rw [henc.corner z ap hap hcor, resources_val P R hR hinc z ap hap]
    exact mDn_le R hR2 z ap
  · omega
  · exact encLoAt_sound P R hR2 hR hinc hg k S hmono hconc hnn henc z ap _ hap

/-! ### The upper bounds -/

/-- The left secant, rounded up, is above the real left secant. -/
theorem leftSec_ge {am a0 ap lm h0 : ℕ} (h : am < a0) (h0ap : a0 ≤ ap) :
    val h0 + (val ap - val a0) * ((val h0 - val lm) / (val a0 - val am))
      ≤ val (leftSec am a0 ap lm h0) := by
  unfold leftSec val
  have hD := D_pos
  have hd : (0 : ℝ) < (a0 : ℝ) - am := by rw [sub_pos]; exact_mod_cast h
  have hdn : 0 < a0 - am := by omega
  -- the inner ceiling is above the slope times D
  have hs : ((h0 : ℝ) - lm) * D / ((a0 : ℝ) - am) ≤ (ceilDiv ((h0 - lm) * D) (a0 - am) : ℝ) := by
    rcases le_or_gt lm h0 with hlm | hlm
    · have := le_ceilDiv_real (a := (h0 - lm) * D) (b := a0 - am) hdn
      rw [Nat.cast_mul, Nat.cast_sub hlm, Nat.cast_sub h.le] at this
      exact this
    · have hneg : ((h0 : ℝ) - lm) * D / ((a0 : ℝ) - am) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ hd.le
        have : (h0 : ℝ) < lm := by exact_mod_cast hlm
        nlinarith
      exact le_trans hneg (by positivity)
  have hs' : ((ap : ℝ) - a0) * (((h0 : ℝ) - lm) * D / ((a0 : ℝ) - am))
      ≤ ((ap : ℝ) - a0) * (ceilDiv ((h0 - lm) * D) (a0 - am) : ℝ) :=
    mul_le_mul_of_nonneg_left hs (by rw [sub_nonneg]; exact_mod_cast h0ap)
  have hc : ((ap : ℝ) - a0) * (ceilDiv ((h0 - lm) * D) (a0 - am) : ℝ) / D
      ≤ (ceilDiv ((ap - a0) * ceilDiv ((h0 - lm) * D) (a0 - am)) D : ℝ) := by
    have := le_ceilDiv_real (a := (ap - a0) * ceilDiv ((h0 - lm) * D) (a0 - am)) (b := D)
      (by norm_num [D])
    rw [Nat.cast_mul, Nat.cast_sub h0ap] at this
    exact this
  rw [Nat.cast_add]
  have hlhs : (h0 : ℝ) / D
        + ((ap : ℝ) / D - a0 / D) * (((h0 : ℝ) / D - lm / D) / ((a0 : ℝ) / D - am / D))
      = (h0 : ℝ) / D + ((ap : ℝ) - a0) * (((h0 : ℝ) - lm) * D / ((a0 : ℝ) - am)) / D / D := by
    field_simp
  rw [hlhs, add_div]
  refine add_le_add le_rfl ?_
  calc ((ap : ℝ) - a0) * (((h0 : ℝ) - lm) * D / ((a0 : ℝ) - am)) / D / D
      ≤ ((ap : ℝ) - a0) * (ceilDiv ((h0 - lm) * D) (a0 - am) : ℝ) / D / D :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hs' hD.le) hD.le
    _ ≤ (ceilDiv ((ap - a0) * ceilDiv ((h0 - lm) * D) (a0 - am)) D : ℝ) / D :=
        div_le_div_of_nonneg_right hc hD.le

/-- The right secant, rounded down, is above the real right secant with its slope floored at
zero. -/
theorem rightSec_ge {a1 a2 ap h1 l2 : ℕ} (h : a1 < a2) (hap : ap ≤ a1) :
    val h1 - (val a1 - val ap) * max 0 ((val l2 - val h1) / (val a2 - val a1))
      ≤ val (rightSec a1 a2 ap h1 l2) := by
  unfold rightSec val
  have hD := D_pos
  have hd : (0 : ℝ) < (a2 : ℝ) - a1 := by rw [sub_pos]; exact_mod_cast h
  have hdn : 0 < a2 - a1 := by omega
  -- the floored slope is below the real slope, and nonnegative
  have hs : (((l2 - h1) * D / (a2 - a1) : ℕ) : ℝ)
      ≤ max 0 (((l2 : ℝ) - h1) * D / ((a2 : ℝ) - a1)) := by
    rcases le_or_gt h1 l2 with hl | hl
    · have := natDiv_le_real ((l2 - h1) * D) (a2 - a1)
      rw [Nat.cast_mul, Nat.cast_sub hl, Nat.cast_sub h.le] at this
      exact le_trans this (le_max_right _ _)
    · have : l2 - h1 = 0 := by omega
      simp [this]
  have hq : (((a1 - ap) * ((l2 - h1) * D / (a2 - a1)) / D : ℕ) : ℝ)
      ≤ ((a1 : ℝ) - ap) * max 0 (((l2 : ℝ) - h1) * D / ((a2 : ℝ) - a1)) / D := by
    have := natDiv_le_real ((a1 - ap) * ((l2 - h1) * D / (a2 - a1))) D
    rw [Nat.cast_mul, Nat.cast_sub hap] at this
    refine le_trans this (div_le_div_of_nonneg_right ?_ hD.le)
    exact mul_le_mul_of_nonneg_left hs (by rw [sub_nonneg]; exact_mod_cast hap)
  have hcast : (((h1 - (a1 - ap) * ((l2 - h1) * D / (a2 - a1)) / D : ℕ)) : ℝ)
      ≥ (h1 : ℝ) - (((a1 - ap) * ((l2 - h1) * D / (a2 - a1)) / D : ℕ) : ℝ) := by
    rcases le_or_gt ((a1 - ap) * ((l2 - h1) * D / (a2 - a1)) / D) h1 with hle | hlt
    · rw [Nat.cast_sub hle]
    · have : h1 - (a1 - ap) * ((l2 - h1) * D / (a2 - a1)) / D = 0 := by omega
      rw [this]; push_cast
      have : (h1 : ℝ) < (((a1 - ap) * ((l2 - h1) * D / (a2 - a1)) / D : ℕ) : ℝ) := by
        exact_mod_cast hlt
      linarith
  set X : ℝ := ((l2 : ℝ) - h1) * D / ((a2 : ℝ) - a1) with hX
  have hinner : ((l2 : ℝ) / D - h1 / D) / ((a2 : ℝ) / D - a1 / D) = X / D := by
    rw [hX]; field_simp
  have hmax : max 0 (X / D) = max 0 X / D := by
    rcases le_or_gt 0 X with hx | hx
    · rw [max_eq_right (div_nonneg hx hD.le), max_eq_right hx]
    · rw [max_eq_left (div_neg_of_neg_of_pos hx hD).le, max_eq_left hx.le, zero_div]
  rw [hinner, hmax]
  have hlhs : (h1 : ℝ) / D - ((a1 : ℝ) / D - ap / D) * (max 0 X / D)
      = ((h1 : ℝ) - ((a1 : ℝ) - ap) * max 0 X / D) / D := by
    field_simp
  rw [hlhs]
  refine div_le_div_of_nonneg_right ?_ hD.le
  linarith

theorem val_min (a b : ℕ) : val (min a b) = min (val a) (val b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (val_le_val h)]
  · rw [min_eq_right h, min_eq_right (val_le_val h)]

/-- **`encHiAt` is an upper bound on stage consumption.** -/
theorem encHiAt_sound (P : IncomeFluctuation (Fin 7) 0 2000) (R : ℕ × ℕ) (hR2 : 0 < R.2)
    (hR : 1 + P.interest = rate R) (hinc : ∀ z, P.income z = (yQ z : ℝ)) (hg : gridOK () = true)
    (k : ℕ) (S : Stage) (hmono : ∀ z, MonotoneOn (P.stageConsumption k z) (Icc (0 : ℝ) 2000))
    (hconc : ∀ z, ConcaveOn ℝ (Icc (0 : ℝ) 2000) (P.stageConsumption k z))
    (henc : StageEnc P k S) (z : Fin 7) (ap i : ℕ) (hap : ap ≤ CAP) :
    P.stageConsumption k z (val ap) ≤ val (encHiAt R S z ap i (mUp R z ap)) := by
  have hmU : P.stageConsumption k z (val ap) ≤ val (mUp R z ap) :=
    le_trans (P.stageConsumption_le_resources k z (val ap))
      (by rw [resources_val P R hR hinc z ap hap]; exact le_mUp R hR2 z ap)
  unfold encHiAt
  split_ifs with hbr hl hr hr
  all_goals simp only [Bool.and_eq_true, decide_eq_true_eq] at hbr
  all_goals try simp only [Bool.and_eq_true, decide_eq_true_eq] at hl hr
  all_goals try (exact hmU)
  all_goals obtain ⟨⟨⟨hi1, hgi⟩, hgi1⟩, hlt⟩ := hbr
  all_goals have hC1 : grid[i+1]! ≤ CAP := grid_le_CAP hg _ hi1
  all_goals have hC0 : grid[i]! ≤ CAP := grid_le_CAP hg i (by omega)
  all_goals have hhi1 : P.stageConsumption k z (val ap) ≤ val (at2 S.hi z (i + 1)) :=
    le_trans (hmono z (val_mem ap hap) (val_mem _ hC1) (val_le_val hgi1)) (henc.hi z (i + 1) hi1)
  all_goals rw [val_min, val_min, val_min]
  all_goals refine le_min (le_min hmU hhi1) (le_min ?_ ?_)
  -- the four combinations of the two secants
  · obtain ⟨hi0, hgm⟩ := hl
    have hCm : grid[i-1]! ≤ CAP := grid_le_CAP hg _ (by omega)
    have h := le_of_left_secant (hconc z) (val_mem _ hCm) (val_mem ap hap) (val_lt_val hgm)
      (val_le_val hgi) (henc.lo z (i - 1) (by omega)) (henc.hi z i (by omega))
    exact le_trans h (leftSec_ge hgm hgi)
  · obtain ⟨hi2, hg12⟩ := hr
    have hC2 : grid[i+2]! ≤ CAP := grid_le_CAP hg _ hi2
    have h := le_of_right_secant (hconc z) (hmono z) (val_mem ap hap) (val_mem _ hC1)
      (val_mem _ hC2) (val_le_val hgi1) (val_lt_val hg12) (henc.hi z (i + 1) hi1)
      (henc.lo z (i + 2) hi2)
    exact le_trans h (rightSec_ge hg12 hgi1)
  · obtain ⟨hi0, hgm⟩ := hl
    have hCm : grid[i-1]! ≤ CAP := grid_le_CAP hg _ (by omega)
    have h := le_of_left_secant (hconc z) (val_mem _ hCm) (val_mem ap hap) (val_lt_val hgm)
      (val_le_val hgi) (henc.lo z (i - 1) (by omega)) (henc.hi z i (by omega))
    exact le_trans h (leftSec_ge hgm hgi)
  · exact hmU
  · exact hmU
  · obtain ⟨hi2, hg12⟩ := hr
    have hC2 : grid[i+2]! ≤ CAP := grid_le_CAP hg _ hi2
    have h := le_of_right_secant (hconc z) (hmono z) (val_mem ap hap) (val_mem _ hC1)
      (val_mem _ hC2) (val_le_val hgi1) (val_lt_val hg12) (henc.hi z (i + 1) hi1)
      (henc.lo z (i + 2) hi2)
    exact le_trans h (rightSec_ge hg12 hgi1)
  · exact hmU
  · exact hmU

/-- **`encHi` is an upper bound on stage consumption.** -/
theorem encHi_sound (P : IncomeFluctuation (Fin 7) 0 2000) (R : ℕ × ℕ)
    (hR : 1 + P.interest = rate R) (hinc : ∀ z, P.income z = (yQ z : ℝ)) (hg : gridOK () = true)
    (k : ℕ) (S : Stage) (hmono : ∀ z, MonotoneOn (P.stageConsumption k z) (Icc (0 : ℝ) 2000))
    (hconc : ∀ z, ConcaveOn ℝ (Icc (0 : ℝ) 2000) (P.stageConsumption k z))
    (henc : StageEnc P k S) (z : Fin 7) (ap : ℕ) (hap : ap ≤ CAP) :
    P.stageConsumption k z (val ap) ≤ val (encHi R S z ap) := by
  have hR2 := rate_pos_den P R hR
  have hmU : P.stageConsumption k z (val ap) ≤ val (mUp R z ap) :=
    le_trans (P.stageConsumption_le_resources k z (val ap))
      (by rw [resources_val P R hR hinc z ap hap]; exact le_mUp R hR2 z ap)
  unfold encHi
  split_ifs with hcor hcap
  · exact hmU
  · exact hmU
  · exact encHiAt_sound P R hR2 hR hinc hg k S hmono hconc henc z ap _ hap

end LeanEconomics.EnclCert
