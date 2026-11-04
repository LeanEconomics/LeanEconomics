/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.Inada
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Cobb–Douglas prices, clamped

With production `Y = z K^α L^{1-α}` the gross return `1 - δ + α z (L/K)^{1-α}` grows without
bound as aggregate capital falls to zero, and the wage `(1 - α) z (K/L)^α` falls to zero, so
neither is a bounded price function with a positive wage floor, as `KSModel` and `KSInada` ask.
This module evaluates the marginal products at capital **clamped** to `[capLo, capHi]` and labour
clamped to `[labLo, labHi]`, with `capLo, labLo > 0`, which gives prices of the required kind.

* `continuous_grossReturn`, `grossReturn_nonneg`, `grossReturn_le`, `continuous_wage`,
  `wage_nonneg`, `wage_le`, `wageLo_le_wage`: the clamped prices satisfy the price conditions of
  `KSModel` and `KSInada`, with a wage floor `wageLo > 0`.
* `grossReturn_of_mem`, `wage_of_mem`: inside the clamping box the prices are the Cobb–Douglas
  marginal products.
* `KSInada.labour_mem`: with total mass one and efficiencies in `[effLo, effHi]`, aggregate labour
  at every node lies in `[effLo, effHi]`. Clamping labour to that interval therefore **never
  binds**: only the capital clamp is a real restriction.
* `logEconomy`: a Krusell–Smith economy with log utility and clamped Cobb–Douglas prices, as a
  `KSInada`; `logEconomy_exists_equilibrium`: it has a sequential equilibrium, and at every node
  where equilibrium capital is at least `capLo` the prices are the unclamped Cobb–Douglas prices
  at equilibrium capital and labour.

Showing that equilibrium capital never falls below some `capLo > 0`, which would remove the
clamp altogether, needs quantitative lower bounds on saving and is not done here.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace KrusellSmith

/-- **Clamped Cobb–Douglas technology.** Total factor productivity `tfp z` in each aggregate
state, capital share `share`, depreciation `depreciation`, and the clamping box. -/
structure CobbDouglas (Z : Type*) where
  tfp : Z → ℝ
  tfpLo : ℝ
  tfpHi : ℝ
  tfpLo_pos : 0 < tfpLo
  tfpLo_le : ∀ z, tfpLo ≤ tfp z
  tfp_le : ∀ z, tfp z ≤ tfpHi
  share : ℝ
  share_pos : 0 < share
  share_lt_one : share < 1
  depreciation : ℝ
  depreciation_nonneg : 0 ≤ depreciation
  depreciation_le_one : depreciation ≤ 1
  capLo : ℝ
  capHi : ℝ
  capLo_pos : 0 < capLo
  capLo_le : capLo ≤ capHi
  labLo : ℝ
  labHi : ℝ
  labLo_pos : 0 < labLo
  labLo_le : labLo ≤ labHi

namespace CobbDouglas

variable {Z : Type*} (T : CobbDouglas Z)

/-- Capital clamped to `[capLo, capHi]`. -/
def clampCap (K : ℝ) : ℝ := max T.capLo (min T.capHi K)

/-- Labour clamped to `[labLo, labHi]`. -/
def clampLab (L : ℝ) : ℝ := max T.labLo (min T.labHi L)

theorem clampCap_mem (K : ℝ) : T.clampCap K ∈ Icc T.capLo T.capHi :=
  ⟨le_max_left _ _, max_le T.capLo_le (min_le_left _ _)⟩

theorem clampLab_mem (L : ℝ) : T.clampLab L ∈ Icc T.labLo T.labHi :=
  ⟨le_max_left _ _, max_le T.labLo_le (min_le_left _ _)⟩

theorem clampCap_of_mem {K : ℝ} (hK : K ∈ Icc T.capLo T.capHi) : T.clampCap K = K := by
  rw [clampCap, min_eq_right hK.2, max_eq_right hK.1]

theorem clampLab_of_mem {L : ℝ} (hL : L ∈ Icc T.labLo T.labHi) : T.clampLab L = L := by
  rw [clampLab, min_eq_right hL.2, max_eq_right hL.1]

theorem continuous_clampCap : Continuous T.clampCap :=
  continuous_const.max (continuous_const.min continuous_id)

theorem continuous_clampLab : Continuous T.clampLab :=
  continuous_const.max (continuous_const.min continuous_id)

/-- The **gross return**: one less depreciation plus the marginal product of capital, at clamped
capital and labour. -/
noncomputable def grossReturn (z : Z) (K L : ℝ) : ℝ :=
  1 - T.depreciation
    + T.share * T.tfp z * T.clampCap K ^ (T.share - 1) * T.clampLab L ^ (1 - T.share)

/-- The **wage**: the marginal product of labour, at clamped capital and labour. -/
noncomputable def wage (z : Z) (K L : ℝ) : ℝ :=
  (1 - T.share) * T.tfp z * T.clampCap K ^ T.share * T.clampLab L ^ (-T.share)

theorem clampCap_pos (K : ℝ) : 0 < T.clampCap K := T.capLo_pos.trans_le (T.clampCap_mem K).1

theorem clampLab_pos (L : ℝ) : 0 < T.clampLab L := T.labLo_pos.trans_le (T.clampLab_mem L).1

theorem continuous_rpow_clampCap (q : ℝ) : Continuous fun K => T.clampCap K ^ q :=
  continuous_iff_continuousAt.2 fun K =>
    (Real.continuousAt_rpow_const _ q (Or.inl (T.clampCap_pos K).ne')).comp
      T.continuous_clampCap.continuousAt

theorem continuous_rpow_clampLab (q : ℝ) : Continuous fun L => T.clampLab L ^ q :=
  continuous_iff_continuousAt.2 fun L =>
    (Real.continuousAt_rpow_const _ q (Or.inl (T.clampLab_pos L).ne')).comp
      T.continuous_clampLab.continuousAt

theorem continuous_grossReturn (z : Z) :
    Continuous fun p : ℝ × ℝ => T.grossReturn z p.1 p.2 :=
  continuous_const.add ((continuous_const.mul ((T.continuous_rpow_clampCap _).comp
    continuous_fst)).mul ((T.continuous_rpow_clampLab _).comp continuous_snd))

theorem continuous_wage (z : Z) : Continuous fun p : ℝ × ℝ => T.wage z p.1 p.2 :=
  (continuous_const.mul ((T.continuous_rpow_clampCap _).comp continuous_fst)).mul
    ((T.continuous_rpow_clampLab _).comp continuous_snd)

theorem tfp_pos (z : Z) : 0 < T.tfp z := T.tfpLo_pos.trans_le (T.tfpLo_le z)

theorem grossReturn_nonneg (z : Z) (K L : ℝ) : 0 ≤ T.grossReturn z K L := by
  have h1 : 0 ≤ 1 - T.depreciation := sub_nonneg.2 T.depreciation_le_one
  have h2 : 0 ≤ T.share * T.tfp z * T.clampCap K ^ (T.share - 1) * T.clampLab L ^ (1 - T.share) :=
    mul_nonneg (mul_nonneg (mul_nonneg T.share_pos.le (T.tfp_pos z).le)
      (Real.rpow_nonneg (T.clampCap_pos K).le _)) (Real.rpow_nonneg (T.clampLab_pos L).le _)
  exact add_nonneg h1 h2

/-- An upper bound on the clamped gross return. -/
noncomputable def returnBound : ℝ :=
  1 - T.depreciation
    + T.share * T.tfpHi * T.capLo ^ (T.share - 1) * T.labHi ^ (1 - T.share)

theorem grossReturn_le (z : Z) (K L : ℝ) : T.grossReturn z K L ≤ T.returnBound := by
  have hK : T.clampCap K ^ (T.share - 1) ≤ T.capLo ^ (T.share - 1) :=
    Real.rpow_le_rpow_of_nonpos T.capLo_pos (T.clampCap_mem K).1 (by linarith [T.share_lt_one])
  have hL : T.clampLab L ^ (1 - T.share) ≤ T.labHi ^ (1 - T.share) :=
    Real.rpow_le_rpow (T.clampLab_pos L).le (T.clampLab_mem L).2 (by linarith [T.share_lt_one])
  have hz := T.tfp_le z
  have h0K := Real.rpow_nonneg (T.clampCap_pos K).le (T.share - 1)
  have h0L := Real.rpow_nonneg (T.clampLab_pos L).le (1 - T.share)
  have hs := T.share_pos
  have htz := T.tfp_pos z
  have hHi : 0 ≤ T.tfpHi := htz.le.trans hz
  have : T.share * T.tfp z * T.clampCap K ^ (T.share - 1) * T.clampLab L ^ (1 - T.share)
      ≤ T.share * T.tfpHi * T.capLo ^ (T.share - 1) * T.labHi ^ (1 - T.share) :=
    mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hz hs.le) hK h0K (mul_nonneg hs.le hHi)) hL
      h0L (mul_nonneg (mul_nonneg hs.le hHi) (Real.rpow_nonneg T.capLo_pos.le _))
  unfold grossReturn returnBound
  linarith

theorem wage_nonneg (z : Z) (K L : ℝ) : 0 ≤ T.wage z K L :=
  mul_nonneg (mul_nonneg (mul_nonneg (by linarith [T.share_lt_one]) (T.tfp_pos z).le)
    (Real.rpow_nonneg (T.clampCap_pos K).le _)) (Real.rpow_nonneg (T.clampLab_pos L).le _)

/-- An upper bound on the clamped wage. -/
noncomputable def wageBound : ℝ :=
  (1 - T.share) * T.tfpHi * T.capHi ^ T.share * T.labLo ^ (-T.share)

theorem wage_le (z : Z) (K L : ℝ) : T.wage z K L ≤ T.wageBound := by
  have hK : T.clampCap K ^ T.share ≤ T.capHi ^ T.share :=
    Real.rpow_le_rpow (T.clampCap_pos K).le (T.clampCap_mem K).2 T.share_pos.le
  have hL : T.clampLab L ^ (-T.share) ≤ T.labLo ^ (-T.share) :=
    Real.rpow_le_rpow_of_nonpos T.labLo_pos (T.clampLab_mem L).1 (by linarith [T.share_pos])
  have hs : 0 ≤ 1 - T.share := by linarith [T.share_lt_one]
  have hHi : 0 ≤ T.tfpHi := (T.tfp_pos z).le.trans (T.tfp_le z)
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (T.tfp_le z) hs) hK
    (Real.rpow_nonneg (T.clampCap_pos K).le _) (mul_nonneg hs hHi)) hL
    (Real.rpow_nonneg (T.clampLab_pos L).le _)
    (mul_nonneg (mul_nonneg hs hHi) (Real.rpow_nonneg (T.capLo_pos.trans_le T.capLo_le).le _))

/-- A positive lower bound on the clamped wage. -/
noncomputable def wageLo : ℝ :=
  (1 - T.share) * T.tfpLo * T.capLo ^ T.share * T.labHi ^ (-T.share)

theorem wageLo_pos : 0 < T.wageLo :=
  mul_pos (mul_pos (mul_pos (by linarith [T.share_lt_one]) T.tfpLo_pos)
    (Real.rpow_pos_of_pos T.capLo_pos _))
    (Real.rpow_pos_of_pos (T.labLo_pos.trans_le T.labLo_le) _)

theorem wageLo_le_wage (z : Z) (K L : ℝ) : T.wageLo ≤ T.wage z K L := by
  have hK : T.capLo ^ T.share ≤ T.clampCap K ^ T.share :=
    Real.rpow_le_rpow T.capLo_pos.le (T.clampCap_mem K).1 T.share_pos.le
  have hL : T.labHi ^ (-T.share) ≤ T.clampLab L ^ (-T.share) :=
    Real.rpow_le_rpow_of_nonpos (T.clampLab_pos L) (T.clampLab_mem L).2 (by linarith [T.share_pos])
  have hs : 0 ≤ 1 - T.share := by linarith [T.share_lt_one]
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (T.tfpLo_le z) hs) hK
    (Real.rpow_nonneg T.capLo_pos.le _) (mul_nonneg hs (T.tfp_pos z).le)) hL
    (Real.rpow_nonneg (T.labLo_pos.trans_le T.labLo_le).le _)
    (mul_nonneg (mul_nonneg hs (T.tfp_pos z).le) (Real.rpow_nonneg (T.clampCap_pos K).le _))

/-- Inside the clamping box the gross return is one less depreciation plus the marginal product
of capital. -/
theorem grossReturn_of_mem (z : Z) {K L : ℝ} (hK : K ∈ Icc T.capLo T.capHi)
    (hL : L ∈ Icc T.labLo T.labHi) :
    T.grossReturn z K L
      = 1 - T.depreciation + T.share * T.tfp z * K ^ (T.share - 1) * L ^ (1 - T.share) := by
  rw [grossReturn, T.clampCap_of_mem hK, T.clampLab_of_mem hL]

/-- Inside the clamping box the wage is the marginal product of labour. -/
theorem wage_of_mem (z : Z) {K L : ℝ} (hK : K ∈ Icc T.capLo T.capHi)
    (hL : L ∈ Icc T.labLo T.labHi) :
    T.wage z K L = (1 - T.share) * T.tfp z * K ^ T.share * L ^ (-T.share) := by
  rw [wage, T.clampCap_of_mem hK, T.clampLab_of_mem hL]

end CobbDouglas

variable {Z E : Type*} [Fintype Z] [Fintype E]

namespace KSModel

variable (M : KSModel Z E) (z₀ : Z)

/-- The initial masses of a probability distribution are nonnegative and sum to one. -/
theorem initMass_nonneg (μ₀ : Measure M.AState) (e : E) : 0 ≤ M.initMass μ₀ e :=
  measureReal_nonneg

theorem sum_initMass (μ₀ : Measure M.AState) [IsProbabilityMeasure μ₀] :
    ∑ e, M.initMass μ₀ e = 1 := by
  have h := M.integral_of_idio (μ := μ₀) (fun _ => (1 : ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, one_mul] at h
  exact h.symm

/-- **Aggregate labour at every node lies between the lowest and the highest efficiency.** -/
theorem labour_mem (μ₀ : Measure M.AState) [IsProbabilityMeasure μ₀] {effLo effHi : ℝ}
    (hlo : ∀ e, effLo ≤ M.efficiency e) (hhi : ∀ e, M.efficiency e ≤ effHi) (h : List Z) :
    M.labour z₀ (M.initMass μ₀) h ∈ Icc effLo effHi := by
  have hm := M.stateMass_nonneg z₀ (M.initMass_nonneg μ₀) h
  have hsum : ∑ e, M.stateMass z₀ (M.initMass μ₀) h e = 1 := by
    rw [M.sum_stateMass, M.sum_initMass μ₀]
  constructor
  · calc effLo = ∑ e, M.stateMass z₀ (M.initMass μ₀) h e * effLo := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ M.labour z₀ (M.initMass μ₀) h :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hlo e) (hm e)
  · calc M.labour z₀ (M.initMass μ₀) h
        ≤ ∑ e, M.stateMass z₀ (M.initMass μ₀) h e * effHi :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hhi e) (hm e)
      _ = effHi := by rw [← Finset.sum_mul, hsum, one_mul]

end KSModel

/-! ### A log-utility Krusell–Smith economy with Cobb–Douglas production -/

/-- The primitives of a Krusell–Smith economy apart from technology and preferences. -/
structure KSEnvironment (Z E : Type*) [Fintype Z] [Fintype E] where
  aggProb : Z → Z → ℝ
  aggProb_nonneg : ∀ z z', 0 ≤ aggProb z z'
  aggProb_sum : ∀ z, ∑ z', aggProb z z' = 1
  idioProb : Z → Z → E → E → ℝ
  idioProb_nonneg : ∀ z z' e e', 0 ≤ idioProb z z' e e'
  idioProb_sum : ∀ z z' e, ∑ e', idioProb z z' e e' = 1
  efficiency : E → ℝ
  effLo : ℝ
  effHi : ℝ
  effLo_pos : 0 < effLo
  effLo_le : ∀ e, effLo ≤ efficiency e
  le_effHi : ∀ e, efficiency e ≤ effHi
  assetCap : ℝ
  assetCap_pos : 0 < assetCap
  discount : ℝ
  discount_pos : 0 < discount
  discount_lt_one : discount < 1

/-- **A Krusell–Smith economy with log utility and clamped Cobb–Douglas prices.** -/
noncomputable def logEconomy (V : KSEnvironment Z E) (T : CobbDouglas Z) : KSInada Z E where
  aggProb := V.aggProb
  aggProb_nonneg := V.aggProb_nonneg
  aggProb_sum := V.aggProb_sum
  idioProb := V.idioProb
  idioProb_nonneg := V.idioProb_nonneg
  idioProb_sum := V.idioProb_sum
  efficiency := V.efficiency
  efficiency_nonneg e := V.effLo_pos.le.trans (V.effLo_le e)
  assetCap := V.assetCap
  assetCap_pos := V.assetCap_pos
  discount := V.discount
  discount_pos := V.discount_pos
  discount_lt_one := V.discount_lt_one
  grossReturn := T.grossReturn
  continuous_grossReturn := T.continuous_grossReturn
  grossReturn_nonneg := T.grossReturn_nonneg
  returnBound := T.returnBound
  grossReturn_le := T.grossReturn_le
  wage := T.wage
  continuous_wage := T.continuous_wage
  wage_nonneg := T.wage_nonneg
  wageBound := T.wageBound
  wage_le := T.wage_le
  incomeFloor := T.wageLo * V.effLo
  incomeFloor_pos := mul_pos T.wageLo_pos V.effLo_pos
  incomeFloor_le z K L e :=
    mul_le_mul (T.wageLo_le_wage z K L) (V.effLo_le e) V.effLo_pos.le (T.wage_nonneg z K L)
  utility := crraUtility 1
  continuousOn_utility := continuousOn_crraUtility 1
  strictConcaveOn_utility := strictConcaveOn_crraUtility one_pos
  monotoneOn_utility := monotoneOn_crraUtility 1
  marginalInada := marginalInada_crraUtility one_pos

/-- **Sequential equilibrium with log utility and Cobb–Douglas production.** The log economy
with clamped Cobb–Douglas prices has a sequential equilibrium, with households optimal among all
savings with positive consumption. At every node, aggregate labour lies within the labour clamp,
and wherever equilibrium capital is at least `capLo` (and at most `capHi`) the gross return and
the wage are the unclamped Cobb–Douglas marginal products at equilibrium capital and labour. -/
theorem logEconomy_exists_equilibrium (V : KSEnvironment Z E) (T : CobbDouglas Z)
    (hlab : T.labLo = V.effLo ∧ T.labHi = V.effHi) (z₀ : Z)
    (μ₀ : Measure (logEconomy V T).floored.AState) [IsProbabilityMeasure μ₀] :
    ∃ K ∈ (logEconomy V T).floored.capitalPaths
        ((logEconomy V T).floored.initCapital μ₀),
      (logEconomy V T).floored.IsSequentialEquilibrium z₀ μ₀ K ∧
      (∀ s : (logEconomy V T).floored.State,
        (logEconomy V T).floorLevel
          ≤ (logEconomy V T).floored.cash z₀ ((logEconomy V T).floored.pricePath z₀
                ((logEconomy V T).floored.initMass μ₀) K) s
            - (logEconomy V T).floored.policy z₀
                ((logEconomy V T).floored.pricePath z₀
                ((logEconomy V T).floored.initMass μ₀) K) s) ∧
      ∀ h, (logEconomy V T).floored.labour z₀ ((logEconomy V T).floored.initMass μ₀) h
          ∈ Icc T.labLo T.labHi ∧
        (K h ∈ Icc T.capLo T.capHi →
          (logEconomy V T).floored.returnAt z₀ ((logEconomy V T).floored.pricePath z₀
                ((logEconomy V T).floored.initMass μ₀) K) h
            = 1 - T.depreciation + T.share * T.tfp (shockAt z₀ h) * K h ^ (T.share - 1)
                * (logEconomy V T).floored.labour z₀
                    ((logEconomy V T).floored.initMass μ₀) h ^ (1 - T.share) ∧
          (logEconomy V T).floored.wageAt z₀ ((logEconomy V T).floored.pricePath z₀
                ((logEconomy V T).floored.initMass μ₀) K) h
            = (1 - T.share) * T.tfp (shockAt z₀ h) * K h ^ T.share
                * (logEconomy V T).floored.labour z₀
                    ((logEconomy V T).floored.initMass μ₀) h ^ (-T.share)) := by
  revert μ₀
  set P := logEconomy V T with hP
  intro μ₀ _
  obtain ⟨K, hK, heq, -, hopt⟩ := P.exists_sequentialEquilibrium z₀ μ₀
  have hL : ∀ h, P.floored.labour z₀ (P.floored.initMass μ₀) h ∈ Icc T.labLo T.labHi := by
    intro h
    rw [hlab.1, hlab.2]
    exact P.floored.labour_mem z₀ μ₀ V.effLo_le V.le_effHi h
  refine ⟨K, hK, heq, fun s => (hopt s).1, fun h => ⟨hL h, fun hKh => ⟨?_, ?_⟩⟩⟩
  · exact T.grossReturn_of_mem _ hKh (hL h)
  · exact T.wage_of_mem _ hKh (hL h)

end KrusellSmith

end LeanEconomics
