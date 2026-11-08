/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.CRRAContraction

/-!
# Existence with a borrowing limit

The model carries a borrowing limit `b ≥ 0` (`KSModel.borrowLimit`): a household's position is
`a − b ≥ −b`, recorded through the shifted coordinate `a ∈ [0, ā]`; it pays the return on its
position, so cash on hand is `R (a − b) + w e`; and the price functions read the shifted mean.
Every existence theorem for `KSModel` and `KSInada` holds for every `b`; the results that need
`b = 0` say so (the monotone route `savingMonotone_of`, Light's step `incDiff_bellman`, the
capital lower bound `capital_ge`).

**`crraBorrowEconomy`**: CRRA utility, clamped Cobb–Douglas prices of **actual** capital — mean
position `K − b` — and a borrowing limit `b` below the natural bound `w̲ e̲ / R̄`, so that labour
income covers debt service at the limit. **`crraBorrow_exists_sequentialEquilibrium`**: from every
initial shock and distribution there is a sequential equilibrium in which households may borrow up
to `b`, with consumption bounded away from zero.
-/

open MeasureTheory Set

namespace LeanEconomics

namespace KrusellSmith

variable {Z E : Type*} [Fintype Z] [Fintype E]

/-- **A Krusell–Smith economy with borrowing**: CRRA utility, clamped Cobb–Douglas prices of
actual capital `K − b`, and the borrowing limit `b < w̲ e̲ / R̄`. -/
noncomputable def crraBorrowEconomy (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ}
    (hγ : 0 < γ) (b : ℝ) (hb : 0 ≤ b) (hbw : T.returnBound * b < T.wageLo * V.effLo) :
    KSInada Z E where
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
  grossReturn z K L := T.grossReturn z (K - b) L
  continuous_grossReturn z := (T.continuous_grossReturn z).comp
    ((continuous_fst.sub continuous_const).prodMk continuous_snd)
  grossReturn_nonneg z K L := T.grossReturn_nonneg z _ _
  returnBound := T.returnBound
  grossReturn_le z K L := T.grossReturn_le z _ _
  wage z K L := T.wage z (K - b) L
  continuous_wage z := (T.continuous_wage z).comp
    ((continuous_fst.sub continuous_const).prodMk continuous_snd)
  wage_nonneg z K L := T.wage_nonneg z _ _
  wageBound := T.wageBound
  wage_le z K L := T.wage_le z _ _
  borrowLimit := b
  borrowLimit_nonneg := hb
  incomeFloor := T.wageLo * V.effLo - T.returnBound * b
  incomeFloor_pos := sub_pos.2 hbw
  incomeFloor_le z K L e := by
    have h1 := mul_le_mul (T.wageLo_le_wage z (K - b) L) (V.effLo_le e) V.effLo_pos.le
      (T.wage_nonneg z (K - b) L)
    have h2 := mul_le_mul_of_nonneg_right (T.grossReturn_le z (K - b) L) hb
    linarith
  utility := crraUtility γ
  continuousOn_utility := continuousOn_crraUtility γ
  strictConcaveOn_utility := strictConcaveOn_crraUtility hγ
  monotoneOn_utility := monotoneOn_crraUtility γ
  marginalInada := marginalInada_crraUtility hγ

variable (V : KSEnvironment Z E) (T : CobbDouglas Z) {γ : ℝ} (hγ : 0 < γ) (b : ℝ) (hb : 0 ≤ b)
  (hbw : T.returnBound * b < T.wageLo * V.effLo)

theorem crraBorrowEconomy_borrowLimit :
    (crraBorrowEconomy V T hγ b hb hbw).floored.borrowLimit = b := rfl

/-- Cash on hand in the borrowing economy: the return on the position `a − b` plus labour income,
at the Cobb–Douglas prices of actual capital. -/
theorem crraBorrowEconomy_cash (z₀ : Z) (K : List Z → ℝ × ℝ)
    (s : (crraBorrowEconomy V T hγ b hb hbw).floored.State) :
    (crraBorrowEconomy V T hγ b hb hbw).floored.cash z₀ K s
      = T.grossReturn (shockAt z₀ s.2.node) ((K s.2.node).1 - b) (K s.2.node).2 * ((s.1 : ℝ) - b)
        + T.wage (shockAt z₀ s.2.node) ((K s.2.node).1 - b) (K s.2.node).2 * V.efficiency s.2.idio := by
  change T.grossReturn _ _ _ * (s.1 : ℝ) + T.wage _ _ _ * V.efficiency s.2.idio
      - T.grossReturn _ _ _ * b = _
  ring

/-- **Existence of sequential equilibrium with borrowing**: for CRRA utility and clamped
Cobb–Douglas prices of actual capital, with a borrowing limit `0 ≤ b < w̲ e̲ / R̄`, from every
initial shock and distribution of positions there is a sequential equilibrium: at every node the
shifted capital is mean shifted assets (actual capital is mean position `K − b`), every household
saves optimally with positions down to `−b`, and consumption is bounded away from zero. -/
theorem crraBorrow_exists_sequentialEquilibrium (z₀ : Z)
    (μ₀ : Measure (crraBorrowEconomy V T hγ b hb hbw).floored.AState) [IsProbabilityMeasure μ₀] :
    ∃ K ∈ (crraBorrowEconomy V T hγ b hb hbw).floored.capitalPaths
        ((crraBorrowEconomy V T hγ b hb hbw).floored.initCapital μ₀),
      (crraBorrowEconomy V T hγ b hb hbw).floored.IsSequentialEquilibrium z₀ μ₀ K ∧
      ∀ s : (crraBorrowEconomy V T hγ b hb hbw).floored.State,
        (crraBorrowEconomy V T hγ b hb hbw).floorLevel
          ≤ (crraBorrowEconomy V T hγ b hb hbw).floored.cash z₀
            ((crraBorrowEconomy V T hγ b hb hbw).floored.pricePath z₀
              ((crraBorrowEconomy V T hγ b hb hbw).floored.initMass μ₀) K) s
          - (crraBorrowEconomy V T hγ b hb hbw).floored.policy z₀
            ((crraBorrowEconomy V T hγ b hb hbw).floored.pricePath z₀
              ((crraBorrowEconomy V T hγ b hb hbw).floored.initMass μ₀) K) s := by
  obtain ⟨K, hK, hE, -, hc⟩ := (crraBorrowEconomy V T hγ b hb hbw).exists_sequentialEquilibrium z₀ μ₀
  exact ⟨K, hK, hE, fun s => (hc s).1⟩

end KrusellSmith

end LeanEconomics
