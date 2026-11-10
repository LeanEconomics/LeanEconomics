/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.KrusellSmith.ColemanEuler

/-!
# The Coleman operator and its fixed point

Milestones CO2–CO3 of `COLEMAN_PLAN.md`, as real analysis on `(z, k)`, `k ∈ [0, ā]`.

**Data** (`Data`): a Markov chain `π` on finitely many shocks, discount `β`, marginal utility `u'`
(strictly decreasing, continuous, positive, Inada at zero), a return `R(z, k)` continuous, positive
and **nonincreasing in capital** (Cobb–Douglas), cash `y(z, k)` continuous and nondecreasing in
capital (`CobbDouglas.repCash_mono`) with `y ≥ m > 0`, and **`β R̄ ≤ 1`**.

**The lattice** (`Pol`): consumption policies with `m ≤ c ≤ y`, `c` nondecreasing in capital and
saving `y − c` nondecreasing in capital. Infima are pointwise (`sInf`, `isGLB_sInf`), so `Pol` is a
complete lattice. Members are continuous: `|c(b) − c(a)| ≤ |y(b) − y(a)|` (`continuous_ext`).

**The operator** (`T`): against a policy `c`, the continuation `B(s) = β Σ π(z, z') R(z', s)
u'(c(z', s))` is continuous and antitone in saving (`continuous_cont`, `antitoneOn_cont`); the Euler
root at cash `y(z, k)` gives saving, and `T c = y − saving`. It stays in the lattice:
`m ≤ T c` because `β R̄ ≤ 1`, monotonicity and saving monotonicity from the comparative statics of
the Euler root in cash. It preserves order: a higher `c` lowers the continuation and raises
consumption (`T_mono`).

**`exists_fixed`**: Tarski gives a fixed point — **a policy solving the Euler equation, with the
corners, at every state**.
-/

open Set Filter Topology

namespace LeanEconomics

namespace KrusellSmith

namespace Coleman

/-- The data of the representative-agent Euler problem. -/
structure Data (Z : Type*) [Fintype Z] where
  π : Z → Z → ℝ
  π_nonneg : ∀ z z', 0 ≤ π z z'
  π_sum : ∀ z, ∑ z', π z z' = 1
  β : ℝ
  β_pos : 0 < β
  cap : ℝ
  cap_pos : 0 < cap
  du : ℝ → ℝ
  du_anti : StrictAntiOn du (Ioi 0)
  du_cont : ContinuousOn du (Ioi 0)
  du_pos : ∀ c, 0 < c → 0 < du c
  du_inada : Tendsto du (𝓝[>] 0) atTop
  R : Z → ℝ → ℝ
  R_cont : ∀ z, Continuous (R z)
  R_nonneg : ∀ z k, 0 ≤ R z k
  R_anti : ∀ z, AntitoneOn (R z) (Icc 0 cap)
  Rbar : ℝ
  R_le : ∀ z k, R z k ≤ Rbar
  βR_le : β * Rbar ≤ 1
  y : Z → ℝ → ℝ
  y_cont : ∀ z, Continuous (y z)
  y_mono : ∀ z, MonotoneOn (y z) (Icc 0 cap)
  m : ℝ
  m_pos : 0 < m
  m_le_y : ∀ z k, k ∈ Icc 0 cap → m ≤ y z k

variable {Z : Type*} [Fintype Z] (D : Data Z)

namespace Data

/-- Capital levels. -/
abbrev Box := ↥(Icc (0 : ℝ) D.cap)

/-- **The policy constraints**: `m ≤ c ≤ y`, consumption and saving nondecreasing in capital. -/
def InC (c : Z → D.Box → ℝ) : Prop :=
  (∀ z k, D.m ≤ c z k) ∧ (∀ z (k : D.Box), c z k ≤ D.y z k) ∧
    (∀ z (a b : D.Box), (a : ℝ) ≤ b → c z a ≤ c z b) ∧
    (∀ z (a b : D.Box), (a : ℝ) ≤ b → c z b - c z a ≤ D.y z b - D.y z a)

/-- **The lattice of policies.** -/
def Pol := {c : Z → D.Box → ℝ // D.InC c}

instance : PartialOrder D.Pol := Subtype.partialOrder _

/-- Consuming all cash is a policy (the top). -/
theorem inC_y : D.InC fun z k => D.y z k :=
  ⟨fun z k => D.m_le_y z k k.2, fun _ _ => le_rfl, fun z a b hab => D.y_mono z a.2 b.2 hab,
    fun _ _ _ _ => le_rfl⟩

open Classical in
/-- Pointwise infima (consume all cash for the empty set). -/
noncomputable instance : InfSet D.Pol where
  sInf S := if hS : S.Nonempty then
      ⟨fun z k => sInf ((fun c : D.Pol => c.1 z k) '' S), by
        have hb : ∀ z k, BddBelow ((fun c : D.Pol => c.1 z k) '' S) := fun z k =>
          ⟨D.m, by rintro _ ⟨c, -, rfl⟩; exact c.2.1 z k⟩
        have hne : ∀ z k, ((fun c : D.Pol => c.1 z k) '' S).Nonempty := fun z k =>
          hS.image _
        obtain ⟨c₀, hc₀⟩ := hS
        refine ⟨fun z k => le_csInf (hne z k) ?_, fun z k => ?_, fun z a b hab => ?_,
          fun z a b hab => ?_⟩
        · rintro _ ⟨c, -, rfl⟩; exact c.2.1 z k
        · exact (csInf_le (hb z k) ⟨c₀, hc₀, rfl⟩).trans (c₀.2.2.1 z k)
        · refine le_csInf (hne z b) ?_
          rintro _ ⟨c, hc, rfl⟩
          exact (csInf_le (hb z a) ⟨c, hc, rfl⟩).trans (c.2.2.2.1 z a b hab)
        · have : sInf ((fun c : D.Pol => c.1 z b) '' S) - (D.y z b - D.y z a)
              ≤ sInf ((fun c : D.Pol => c.1 z a) '' S) := by
            refine le_csInf (hne z a) ?_
            rintro _ ⟨c, hc, rfl⟩
            have h1 := csInf_le (hb z b) ⟨c, hc, rfl⟩
            have h2 := c.2.2.2.2 z a b hab
            simp only at h1 ⊢
            linarith
          linarith⟩
    else ⟨fun z k => D.y z k, D.inC_y⟩

open Classical in
theorem isGLB_sInf (S : Set D.Pol) : IsGLB S (sInf S) := by
  by_cases hS : S.Nonempty
  · have hval : ∀ z k, (sInf S : D.Pol).1 z k = sInf ((fun c : D.Pol => c.1 z k) '' S) :=
      fun z k => by
        change (if hS : S.Nonempty then _ else _ : D.Pol).1 z k = _
        simp only [hS, ↓reduceDIte]
    have hb : ∀ z k, BddBelow ((fun c : D.Pol => c.1 z k) '' S) := fun z k =>
      ⟨D.m, by rintro _ ⟨c, -, rfl⟩; exact c.2.1 z k⟩
    refine ⟨fun c hc z k => ?_, fun d hd z k => ?_⟩
    · rw [hval]
      exact csInf_le (hb z k) ⟨c, hc, rfl⟩
    · change d.1 z k ≤ (sInf S : D.Pol).1 z k
      rw [hval]
      refine le_csInf (hS.image _) ?_
      rintro _ ⟨c, hc, rfl⟩
      exact hd hc z k
  · have hval : (sInf S : D.Pol).1 = fun z (k : D.Box) => D.y z k := by
      change (if hS : S.Nonempty then _ else _ : D.Pol).1 = _
      simp only [hS, ↓reduceDIte]
    refine ⟨fun c hc => absurd ⟨c, hc⟩ hS, fun d _ z k => ?_⟩
    change d.1 z k ≤ (sInf S : D.Pol).1 z k
    rw [hval]
    exact d.2.2.1 z k

/-- **The policies form a complete lattice.** -/
noncomputable instance : CompleteLattice D.Pol := completeLatticeOfInf D.Pol D.isGLB_sInf

/-! ### The continuation -/

/-- A policy extended to all saving levels (clamped into `[0, ā]`). -/
noncomputable def ext (c : D.Pol) (z : Z) (s : ℝ) : ℝ :=
  c.1 z (projIcc 0 D.cap D.cap_pos.le s)

theorem continuous_pol (c : D.Pol) (z : Z) : Continuous (c.1 z) := by
  have hy : Continuous fun k : D.Box => D.y z k := (D.y_cont z).comp continuous_subtype_val
  rw [Metric.continuous_iff] at hy ⊢
  intro b ε hε
  obtain ⟨δ, hδ, h⟩ := hy b ε hε
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have hya := h a ha
  rw [Real.dist_eq] at hya ⊢
  refine lt_of_le_of_lt ?_ hya
  rcases le_total (a : ℝ) b with hab | hab
  · have h1 := c.2.2.2.1 z a b hab
    have h2 := c.2.2.2.2 z a b hab
    have h3 := D.y_mono z a.2 b.2 hab
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h1 := c.2.2.2.1 z b a hab
    have h2 := c.2.2.2.2 z b a hab
    have h3 := D.y_mono z b.2 a.2 hab
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

theorem continuous_ext (c : D.Pol) (z : Z) : Continuous (D.ext c z) :=
  (D.continuous_pol c z).comp continuous_projIcc

/-- **The continuation** against `c`: discounted expected return times marginal utility. -/
noncomputable def cont (c : D.Pol) (z : Z) (s : ℝ) : ℝ :=
  D.β * ∑ z', D.π z z' * D.R z' s * D.du (D.ext c z' s)

theorem continuous_cont (c : D.Pol) (z : Z) : Continuous (D.cont c z) := by
  refine continuous_const.mul (continuous_finsetSum _ fun z' _ => ?_)
  refine (continuous_const.mul (D.R_cont z')).mul ?_
  exact D.du_cont.comp_continuous (D.continuous_ext c z')
    fun s => mem_Ioi.2 (D.m_pos.trans_le (c.2.1 z' _))

theorem du_le_du_m (c : D.Pol) (z : Z) (s : ℝ) : D.du (D.ext c z s) ≤ D.du D.m := by
  rcases (c.2.1 z (projIcc 0 D.cap D.cap_pos.le s)).lt_or_eq with h | h
  · exact (D.du_anti (mem_Ioi.2 D.m_pos) (mem_Ioi.2 (D.m_pos.trans h)) h).le
  · rw [ext, ← h]

theorem antitoneOn_cont (c : D.Pol) (z : Z) : AntitoneOn (D.cont c z) (Icc 0 D.cap) := by
  intro a ha b hb hab
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z' _ => ?_) D.β_pos.le
  have hR := D.R_anti z' ha hb hab
  have hpa : projIcc 0 D.cap D.cap_pos.le a = ⟨a, ha⟩ := projIcc_of_mem _ ha
  have hpb : projIcc 0 D.cap D.cap_pos.le b = ⟨b, hb⟩ := projIcc_of_mem _ hb
  have hc : D.ext c z' a ≤ D.ext c z' b := by
    simp only [ext, hpa, hpb]
    exact c.2.2.2.1 z' ⟨a, ha⟩ ⟨b, hb⟩ hab
  have hu : D.du (D.ext c z' b) ≤ D.du (D.ext c z' a) := by
    rcases hc.lt_or_eq with h | h
    · exact (D.du_anti (mem_Ioi.2 (D.m_pos.trans_le (c.2.1 z' _)))
        (mem_Ioi.2 (D.m_pos.trans_le (c.2.1 z' _))) h).le
    · rw [h]
  have hu0 : 0 ≤ D.du (D.ext c z' b) := (D.du_pos _ (D.m_pos.trans_le (c.2.1 z' _))).le
  have := mul_le_mul hR hu hu0 (D.R_nonneg z' a)
  have hp := D.π_nonneg z z'
  calc D.π z z' * D.R z' b * D.du (D.ext c z' b)
      = D.π z z' * (D.R z' b * D.du (D.ext c z' b)) := by ring
    _ ≤ D.π z z' * (D.R z' a * D.du (D.ext c z' a)) := mul_le_mul_of_nonneg_left this hp
    _ = D.π z z' * D.R z' a * D.du (D.ext c z' a) := by ring

theorem cont_le (c : D.Pol) (z : Z) (s : ℝ) : D.cont c z s ≤ D.du D.m := by
  have hdm := (D.du_pos _ D.m_pos).le
  have h : ∑ z', D.π z z' * D.R z' s * D.du (D.ext c z' s) ≤ D.Rbar * D.du D.m := by
    calc ∑ z', D.π z z' * D.R z' s * D.du (D.ext c z' s)
        ≤ ∑ z', D.π z z' * (D.Rbar * D.du D.m) := Finset.sum_le_sum fun z' _ => by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (D.R_le z' s) (D.du_le_du_m c z' s)
            (D.du_pos _ (D.m_pos.trans_le (c.2.1 z' _))).le
            ((D.R_nonneg z' s).trans (D.R_le z' s))) (D.π_nonneg z z')
      _ = D.Rbar * D.du D.m := by rw [← Finset.sum_mul, D.π_sum, one_mul]
  have hRb : 0 ≤ D.Rbar := (D.R_nonneg z 0).trans (D.R_le z 0)
  calc D.cont c z s ≤ D.β * (D.Rbar * D.du D.m) := mul_le_mul_of_nonneg_left h D.β_pos.le
    _ = (D.β * D.Rbar) * D.du D.m := by ring
    _ ≤ 1 * D.du D.m := mul_le_mul_of_nonneg_right D.βR_le hdm
    _ = D.du D.m := one_mul _

/-- Higher consumption tomorrow lowers the continuation. -/
theorem cont_anti_pol {c c' : D.Pol} (h : c ≤ c') (z : Z) (s : ℝ) :
    D.cont c' z s ≤ D.cont c z s := by
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z' _ => ?_) D.β_pos.le
  have hc : D.ext c z' s ≤ D.ext c' z' s := h z' _
  have hu : D.du (D.ext c' z' s) ≤ D.du (D.ext c z' s) := by
    rcases hc.lt_or_eq with h' | h'
    · exact (D.du_anti (mem_Ioi.2 (D.m_pos.trans_le (c.2.1 z' _)))
        (mem_Ioi.2 (D.m_pos.trans_le (c'.2.1 z' _))) h').le
    · rw [h']
  exact mul_le_mul_of_nonneg_left hu (mul_nonneg (D.π_nonneg z z') (D.R_nonneg z' s))

/-! ### The operator -/

theorem y_pos (z : Z) (k : D.Box) : 0 < D.y z k := D.m_pos.trans_le (D.m_le_y z k k.2)

/-- Saving at `(z, k)` against `c`: the Euler root. -/
noncomputable def saving (c : D.Pol) (z : Z) (k : D.Box) : ℝ :=
  Classical.choose (exists_eulerRoot D.du_cont D.du_inada (D.continuous_cont c z).continuousOn
    D.cap_pos (D.y_pos z k))

theorem saving_spec (c : D.Pol) (z : Z) (k : D.Box) :
    IsEulerRoot D.du (D.cont c z) D.cap (D.y z k) (D.saving c z k) :=
  Classical.choose_spec (exists_eulerRoot D.du_cont D.du_inada
    (D.continuous_cont c z).continuousOn D.cap_pos (D.y_pos z k))

/-- **The Coleman operator stays in the lattice.** -/
theorem inC_T (c : D.Pol) : D.InC fun z k => D.y z k - D.saving c z k := by
  refine ⟨fun z k => ?_, fun z k => ?_, fun z a b hab => ?_, fun z a b hab => ?_⟩
  · -- `m ≤ T c`: at a positive saving the Euler inequality and `β R̄ ≤ 1`
    show D.m ≤ D.y z k - D.saving c z k
    obtain ⟨hs0, -, hsy, hs1, -⟩ := D.saving_spec c z k
    rcases hs0.lt_or_eq with hpos | hzero
    · by_contra hlt
      push Not at hlt
      have h1 := hs1 hpos
      have h2 := D.cont_le c z (D.saving c z k)
      have h3 : D.du D.m < D.du (D.y z k - D.saving c z k) :=
        D.du_anti (mem_Ioi.2 (by linarith)) (mem_Ioi.2 D.m_pos) hlt
      linarith
    · rw [← hzero, sub_zero]
      exact D.m_le_y z k k.2
  · linarith [(D.saving_spec c z k).1]
  · exact eulerRoot_cons_le D.du_anti (D.antitoneOn_cont c z) (fun _ _ => le_rfl)
      (D.y_mono z a.2 b.2 hab) (D.saving_spec c z a) (D.saving_spec c z b)
  · have := eulerRoot_saving_le D.du_anti (D.antitoneOn_cont c z) (D.y_mono z a.2 b.2 hab)
      (D.saving_spec c z a) (D.saving_spec c z b)
    linarith

/-- **The Coleman operator**: solve today's Euler equation against tomorrow's policy. -/
noncomputable def T : D.Pol →o D.Pol where
  toFun c := ⟨fun z k => D.y z k - D.saving c z k, D.inC_T c⟩
  monotone' c c' h z k := by
    change D.y z k - D.saving c z k ≤ D.y z k - D.saving c' z k
    exact eulerRoot_cons_le D.du_anti (D.antitoneOn_cont c z)
      (fun s _ => D.cont_anti_pol h z s) le_rfl (D.saving_spec c z k) (D.saving_spec c' z k)

/-- **A fixed point of the Coleman operator**: a policy in the lattice that solves the Euler
equation, with the corners at zero saving and at the cap, at every state. -/
theorem exists_fixed : ∃ c : D.Pol, ∀ z (k : D.Box),
    IsEulerRoot D.du (D.cont c z) D.cap (D.y z k) (D.y z k - c.1 z k) := by
  refine ⟨OrderHom.gfp D.T, fun z k => ?_⟩
  have hfix : D.T (OrderHom.gfp D.T) = OrderHom.gfp D.T := OrderHom.map_gfp D.T
  have hval : (OrderHom.gfp D.T).1 z k = D.y z k - D.saving (OrderHom.gfp D.T) z k := by
    conv_lhs => rw [← hfix]
    rfl
  rw [hval, sub_sub_cancel]
  exact D.saving_spec _ z k

end Data

end Coleman

end KrusellSmith

end LeanEconomics
