/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.PositiveCapital

/-!
# Impatience is a theorem, not an assumption

**Marcet, Obiols-Homs and Weil (2007, JME 54, 2621–2635), Proposition 3**: in a stationary
equilibrium with positive capital and labour, `β (1 + r) < 1`. Their proof runs through
Chamberlain and Wilson (2000) for `β (1 + r) > 1` and through the labour margin for
`β (1 + r) = 1`, neither of which this development has. What it does have is the secant-slope
technology, and that is enough for the exogenous-labour analogue:

  **if `β (1 + r) ≥ 1` then assets never fall, so the asset cap binds at the top.**

Every decline condition in this development — `exists_decline_of_consumption_lower_bound`, and
through it the whole Doeblin uniqueness and convergence argument — assumes impatience. The
results below say that assumption is not a restriction chosen for convenience: without it the
objects those arguments are about do not exist.

## The argument, with no derivatives

The Euler route is `u'(c) ≥ β (1 + r) E u'(c')`, so `β (1 + r) ≥ 1` makes marginal utility a
supermartingale and consumption cannot fall. That needs a derivative. The secant version needs
none. Deviate from the optimum by saving `ε` more:

* optimality bounds the utility cost by the continuation gain,
  `u c - u (c - ε) ≥ β (cont (b + ε) - cont b)`;
* `valueFunction_sub_ge` bounds the continuation gain from below by next period's one-period
  utility gain, `cont (b + ε) - cont b ≥ Σ π z' (u (c' + (1+r) ε) - u c')`;
* and if `c'` sat a clear distance BELOW `c - ε`, strict concavity would make the secant slope
  over `[c', c' + (1+r) ε]` strictly steeper than the one over `[c - ε, c]`, giving
  `u (c' + (1+r) ε) - u c' > (1 + r) (u c - u (c - ε))`.

Chaining the three: `u c - u (c - ε) > β (1 + r) (u c - u (c - ε)) ≥ u c - u (c - ε)`. So no such
`ε` exists, and letting `ε` shrink says consumption cannot fall in EVERY successor state
(`exists_consumption_ge_of_patient`). That much holds with genuine income risk.

## Why the asset conclusion is deterministic

Turning "consumption does not fall" into "assets do not fall" uses the budget identity, and with
fluctuating income the successor that keeps consumption up may be the one with the high income
draw rather than the one with high assets — the slack `income z' - income z` breaks the
recursion. With income constant the slack vanishes and the decrements `aₜ - aₜ₊₁` are forced to
GROW by a factor `1 + r ≥ 1` each period, which no borrowing limit can absorb. So
`le_policy_of_patient` and everything after it is stated for `Subsingleton Z`: the deterministic
consumption-savings problem. That is exactly the margin MOHW's Proposition 2(c) works on before
the labour margin is added.

## What it settles

`policy_assetCap_of_patient` is the converse of `crra_policy_lt_assetCap`: the cap is slack
under impatience and binds without it. So the asset cap, which the development treats as an
artefact to be discharged, is an artefact PRECISELY when `β (1 + r) < 1`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### Two small facts -/

theorem exists_transitionMatrix_pos (z : Z) : ∃ z' : Z, 0 < P.transitionMatrix z z' := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hzero : ∑ z' : Z, P.transitionMatrix z z' = 0 :=
    Finset.sum_eq_zero fun z' _ => le_antisymm (h z') (P.transitionMatrix_nonneg z z')
  rw [P.transitionMatrix_sum z] at hzero
  norm_num at hzero

theorem discount_pos_of_patient (hβR : 1 ≤ (P.discount : ℝ) * (1 + P.interest)) :
    0 < (P.discount : ℝ) := by
  rcases eq_or_lt_of_le P.discount.coe_nonneg with h | h
  · rw [← h, zero_mul] at hβR; linarith
  · exact h

/-- Patience forces a positive interest rate: `β (1 + r) ≥ 1` with `β < 1` leaves no room. -/
theorem one_le_one_add_interest_of_patient
    (hβR : 1 ≤ (P.discount : ℝ) * (1 + P.interest)) : 1 ≤ 1 + P.interest := by
  have hβ1 : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
  have hβ0 := P.discount_pos_of_patient hβR
  nlinarith [P.interest_gt_neg_one]

/-! ### The secant step

The one place concavity is used, isolated so that the economics below is pure bookkeeping. -/

/-- **Moving consumption down the concave curve pays more than the gross interest.** If `d` sits
strictly below `c - ε`, even after being handed `(1 + r) ε`, then the secant slope of `u` over
`[d, d + (1+r) ε]` is strictly steeper than the one over `[c - ε, c]`, and the gain beats the
loss by the whole gross interest factor. No derivative, and no modulus: the gap `hgap` is what
buys the strict inequality. -/
theorem strict_secant_gain {c d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hgap : d + (1 + P.interest) * ε < c - ε) :
    (1 + P.interest) * (P.u c - P.u (c - ε)) < P.u (d + (1 + P.interest) * ε) - P.u d := by
  have hR : 0 < 1 + P.interest := P.interest_gt_neg_one
  have hRe : 0 < (1 + P.interest) * ε := by positivity
  have h1 : d < d + (1 + P.interest) * ε := by linarith
  have h3 : c - ε < c := by linarith
  have hd0 : d ∈ Ioi (0 : ℝ) := hd
  have hce : c - ε ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
  have hc : c ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
  have hm : d + (1 + P.interest) * ε ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
  have s1 := P.strictConcaveOn_u.slope_anti_adjacent hd0 hce h1 hgap
  have s2 := P.strictConcaveOn_u.slope_anti_adjacent hm hc hgap h3
  rw [show c - (c - ε) = ε from by ring] at s2
  rw [show d + (1 + P.interest) * ε - d = (1 + P.interest) * ε from by ring] at s1
  have hchain : (P.u c - P.u (c - ε)) / ε
      < (P.u (d + (1 + P.interest) * ε) - P.u d) / ((1 + P.interest) * ε) := lt_trans s2 s1
  rw [div_lt_div_iff₀ hε hRe] at hchain
  have hkey : ((1 + P.interest) * (P.u c - P.u (c - ε))) * ε
      < (P.u (d + (1 + P.interest) * ε) - P.u d) * ε := by nlinarith [hchain]
  exact lt_of_mul_lt_mul_right hkey hε.le

/-! ### Consumption cannot fall in every successor state -/

/-- **The core comparison.** Under `β (1 + r) ≥ 1` there is no feasible upward deviation `ε`
that would leave next period's consumption below `c - ε` in every income state. -/
theorem not_forall_consumption_drop (hpc : P.PositiveConsumption)
    (hβR : 1 ≤ (P.discount : ℝ) * (1 + P.interest))
    {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) {ε : ℝ} (hε : 0 < ε)
    (hfeas : P.policy s + ε ≤ P.maxSaving s) :
    ¬ ∀ z' : Z, P.consumption (P.policy s, z') (P.policy (P.policy s, z'))
        + (1 + P.interest) * ε < P.consumption s (P.policy s) - ε := by
  intro hdrop
  have hR : 0 < 1 + P.interest := P.interest_gt_neg_one
  have hβ0 := P.discount_pos_of_patient hβR
  set b : ℝ := P.policy s with hbdef
  set c : ℝ := P.consumption s b with hcdef
  have hbreg : b ∈ Icc assetFloor assetCap := P.policy_mem_region s
  have hbeps : b + ε ∈ Icc assetFloor assetCap :=
    ⟨by linarith [hbreg.1], le_trans hfeas (P.maxSaving_le_assetCap s)⟩
  have hcpos : 0 < c := P.consumption_policy_pos hpc hs
  -- the deviation is feasible and leaves positive consumption
  have hdev : b + ε ∈ P.toExtended.feasible s := by
    rw [P.feasible_eq]; exact ⟨by linarith [hbreg.1], hfeas⟩
  have hcdev : P.consumption s (b + ε) = c - ε := by simp only [hcdef, consumption]; ring
  have hcdevpos : 0 < c - ε := by
    obtain ⟨z₁, -⟩ := P.exists_transitionMatrix_pos s.2
    have h0 := hdrop z₁
    have h1 : 0 < P.consumption (b, z₁) (P.policy (b, z₁)) :=
      P.consumption_policy_pos hpc hbreg
    nlinarith [mul_pos hR hε]
  -- optimality: the utility cost dominates the discounted continuation gain
  have hopt := P.objR_le_of_mem hs hdev (P.mem_dom_of_pos (by rw [hcdev]; exact hcdevpos))
  simp only [objR, hcdev] at hopt
  set D : ℝ := P.u c - P.u (c - ε) with hDdef
  have hD0 : 0 ≤ D := by
    have := P.monotoneOn_u (by simp only [mem_Ioi]; linarith)
      (by simp only [mem_Ioi]; exact hcpos) (by linarith : c - ε ≤ c)
    linarith
  have hcost : (P.discount : ℝ) * (P.cont s.2 (b + ε) - P.cont s.2 b) ≤ D := by
    rw [hDdef]; linarith [hopt]
  -- the continuation gain beats `(1 + r) D` in every state, strictly where the chain can move
  have hterm : ∀ z' : Z, (1 + P.interest) * D
      ≤ P.toExtended.valueFunction (b + ε, z') - P.toExtended.valueFunction (b, z') := by
    intro z'
    have henv := P.valueFunction_sub_ge hpc hbreg hbeps (by linarith) z'
    rw [show (1 + P.interest) * (b + ε - b) = (1 + P.interest) * ε from by ring] at henv
    have hgain := P.strict_secant_gain (P.consumption_policy_pos hpc hbreg (s := (b, z')))
      hε (hdrop z')
    exact le_trans (le_of_lt hgain) henv
  obtain ⟨z₀, hz₀⟩ := P.exists_transitionMatrix_pos s.2
  have hsum : (1 + P.interest) * D < P.cont s.2 (b + ε) - P.cont s.2 b := by
    have hrw : P.cont s.2 (b + ε) - P.cont s.2 b
        = ∑ z' : Z, P.transitionMatrix s.2 z'
            * (P.toExtended.valueFunction (b + ε, z')
              - P.toExtended.valueFunction (b, z')) := by
      simp only [cont, ← Finset.sum_sub_distrib, ← mul_sub]
    have hconst : ∑ _z' : Z, P.transitionMatrix s.2 _z' * ((1 + P.interest) * D)
        = (1 + P.interest) * D := by
      rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]
    rw [hrw, ← hconst]
    refine Finset.sum_lt_sum (fun z' _ => ?_) ⟨z₀, Finset.mem_univ _, ?_⟩
    · exact mul_le_mul_of_nonneg_left (hterm z') (P.transitionMatrix_nonneg _ _)
    · refine mul_lt_mul_of_pos_left ?_ hz₀
      have henv := P.valueFunction_sub_ge hpc hbreg hbeps (by linarith) z₀
      rw [show (1 + P.interest) * (b + ε - b) = (1 + P.interest) * ε from by ring] at henv
      exact lt_of_lt_of_le
        (P.strict_secant_gain (P.consumption_policy_pos hpc hbreg (s := (b, z₀))) hε
          (hdrop z₀)) henv
  -- and that closes the circle
  have hfin : (P.discount : ℝ) * ((1 + P.interest) * D) < D := by
    have := mul_lt_mul_of_pos_left hsum hβ0
    linarith [hcost]
  nlinarith [hfin, mul_le_mul_of_nonneg_right hβR hD0]

/-- **Consumption cannot fall in every successor state.** The pathwise form of the
supermartingale property of marginal utility, with the derivative removed. -/
theorem exists_consumption_ge_of_patient (hpc : P.PositiveConsumption)
    (hβR : 1 ≤ (P.discount : ℝ) * (1 + P.interest))
    {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap)
    (hint : P.policy s < P.maxSaving s) :
    ∃ z' : Z, P.consumption s (P.policy s)
      ≤ P.consumption (P.policy s, z') (P.policy (P.policy s, z')) := by
  classical
  have hR : 0 < 1 + P.interest := P.interest_gt_neg_one
  obtain ⟨zm, -, hzm⟩ := Finset.exists_max_image Finset.univ
    (fun z' : Z => P.consumption (P.policy s, z') (P.policy (P.policy s, z')))
    ⟨Classical.ofNonempty, Finset.mem_univ _⟩
  refine ⟨zm, ?_⟩
  by_contra hlt
  replace hlt := not_le.mp hlt
  set c : ℝ := P.consumption s (P.policy s) with hcdef
  set cm : ℝ := P.consumption (P.policy s, zm) (P.policy (P.policy s, zm)) with hcmdef
  have hδ : 0 < c - cm := by linarith
  set ε : ℝ := min ((c - cm) / (3 + P.interest)) (P.maxSaving s - P.policy s) with hεdef
  have hεle : ε ≤ (c - cm) / (3 + P.interest) := min_le_left _ _
  have hεle2 : ε ≤ P.maxSaving s - P.policy s := min_le_right _ _
  have hε : 0 < ε := lt_min (div_pos hδ (by linarith)) (by linarith)
  have hgap : (2 + P.interest) * ε < c - cm := by
    rw [le_div_iff₀ (by linarith)] at hεle
    linarith
  refine P.not_forall_consumption_drop hpc hβR hs hε (by linarith) fun z' => ?_
  have hz := hzm z' (Finset.mem_univ _)
  linarith

/-! ### The deterministic problem: assets cannot fall either

With income constant the budget identity turns "consumption does not fall" into a recursion on
the asset decrements which forces them to grow, and a borrowing limit cannot absorb that. -/

section Deterministic

variable [Subsingleton Z]

/-- **Under `β (1 + r) ≥ 1` the household never runs its assets down.** The deterministic
exogenous-labour analogue of Marcet–Obiols-Homs–Weil Proposition 3, in its policy-function
form. -/
theorem le_policy_of_patient (hpc : P.PositiveConsumption)
    (hβR : 1 ≤ (P.discount : ℝ) * (1 + P.interest))
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    a ≤ P.policy (a, z) := by
  classical
  by_contra hcon
  replace hcon := not_le.mp hcon
  have hR : 0 < 1 + P.interest := P.interest_gt_neg_one
  have hR1 : 1 ≤ 1 + P.interest := P.one_le_one_add_interest_of_patient hβR
  set x : ℕ → ℝ := fun n => (fun t => P.policy (t, z))^[n] a with hxdef
  have hx0 : x 0 = a := rfl
  have hxsucc : ∀ n : ℕ, x (n + 1) = P.policy (x n, z) := fun n =>
    Function.iterate_succ_apply' _ n a
  set d : ℝ := a - x 1 with hddef
  have hd : 0 < d := by rw [hddef, hxsucc 0, hx0]; linarith
  have key : ∀ n : ℕ, x n ∈ Icc assetFloor assetCap ∧ d ≤ x n - x (n + 1)
      ∧ x n ≤ a - n * d := by
    intro n
    induction n with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · simp only [hx0]; exact ha
        · simp only [hx0]; exact le_of_eq hddef
        · simp only [hx0]; norm_num
    | succ n ih =>
        obtain ⟨hmem, hdec, hbnd⟩ := ih
        have hmem' : x (n + 1) ∈ Icc assetFloor assetCap := by
          rw [hxsucc n]; exact P.policy_mem_region _
        refine ⟨hmem', ?_, by push_cast; linarith⟩
        -- the saving choice at `x n` is strictly interior, so the comparison applies
        have hpos : 0 < x n - x (n + 1) := by linarith
        have hcn : 0 < P.consumption (x n, z) (P.policy (x n, z)) :=
          P.consumption_policy_pos hpc hmem
        have hint : P.policy (x n, z) < P.maxSaving (x n, z) := by
          rw [P.maxSaving_eq]
          refine lt_min ?_ ?_
          · rw [← hxsucc n]; linarith [hmem.2]
          · simp only [consumption] at hcn; linarith
        obtain ⟨z', hz'⟩ := P.exists_consumption_ge_of_patient hpc hβR (s := (x n, z)) hmem hint
        rw [Subsingleton.elim z' z, ← hxsucc n] at hz'
        -- budget identities on both sides
        have hres : ∀ t : ℝ, assetFloor ≤ t →
            P.resources (t, z) = P.income z + (1 + P.interest) * t := by
          intro t ht; simp only [resources, max_eq_right ht]
        have hc1 : P.consumption (x n, z) (x (n + 1))
            = P.income z + (1 + P.interest) * x n - x (n + 1) := by
          simp only [consumption, hres (x n) hmem.1]
        have hc2 : P.consumption (x (n + 1), z) (P.policy (x (n + 1), z))
            = P.income z + (1 + P.interest) * x (n + 1) - x (n + 1 + 1) := by
          rw [← hxsucc (n + 1)]
          simp only [consumption, hres (x (n + 1)) hmem'.1]
        rw [hc1, hc2] at hz'
        nlinarith [hz', hpos, hdec, hR1]
  obtain ⟨N, hN⟩ := exists_nat_gt ((a - assetFloor) / d)
  rw [div_lt_iff₀ hd] at hN
  have h1 := (key N).1.1
  have h2 := (key N).2.2
  linarith

/-- **The asset cap binds at the top when the household is not impatient.** The exact converse
of `crra_policy_lt_assetCap`, which discharges the cap under `β (1 + r) < 1`. -/
theorem policy_assetCap_of_patient (hpc : P.PositiveConsumption)
    (hβR : 1 ≤ (P.discount : ℝ) * (1 + P.interest)) (z : Z) :
    P.policy (assetCap, z) = assetCap :=
  le_antisymm (P.policy_mem_region _).2
    (P.le_policy_of_patient hpc hβR ⟨P.assetFloor_le_assetCap, le_rfl⟩ z)

/-- **Marcet–Obiols-Homs–Weil, Proposition 3.** Assets declining anywhere — which is what every
ergodic argument in this development runs on — forces `β (1 + r) < 1`. Impatience is not an
assumption about tastes; it is a property of any economy in which the asset distribution can
settle away from the cap. -/
theorem discount_mul_lt_one_of_decline (hpc : P.PositiveConsumption)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z) (hlt : P.policy (a, z) < a) :
    (P.discount : ℝ) * (1 + P.interest) < 1 := by
  by_contra h
  exact absurd (P.le_policy_of_patient hpc (not_lt.mp h) ha z) (not_le.mpr hlt)

/-- The decline hypothesis of `exists_exhaust_of_decline` is unsatisfiable without impatience,
so the Doeblin uniqueness argument cannot even be stated for a patient household. -/
theorem not_decline_of_patient (hpc : P.PositiveConsumption)
    (hβR : 1 ≤ (P.discount : ℝ) * (1 + P.interest)) (z : Z) {a₀ : ℝ}
    (ha₀ : assetFloor ≤ a₀) (hle : a₀ ≤ assetCap) :
    ¬ ∀ a ∈ Icc a₀ assetCap, P.policy (a, z) < a := fun hdecl =>
  absurd (P.le_policy_of_patient hpc hβR ⟨ha₀, hle⟩ z)
    (not_le.mpr (hdecl a₀ ⟨le_rfl, hle⟩))

/-! ### Not vacuous

A household that is exactly on the knife edge, `β (1 + r) = 1`. Nothing above is an empty
statement about an impossible economy: this one saves its way to the cap and stays there. -/

/-- A patient household with no income risk: `β = 1/2`, `r = 1`, income `1`, cap `1`. The
discount factor and the gross interest rate are exact reciprocals, `β (1 + r) = 1`. -/
noncomputable def patient : IncomeFluctuation (Fin 1) 0 1 where
  income _ := 1
  transitionMatrix _ _ := 1
  interest := 1
  discount := 1 / 2
  u := fun c => -c⁻¹
  minIncome := 1
  maxIncome := 1
  minIncome_pos := by norm_num
  minIncome_le _ := le_rfl
  le_maxIncome _ := le_rfl
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  assetFloor_le_assetCap := by norm_num
  assetCap_nonneg := by norm_num
  minConsumption_pos := by norm_num
  minConsumption_le_floor := le_rfl
  discount_lt_one := by norm_num
  dom := Ioi 0
  Ioi_subset_dom := subset_rfl
  dom_subset_Ici := Ioi_subset_Ici_self
  continuousOn_u_dom := (continuousOn_id.inv₀ fun x hx => ne_of_gt hx).neg
  monotoneOn_u_dom := by
    intro x hx y _ hxy
    have : (0 : ℝ) < x := hx
    simp only [neg_le_neg_iff]
    gcongr
  strictConcaveOn_u_dom := strictConcaveOn_neg_inv
  continuousOn_extendDom :=
    continuousOn_extendDom_Ioi ((continuousOn_id.inv₀ fun x hx => ne_of_gt hx).neg)
      (tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero)

@[simp] theorem patient_interest : patient.interest = 1 := rfl
@[simp] theorem patient_discount : (patient.discount : ℝ) = 1 / 2 := rfl

theorem patient_unbounded : patient.Unbounded := rfl

theorem patient_positiveConsumption : patient.PositiveConsumption :=
  patient.positiveConsumption_of_unbounded patient_unbounded

theorem patient_knife_edge : 1 ≤ (patient.discount : ℝ) * (1 + patient.interest) := by
  rw [patient_discount, patient_interest]; norm_num

/-- **The cap really does bind.** -/
theorem patient_policy_assetCap (z : Fin 1) : patient.policy (1, z) = 1 :=
  patient.policy_assetCap_of_patient patient_positiveConsumption patient_knife_edge z

/-- **And assets never fall**, at any asset level. -/
theorem patient_le_policy {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 1) :
    a ≤ patient.policy (a, z) :=
  patient.le_policy_of_patient patient_positiveConsumption patient_knife_edge ha z

end Deterministic

end IncomeFluctuation

end LeanEconomics
