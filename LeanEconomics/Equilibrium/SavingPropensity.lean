/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.Equilibrium.SlackEuler
import LeanEconomics.Equilibrium.ShiftedDominance

/-!
# The marginal propensity to save, and the Huggett bound restated through it

`ShiftedDominance` bounds how far capital supply can FALL with the rate in a Huggett economy:
`K₁ ≤ K₂ + (r₂ - r₁)·|floor|/(1 - K)`, where `K` is a Lipschitz constant of the higher-rate
saving policy in assets, its marginal propensity to save. The bound needs `K < 1`.

## What is true and what is provable

For CRRA the policy's slope in assets is `R(1 - MPC)`, so `K < 1` says the marginal propensity
to consume out of cash on hand exceeds `r/R`. Asymptotically the MPC is the minimal MPC
`κ = 1 - Þ/R` (Ma–Toda), giving `K = R(1 - κ) = Þ = (βR)^{1/γ} < 1` — with almost no room:
at Aiyagari's numbers `κ ≈ 0.0390` against `r/R ≈ 0.0385`.

The natural route is Carroll–Kimball concavity of the consumption function plus the minimal-MPC
level bound `c(x) ≥ κ x`: on a RAY a concave function lying above `κ·x` has every secant slope
at least `κ` (`secant_ge_of_concaveOn_Ici`, derivative-free, via one chord far out). But the
household here lives on `[floor, cap]`, and on a bounded interval the two facts imply NO
positive secant slope at all: the constant function at the level of the bound at the cap is
concave, lies above the bound, and is flat (`exists_concaveOn_ge_flat`). The MPC floor is an
asymptotic property of the uncapped problem; the capped model's tools cannot see it, and the
level bound near the cap is far below actual consumption, so the chord there says nothing.

So the closure is not available on the region, and this file does not pretend otherwise. What
it does is restate the Huggett bound with the economics in view:

* an MPC floor `(R - K)(b - a) ≤ c(b) - c(a)` on the region is exactly the asset-Lipschitz bound
  `K` for the policy (`policy_lipschitz_of_consumption_slope`), given that the policy is
  increasing in assets;
* the Huggett bound with the SLACK elasticity condition of `SlackEuler` and the MPC floor as
  hypotheses (`huggett_aggregateCapital_le_add_of_slack`);
* the CRRA form with `K = Þ₂` and the floor `κ₂R₂(b - a) ≤ c₂(b) - c₂(a)`, where `K < 1` is
  impatience (`crra_huggett_aggregateCapital_le_add_of_slack`).

What remains for Huggett is the floor itself on the region — the same asymptotic structure that
blocks the slack elasticity condition at `γ > 1` — and a quantitative lower bound on the
creditors' gain to set against `(r₂ - r₁)|floor|/(1 - Þ₂)`, about `1500·|floor|·Δr` at
Huggett's numbers. Neither is done.
-/

open Set Filter Topology MeasureTheory

namespace LeanEconomics

/-! ### Secant slopes of concave functions above a line -/

/-- **On a ray, a concave function above `κ·x` has every secant slope at least `κ`.** One chord
far to the right does it: the secant from `x` to `y` is at least the secant from `y` to `w`,
which is at least `(κ w - c y)/(w - y) → κ`. No derivative, no limit: `w` is chosen explicitly. -/
theorem secant_ge_of_concaveOn_Ici {κ : ℝ} {c : ℝ → ℝ} (hc : ConcaveOn ℝ (Ici (0 : ℝ)) c)
    (hκ : ∀ x, 0 ≤ x → κ * x ≤ c x) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    κ * (y - x) ≤ c y - c x := by
  rcases hxy.lt_or_eq with hlt | rfl
  · by_contra hcon
    push Not at hcon
    set ε : ℝ := κ * (y - x) - (c y - c x) with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have hy0 : 0 ≤ y := le_trans hx hlt.le
    have hcy : 0 ≤ c y - κ * y := by linarith [hκ y hy0]
    set w : ℝ := y + ((c y - κ * y) + 1) * (y - x) / ε with hw
    have hyw : y < w := by
      rw [hw]
      have : 0 < ((c y - κ * y) + 1) * (y - x) / ε := by
        apply div_pos (mul_pos (by linarith) (by linarith)) hεpos
      linarith
    have hchoice : (c y - κ * y) * (y - x) < ε * (w - y) := by
      rw [hw, add_sub_cancel_left, mul_div_cancel₀ _ hεpos.ne']
      nlinarith
    have hs := hc.slope_anti_adjacent (mem_Ici.mpr hx) (mem_Ici.mpr (le_trans hy0 hyw.le))
      hlt hyw
    rw [div_le_div_iff₀ (sub_pos.2 hyw) (sub_pos.2 hlt)] at hs
    have h1 : (κ * w - c y) * (y - x) ≤ (c w - c y) * (y - x) :=
      mul_le_mul_of_nonneg_right (by linarith [hκ w (le_trans hy0 hyw.le)]) (by linarith)
    nlinarith [hs, h1, hchoice]
  · simp

/-- **On a bounded interval the two facts give nothing.** The constant function at the level of
the bound at the cap is concave, lies above the bound, and has secant slope zero. -/
theorem exists_concaveOn_ge_flat {κ R y cap : ℝ} (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hcap : 0 < cap) :
    ∃ c : ℝ → ℝ, ConcaveOn ℝ (Icc (0 : ℝ) cap) c ∧
      (∀ a ∈ Icc (0 : ℝ) cap, κ * (y + R * a) ≤ c a) ∧
      ∀ m : ℝ, 0 < m → ∃ a ∈ Icc (0 : ℝ) cap, ∃ b ∈ Icc (0 : ℝ) cap, a < b ∧
        c b - c a < m * (b - a) := by
  refine ⟨fun _ => κ * (y + R * cap), concaveOn_const _ (convex_Icc _ _), fun a ha => ?_,
    fun m hm => ⟨0, ⟨le_rfl, hcap.le⟩, cap, ⟨hcap.le, le_rfl⟩, hcap, ?_⟩⟩
  · have := mul_le_mul_of_nonneg_left ha.2 hR
    nlinarith
  · simp only [sub_self, sub_zero]
    positivity

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}

/-! ### An MPC floor is an asset-Lipschitz bound on the policy -/

/-- **A consumption slope floor `R - K` is a policy Lipschitz constant `K`**, given that the policy
is increasing in assets: `policy(b) - policy(a) = R(b - a) - (c(b) - c(a))`. (`K ≥ 0` follows.) -/
theorem policy_lipschitz_of_consumption_slope (P : IncomeFluctuation Z assetFloor assetCap)
    {K : ℝ}
    (hmpc : ∀ (z : Z) (a b : ℝ), a ∈ Icc assetFloor assetCap → b ∈ Icc assetFloor assetCap →
      a ≤ b → (1 + P.interest - K) * (b - a) ≤ P.consumptionFn z b - P.consumptionFn z a)
    (z : Z) (a b : ℝ) (ha : a ∈ Icc assetFloor assetCap) (hb : b ∈ Icc assetFloor assetCap) :
    |P.policy (a, z) - P.policy (b, z)| ≤ K * |a - b| := by
  have hc : ∀ x ∈ Icc assetFloor assetCap,
      P.consumptionFn z x = P.income z + (1 + P.interest) * x - P.policy (x, z) := by
    intro x hx
    simp only [consumptionFn, consumption, resources, max_eq_right hx.1]
  rcases le_total a b with hab | hab
  · have h1 := hmpc z a b ha hb hab
    have h2 := P.policy_mono (z := z) ha hb hab
    rw [hc a ha, hc b hb] at h1
    have hab' : |a - b| = b - a := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]
    rw [hab', abs_le]
    constructor <;> nlinarith
  · have h1 := hmpc z b a hb ha hab
    have h2 := P.policy_mono (z := z) hb ha hab
    rw [hc a ha, hc b hb] at h1
    have hab' : |a - b| = a - b := abs_of_nonneg (sub_nonneg.2 hab)
    rw [hab', abs_le]
    constructor <;> nlinarith

/-! ### The Huggett bound through the slack condition and an MPC floor -/

/-- **Huggett: capital supply at a higher rate is at most `(r₂ - r₁)·|floor|/(1 - K)` below
capital supply at the lower rate**, given the SLACK elasticity condition at every state and a
consumption slope floor `R₂ - K` for the higher-rate economy, `K < 1`. -/
theorem huggett_aggregateCapital_le_add_of_slack [MeasurableSpace Z] [BorelSpace Z]
    (P : IncomeFluctuation Z assetFloor assetCap)
    {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂) (hfl : assetFloor ≤ 0)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : StrictAntiOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₂ h₂).policy s < assetCap)
    (helas : ∀ a ∈ Icc assetFloor assetCap, ∀ z z' : Z,
      (1 + r₁) * du ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
          * du ((P.withRate r₁ h₁).consumptionFn z a + (r₂ - r₁) * max 0 a)
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z)))
          * du ((P.withRate r₁ h₁).consumptionFn z a))
    {K : ℝ} (hK : 0 ≤ K) (hK1 : K < 1)
    (hmpc : ∀ (z : Z) (a b : ℝ), a ∈ Icc assetFloor assetCap → b ∈ Icc assetFloor assetCap →
      a ≤ b → (1 + r₂ - K) * (b - a)
        ≤ (P.withRate r₂ h₂).consumptionFn z b - (P.withRate r₂ h₂).consumptionFn z a)
    {μ₀ μ₁ μ₂ : ProbabilityMeasure P.State}
    (hP : Tendsto (fun m => (P.withRate r₁ h₁).pushProb^[m] μ₀) atTop (𝓝 μ₁))
    (hQ : Tendsto (fun m => (P.withRate r₂ h₂).pushProb^[m] μ₀) atTop (𝓝 μ₂)) :
    P.aggregateCapital μ₁ ≤ P.aggregateCapital μ₂ + (r₂ - r₁) * (-assetFloor) / (1 - K) := by
  have hγ : 0 ≤ (r₂ - r₁) * (-assetFloor) := mul_nonneg (by linarith) (by linarith)
  have hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s ≤ (P.withRate r₂ h₂).policy s + (r₂ - r₁) * (-assetFloor) := by
    intro s hs
    obtain ⟨a, z⟩ := s
    have h := P.policy_le_policy_add_withRate_of_slack_at h₁ h₂ hr hderiv hanti hdupos hpc₁ hpc₂
      hslack₁ hslack₂ hs z (helas a hs z)
    have hmax : max 0 (-a) ≤ -assetFloor := by
      rcases le_total 0 a with h0 | h0
      · rw [max_eq_left (by linarith)]; linarith
      · rw [max_eq_right (by linarith)]; linarith [hs.1]
    have := mul_le_mul_of_nonneg_left hmax (by linarith : (0 : ℝ) ≤ r₂ - r₁)
    linarith
  have hpolK := (P.withRate r₂ h₂).policy_lipschitz_of_consumption_slope
    (by simpa only [IncomeFluctuation.withRate_interest] using hmpc)
  exact aggregateCapital_le_add_of_policy_le_add (P.withRate r₁ h₁) (P.withRate r₂ h₂) hγ hK hK1
    (fun _ _ => rfl) hpol hpolK hP hQ

/-- **CRRA: the Huggett bound with `K = Þ₂ = (βR₂)^{1/γ}`.** The consumption slope floor is the
minimal MPC times the gross rate, `κ₂R₂ (b - a) ≤ c₂(b) - c₂(a)`, and `K < 1` is impatience
`βR₂ < 1`. The amplification `1/(1 - Þ₂)` is about `1500` at Huggett's numbers. -/
theorem crra_huggett_aggregateCapital_le_add_of_slack [MeasurableSpace Z] [BorelSpace Z]
    (P : IncomeFluctuation Z assetFloor assetCap) {γ : ℝ} (hγ0 : 0 < γ)
    (hu : P.u = crraUtility γ) (hβ : 0 < (P.discount : ℝ))
    {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂) (hfl : assetFloor ≤ 0)
    (hβR : (P.discount : ℝ) * (1 + r₂) < 1)
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumption)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumption)
    (hslack₁ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₁ h₁).policy s < assetCap)
    (hslack₂ : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (P.withRate r₂ h₂).policy s < assetCap)
    (helas : ∀ a ∈ Icc assetFloor assetCap, ∀ z z' : Z,
      (1 + r₁) * ((P.withRate r₁ h₁).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z))) ^ (-γ)
          * ((P.withRate r₁ h₁).consumptionFn z a + (r₂ - r₁) * max 0 a) ^ (-γ)
        ≤ (1 + r₂) * ((P.withRate r₂ h₂).consumptionFn z' ((P.withRate r₁ h₁).policy (a, z))) ^ (-γ)
          * ((P.withRate r₁ h₁).consumptionFn z a) ^ (-γ))
    (hmpc : ∀ (z : Z) (a b : ℝ), a ∈ Icc assetFloor assetCap → b ∈ Icc assetFloor assetCap →
      a ≤ b → (P.withRate r₂ h₂).minMPC γ * (1 + r₂) * (b - a)
        ≤ (P.withRate r₂ h₂).consumptionFn z b - (P.withRate r₂ h₂).consumptionFn z a)
    {μ₀ μ₁ μ₂ : ProbabilityMeasure P.State}
    (hP : Tendsto (fun m => (P.withRate r₁ h₁).pushProb^[m] μ₀) atTop (𝓝 μ₁))
    (hQ : Tendsto (fun m => (P.withRate r₂ h₂).pushProb^[m] μ₀) atTop (𝓝 μ₂)) :
    P.aggregateCapital μ₁ ≤ P.aggregateCapital μ₂
      + (r₂ - r₁) * (-assetFloor) / (1 - ((P.discount : ℝ) * (1 + r₂)) ^ (1 / γ)) := by
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  -- `K = Þ₂ = (1 - κ₂) R₂`
  have hÞ : (1 - (P.withRate r₂ h₂).minMPC γ) * (1 + r₂)
      = ((P.discount : ℝ) * (1 + r₂)) ^ (1 / γ) := by
    have := (P.withRate r₂ h₂).one_sub_minMPC_mul (γ := γ)
    simpa only [IncomeFluctuation.withRate_interest, IncomeFluctuation.withRate_discount] using this
  have hK : 0 ≤ ((P.discount : ℝ) * (1 + r₂)) ^ (1 / γ) := Real.rpow_nonneg (by positivity) _
  have hK1 : ((P.discount : ℝ) * (1 + r₂)) ^ (1 / γ) < 1 :=
    Real.rpow_lt_one (by positivity) hβR (by positivity)
  refine P.huggett_aggregateCapital_le_add_of_slack h₁ h₂ hr hfl
    (du := fun c => c ^ (-γ)) (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility γ hc)
    (fun x hx y _ hxy => Real.rpow_lt_rpow_of_neg hx hxy (by linarith))
    (fun c hc => Real.rpow_pos_of_pos hc _) hpc₁ hpc₂ hslack₁ hslack₂ helas hK hK1
    (fun z a b ha hb hab => ?_) hP hQ
  have := hmpc z a b ha hb hab
  rw [← hÞ]
  calc (1 + r₂ - (1 - (P.withRate r₂ h₂).minMPC γ) * (1 + r₂)) * (b - a)
      = (P.withRate r₂ h₂).minMPC γ * (1 + r₂) * (b - a) := by ring
    _ ≤ _ := this

end IncomeFluctuation

end LeanEconomics
