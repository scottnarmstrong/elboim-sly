/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.BlockCore
public import ElboimSly.Paper.Step.Lemma76Stmt
public import ElboimSly.Paper.Step.TravelEv
public import Mathlib

/-!
# Lemma 7.6 (coupling with Brownian motion), conditional on Corollary 7.2

ES22 Lemma 7.6 (§7) with the σ-estimate.

`StepSigmaClaim d hd` is the conclusion of the σ-estimate: for blocks of length
`T ∈ [t_n^{1-a_H}/2, t_n^{1-a_H}]`, `a_H = 79/200`, the standard deviation `σ` of the first
coordinate of the normalised truncated block endpoint satisfies
`|σ - √2| ≤ 3β^{-1/16} - t_n^{-1/16}`.

`step_lemma76_of_cor72_sigma` proves the conclusion of Lemma 7.6 (`StepBm`) from `StepCor72`
(Corollary 7.2) and `StepSigmaClaim`; it is a conditional helper under a distinct name.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

/-- The conclusion of the σ-estimate. -/
def StepSigmaClaim (d : ℕ) (hd : 1 ≤ d) : Prop :=
  ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∃ βSig : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), βSig ≤ β →
    StepRegime d n₁ β n t₀ →
    ∀ (Ωe : Type) [MeasurableSpace Ωe] (Pe : Measure Ωe) (N : Ωe → Measure (ℕ × RingSpace d β)),
      IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe →
      ∀ T : ℝ≥0, indScale t₀ n ^ ((121 : ℝ) / 200) / 2 ≤ T → (T : ℝ) ≤ indScale t₀ n ^ ((121 : ℝ) / 200) →
        |Real.sqrt (∫ w, (blockY T ((n : ℝ) ^ 2 * Real.sqrt T) w ⟨0, hd⟩) ^ 2 ∂ppLaw Pe N T) -
            Real.sqrt 2| ≤ 3 * β ^ (-(1 : ℝ) / 16) - indScale t₀ n ^ (-(1 : ℝ) / 16)

variable {d : ℕ}

/-- The largeness conditions on `n` of Lemma 7.6. -/
theorem lemma76_eventually (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, StrongApprox.nX d ≤ n ∧ 400 ≤ n ∧
      (16 * (n : ℝ) ^ 2) ^ 400 ≤ 4 ^ (43 * n) ∧
      ((4 * d + 3) * (2 * 4 ^ (n + 1)) : ℝ) ≤ Real.exp (c / 2 * (n : ℝ) ^ 3) := by
  have e1 : ∀ᶠ n : ℕ in atTop, StrongApprox.nX d ≤ n := eventually_ge_atTop _
  have e2 : ∀ᶠ n : ℕ in atTop, 400 ≤ n := eventually_ge_atTop 400
  have e3 : ∀ᶠ n : ℕ in atTop, (16 * (n : ℝ) ^ 2) ^ 400 ≤ 4 ^ (43 * n) := by
    have := eventually_pow_mul_exp_neg_le 800 (c := 43 * Real.log 4) (δ := 1 / 16 ^ 400)
      (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); positivity) (by positivity)
    filter_upwards [this] with n hn
    have h4 : (4 : ℝ) ^ (43 * n) = Real.exp (43 * Real.log 4 * n) := by
      rw [pow_mul', four_pow_eq_exp]
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h4]
    have h1 : (16 * (n : ℝ) ^ 2) ^ 400 = 16 ^ 400 * (n : ℝ) ^ 800 := by
      rw [mul_pow, ← pow_mul]
    rw [h1]
    have h2 : Real.exp (-(43 * Real.log 4 * n)) = (Real.exp (43 * Real.log 4 * n))⁻¹ :=
      Real.exp_neg _
    rw [h2] at hn
    have hpos := Real.exp_pos (43 * Real.log 4 * n)
    rw [← div_eq_mul_inv, div_le_iff₀ hpos] at hn
    calc 16 ^ 400 * (n : ℝ) ^ 800 ≤ 16 ^ 400 * (1 / 16 ^ 400 * Real.exp (43 * Real.log 4 * n)) := by
          gcongr
      _ = Real.exp (43 * Real.log 4 * n) := by
          rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul]
  have e4 : ∀ᶠ n : ℕ in atTop, ((4 * d + 3) * (2 * 4 ^ (n + 1)) : ℝ) ≤
      Real.exp (c / 2 * (n : ℝ) ^ 3) := by
    have := eventually_linear_le_cube (Real.log 4) (Real.log ((4 * d + 3) * 8)) (c := c / 2)
      (by positivity)
    filter_upwards [this] with n hn
    have h1 : ((4 * d + 3) * (2 * 4 ^ (n + 1)) : ℝ) = ((4 * d + 3) * 8) * 4 ^ n := by ring
    rw [h1, four_pow_eq_exp]
    calc ((4 * d + 3) * 8 : ℝ) * Real.exp (Real.log 4 * n) =
        Real.exp (Real.log 4 * n + Real.log ((4 * d + 3) * 8)) := by
          rw [Real.exp_add, Real.exp_log (by positivity)]; ring
      _ ≤ _ := Real.exp_le_exp.2 hn
  filter_upwards [e1, e2, e3, e4] with n a b c d
  exact ⟨a, b, c, d⟩

/-- **Lemma 7.6**, conditional on `StepCor72` (Corollary 7.2), `StepTr` (Lemma 7.4) and
`StepSigmaClaim` (the σ-estimate). ES22 Lemma 7.6. -/
theorem step_lemma76_of_cor72_sigma (hd : 1 ≤ d) {cCat : ℝ} (hc : 0 < cCat) {βCat : ℕ → ℝ}
    (hCor : StepCor72 d cCat βCat) {cTr : ℝ} (hcTr : 0 < cTr) {βTr : ℕ → ℝ}
    (hTr : StepTr d cTr βTr) (hσ : StepSigmaClaim d hd) :
    ∃ cBm : ℝ, 0 < cBm ∧ ∃ βBm : ℕ → ℝ, StepBm d cBm βBm := by
  set c' : ℝ := min (min cCat cTr) (1 / 7) with hc'
  have hc'0 : 0 < c' := lt_min (lt_min hc hcTr) (by norm_num)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (lemma76_eventually d hc'0)
  choose βSig hβSig using hσ
  refine ⟨c' / 2, by positivity, fun n₁ => max (βCat n₁) (max (βTr n₁)
    (max (if h : 8 * d ≤ n₁ then βSig n₁ h else 0) (max ((12 : ℝ) ^ 16)
    ((4 : ℝ) ^ (N0 + 1))))), ?_⟩
  intro n₁ hn₁ β _ n t₀ hβ hR Ω _ P N hN
  have hβ' : max (βCat n₁) (max (βTr n₁) (max (if h : 8 * d ≤ n₁ then βSig n₁ h else 0)
    (max ((12 : ℝ) ^ 16) ((4 : ℝ) ^ (N0 + 1))))) ≤ β := hβ
  simp only [max_le_iff] at hβ'
  obtain ⟨hβc, hβt, hβs, hβ12, hβN⟩ := hβ'
  have hβs' : βSig n₁ hn₁ ≤ β := by simpa [hn₁] using hβs
  obtain ⟨-, hβ1, hn1, ht0, htn_lt, -⟩ := id hR
  obtain ⟨htn_gt, htn_le⟩ := indScale_bounds (n := n) ht0
  have htn0 : 0 < indScale t₀ n := lt_trans (by positivity) htn_gt
  have hnN : N0 ≤ n := by
    have h1 : (4 : ℝ) ^ (N0 + 1) < 4 ^ (n + 1) :=
      lt_of_le_of_lt hβN (lt_of_lt_of_le htn_lt htn_le)
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 h1
    omega
  obtain ⟨hnX, h400, h16, hbig⟩ := hN0 n hnN
  obtain ⟨ℓ, T, hℓ, hT, hℓa, hℓb, hℓT, hTlo, hThi, hrad, hT1, hT2⟩ :=
    lemma76_params hd htn_gt h400 h16
  -- the variance
  set V : ℝ := ∫ w, (blockY T ((n : ℝ) ^ 2 * Real.sqrt T) w ⟨0, hd⟩) ^ 2 ∂ppLaw P N T with hV
  have hV0 : 0 ≤ V := integral_nonneg fun w => sq_nonneg _
  set σ : ℝ := Real.sqrt V with hσdef
  have hclaim := hβSig n₁ hn₁ β n t₀ hβs' hR Ω P N hN T hT1 hT2
  have hσb : |σ - Real.sqrt 2| ≤
      max (3 * β ^ (-(1 : ℝ) / 16) - indScale t₀ n ^ (-(1 : ℝ) / 16)) 0 :=
    hclaim.trans (le_max_left _ _)
  obtain ⟨hσ1, hσ2, -⟩ := step_sigma_bounds hβ12 htn0 hσb
  have hvar : V = σ ^ 2 := (Real.sq_sqrt hV0).symm
  refine ⟨σ, hσb, ?_⟩
  have hn16 : 16 ≤ n := by omega
  have hbig' : ((4 * d + 3) * ℓ : ℝ) ≤
      Real.exp (min (min cCat cTr) (1 / 7) / 2 * (n : ℝ) ^ 3) := by
    refine le_trans ?_ hbig
    have hℓ2 : (ℓ : ℝ) ≤ 2 * 4 ^ (n + 1) := by
      have h1 : indScale t₀ n ^ ((79 : ℝ) / 200) ≤ indScale t₀ n := by
        have : (1 : ℝ) ≤ indScale t₀ n := by
          have : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
          linarith
        calc indScale t₀ n ^ ((79 : ℝ) / 200) ≤ indScale t₀ n ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le this (by norm_num)
          _ = indScale t₀ n := Real.rpow_one _
      linarith
    have : (0 : ℝ) ≤ 4 * d + 3 := by positivity
    exact mul_le_mul_of_nonneg_left hℓ2 this
  exact lemma76_core hd hCor hc hTr hcTr hR hβc hβt hn₁ hnX hn16 hℓ hT hℓa hℓb hℓT hTlo hThi hrad
    hbig' hN hσ1 hσ2 hvar

end ElboimSly.Paper.Step
