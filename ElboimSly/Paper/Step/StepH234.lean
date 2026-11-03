/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Levels
public import ElboimSly.Paper.Step.Lemma74
public import ElboimSly.Paper.Step.Lemma76Stmt
public import ElboimSly.Paper.Step.Lemma77
public import ElboimSly.Paper.Base.IdentH3
public import Mathlib

/-!
# (H2), (H3), (H4) at level `n` from Lemmas 7.4, 7.6, 7.7

The induction step, items (H2), (H3), (H4).

Each result takes the conclusion of the corresponding lemma (`StepTp`, `StepTr`, `StepBm`) as a
hypothesis, and the large-`n` condition `1/c ≤ n` as an explicit hypothesis (absorbed into the
threshold of the step in `StepFinal`). They are conditional helpers under distinct names: they never
stand in for the lemmas.

* (H2): `t ≤ t_n/4` from levels (c) (`stepRegime_H2_pow`), `t ∈ [t_n/4, t_n]` from
  Lemma 7.7.
* (H3): Lemma 7.4 at `t = t_n`, `e^{-c n³} ≤ e^{-n²}`.
* (H4): Lemma 7.6, with failure probability `e^{-c n³} ≤ e^{-n²}`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.SRW

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- In the step regime, `p_n = e^{-n²}`. -/
theorem step_pn_eq {n₁ n : ℕ} {t₀ : ℝ} (h : StepRegime d n₁ β n t₀) :
    indFailBound β t₀ n = Real.exp (-((n : ℝ) ^ 2)) := by
  unfold indFailBound
  rw [ite_eq_right (not_lt.2 h.2.2.2.2.1.le)]

/-- `e^{-c n³} ≤ e^{-n²}` once `n ≥ 1/c`. -/
theorem exp_neg_mul_cube_le {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 / c ≤ n) :
    Real.exp (-(c * (n : ℝ) ^ 3)) ≤ Real.exp (-((n : ℝ) ^ 2)) := by
  apply Real.exp_le_exp.2
  have h1 : 1 ≤ c * n := by
    have := (div_le_iff₀ hc).1 hn
    linarith
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (n : ℝ))
  nlinarith

/-- A large-`n` condition holds once `β ≥ 4^{N+1}`. -/
theorem step_n_gt {n₁ n : ℕ} {t₀ : ℝ} (h : StepRegime d n₁ β n t₀) {N : ℕ}
    (hβ : (4 : ℝ) ^ (N + 1) ≤ β) : N < n := by
  have h1 := stepRegime_log_lt h
  have h2 : ((N + 1 : ℕ) : ℝ) ≤ Real.logb 4 β := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 4) (by linarith [h.2.1])]
    rw [Real.rpow_natCast]; exact hβ
  push_cast at h2
  have : (N : ℝ) < n := by linarith
  exact_mod_cast this

theorem step_one_le_scale {n₁ n : ℕ} {t₀ : ℝ} (h : StepRegime d n₁ β n t₀) :
    1 ≤ indScale t₀ n := by
  obtain ⟨-, hβ1, -, -, hlt, -⟩ := h
  linarith

/-- (H2) at level `n`, from levels (c) and Lemma 7.7. -/
theorem step_H2_of_tp {βTp : ℕ → ℝ} (hTp : StepTp d βTp) {n₁ n : ℕ} {t₀ : ℝ} (hn₁ : 8 * d ≤ n₁)
    (hβ : βTp n₁ ≤ β) (hβ2 : (4 : ℝ) ^ (n₁ + 2) ≤ β) (h : StepRegime d n₁ β n t₀)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β))
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    IndH2 P N n t₀ := by
  intro t ht u
  by_cases hlow : t ≤ indScale t₀ n / 4
  · have h4 : indScale t₀ n / 4 ≤ (4 : ℝ) ^ n := by
      unfold indScale
      have := h.2.2.2.1.2
      have hp : (0 : ℝ) < 4 ^ n := by positivity
      nlinarith
    exact stepRegime_H2_pow h hβ2 Ω P N hN t ⟨ht.1, hlow.trans h4⟩ u
  · exact hTp n₁ hn₁ β n t₀ hβ h Ω P N hN t (not_le.1 hlow).le ht.2 u

/-- (H3) at level `n`, from Lemma 7.4 at `t = t_n`. -/
theorem step_H3_of_tr {cTr : ℝ} {βTr : ℕ → ℝ} (hc : 0 < cTr) (hTr : StepTr d cTr βTr)
    {n₁ n : ℕ} {t₀ : ℝ} (hn₁ : 8 * d ≤ n₁) (hβ : βTr n₁ ≤ β) (h : StepRegime d n₁ β n t₀)
    (hn : 1 / cTr ≤ n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β))
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    IndH3 P N n t₀ := by
  have := hN.isProbabilityMeasure
  have h1 := step_one_le_scale h
  have hsq : Real.sqrt (indScale t₀ n) ≤ indScale t₀ n :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have key := hTr n₁ hn₁ β n t₀ hβ h Ω P N hN (indScale t₀ n) hsq le_rfl
  have : Nonempty (Set.Icc (0 : ℝ) (indScale t₀ n)) := ⟨⟨0, le_rfl, by linarith⟩⟩
  have hsub : {ω | ENNReal.ofReal ((n : ℝ) ^ 2 * Real.sqrt (indScale t₀ n)) ≤
      ⨆ s : Set.Icc (0 : ℝ) (indScale t₀ n),
        ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (s : ℝ)‖} ⊆
      {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ indScale t₀ n ∧ (n : ℝ) ^ 2 * Real.sqrt (indScale t₀ n) ≤
          ‖regenWalk (fun j => copyEnv (N ω) j) (s : ℝ)‖} := by
    intro ω hω
    have := (ofReal_le_iSup_iff_nat (ι := Set.Icc (0 : ℝ) (indScale t₀ n))
      (fun s => SRW.nrm (regenWalk (fun k => copyEnv (N ω) k) (s : ℝ)))
      ((n : ℝ) ^ 2 * Real.sqrt (indScale t₀ n)))
    simp only [← norm_eq_nrm] at this
    obtain ⟨⟨s, hs0, hs1⟩, hs⟩ := this.1 hω
    refine ⟨s.toNNReal, ?_, ?_⟩
    · rw [Real.coe_toNNReal _ hs0]; exact hs1
    · rw [Real.coe_toNNReal _ hs0]; exact hs
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [step_pn_eq h]
  exact key.trans (exp_neg_mul_cube_le hc hn)

/-- (H4) at level `n`, from Lemma 7.6. -/
theorem step_H4_of_bm {cBm : ℝ} {βBm : ℕ → ℝ} (hc : 0 < cBm) (hBm : StepBm d cBm βBm)
    {n₁ n : ℕ} {t₀ : ℝ} (hn₁ : 8 * d ≤ n₁) (hβ : βBm n₁ ≤ β) (h : StepRegime d n₁ β n t₀)
    (hn : 1 / cBm ≤ n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β))
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    IndH4 P N n t₀ := by
  obtain ⟨σ, hσ, Q, hQ1, hQ2, hQ3, hQ4⟩ := hBm n₁ hn₁ β n t₀ hβ h Ω P N hN
  refine ⟨σ, hσ, Q, hQ1, hQ2, hQ3, hQ4.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [step_pn_eq h]
  exact exp_neg_mul_cube_le hc hn

end ElboimSly.Paper.Step

end
