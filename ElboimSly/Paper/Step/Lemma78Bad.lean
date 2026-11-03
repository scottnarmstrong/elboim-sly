/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78BadIncl
public import ElboimSly.Paper.Step.Lemma78BadGamma
public import ElboimSly.Paper.Step.Lemma78BadCount
public import ElboimSly.Paper.Step.H5Cov
public import Mathlib

/-!
# Lemma 7.8: discovered bad blocks for two walks

Discovered bad blocks for two walks (ES22 §7).  With `Γ₁₂ = {W₁ ∈ Γ_n} ∩ {w₂ ∈ Γ_n}`:
`P(Γ₁₂ᶜ) ≤ 2 A_n e^{-c n³}` and `P(Ω ∩ Γ₁₂ ∩ {τ'_bad ≤ t'_n}) ≤ 2 e^{-c♭ n³}`, where
`c♭ = min(δ²/(2·33^d), δ³/2)` (`step78Cflat`).

The two environments are `N` (for `W₁ = W^N_{0,0}`) and `N* = stepShiftEnv u (-q) N`
(for `w₂ = W₂ - u = W^{N*}_{0,0}`), both Poisson point processes of intensity `μ_β`.
The residual hypotheses are the interface `hI` at the single instance used, and the induction
hypothesis `hH`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The constant `c♭ = min(δ²/(2·33^d), δ³/2)` of discovered bad blocks for two walks. -/
noncomputable def step78Cflat (d : ℕ) : ℝ :=
  min (indDelta d ^ 2 / (2 * 33 ^ d)) (indDelta d ^ 3 / 2)

theorem exp_six_le_cflat (n : ℕ) :
    Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d))) ≤
      Real.exp (-(step78Cflat d * (n : ℝ) ^ 3)) := by
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have h : step78Cflat d ≤ indDelta d ^ 2 / (2 * 33 ^ d) := min_le_left _ _
  have h3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  calc step78Cflat d * (n : ℝ) ^ 3 ≤ indDelta d ^ 2 / (2 * 33 ^ d) * (n : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right h h3
    _ = _ := by ring

theorem exp_seven_le_cflat (n : ℕ) :
    Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3 / 2)) ≤
      Real.exp (-(step78Cflat d * (n : ℝ) ^ 3)) := by
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have h : step78Cflat d ≤ indDelta d ^ 3 / 2 := min_le_right _ _
  have h3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  calc step78Cflat d * (n : ℝ) ^ 3 ≤ indDelta d ^ 3 / 2 * (n : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right h h3
    _ = _ := by ring

/-- Discovered bad blocks for two walks.  Let `N` be a Poisson point process of intensity `μ_β`,
`u ∈ ℤ^d`, `q ∈ [0, β]`, `W₁ = W^N_{0,0}`, `W₂ = W^N_{u,q}`, `T = t'_n`.  Then
`P(Γ₁₂ᶜ) ≤ 2 A_n e^{-c n³}` and `P(Ω ∩ Γ₁₂ ∩ {τ'_bad ≤ t'_n}) ≤ 2 e^{-c♭ n³}`.
The hypotheses `hI`, `hH` are the interface at the single instance used and the induction
hypothesis. -/
theorem step78_bad {E : HeavyEscConsts} {n₀ n : ℕ} {t₀ : ℝ} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hp : Es4Params d β n₀ n t₀) (hT : HeavyT d n₀ E n)
    (hβ5 : E.beta5 ≤ β) (hβ6 : (10 : ℝ) ^ 14 ≤ β) (hβt : β < indScale t₀ n)
    (hI : HeavyEscInterface d β E n₀ n t₀)
    (hH : ∀ n', n₀ ≤ n' → n' < n → ∀ t₀' : ℝ, 1 < t₀' → t₀' ≤ 4 → IndHyp d β n' t₀')
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (RingSpace d β)}
    (hN : IsPoissonPointProcess N (ringIntensity d β) P) (u : Fin d → ℤ) (q : ℝ) :
    P {ω | ¬ (heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) 0 0 s) ∧
        heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) u q s - u))} ≤
      ENNReal.ofReal (2 * (heavyA d n * Real.exp (-(heavyc d E * (n : ℝ) ^ 3)))) ∧
    P {ω | cycOmega (N ω) 0 u 0 q (indScaleReduced t₀ n) ∧
        (heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) 0 0 s) ∧
          heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) u q s - u)) ∧
        step78TauBad d β t₀ n q (indScaleReduced t₀ n) u (fun s : ℝ => cycWalk (N ω) 0 0 s)
          (fun s : ℝ => cycWalk (N ω) u q s) ≤ ENNReal.ofReal (indScaleReduced t₀ n)} ≤
      ENNReal.ofReal (2 * Real.exp (-(step78Cflat d * (n : ℝ) ^ 3))) := by
  have ht0 : 0 < t₀ := by linarith
  have hn : 1 ≤ n := by have := hT.t4; omega
  have hN' : IsPoissonPointProcess (fun ω => stepShiftEnv u (-q) (N ω)) (ringIntensity d β) P :=
    isPoissonPointProcess_stepShiftEnv hN u (-q)
  have hgood := ae_good hN
  have hfun : ∀ ω, Good (N ω) → (fun s : ℝ => cycWalk (stepShiftEnv u (-q) (N ω)) 0 0 s) =
      fun s : ℝ => cycWalk (N ω) u q s - u := fun ω hω => by
    funext s; exact cycWalk_stepShiftEnv_all hω u q s
  constructor
  · have hsub : {ω | ¬ (heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) 0 0 s) ∧
        heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) u q s - u))} ≤ᵐ[P]
        {ω | ¬ heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) 0 0 s)} ∪
        {ω | ¬ heavyGamma d β t₀ n (fun s : ℝ => cycWalk (stepShiftEnv u (-q) (N ω)) 0 0 s)} := by
      filter_upwards [hgood] with ω hω hmem
      simp only [mem_union, mem_ofPred_eq]
      rw [hfun ω hω]
      by_contra hc
      push Not at hc
      exact hmem hc
    refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans ?_)
    have h1 := heavyGamma_single hI hp hT hβ5 ht0 hn hN
    have h2 := heavyGamma_single hI hp hT hβ5 ht0 hn hN'
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← two_mul]
    simp
  · by_cases hc : β < indScale t₀ n ^ (5 * indDelta d)
    · have hsub : {ω | cycOmega (N ω) 0 u 0 q (indScaleReduced t₀ n) ∧
          (heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) 0 0 s) ∧
            heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) u q s - u)) ∧
          step78TauBad d β t₀ n q (indScaleReduced t₀ n) u (fun s : ℝ => cycWalk (N ω) 0 0 s)
            (fun s : ℝ => cycWalk (N ω) u q s) ≤ ENNReal.ofReal (indScaleReduced t₀ n)} ≤ᵐ[P]
          {ω | n < {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n (N ω) ι}.ncard} ∪
          {ω | n < {ι | ι ∈ heavyBstar d n ∧
            HeavyBlockBad d β t₀ n (stepShiftEnv u (-q) (N ω)) ι}.ncard} := by
        filter_upwards [hgood] with ω hω ⟨hΩ, ⟨hΓ₁, hΓ₂⟩, hτ⟩
        rw [← hfun ω hω] at hΓ₂
        exact (step78_det hd ht1 ht4 hT hω u q hΩ hΓ₁ hΓ₂ hτ).1 hc
      refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans ?_)
      have h1 := es6_six_single hd hn0 ht1 ht4 hT hβ6 hβt hH hN
      have h2 := es6_six_single hd hn0 ht1 ht4 hT hβ6 hβt hH hN'
      have e := ENNReal.ofReal_le_ofReal (exp_six_le_cflat (d := d) n)
      refine (add_le_add (h1.trans e) (h2.trans e)).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← two_mul]
      simp
    · have h5 : indScale t₀ n ^ (5 * indDelta d) ≤ β := not_lt.1 hc
      have hsub : {ω | cycOmega (N ω) 0 u 0 q (indScaleReduced t₀ n) ∧
          (heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) 0 0 s) ∧
            heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) u q s - u)) ∧
          step78TauBad d β t₀ n q (indScaleReduced t₀ n) u (fun s : ℝ => cycWalk (N ω) 0 0 s)
            (fun s : ℝ => cycWalk (N ω) u q s) ≤ ENNReal.ofReal (indScaleReduced t₀ n)} ≤ᵐ[P]
          {ω | ∃ ι ∈ heavyBstar d n, HeavyBlockBad d β t₀ n (N ω) ι} ∪
          {ω | ∃ ι ∈ heavyBstar d n,
            HeavyBlockBad d β t₀ n (stepShiftEnv u (-q) (N ω)) ι} := by
        filter_upwards [hgood] with ω hω ⟨hΩ, ⟨hΓ₁, hΓ₂⟩, hτ⟩
        rw [← hfun ω hω] at hΓ₂
        exact (step78_det hd ht1 ht4 hT hω u q hΩ hΓ₁ hΓ₂ hτ).2 hc
      refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans ?_)
      have h1 := es6_seven_single hd hn0 ht1 ht4 hT hβ6 hβt h5 hH hN
      have h2 := es6_seven_single hd hn0 ht1 ht4 hT hβ6 hβt h5 hH hN'
      have e := ENNReal.ofReal_le_ofReal (exp_seven_le_cflat (d := d) n)
      refine (add_le_add (h1.trans e) (h2.trans e)).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← two_mul]
      simp

end ElboimSly.Paper.Step

end
