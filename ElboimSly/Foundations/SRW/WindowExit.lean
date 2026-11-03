/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.KernelOneD
public import ElboimSly.Foundations.SRW.Levy
public import ElboimSly.Foundations.SRW.Chernoff
public import ElboimSly.Foundations.SRW.LocalLower
public import Mathlib

/-!
# One window: exit probability and numerics

One window (first half).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

theorem exp_six_ge : (128 : ℝ) ≤ Real.exp 6 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 6 = Real.exp 1 ^ 6 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (128 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
    _ ≤ Real.exp 1 ^ 6 := by gcongr

theorem real_one_sub_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S T : Set Ω) (h : Sᶜ ⊆ T) : 1 - P.real S ≤ P.real T := by
  have h1 : P.real (S ∪ Sᶜ) ≤ P.real S + P.real Sᶜ := measureReal_union_le _ _
  rw [union_compl_self, probReal_univ] at h1
  have := measureReal_mono (μ := P) h
  linarith

/-- The exit probability from the interval `[-ℓ, ℓ]` by time `ρ/2`, started at `x`. -/
theorem exit_mass {ρ : ℝ≥0} (hρ : 2 ≤ (ρ : ℝ)) {ℓ x : ℤ} (hℓ : 16 * √(ρ : ℝ) ≤ ℓ)
    (hx : |(x : ℝ)| ≤ √(ρ : ℝ)) :
    1 - ∑' b, kernel1 (Icc (-ℓ) ℓ) (ρ / 2) x b ≤ 4 * Real.exp (-10) := by
  have hY := srwZ_isSRW 1
  have := hY.isProbabilityMeasure
  rw [kernel1_tsum]
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hsq : 0 < √(ρ : ℝ) := Real.sqrt_pos.2 hρ0
  have hsq2 : (√(ρ : ℝ)) ^ 2 = ρ := Real.sq_sqrt hρ0.le
  show 1 - (srwP 1).real _ ≤ _
  set P := srwP 1 with hPdef
  set S : Set (srwΩ 1) := {ω | ∀ s : ℝ≥0, s ≤ ρ / 2 → x + srwZ 1 ω s 0 ∈ Icc (-ℓ) ℓ} with hS
  set T : Set (srwΩ 1) := {ω | ∃ s : ℝ≥0, s ≤ ρ / 2 ∧ 15 * √(ρ : ℝ) ≤ |(srwZ 1 ω s 0 : ℝ)|}
    with hT
  have hsub : Sᶜ ⊆ T := by
    intro ω hω
    simp only [hS, mem_compl_iff, mem_ofPred_eq, not_forall] at hω
    obtain ⟨s, hs, hns⟩ := hω
    refine ⟨s, hs, ?_⟩
    have h1 : (ℓ : ℝ) < |((x + srwZ 1 ω s 0 : ℤ) : ℝ)| := by
      simp only [mem_Icc, not_and_or, not_le] at hns
      rcases hns with h | h
      · have : (x + srwZ 1 ω s 0 : ℤ) < -ℓ := h
        have : ((x + srwZ 1 ω s 0 : ℤ) : ℝ) < -(ℓ : ℝ) := by exact_mod_cast this
        have := neg_abs_le ((x + srwZ 1 ω s 0 : ℤ) : ℝ)
        linarith
      · have : ℓ < (x + srwZ 1 ω s 0 : ℤ) := h
        have : (ℓ : ℝ) < ((x + srwZ 1 ω s 0 : ℤ) : ℝ) := by exact_mod_cast this
        have := le_abs_self ((x + srwZ 1 ω s 0 : ℤ) : ℝ)
        linarith
    have h2 : |((x + srwZ 1 ω s 0 : ℤ) : ℝ)| ≤ |(x : ℝ)| + |(srwZ 1 ω s 0 : ℝ)| := by
      push_cast; exact abs_add_le _ _
    linarith
  have h1 := real_one_sub_le P S T hsub
  have h2 := hY.levy_abs (ρ / 2) (15 * √(ρ : ℝ))
  have hρ2 : 0 < ρ / 2 := by
    have : (0 : ℝ≥0) < ρ := by exact_mod_cast hρ0
    positivity
  have h3 := hY.chernoff_abs hρ2 (a := 15 * √(ρ : ℝ)) (by positivity)
  have hcast : ((ρ / 2 : ℝ≥0) : ℝ) = (ρ : ℝ) / 2 := by push_cast; ring
  rw [hcast] at h3
  have hmin : (10 : ℝ) ≤ min ((15 * √(ρ : ℝ)) ^ 2 / (8 * ((ρ : ℝ) / 2))) (15 * √(ρ : ℝ) / 2) := by
    refine le_min ?_ ?_
    · rw [mul_pow, hsq2, le_div_iff₀ (by positivity)]
      nlinarith
    · have : (4 / 3 : ℝ) ≤ √(ρ : ℝ) := by
        refine Real.le_sqrt_of_sq_le ?_
        nlinarith
      linarith
  have h4 : Real.exp (-min ((15 * √(ρ : ℝ)) ^ 2 / (8 * ((ρ : ℝ) / 2))) (15 * √(ρ : ℝ) / 2)) ≤
      Real.exp (-10) := Real.exp_le_exp.2 (by linarith)
  have h5 : P.real T ≤ 2 * P.real {ω | 15 * √(ρ : ℝ) ≤ |(srwZ 1 ω (ρ / 2) 0 : ℝ)|} := h2
  linarith

end SRW
end ElboimSly
