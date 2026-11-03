/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.HitSeries
public import ElboimSly.Foundations.SRW.SrwLaw
public import Mathlib

/-!
# Expected visits to a ball

Used in hitting a box after a given time: `∑_{k ≥ K₀} P(‖Z(k) - c‖ < R) ≤ 3 (2R+1)^d π^{-d/2} K₀^{1-d/2}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

/-- The event that the walk is within distance `< R` of `c` at the integer time `k`, for
`k ≥ K₀`. -/
def ballVisit (Z : Ω → PathSpace d) (c : Fin d → ℤ) (R : ℝ) (K₀ k : ℕ) : Set Ω :=
  {ω | K₀ ≤ k ∧ ‖fun i => ((Z ω (k : ℝ≥0) i - c i : ℤ) : ℝ)‖ < R}

theorem prob_ballVisit_le (hZ : IsSRW P Z) (c : Fin d → ℤ) {R : ℝ} (hR : 0 < R) {K₀ : ℕ}
    (hK₀ : 1 ≤ K₀) (k : ℕ) :
    P (ballVisit Z c R K₀ k) ≤
      if K₀ ≤ k then ENNReal.ofReal ((2 * R + 1) ^ d * (π * k) ^ (-(d : ℝ) / 2)) else 0 := by
  by_cases hk : K₀ ≤ k
  · rw [ite_eq_left hk]
    have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hK₀.trans hk
    have hsub : ballVisit Z c R K₀ k ⊆ ⋃ z ∈ ballBox c R, {ω | Z ω (k : ℝ≥0) = z} := by
      intro ω hω
      exact mem_iUnion₂.2 ⟨Z ω k, mem_ballBox hω.2, rfl⟩
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    have hterm : ∀ z, P {ω | Z ω (k : ℝ≥0) = z} ≤ ENNReal.ofReal ((π * k) ^ (-(d : ℝ) / 2)) := by
      intro z
      exact hZ.prob_eq_le (t := (k : ℝ≥0)) (by simpa using hk1) z
    calc ∑ z ∈ ballBox c R, P {ω | Z ω (k : ℝ≥0) = z}
        ≤ ∑ _z ∈ ballBox c R, ENNReal.ofReal ((π * k) ^ (-(d : ℝ) / 2)) :=
          Finset.sum_le_sum fun z _ => hterm z
      _ = (ballBox c R).card * ENNReal.ofReal ((π * k) ^ (-(d : ℝ) / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal ((2 * R + 1) ^ d) * ENNReal.ofReal ((π * k) ^ (-(d : ℝ) / 2)) := by
          gcongr
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (card_ballBox_le c hR)
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  · rw [ite_eq_right hk]
    have : ballVisit Z c R K₀ k = ∅ := by
      ext ω; simp [ballVisit, hk]
    rw [this]; simp

theorem tsum_ballVisit_le (hZ : IsSRW P Z) (hd : 3 ≤ d) (c : Fin d → ℤ) {R : ℝ} (hR : 0 < R)
    {K₀ : ℕ} (hK₀ : 1 ≤ K₀) :
    ∑' k : ℕ, P (ballVisit Z c R K₀ k) ≤
      ENNReal.ofReal ((2 * R + 1) ^ d * π ^ (-(d : ℝ) / 2) *
        (3 * (K₀ : ℝ) ^ (1 - (d : ℝ) / 2))) := by
  have hp : (3 / 2 : ℝ) ≤ (d : ℝ) / 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  have h1 : ∀ k ∈ Finset.range n, P (ballVisit Z c R K₀ k) ≤
      if K₀ ≤ k then ENNReal.ofReal ((2 * R + 1) ^ d * π ^ (-(d : ℝ) / 2) *
        (k : ℝ) ^ (-((d : ℝ) / 2))) else 0 := by
    intro k hk
    refine (prob_ballVisit_le hZ c hR hK₀ k).trans ?_
    split_ifs with h
    · refine le_of_eq ?_
      congr 1
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      rw [Real.mul_rpow Real.pi_pos.le hk0, mul_assoc]
      congr 2
      rw [neg_div]
    · exact le_rfl
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.sum_filter]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  have := sum_rpow_tail_le hp hK₀ n
  have hC : 0 ≤ (2 * R + 1) ^ d * π ^ (-(d : ℝ) / 2) := by positivity
  calc (2 * R + 1) ^ d * π ^ (-(d : ℝ) / 2) *
        ∑ k ∈ (Finset.range n).filter (K₀ ≤ ·), (k : ℝ) ^ (-((d : ℝ) / 2))
      ≤ (2 * R + 1) ^ d * π ^ (-(d : ℝ) / 2) * (3 * (K₀ : ℝ) ^ (1 - (d : ℝ) / 2)) := by
        gcongr

end SRW
end ElboimSly
