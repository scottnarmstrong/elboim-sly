/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.TransienceR
public import Mathlib

/-!
# Transience from a far start

Transience: escape from the unit box, "far start".
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

theorem norm_cast_lt_two {w : Fin d → ℤ} (h : ‖fun i => ((w i : ℤ) : ℝ)‖ < 2) :
    ‖fun i => ((w i : ℤ) : ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  have h1 : ‖((w i : ℤ) : ℝ)‖ < 2 := lt_of_le_of_lt (norm_le_pi_norm (fun i => ((w i : ℤ) : ℝ)) i) h
  rw [Real.norm_eq_abs] at h1 ⊢
  have h2 : |w i| < 2 := by
    have : ((|w i| : ℤ) : ℝ) < 2 := by rw [Int.cast_abs]; exact h1
    exact_mod_cast this
  have h3 : |w i| ≤ 1 := by omega
  have : ((|w i| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h3
  rwa [Int.cast_abs] at this

/-- Transience: escape from the unit box, far start. -/
theorem far_start (hZ : IsSRW P Z) (hd : 3 ≤ d) {z : Fin d → ℤ} (hz : (escR d : ℝ) ≤ ‖z‖) :
    1 / 2 ≤ P.real {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((z i + Z ω s i : ℤ) : ℝ)‖} := by
  have : NeZero d := ⟨by omega⟩
  have := hZ.isProbabilityMeasure
  obtain ⟨hR2, hRb⟩ := escR_spec hd
  set R := escR d with hRdef
  have hR2' : (2 : ℝ) ≤ R := by exact_mod_cast hR2
  have hR0 : (0 : ℝ) < R := by linarith
  set a : ℝ≥0 := ((R : ℝ) ^ (3 / 2 : ℝ)).toNNReal with ha
  have hac : (a : ℝ) = (R : ℝ) ^ (3 / 2 : ℝ) := Real.coe_toNNReal _ (by positivity)
  have ha0 : 0 < a := by
    have : (0 : ℝ) < a := by rw [hac]; positivity
    exact_mod_cast this
  set S := {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((z i + Z ω s i : ℤ) : ℝ)‖} with hS
  set B1 := {ω | ∃ s : ℝ≥0, s ≤ a ∧ (R : ℝ) - 1 ≤ ‖Z ω s‖} with hB1
  set B2 := {ω | ∃ s : ℝ≥0, a ≤ s ∧
    ‖fun i => ((z i + Z ω s i - (0 : Fin d → ℤ) i : ℤ) : ℝ)‖ ≤ 1} with hB2
  have hsub : Sᶜ ⊆ B1 ∪ B2 := by
    intro ω hω
    simp only [hS, mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨s, hs⟩ := hω
    have hs1 := norm_cast_lt_two hs
    rcases le_or_gt s a with h | h
    · left
      refine ⟨s, h, ?_⟩
      have hz' : ‖fun i => ((z i : ℤ) : ℝ)‖ = ‖z‖ := norm_cast_vec z
      have hZs : ‖fun i => ((Z ω s i : ℤ) : ℝ)‖ = ‖Z ω s‖ := norm_cast_vec _
      have e : (fun i => ((z i : ℤ) : ℝ)) =
          (fun i => ((z i + Z ω s i : ℤ) : ℝ)) - (fun i => ((Z ω s i : ℤ) : ℝ)) := by
        funext i; simp
      have : ‖fun i => ((z i : ℤ) : ℝ)‖ ≤ ‖fun i => ((z i + Z ω s i : ℤ) : ℝ)‖ +
          ‖fun i => ((Z ω s i : ℤ) : ℝ)‖ := by
        rw [e]; exact norm_sub_le _ _
      linarith
    · right
      exact ⟨s, h.le, by simpa using hs1⟩
  have h1 := real_one_sub_le P S (B1 ∪ B2) hsub
  have h2 : P.real (B1 ∪ B2) ≤ P.real B1 + P.real B2 := measureReal_union_le _ _
  -- B1
  have hB1b : P.real B1 ≤ 4 * (d : ℝ) * Real.exp (-(√(R : ℝ) / 32)) := by
    have := hZ.maximal ha0 (a := (R : ℝ) - 1) (by linarith)
    refine this.trans ?_
    gcongr
    have hsq : √(R : ℝ) ^ 2 = R := Real.sq_sqrt hR0.le
    have hs0 : 0 < √(R : ℝ) := Real.sqrt_pos.2 hR0
    have hRs : (R : ℝ) ^ (3 / 2 : ℝ) = R * √R := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hR0, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    rw [hac, hRs]
    refine le_min ?_ ?_
    · rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [sq_nonneg ((R : ℝ) - 2)]
    · nlinarith
  -- B2
  have hB2b : P.real B2 ≤ Chit d * (R : ℝ) ^ (-(3 * ((d : ℝ) - 2) / 4)) := by
    have := hit hZ hd z 0 (ρ := 1) le_rfl ha0
    refine this.trans (le_of_eq ?_)
    congr 1
    have hsa : √(a : ℝ) = (R : ℝ) ^ (3 / 4 : ℝ) := by
      rw [hac, Real.sqrt_eq_rpow, ← Real.rpow_mul hR0.le]; norm_num
    rw [hsa, one_div, ← Real.rpow_neg hR0.le, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
    congr 1
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  linarith

end SRW
end ElboimSly
