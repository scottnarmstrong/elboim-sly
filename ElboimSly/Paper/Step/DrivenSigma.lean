/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.DrivenLaw
public import Mathlib

/-!
# Regeneration times are read from the path

The driven regenerated walk (d): `σ_i = inf {r ∈ βℤ : r > σ_{i-1}, w(r) = 0}` for the
regenerated walk `w = W^x_reg` driven by `x`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Cyclic
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ} {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ}

theorem drivenPieces_regPath (hx : IsRegPath x) (n : ℕ) : IsRegPath (drivenPieces b x n) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact isRegPath_shiftPath ih _

theorem drivenSigma_top_or (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (n : ℕ) :
    drivenSigma b x n = ⊤ ∨ ∃ m : ℕ, drivenSigma b x n = (((m : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) := by
  induction n with
  | zero => exact Or.inr ⟨0, by simp [drivenSigma_zero]⟩
  | succ n ih =>
    rw [drivenSigma_succ]
    rcases ih with h | ⟨m, hm⟩
    · left; simp [h]
    · rcases pathTreg_top_or b (drivenWalk b (drivenPieces b x n)) with h' | ⟨k, -, hk, -⟩
      · left; show _ + pathTreg b (drivenWalk b (drivenPieces b x n)) = _
        rw [h']; simp
      · right
        refine ⟨m + k, ?_⟩
        show _ + pathTreg b (drivenWalk b (drivenPieces b x n)) = _
        rw [hk, hm]
        push_cast
        rw [add_mul]

theorem drivenRegenFrom_piece {t : ℝ≥0} {n : ℕ} (hn : drivenSigma b x n ≤ t)
    (ht : (t : ℝ≥0∞) < drivenSigma b x (n + 1)) :
    drivenRegenFrom b x t =
      drivenWalk b (drivenPieces b x n) (t - (drivenSigma b x n).toNNReal) := by
  unfold drivenRegenFrom drivenRegenWalk gluedWalk
  have hc := gluedCount_eq (drivenSigma_mono b x) hn ht
  change drivenWalk b (drivenPieces b x (gluedCount (drivenSigma b x) t))
    (t - (drivenSigma b x (gluedCount (drivenSigma b x) t)).toNNReal) = _
  rw [hc]

/-- The regenerated walk is `0` at a finite regeneration time `σ_{n+1}`. -/
theorem drivenRegenFrom_sigma (hb : 0 < b) (hx : IsRegPath x) {n : ℕ} {s : ℝ≥0}
    (hs : drivenSigma b x (n + 1) = s) : drivenRegenFrom b x s = 0 := by
  have hbt : (b : ℝ≥0∞) ≤ drivenTreg b (drivenPieces b x (n + 1)) := le_pathTreg _ _
  have hlt : (s : ℝ≥0∞) < drivenSigma b x (n + 1 + 1) := by
    rw [drivenSigma_succ, hs]
    calc (s : ℝ≥0∞) < s + b := ENNReal.lt_add_right (by simp) (by simpa using hb.ne')
      _ ≤ _ := add_le_add le_rfl hbt
  rw [drivenRegenFrom_piece (n := n + 1) (by rw [hs]) hlt, hs, ENNReal.toNNReal_coe, tsub_self]
  exact drivenWalk_zero (drivenPieces_regPath hx _) hb

/-- **Regeneration times are read from the path** (the driven regenerated walk (d)). -/
theorem drivenSigma_succ_eq_iInf (hb : 0 < b) (hx : IsRegPath x) (n : ℕ) :
    drivenSigma b x (n + 1) =
      ⨅ r ∈ {r : ℝ≥0 | (∃ k : ℕ, r = (k : ℝ≥0) * b) ∧ drivenSigma b x n < r ∧
        drivenRegenFrom b x r = 0}, (r : ℝ≥0∞) := by
  apply le_antisymm
  · refine le_iInf₂ fun r hr => ?_
    obtain ⟨⟨k, rfl⟩, hSr, hw⟩ := hr
    by_contra hlt
    push Not at hlt
    have hSne : drivenSigma b x n ≠ ⊤ := ne_top_of_lt hSr
    rcases drivenSigma_top_or b x n with h | ⟨m, hm⟩
    · exact hSne h
    have hmk : m < k := by
      rw [hm] at hSr
      have : (m : ℝ≥0) * b < (k : ℝ≥0) * b := by exact_mod_cast hSr
      exact_mod_cast lt_of_mul_lt_mul_right this zero_le
    rw [drivenRegenFrom_piece (n := n) hSr.le
      hlt, hm, ENNReal.toNNReal_coe] at hw
    have hsub : (k : ℝ≥0) * b - (m : ℝ≥0) * b = ((k - m : ℕ) : ℝ≥0) * b := by
      calc (k : ℝ≥0) * b - (m : ℝ≥0) * b
          = ((k - m : ℕ) : ℝ≥0) * b + (m : ℝ≥0) * b - (m : ℝ≥0) * b := by
            rw [← add_mul, ← Nat.cast_add, Nat.sub_add_cancel hmk.le]
        _ = _ := add_tsub_cancel_right _ _
    rw [hsub] at hw
    have hT : drivenTreg b (drivenPieces b x n) ≤ (((k - m : ℕ) : ℝ≥0) * b : ℝ≥0) := by
      unfold drivenTreg pathTreg
      exact iInf_le (fun j : {j : ℕ // 1 ≤ j ∧ drivenWalk b (drivenPieces b x n)
        ((j : ℝ≥0) * b) = 0} => (((j.1 : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞))
        ⟨k - m, by omega, hw⟩
    have : drivenSigma b x (n + 1) ≤ (((k : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) := by
      rw [drivenSigma_succ, hm]
      calc (((m : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) + drivenTreg b (drivenPieces b x n)
          ≤ (((m : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) + (((k - m : ℕ) : ℝ≥0) * b : ℝ≥0) :=
            add_le_add le_rfl hT
        _ = (((k : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) := by
            rw [← ENNReal.coe_add, ← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hmk.le]
    exact absurd hlt (not_lt.2 this)
  · by_cases htop : drivenSigma b x (n + 1) = ⊤
    · rw [htop]; exact le_top
    · obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, drivenSigma b x (n + 1) = s := ⟨_, (ENNReal.coe_toNNReal htop).symm⟩
      have hSne : drivenSigma b x n ≠ ⊤ := by
        intro h
        apply htop
        rw [drivenSigma_succ, h]; simp
      rcases drivenSigma_top_or b x n with h | ⟨m, hm⟩
      · exact absurd h hSne
      have hTne : drivenTreg b (drivenPieces b x n) ≠ ⊤ := by
        intro h; apply htop; rw [drivenSigma_succ, h]; simp
      rcases pathTreg_top_or b (drivenWalk b (drivenPieces b x n)) with h | ⟨k, hk1, hk, -⟩
      · exact absurd h hTne
      refine iInf₂_le_of_le s ⟨⟨m + k, ?_⟩, ?_, drivenRegenFrom_sigma hb hx hs⟩ ?_
      · have : (s : ℝ≥0∞) = (((m + k : ℕ) : ℝ≥0) * b : ℝ≥0) := by
          rw [← hs, drivenSigma_succ, hm]
          show _ + pathTreg b (drivenWalk b (drivenPieces b x n)) = _
          rw [hk, ← ENNReal.coe_add, ← add_mul, ← Nat.cast_add]
        exact_mod_cast this
      · rw [← hs, drivenSigma_succ, hm]
        show _ < _ + pathTreg b (drivenWalk b (drivenPieces b x n))
        rw [hk]
        exact ENNReal.lt_add_right ENNReal.coe_ne_top
          (ENNReal.coe_ne_zero.2 (mul_pos (Nat.cast_pos.2 hk1) hb).ne')
      · rw [hs]

/-- The driven regenerated walk (d), in the notation of driving paths; the regenerated walk driven by a path. -/
theorem stepSigma_succ_eq_iInf {β : ℝ} [Fact (0 < β)] (hx : x ∈ StepPath d) (n : ℕ) :
    stepSigma β x (n + 1) =
      ⨅ r ∈ {r : ℝ≥0 | (∃ k : ℕ, r = (k : ℝ≥0) * β.toNNReal) ∧ stepSigma β x n < r ∧
        stepReg β x r = 0}, (r : ℝ≥0∞) :=
  drivenSigma_succ_eq_iInf toNNReal_pos' hx.toIsRegPath n

end ElboimSly.Paper
