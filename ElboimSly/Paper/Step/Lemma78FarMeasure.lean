/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Lemma 7.8, far lemma: the measure of the near set

ES22 Lemma 6.8, "The near set": `|Nr| ≤ 2^d L_cov 3.9^k + 1`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

/-- A set covered, on `[c, c + tk]`, by finitely many translates of sets of measure `≤ g`
(`#M · L` of them), and contained in `[c, t]` with `t ≤ c + tk + 1`, has measure `≤ #M L g + 1`. -/
theorem measure_near_le {ι : Type*} {S : Set ℝ} {c tk t g L : ℝ} (M : Finset ι) (G : ι → Finset ℝ)
    (X : ι → ℝ → Set ℝ) (hg : 0 ≤ g) (hL0 : 0 ≤ L) (hL : ∀ i ∈ M, ((G i).card : ℝ) ≤ L)
    (hcov : ∀ s ∈ S ∩ Icc c (c + tk), ∃ i ∈ M, ∃ b ∈ G i, s - c ∈ X i b)
    (hX : ∀ i ∈ M, ∀ b ∈ G i, volume (X i b) ≤ ENNReal.ofReal g)
    (hS : S ⊆ Icc c t) (ht : t ≤ c + tk + 1) :
    volume S ≤ ENNReal.ofReal (M.card * L * g + 1) := by
  classical
  have hsub : S ⊆ (⋃ i ∈ M, ⋃ b ∈ G i, (fun s => s - c) ⁻¹' X i b) ∪ Icc (c + tk) t := by
    intro s hs
    by_cases h : s ≤ c + tk
    · obtain ⟨i, hi, b, hb, hx⟩ := hcov s ⟨hs, (hS hs).1, h⟩
      left
      simp only [mem_iUnion]
      exact ⟨i, hi, b, hb, hx⟩
    · exact Or.inr ⟨(not_le.1 h).le, (hS hs).2⟩
  have hv1 : volume (⋃ i ∈ M, ⋃ b ∈ G i, (fun s => s - c) ⁻¹' X i b) ≤
      ENNReal.ofReal (M.card * L * g) := by
    refine (measure_biUnion_finset_le M _).trans ?_
    have : ∀ i ∈ M, volume (⋃ b ∈ G i, (fun s => s - c) ⁻¹' X i b) ≤
        ENNReal.ofReal (L * g) := by
      intro i hi
      refine (measure_biUnion_finset_le (G i) _).trans ?_
      have hpre : ∀ b ∈ G i, volume ((fun s => s - c) ⁻¹' X i b) ≤ ENNReal.ofReal g := by
        intro b hb
        have : (fun s : ℝ => s - c) ⁻¹' X i b = (fun s => s + -c) ⁻¹' X i b := by
          ext s; simp [sub_eq_add_neg]
        rw [this, measure_preimage_add_right]
        exact hX i hi b hb
      refine (Finset.sum_le_sum hpre).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have : ((G i).card : ℝ≥0∞) * ENNReal.ofReal g = ENNReal.ofReal ((G i).card * g) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      rw [this]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hL i hi) hg)
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact le_of_eq (by congr 1; ring)
  have hv2 : volume (Icc (c + tk) t) ≤ ENNReal.ofReal 1 := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hLg : 0 ≤ (M.card : ℝ) * L * g := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hL0) hg
  calc volume S ≤ _ := (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (M.card * L * g) + ENNReal.ofReal 1 := add_le_add hv1 hv2
    _ = _ := (ENNReal.ofReal_add hLg zero_le_one).symm

end ElboimSly.Paper.Step

end
