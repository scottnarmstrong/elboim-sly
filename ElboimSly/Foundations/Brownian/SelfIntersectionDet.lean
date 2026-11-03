/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.SelfIntersectionBlock

import Mathlib

/-!
# A deterministic bound on `|T|`

ES22 Claim 9.4, Step 1.

With the blocks `[s_j, s_{j+1}]`, `s_j = j r²`, and the block events `E_j`
(`blockEvent`), `Leb T` is at most `J K + r² #{j < J : E_j} + (t - s_J)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} {B : ℝ≥0 → Ω → R5}

lemma nnLebesgue_Icc_sub (x y : ℝ≥0) : nnLebesgue (Set.Icc x y) = ((y - x : ℝ≥0) : ℝ≥0∞) := by
  unfold nnLebesgue
  rw [Measure.comap_apply _ NNReal.coe_injective (fun s hs =>
    hs.image_of_continuousOn_injOn NNReal.continuous_coe.continuousOn NNReal.coe_injective.injOn)
    _ measurableSet_Icc]
  have : ((↑) : ℝ≥0 → ℝ) '' Set.Icc x y = Set.Icc (x : ℝ) y := by
    ext z
    constructor
    · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h0, h1⟩
      exact ⟨⟨z, x.2.trans h0⟩, ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩, rfl⟩
  rw [this, Real.volume_Icc]
  rcases le_total x y with hxy | hxy
  · rw [← NNReal.coe_sub hxy, ENNReal.ofReal_coe_nnreal]
  · rw [tsub_eq_zero_of_le hxy]
    simp [ENNReal.ofReal_of_nonpos, sub_nonpos.2 (show (y : ℝ) ≤ x from hxy)]

/-- The block endpoints `s_j = j r²`. -/
noncomputable def blkT (r2 : ℝ) (j : ℕ) : ℝ≥0 := Real.toNNReal (j * r2)

lemma blkT_coe {r2 : ℝ} (h : 0 ≤ r2) (j : ℕ) : (blkT r2 j : ℝ) = j * r2 :=
  Real.coe_toNNReal _ (by positivity)

lemma blkT_succ {r2 : ℝ} (h : 0 ≤ r2) (j : ℕ) : (blkT r2 (j + 1) : ℝ) = blkT r2 j + r2 := by
  rw [blkT_coe h, blkT_coe h]; push_cast; ring

lemma blkT_mono {r2 : ℝ} (h : 0 ≤ r2) : Monotone (blkT r2) := by
  intro i j hij
  rw [← NNReal.coe_le_coe, blkT_coe h, blkT_coe h]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) h

lemma blkT_sub {r2 : ℝ} (h : 0 ≤ r2) (j : ℕ) :
    ((blkT r2 (j + 1) - blkT r2 j : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal r2 := by
  have h1 : ((blkT r2 (j + 1) - blkT r2 j : ℝ≥0) : ℝ) = r2 := by
    rw [NNReal.coe_sub (blkT_mono h (Nat.le_succ j)), blkT_succ h]; ring
  rw [← ENNReal.ofReal_coe_nnreal, h1]

/-- The integer times of the block `[s_j, s_{j+1}]` lying at least `K - 1` after `s_j`. -/
noncomputable def blkI (r2 K : ℝ) (j : ℕ) : Finset ℕ :=
  Finset.Icc ⌈(blkT r2 j : ℝ) + K - 1⌉₊ ⌊(blkT r2 (j + 1) : ℝ)⌋₊

/-- The block event `E_j`. -/
def blkE (B : ℝ≥0 → Ω → R5) (r2 K ρ : ℝ) (j : ℕ) : Set Ω :=
  blockEvent B (blkT r2 j) (blkT r2 (j + 1)) (blkI r2 K j) ρ

/-- If `s ∈ T` lies in block `j` beyond `s_j + K`, then `E_j` holds. -/
lemma blkE_of_mem {ω : Ω} {r2 K ρ : ℝ} (hr2 : 0 ≤ r2) (hK : 2 ≤ K) {L : ℝ≥0}
    (hL : (L : ℝ) = r2) {j : ℕ} {s s' : ℝ≥0} (hs1 : (blkT r2 j : ℝ) + K < s)
    (hs2 : (s : ℝ) < blkT r2 (j + 1)) (hs' : s' + L ≤ s)
    (hn : ‖(1 : ℝ) • B s ω - (1 : ℝ) • B s' ω‖ ≤ 1) : ω ∈ blkE B r2 K ρ j := by
  have hb := blkT_succ hr2 j
  set a := blkT r2 j with ha
  have hs'a : s' ≤ a := by
    have : (s' : ℝ) + r2 ≤ s := by rw [← hL]; exact_mod_cast hs'
    rw [← NNReal.coe_le_coe]; linarith
  set i : ℕ := ⌊(s : ℝ)⌋₊ with hi
  have hi1 : (i : ℝ) ≤ s := Nat.floor_le s.2
  have hi2 : (s : ℝ) < i + 1 := Nat.lt_floor_add_one _
  have hiI : i ∈ blkI r2 K j := by
    unfold blkI
    rw [Finset.mem_Icc]
    refine ⟨Nat.ceil_le.2 (by linarith), Nat.le_floor (by linarith)⟩
  have hai : (a : ℝ) + 1 ≤ i := by linarith
  by_cases h : ‖B s ω - B (i : ℝ≥0) ω‖ ≤ ρ
  · left
    refine ⟨i, hiI, s', hs'a, ?_⟩
    simp only [one_smul] at hn
    calc ‖B (i : ℝ≥0) ω - B s' ω‖ = ‖-(B s ω - B (i : ℝ≥0) ω) + (B s ω - B s' ω)‖ := by
          congr 1; abel
      _ ≤ ‖-(B s ω - B (i : ℝ≥0) ω)‖ + ‖B s ω - B s' ω‖ := norm_add_le _ _
      _ ≤ 1 + ρ := by rw [norm_neg]; linarith
  · right
    refine ⟨s, (i : ℝ≥0), ?_, ?_, ?_, ?_, ?_, not_le.1 h⟩
    · rw [← NNReal.coe_le_coe]; linarith
    · rw [← NNReal.coe_le_coe]; linarith
    · rw [← NNReal.coe_le_coe]; push_cast; linarith
    · rw [← NNReal.coe_le_coe]; push_cast; linarith
    · rw [NNReal.dist_eq, abs_le]; push_cast
      constructor <;> linarith

open scoped Classical in
/-- ES22 Claim 9.4, Step 1. -/
theorem sepVol_le {ω : Ω} {r2 K ρ : ℝ} (hr2 : 0 ≤ r2) (hK : 2 ≤ K) {L t : ℝ≥0}
    (hL : (L : ℝ) = r2) (J : ℕ) (hr : 0 < r2) :
    nnLebesgue (sepSet B 1 L t ω) ≤
      (J : ℝ≥0∞) * ENNReal.ofReal K +
      (((Finset.range J).filter fun j => ω ∈ blkE B r2 K ρ j).card : ℝ≥0∞) *
        ENNReal.ofReal r2 + ((t - blkT r2 J : ℝ≥0) : ℝ≥0∞) := by
  classical
  set Js : Finset ℕ := (Finset.range J).filter fun j => ω ∈ blkE B r2 K ρ j with hJs
  set K' : ℝ≥0 := Real.toNNReal K with hK'
  have hsub : sepSet B 1 L t ω ⊆ Set.Icc (blkT r2 J) t ∪
      ((⋃ j ∈ Finset.range J, Set.Icc (blkT r2 j) (blkT r2 j + K')) ∪
        ⋃ j ∈ Js, Set.Icc (blkT r2 j) (blkT r2 (j + 1))) := by
    rintro s ⟨hst, s', hs', hn⟩
    by_cases hsJ : blkT r2 J ≤ s
    · exact Or.inl ⟨hsJ, hst⟩
    · right
      push Not at hsJ
      have hsJ' : (s : ℝ) < J * r2 := by
        have := (NNReal.coe_lt_coe).2 hsJ
        rwa [blkT_coe hr2] at this
      set j : ℕ := ⌊(s : ℝ) / r2⌋₊ with hj
      have hj1 : (j : ℝ) ≤ s / r2 := Nat.floor_le (div_nonneg s.2 hr2)
      have hj2 : (s : ℝ) / r2 < j + 1 := Nat.lt_floor_add_one _
      have hj1' : (j : ℝ) * r2 ≤ s := by
        rw [le_div_iff₀ hr] at hj1; exact hj1
      have hj2' : (s : ℝ) < (j + 1) * r2 := by
        rw [div_lt_iff₀ hr] at hj2; exact hj2
      have hjJ : j < J := by
        have : (j : ℝ) < J := by
          have h3 : (j : ℝ) * r2 < J * r2 := lt_of_le_of_lt hj1' hsJ'
          exact lt_of_mul_lt_mul_right h3 hr2
        exact_mod_cast this
      have haj : blkT r2 j ≤ s := by rw [← NNReal.coe_le_coe, blkT_coe hr2]; exact hj1'
      have hbj : (s : ℝ) < blkT r2 (j + 1) := by rw [blkT_coe hr2]; push_cast; exact hj2'
      by_cases hsK : (s : ℝ) ≤ blkT r2 j + K
      · left
        refine Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hjJ, haj, ?_⟩
        rw [← NNReal.coe_le_coe]
        push_cast
        rw [hK', Real.coe_toNNReal _ (by linarith)]
        exact hsK
      · right
        push Not at hsK
        have hE : ω ∈ blkE B r2 K ρ j := blkE_of_mem hr2 hK hL hsK hbj hs' hn
        exact Set.mem_iUnion₂.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hjJ, hE⟩, haj,
          (NNReal.coe_le_coe.1 (by exact hbj.le))⟩
  calc nnLebesgue (sepSet B 1 L t ω)
      ≤ nnLebesgue (Set.Icc (blkT r2 J) t ∪
        ((⋃ j ∈ Finset.range J, Set.Icc (blkT r2 j) (blkT r2 j + K')) ∪
          ⋃ j ∈ Js, Set.Icc (blkT r2 j) (blkT r2 (j + 1)))) := measure_mono hsub
    _ ≤ nnLebesgue (Set.Icc (blkT r2 J) t) +
        (nnLebesgue (⋃ j ∈ Finset.range J, Set.Icc (blkT r2 j) (blkT r2 j + K')) +
          nnLebesgue (⋃ j ∈ Js, Set.Icc (blkT r2 j) (blkT r2 (j + 1)))) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ nnLebesgue (Set.Icc (blkT r2 J) t) +
        ((∑ j ∈ Finset.range J, nnLebesgue (Set.Icc (blkT r2 j) (blkT r2 j + K'))) +
          ∑ j ∈ Js, nnLebesgue (Set.Icc (blkT r2 j) (blkT r2 (j + 1)))) :=
        add_le_add le_rfl (add_le_add (measure_biUnion_finset_le _ _)
          (measure_biUnion_finset_le _ _))
    _ = ((t - blkT r2 J : ℝ≥0) : ℝ≥0∞) +
        (((J : ℝ≥0∞) * ENNReal.ofReal K) + (Js.card : ℝ≥0∞) * ENNReal.ofReal r2) := by
        rw [nnLebesgue_Icc_sub]
        congr 2
        · simp only [nnLebesgue_Icc_sub, add_tsub_cancel_left, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
          rfl
        · simp only [nnLebesgue_Icc_sub, blkT_sub hr2, Finset.sum_const, nsmul_eq_mul]
    _ = _ := by ring

end ElboimSly.Brownian
