/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Entrance
public import ElboimSly.Paper.Heavy.CountVisited

/-!
# Visited vertices in one block (Step 1 of ES22 Lemma 6.4)

ES22 Lemma 6.4, Step 1 (ES22 §6; deviation D6, counting jumps).

For a cyclic path `w`, `1 ≤ n`, `j_n ≤ m`, `B = heavyBlock m ι` and `t ≥ 0` with
`t < τ_jump(w; n³)` and `t < τ'(B)`:
`|B ∩ V_{[0,t]}(w)| ≤ K_n · (n³ D_m) · 2^{j d}`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {w : ℝ → Fin d → ℤ}

/-- The windows `U_i` of vertices visited during `[s_i, s_i + D) ∩ [0, t]`. -/
noncomputable def heavyWindow (w : ℝ → Fin d → ℤ) (j m : ℕ) (D : ℕ) (ι : Fin d → ℤ) (t : ℝ)
    (i : ℕ) : Set (Fin d → ℤ) :=
  open scoped Classical in
  if heavyEntSeq w j m (D : ℝ≥0∞) ι i ≤ ENNReal.ofReal t then
    w '' Icc (heavyEntSeq w j m (D : ℝ≥0∞) ι i).toReal
      (min ((heavyEntSeq w j m (D : ℝ≥0∞) ι i).toReal + D) t)
  else ∅

theorem heavyWindow_bound (hw : IsCyclicPath w) {n j m D : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D)
    (ι : Fin d → ℤ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : ENNReal.ofReal t < pathTjump w ((n : ℝ) ^ 3)) (i : ℕ) :
    (heavyWindow w j m D ι t i).Finite ∧ (heavyWindow w j m D ι t i).ncard ≤ n ^ 3 * D := by
  unfold heavyWindow
  split_ifs with hc
  · set a := (heavyEntSeq w j m (D : ℝ≥0∞) ι i).toReal with ha
    set b := min (a + D) t with hb
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have hat : a ≤ t := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
      rwa [ENNReal.toReal_ofReal ht0] at this
    have hab : a ≤ b := le_min (by linarith [show (0 : ℝ) ≤ D by positivity]) hat
    obtain ⟨hfin, hcard⟩ := hw.ncard_image_Icc_le ha0 hab
    refine ⟨hfin, hcard.trans ?_⟩
    have hN : 1 ≤ n ^ 3 * D := Nat.mul_pos (by positivity) hD
    rcases eq_or_lt_of_le hab with hEq | hlt
    · have : cycJumpCount w a b = 0 := by
        unfold cycJumpCount; rw [← hEq]; simp
      omega
    · have hbt : ENNReal.ofReal b < pathTjump w ((n : ℝ) ^ 3) :=
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (min_le_right _ _)) ht1
      have hL : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
      have hJ := jumpCount_lt_of_lt_pathTjump hw hL ha0 hlt hbt
      have hceil : ⌈b - a⌉₊ ≤ D := Nat.ceil_le.2 (by
        have := min_le_left (a + D) t
        simp only [hb]; linarith)
      have h2 : (cycJumpCount w a b : ℝ) < ((n ^ 3 * D : ℕ) : ℝ) := by
        calc (cycJumpCount w a b : ℝ) < (n : ℝ) ^ 3 * ⌈b - a⌉₊ := hJ
          _ ≤ (n : ℝ) ^ 3 * D := by gcongr
          _ = ((n ^ 3 * D : ℕ) : ℝ) := by push_cast; ring
      have h3 : cycJumpCount w a b < n ^ 3 * D := by exact_mod_cast h2
      omega
  · simp

/-- ES22 Lemma 6.4, Step 1. -/
theorem heavy_block_count (hw : IsCyclicPath w) {n m K j D : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D)
    (hjm : j ≤ m) (ι : Fin d → ℤ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : ENNReal.ofReal t < pathTjump w ((n : ℝ) ^ 3))
    (ht2 : ENNReal.ofReal t < heavyEntSeq w j m (D : ℝ≥0∞) ι K) :
    (heavyBlock m ι ∩ visitedSet w 0 t).Finite ∧
      (heavyBlock m ι ∩ visitedSet w 0 t).ncard ≤ K * (n ^ 3 * D) * (2 ^ j) ^ d := by
  classical
  set U := heavyWindow w j m D ι t with hU
  have hUb := heavyWindow_bound (j := j) (m := m) hw hn hD ι ht0 ht1
  set F : ℕ → Finset (Fin d → ℤ) := fun i => ((hUb i).1.toFinset).image (heavyBlockIdx j) with hF
  have hFcard : ∀ i, (F i).card ≤ n ^ 3 * D := fun i => by
    calc (F i).card ≤ (hUb i).1.toFinset.card := Finset.card_image_le
      _ = (U i).ncard := (Set.ncard_eq_toFinset_card _ (hUb i).1).symm
      _ ≤ n ^ 3 * D := (hUb i).2
  have hsub : heavyBlock m ι ∩ visitedSet w 0 t ⊆
      ⋃ i ∈ Finset.range K, ⋃ ι' ∈ F i, heavyBlock j ι' := by
    rintro v ⟨hvB, s, hs, rfl⟩
    obtain ⟨s'', h0, hle, ⟨i, hiK, hi1, hi2⟩, hmem⟩ :=
      heavy_entrance_conseq hw hjm hs.1 hs.2 ht2 hvB
    have hsi : heavyEntSeq w j m (D : ℝ≥0∞) ι i ≤ ENNReal.ofReal t :=
      hi1.trans (ENNReal.ofReal_le_ofReal (hle.trans hs.2))
    have hsi_top : heavyEntSeq w j m (D : ℝ≥0∞) ι i ≠ ⊤ := ne_top_of_le_ne_top
      ENNReal.ofReal_ne_top hsi
    have hid : heavyBlockIdx j (w s'') = heavyBlockIdx j (w s) :=
      heavyBlock_eq_of_mem (mem_heavyBlock_idx j (w s'')) hmem
    have hwin : w s'' ∈ U i := by
      simp only [hU, heavyWindow, ite_eq_left hsi]
      refine ⟨s'', ⟨ENNReal.toReal_le_of_le_ofReal h0 hi1, le_min ?_ (hle.trans hs.2)⟩, rfl⟩
      have h1 : ENNReal.ofReal s'' <
          ENNReal.ofReal ((heavyEntSeq w j m (D : ℝ≥0∞) ι i).toReal + D) := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal hsi_top,
          ENNReal.ofReal_natCast]
        exact hi2
      exact ((ENNReal.ofReal_lt_ofReal_iff' ).1 h1).1.le
    refine mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hiK, mem_iUnion₂.2 ⟨heavyBlockIdx j (w s''), ?_,
      ?_⟩⟩
    · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨w s'', (hUb i).1.mem_toFinset.2 hwin, rfl⟩)
    · rw [hid]; exact mem_heavyBlock_idx j (w s)
  have hfinU : (⋃ i ∈ Finset.range K, ⋃ ι' ∈ F i, heavyBlock j ι').Finite :=
    (Finset.range K).finite_toSet.biUnion fun i _ =>
      (F i).finite_toSet.biUnion fun ι' _ => (ncard_heavyBlock_le j ι').1
  refine ⟨hfinU.subset hsub, ?_⟩
  calc (heavyBlock m ι ∩ visitedSet w 0 t).ncard
      ≤ (⋃ i ∈ Finset.range K, ⋃ ι' ∈ F i, heavyBlock j ι').ncard :=
        Set.ncard_le_ncard hsub hfinU
    _ ≤ ∑ i ∈ Finset.range K, (⋃ ι' ∈ F i, heavyBlock j ι').ncard :=
        Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ i ∈ Finset.range K, (n ^ 3 * D) * (2 ^ j) ^ d := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc (⋃ ι' ∈ F i, heavyBlock j ι').ncard ≤ ∑ ι' ∈ F i, (heavyBlock j ι').ncard :=
              Finset.set_ncard_biUnion_le _ _
          _ ≤ ∑ ι' ∈ F i, (2 ^ j) ^ d := Finset.sum_le_sum fun ι' _ => (ncard_heavyBlock_le j ι').2
          _ = (F i).card * (2 ^ j) ^ d := by simp
          _ ≤ (n ^ 3 * D) * (2 ^ j) ^ d := Nat.mul_le_mul_right _ (hFcard i)
    _ = K * (n ^ 3 * D) * (2 ^ j) ^ d := by simp [Finset.sum_const, mul_assoc]

end ElboimSly.Paper
