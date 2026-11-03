/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasEnd
public import ElboimSly.Paper.Heavy.Agree
public import ElboimSly.Paper.Escape.Blocks

/-!
# Lemma 6.2, Step 1: an escape forces a long gap

ES22 Lemma 6.2, Step 1 (F39).

* `entrance_attained`: a finite entrance time is `ofReal a` for a time `a` with `w a ∈ A`.
* `heavyEntSeq_attained`: a finite `s_i(B)` is `ofReal a` with `w a ∈ B`.
* `heavy_gap_of_escape`: if `s_i < ∞` and the escape event `ℰ(s_i)` holds, then
  `s_{i+1} ≥ s_i + 4^n`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {w : ℝ → Fin d → ℤ} {j m : ℕ} {D : ℝ≥0∞} {ι : Fin d → ℤ}

theorem entrance_attained (hw : IsCyclicPath w) {A : Set (Fin d → ℤ)}
    (h : entranceTime w A < ⊤) :
    ∃ a : ℝ, 0 ≤ a ∧ entranceTime w A = ENNReal.ofReal a ∧ w a ∈ A := by
  have hne : ∃ s : ℝ, 0 ≤ s ∧ w s ∈ A := by
    by_contra hno
    push Not at hno
    rw [entranceTime_eq_top_of_empty hno] at h
    exact absurd h (by simp)
  obtain ⟨s, hs0, hsA⟩ := hne
  obtain ⟨s'', h0, -, hmem, heq⟩ := exists_entrance_real hw hs0 hsA
  exact ⟨s'', h0, heq, hmem⟩

theorem heavyEntSeq_attained (hw : IsCyclicPath w) (hjm : j ≤ m) (i : ℕ)
    (h : heavyEntSeq w j m D ι i < ⊤) :
    ∃ a : ℝ, 0 ≤ a ∧ heavyEntSeq w j m D ι i = ENNReal.ofReal a ∧ w a ∈ heavyBlock m ι := by
  obtain ⟨ι', hι', he⟩ := heavyEntSeq_eq_entrance (D := D) (ι := ι) hw hjm i h
  rw [he] at h
  obtain ⟨a, ha0, hea, haB⟩ := entrance_attained hw h
  exact ⟨a, ha0, he.trans hea, hι' haB⟩

theorem heavyEntrances_attained (hw : IsCyclicPath w) {x : ℝ≥0∞}
    (hx : x ∈ heavyEntrances w j m ι) (hxt : x < ⊤) :
    ∃ a : ℝ, 0 ≤ a ∧ x = ENNReal.ofReal a ∧ w a ∈ heavyBlock m ι := by
  obtain ⟨ι', hι', rfl⟩ := hx
  obtain ⟨a, ha0, hea, haB⟩ := entrance_attained hw hxt
  exact ⟨a, ha0, hea, hι' haB⟩

/-- `‖x - y‖ < 2^m` for two vertices of one block of `ℬ_m`. -/
theorem norm_sub_lt_of_mem_heavyBlock {x y : Fin d → ℤ} (hx : x ∈ heavyBlock m ι)
    (hy : y ∈ heavyBlock m ι) : ‖x - y‖ < (2 : ℝ) ^ m := by
  rw [pi_norm_lt_iff (by positivity)]
  intro c
  have := abs_sub_lt_of_mem_heavyBlock hx hy c
  simp only [Pi.sub_apply, Int.norm_eq_abs]
  have h2 : ((|x c - y c| : ℤ) : ℝ) < ((2 ^ m : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at h2
  simpa using h2

/-- ES22 Lemma 6.2, Step 1. On `{s_i < ∞} ∩ ℰ(s_i)`, `s_{i+1} ≥ s_i + 4^n`. -/
theorem heavy_gap_of_escape {n : ℕ} (hn : 1 ≤ n) (hw : IsCyclicPath w) (hjm : heavyScaleJ n ≤ m)
    (i : ℕ) (hi : heavySi w n m ι i < ⊤)
    (hesc : EscEvent n (heavyScaleJ n) w (heavySi w n m ι i).toReal) :
    heavySi w n m ι i + ENNReal.ofReal ((4 : ℝ) ^ n) ≤ heavySi w n m ι (i + 1) := by
  obtain ⟨a, ha0, hia, haB⟩ := heavyEntSeq_attained (D := (heavyD n m : ℝ≥0∞)) hw hjm i hi
  change heavyEntSeq w (heavyScaleJ n) m (heavyD n m : ℝ≥0∞) ι i + ENNReal.ofReal ((4 : ℝ) ^ n) ≤
    heavyEntSeq w (heavyScaleJ n) m (heavyD n m : ℝ≥0∞) ι (i + 1)
  change heavyEntSeq w (heavyScaleJ n) m (heavyD n m : ℝ≥0∞) ι i < ⊤ at hi
  show _ ≤ sInf _
  refine le_sInf fun x hx => ?_
  obtain ⟨hxE, hxD⟩ := hx
  rcases eq_or_ne x ⊤ with rfl | hxt
  · exact le_top
  obtain ⟨b, hb0, hxb, hbB⟩ := heavyEntrances_attained hw hxE (lt_top_iff_ne_top.2 hxt)
  rw [hia, hxb] at hxD ⊢
  have hDr : ((heavyD n m : ℕ) : ℝ≥0∞) = ENNReal.ofReal (heavyD n m : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  rw [hDr, ← ENNReal.ofReal_add ha0 (by positivity), ENNReal.ofReal_le_ofReal_iff hb0] at hxD
  rw [← ENNReal.ofReal_add ha0 (by positivity), ENNReal.ofReal_le_ofReal_iff hb0]
  by_contra hlt
  push Not at hlt
  -- the escape condition at `s = b - a`
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD4 : (4 : ℝ) ^ heavyScaleJ n ≤ (heavyD n m : ℝ) := by
    have h1 : (4 : ℝ) ^ heavyScaleJ n ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hjm
    have h2 : (4 : ℝ) ^ m ≤ (n : ℝ) ^ 2 * 4 ^ m := by
      have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn'
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) m]
    unfold heavyD; push_cast; linarith
  have hs1 : (4 : ℝ) ^ heavyScaleJ n ≤ b - a := by linarith
  have hs2 : b - a ≤ (4 : ℝ) ^ n := by linarith
  have key := hesc (b - a) hs1 hs2
  have ha : (heavySi w n m ι i).toReal = a := by
    change (heavyEntSeq w (heavyScaleJ n) m (heavyD n m : ℝ≥0∞) ι i).toReal = a
    rw [hia, ENNReal.toReal_ofReal ha0]
  rw [ha, show a + (b - a) = b by ring] at key
  have hnorm : ‖w b - w a‖ < (2 : ℝ) ^ m := norm_sub_lt_of_mem_heavyBlock hbB haB
  have hsq : (2 : ℝ) ^ m ≤ Real.sqrt (b - a) / n := by
    rw [le_div_iff₀ (by linarith)]
    have : (2 : ℝ) ^ m * n = Real.sqrt ((heavyD n m : ℝ)) := by
      rw [show (heavyD n m : ℝ) = ((2 : ℝ) ^ m * n) ^ 2 by
        unfold heavyD; push_cast; rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul]; norm_num; ring]
      rw [Real.sqrt_sq (by positivity)]
    rw [this]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith

end ElboimSly.Paper.Heavy
