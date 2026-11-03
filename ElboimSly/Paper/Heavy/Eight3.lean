/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Eight2

/-!
# Lemma 6.8: numerical facts from the thresholds

Supporting material for ES22 Lemma 6.8, Steps 4-5.  With `t_n^δ ≤ 2^{2δ(n+1)}` and (T6):

* `eight_num_a`: `t_n^δ + 2 n³ ≤ 2^{k-1}`;
* `eight_num_b`: `t_n^δ + n^41 ≤ 1.9^k`.
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {t₀ : ℝ}

theorem indScale_rpow_le (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hδ : 0 < indDelta d) (n : ℕ) :
    indScale t₀ n ^ indDelta d ≤ (2 : ℝ) ^ (2 * indDelta d * (n + 1)) := by
  have h1 := indScale_le_four_pow ht4 n
  have hpos : 0 ≤ indScale t₀ n :=
    (le_of_lt (lt_of_le_of_lt (by positivity) (indScale_gt_four_pow ht1 n)))
  calc indScale t₀ n ^ indDelta d ≤ ((4 : ℝ) ^ (n + 1)) ^ indDelta d :=
        Real.rpow_le_rpow hpos h1 hδ.le
    _ = (2 : ℝ) ^ (2 * indDelta d * (n + 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        congr 1; push_cast; ring

theorem eight_num_a (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) :
    indScale t₀ n ^ indDelta d + 2 * (n : ℝ) ^ 3 ≤ (2 : ℝ) ^ (heavyLevel d n - 1) := by
  have hδ := heavy_indDelta_pos (d := d) (by omega)
  obtain ⟨-, h20, h5, -⟩ := hT.t6
  have hk1 : 1 ≤ heavyLevel d n := by have := hT.t1.2; omega
  have h1 := indScale_rpow_le ht1 ht4 hδ n
  have h2k : (2 : ℝ) ^ heavyLevel d n = 2 * 2 ^ (heavyLevel d n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hk2 : (4 * indDelta d * n : ℝ) ≤ (heavyLevel d n : ℝ) + 1 := (lt_heavyLevel_add_one d n).le
  have h3 : (2 : ℝ) ^ (4 * indDelta d * n) ≤ 2 ^ ((heavyLevel d n : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hk2
  have h4 : (2 : ℝ) ^ ((heavyLevel d n : ℝ) + 1) = 2 * 2 ^ heavyLevel d n := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast]; ring
  linarith

theorem eight_num_b (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) :
    indScale t₀ n ^ indDelta d + (n : ℝ) ^ 41 ≤ (1.9 : ℝ) ^ heavyLevel d n := by
  have hδ := heavy_indDelta_pos (d := d) (by omega)
  obtain ⟨-, -, -, h4⟩ := hT.t6
  have h1 := indScale_rpow_le ht1 ht4 hδ n
  have hk : 4 * indDelta d * n - 1 ≤ (heavyLevel d n : ℝ) := by
    have := lt_heavyLevel_add_one d n; linarith
  have h2 : (1.9 : ℝ) ^ (4 * indDelta d * n - 1) ≤ 1.9 ^ (heavyLevel d n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hk
  rw [Real.rpow_natCast] at h2
  linarith

end ElboimSly.Paper
