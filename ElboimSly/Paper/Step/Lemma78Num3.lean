/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Num2
public import ElboimSly.Paper.Heavy.ScalesFactsB
public import Mathlib

/-!
# The numerics of ES22 Lemma 6.8 from `HeavyT`

ES22 Lemma 6.8 ("for `n` large", bookkeeping of n_0; closing crefprop:ind-step (c)): with `ρ = 1.9^k / 2`,
* `2^{k-1} + 3n³ + 1 + ρ ≤ 2^k` (from (T1), (T6));
* `ρ + n^{41} ≤ 1.9^k` (from (T5), (T6));
* `2^d L_cov 3.9^k + 1 < (0.9 + 4/n) t'_k` (from (T9) and `7 n ≥ 3000 d² 2^d`).
-/

@[expose] public section

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {t₀ : ℝ}

theorem far_N2 (hT : HeavyT d n₀ E n) :
    (2 : ℝ) ^ (heavyLevel d n - 1) + 3 * (n : ℝ) ^ 3 + 1 + (1.9 : ℝ) ^ heavyLevel d n / 2 ≤
      2 ^ heavyLevel d n := by
  have hk := hT.t1.2
  have h20 := hT.t6.2.1
  set k := heavyLevel d n with hkdef
  have hP : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hP16 : (65536 : ℝ) ≤ 2 ^ k := by
    calc (65536 : ℝ) = 2 ^ 16 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have h19 : (1.9 : ℝ) ^ k ≤ 0.45 * 2 ^ k := by
    have e : (1.9 : ℝ) ^ k = 2 ^ k * (0.95 : ℝ) ^ k := by
      rw [← mul_pow]; norm_num
    have h95 : (0.95 : ℝ) ^ k ≤ (0.95 : ℝ) ^ 16 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    have : (0.95 : ℝ) ^ 16 ≤ 0.45 := by norm_num
    rw [e]
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) k]
  nlinarith

theorem far_N3 (hd : 5 ≤ d) (hT : HeavyT d n₀ E n) :
    (1.9 : ℝ) ^ heavyLevel d n / 2 + (n : ℝ) ^ 41 ≤ (1.9 : ℝ) ^ heavyLevel d n := by
  have hn4 := hT.t4
  have hδ : 0 < indDelta d := heavy_indDelta_pos (by omega)
  have h5 := hT.t5
  have h64 := hT.t6.2.2.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hγ : (41 : ℝ) ≤ escGamma d + 8 + 20 * d := by
    have : (3 : ℝ) ≤ escGamma d := le_max_left _ _
    have : (5 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h41 : (n : ℝ) ^ 41 ≤ (n : ℝ) ^ (escGamma d + 8 + 20 * d) := by
    have := Real.rpow_le_rpow_of_exponent_le hn1 hγ
    simpa using this
  have h2 : (n : ℝ) ^ 41 ≤ (2 : ℝ) ^ (2 * indDelta d * (n + 1)) := by
    have h144 : (1 : ℝ) ≤ 144 * 4 ^ d := by
      have : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
      linarith
    have h3 : (n : ℝ) ^ (escGamma d + 8 + 20 * d) ≤ 144 * 4 ^ d * (n : ℝ) ^ (escGamma d + 8 + 20 * d) := by
      have : 0 ≤ (n : ℝ) ^ (escGamma d + 8 + 20 * d) := by positivity
      nlinarith
    have h4 : (2 : ℝ) ^ (indDelta d * n) ≤ (2 : ℝ) ^ (2 * indDelta d * (n + 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    exact h41.trans (h3.trans (h5.le.trans h4))
  have h1 : (1.9 : ℝ) ^ (4 * indDelta d * n - 1) ≤ (1.9 : ℝ) ^ heavyLevel d n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := lt_heavyLevel_add_one d n; linarith)
  linarith

theorem far_num (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n)
    (hn : 3000 * (d : ℝ) ^ 2 * 2 ^ d ≤ 7 * n) :
    2 ^ d * heavyL d n * (3.9 : ℝ) ^ heavyLevel d n + 1 <
      (9 / 10 + 4 / (n : ℝ)) * heavyTkPrime d t₀ n := by
  have hk := hT.t1.2
  have hδ : 0 < indDelta d := heavy_indDelta_pos (by omega)
  have hn0 : (0 : ℝ) < n := by have := hT.t4; exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < (heavyLevel d n : ℝ) ^ 4 := by
    have : (0 : ℝ) < heavyLevel d n := by exact_mod_cast (by omega : 0 < heavyLevel d n)
    positivity
  have h9 := hT.t9
  obtain ⟨-, hQ, -⟩ := scales_facts_c (d := d) (n := n) ht1 ht4 hk
  set Q : ℝ := (4 : ℝ) ^ heavyLevel d n / (heavyLevel d n : ℝ) ^ 4 with hQdef
  have hQ0 : 0 < Q := by positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hδn : (2 : ℝ) ^ d ≤ 7.2 * (indDelta d * n) := by
    unfold indDelta
    rw [show 7.2 * (1 / (3000 * (d : ℝ) ^ 2) * n) = 7.2 * n / (3000 * (d : ℝ) ^ 2) by ring,
      le_div_iff₀ (by positivity)]
    nlinarith
  have hL : heavyL d n * (3.9 : ℝ) ^ heavyLevel d n ≤ Q / (8 * indDelta d * n) - 2 := by
    have := h9
    rw [show (4 : ℝ) ^ heavyLevel d n / (8 * indDelta d * n * (heavyLevel d n : ℝ) ^ 4) =
      Q / (8 * indDelta d * n) by rw [hQdef]; field_simp] at this
    linarith
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hdn : (2 : ℝ) ^ d * (Q / (8 * indDelta d * n)) ≤ 0.9 * Q := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hδ hn0]
  have hmul : (2 : ℝ) ^ d * (heavyL d n * (3.9 : ℝ) ^ heavyLevel d n) ≤
      (2 : ℝ) ^ d * (Q / (8 * indDelta d * n) - 2) := mul_le_mul_of_nonneg_left hL (by positivity)
  have h4n : 0 ≤ 4 / (n : ℝ) := by positivity
  have htk : Q < heavyTkPrime d t₀ n := hQ
  nlinarith [mul_nonneg h4n (hQ0.trans htk).le, mul_pos (by norm_num : (0 : ℝ) < 0.9) hQ0]

end ElboimSly.Paper.Step

end
