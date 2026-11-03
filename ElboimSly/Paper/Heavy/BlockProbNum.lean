/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.ThrFinite
public import ElboimSly.Paper.Heavy.Es6FourMain
public import ElboimSly.Paper.Heavy.Cor610Main
public import ElboimSly.Paper.Escape.Blocks
public import ElboimSly.Paper.Heavy.ScalesFactsB
public import ElboimSly.Paper.Avoid.Hyp
public import Mathlib

/-!
# Numerical facts for probability that a block is bad

* `gb2_numeric`: the Gaussian tail `exp(-(l/σ)²/(2t'_k))` with `l = 2^{k-2}`, `σ ≤ 2`,
  `t'_k ≤ 4^{k+1}/k⁴` is at most `e^{-k⁴/3200}`.
* `heavyT0pp_spec`: `t₀'' ∈ (1, 4]` and `t_{k'}(t₀'') = t'_k`.
-/

@[expose] public section

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

theorem gb2_numeric {k : ℕ} (hk : 16 ≤ k) {tk σ : ℝ} (htk : 0 < tk)
    (htk4 : tk ≤ (4 : ℝ) ^ (k + 1) / (k : ℝ) ^ 4) (hσ : 0 < σ) (hσ2 : σ ≤ 2) :
    Real.exp (-((2 : ℝ) ^ (k - 2) / σ) ^ 2 / (2 * tk)) ≤ Real.exp (-((k : ℝ) ^ 4 / 3200)) := by
  apply Real.exp_le_exp.2
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  set l : ℝ := 2 ^ j with hl
  have hl0 : 0 < l := by positivity
  have hk0 : (0 : ℝ) < ((j + 2 : ℕ) : ℝ) ^ 4 := by positivity
  have h4 : (4 : ℝ) ^ (j + 2 + 1) = 64 * l ^ 2 := by
    rw [hl, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    rw [show 2 * (j + 2 + 1) = 6 + 2 * j by ring, pow_add]
    norm_num; ring
  rw [h4, le_div_iff₀ hk0] at htk4
  have hq : l / 2 ≤ l / σ := div_le_div_of_nonneg_left hl0.le hσ hσ2
  have hq2 : (l / 2) ^ 2 ≤ (l / σ) ^ 2 := pow_le_pow_left₀ (by positivity) hq 2
  rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [hq2, htk4, mul_pos htk hl0]

theorem heavyT0pp_spec {d : ℕ} {t₀ : ℝ} {n : ℕ} (h1 : 1 < heavyTkPrime d t₀ n) :
    1 < heavyT0pp d t₀ n ∧ heavyT0pp d t₀ n ≤ 4 ∧
      indScale (heavyT0pp d t₀ n) (heavyLevelPrime d t₀ n) = heavyTkPrime d t₀ n := by
  have hsp := avoidLevel_spec h1
  have e : avoidLevel (heavyTkPrime d t₀ n) = heavyLevelPrime d t₀ n := rfl
  rw [e] at hsp
  obtain ⟨hlo, hhi⟩ := hsp
  have hpos : (0 : ℝ) < 4 ^ heavyLevelPrime d t₀ n := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold heavyT0pp; rw [lt_div_iff₀ hpos]; linarith
  · unfold heavyT0pp; rw [div_le_iff₀ hpos]; rw [pow_succ] at hhi; linarith
  · unfold indScale heavyT0pp; field_simp

theorem indFailBound_nonneg (β t₀ : ℝ) (m : ℕ) : 0 ≤ indFailBound β t₀ m := by
  unfold indFailBound; split_ifs <;> exact (Real.exp_pos _).le

theorem indFailBound_le_one (β t₀ : ℝ) (m : ℕ) : indFailBound β t₀ m ≤ 1 := by
  unfold indFailBound
  split_ifs <;> exact Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))

end ElboimSly.Paper.Heavy
