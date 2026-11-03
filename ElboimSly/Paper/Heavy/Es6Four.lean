/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BlockCount
public import ElboimSly.Paper.Heavy.BallCover
public import ElboimSly.Paper.Heavy.ScalesFactsB
public import ElboimSly.Frozen.Defs.IsHeavy

/-!
# Lemma 6.4: no heavy block of side at least `t_n^δ`

ES22 Lemma 6.4 (§6; deviations D6, F10, F73).

For a cyclic path `w` and `0 ≤ t < τ_jump(w) ∧ τ'(w)` (and the thresholds `HeavyT` at `n`), no block
`B(x, r)` with `r ≥ t_n^δ` is heavy for `w` on `[0, t]`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {t₀ : ℝ} {w : ℝ → Fin d → ℤ}

/-- The numerical heart of Step 2: `2^d · K n³ D_m (2^j)^d < r^{5/2}`. -/
theorem es6_four_numeric (hd : 5 ≤ d) (ht1 : 1 < t₀) (hT : HeavyT d n₀ E n) {r : ℝ}
    (hr : indScale t₀ n ^ indDelta d ≤ r) {m : ℕ} (hm1 : 2 * r + 1 ≤ (2 : ℝ) ^ m)
    (hm2 : (2 : ℝ) ^ m < 2 * (2 * r + 1)) :
    ((2 ^ d * (heavyTrials d n * (n ^ 3 * heavyD n m) * (2 ^ heavyScaleJ n) ^ d) : ℕ) : ℝ) <
      r ^ (5 / 2 : ℝ) := by
  have hn4 : 4 ≤ n := hT.t4
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hδ := heavy_indDelta_pos (d := d) (by omega)
  -- r ≥ 1
  have htn : (4 : ℝ) ^ n ≤ indScale t₀ n := (indScale_gt_four_pow ht1 n).le
  have hr1 : 1 ≤ r := by
    refine le_trans ?_ hr
    exact Real.one_le_rpow (le_trans (one_le_pow₀ (by norm_num)) htn) hδ.le
  -- 4^m < 36 r^2
  have h4m : (4 : ℝ) ^ m < 36 * r ^ 2 := by
    have h2m : (4 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h2m]
    have : (2 : ℝ) ^ m < 6 * r + 2 := by linarith
    have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ m := by positivity
    nlinarith
  -- K ≤ 2 n^(γ+3)
  set γ := escGamma d with hγ
  have h3γ : 3 ≤ γ := le_max_left _ _
  have hnγ : (1 : ℝ) ≤ (n : ℝ) ^ (γ + 3) := Real.one_le_rpow hn1 (by linarith)
  have hK : (heavyTrials d n : ℝ) ≤ 2 * (n : ℝ) ^ (γ + 3) := by
    have := (Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ (γ + 3) by positivity)).le
    unfold heavyTrials
    linarith
  have hj : ((2 : ℝ) ^ heavyScaleJ n) ≤ 2 * (n : ℝ) ^ 20 := by
    have := (heavyScaleJ_spec (by omega : 2 ≤ n)).2
    exact_mod_cast this.le
  -- T5
  have hT5 := hT.t5
  -- r^(1/2) ≥ 2^(δ n)
  have hhalf : (2 : ℝ) ^ (indDelta d * n) ≤ r ^ (1 / 2 : ℝ) := by
    have h1 : (2 : ℝ) ^ (2 * (indDelta d * n)) = ((4 : ℝ) ^ n) ^ indDelta d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      congr 1; ring
    have h2 : ((4 : ℝ) ^ n) ^ indDelta d ≤ r :=
      le_trans (Real.rpow_le_rpow (by positivity) htn hδ.le) hr
    have h3 : (2 : ℝ) ^ (indDelta d * n) = ((2 : ℝ) ^ (2 * (indDelta d * n))) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
    rw [h3, h1]
    exact Real.rpow_le_rpow (by positivity) h2 (by norm_num)
  -- assemble
  have hr0 : (0 : ℝ) < r := by linarith
  have hr52 : r ^ (5 / 2 : ℝ) = r ^ 2 * r ^ (1 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hr0]
    norm_cast
  have hnpow : (n : ℝ) ^ (γ + 3) * (n : ℝ) ^ 5 * (n : ℝ) ^ (20 * d) =
      (n : ℝ) ^ (γ + 8 + 20 * d) := by
    rw [← Real.rpow_natCast (n : ℝ) 5, ← Real.rpow_natCast (n : ℝ) (20 * d),
      ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1; push_cast; ring
  push_cast
  have hD : ((heavyD n m : ℕ) : ℝ) = (n : ℝ) ^ 2 * 4 ^ m := by unfold heavyD; push_cast; ring
  rw [hD]
  have hjd : ((2 : ℝ) ^ heavyScaleJ n) ^ d ≤ (2 * (n : ℝ) ^ 20) ^ d :=
    pow_le_pow_left₀ (by positivity) hj d
  have hjd' : (2 * (n : ℝ) ^ 20) ^ d = 2 ^ d * (n : ℝ) ^ (20 * d) := by
    rw [mul_pow, ← pow_mul]
  have hA : (2 : ℝ) ^ d * ((heavyTrials d n : ℝ) * ((n : ℝ) ^ 3 * ((n : ℝ) ^ 2 * 4 ^ m)) *
      ((2 : ℝ) ^ heavyScaleJ n) ^ d) ≤
      2 ^ d * (2 * (n : ℝ) ^ (γ + 3) * ((n : ℝ) ^ 3 * ((n : ℝ) ^ 2 * 4 ^ m)) *
        (2 ^ d * (n : ℝ) ^ (20 * d))) := by
    rw [← hjd']
    gcongr
  have hB : (2 : ℝ) ^ d * (2 * (n : ℝ) ^ (γ + 3) * ((n : ℝ) ^ 3 * ((n : ℝ) ^ 2 * 4 ^ m)) *
        (2 ^ d * (n : ℝ) ^ (20 * d))) =
      (2 * 4 ^ d) * (n : ℝ) ^ (γ + 8 + 20 * d) * 4 ^ m := by
    rw [← hnpow]
    have : (4 : ℝ) ^ d = 2 ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
    rw [this]; ring
  have hC : (2 * 4 ^ d) * (n : ℝ) ^ (γ + 8 + 20 * d) * 4 ^ m <
      (2 * 4 ^ d) * (n : ℝ) ^ (γ + 8 + 20 * d) * (36 * r ^ 2) := by
    gcongr
  have hE : (2 * 4 ^ d) * (n : ℝ) ^ (γ + 8 + 20 * d) * (36 * r ^ 2) =
      (72 * 4 ^ d * (n : ℝ) ^ (γ + 8 + 20 * d)) * r ^ 2 := by ring
  have hF : (72 * 4 ^ d * (n : ℝ) ^ (γ + 8 + 20 * d)) * r ^ 2 <
      r ^ (1 / 2 : ℝ) * r ^ 2 := by
    have h5 : 72 * 4 ^ d * (n : ℝ) ^ (γ + 8 + 20 * d) < r ^ (1 / 2 : ℝ) := by
      have : (72 : ℝ) * 4 ^ d * (n : ℝ) ^ (γ + 8 + 20 * d) <
          144 * 4 ^ d * (n : ℝ) ^ (γ + 8 + 20 * d) := by
        have : (0 : ℝ) < 4 ^ d * (n : ℝ) ^ (γ + 8 + 20 * d) := by positivity
        nlinarith
      exact this.trans (hT5.trans_le hhalf)
    exact mul_lt_mul_of_pos_right h5 (by positivity)
  calc _ ≤ _ := hA
    _ = _ := hB
    _ < _ := hC
    _ = _ := hE
    _ < _ := hF
    _ = r ^ (5 / 2 : ℝ) := by rw [hr52]; ring

end ElboimSly.Paper
