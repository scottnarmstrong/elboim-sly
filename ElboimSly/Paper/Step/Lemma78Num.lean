/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.ScalesFactsB
public import ElboimSly.Paper.Heavy.Thresholds
public import ElboimSly.Frozen.Defs.IndScaleReduced
public import Mathlib

/-!
# The "for `n` large" numerics of Lemma 7.8 (asymptotic part)

ES22 Lemma 7.8; Short gaps ("for `n` large"), bookkeeping of n_0; closing crefprop:ind-step (c). There is `N`
(depending only on `d`) such that for all `n ≥ N`, `t₀ ∈ (1, 4]` and `β < t_n` (with `k ≥ 16`):
* `t'_k + 3 ≤ t'_n`;
* `2 t'_k + 4 + t_n^{ε/3} < t_n^ε`;
* `β < t_n^{5δ}` implies `(9^d + 1) 2^{kd} (2n) β ≤ t_n^{ε/3}`;
* `n³ (t_n^ε + 3.89^n) < 3.9^n`.
-/

@[expose] public section

open Filter

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

/-- The asymptotic numerics. -/
structure Step78Asym (d : ℕ) (t₀ : ℝ) (n : ℕ) (β : ℝ) : Prop where
  tk_le : heavyTkPrime d t₀ n + 3 ≤ indScaleReduced t₀ n
  L2 : 2 * heavyTkPrime d t₀ n + 4 + indScale t₀ n ^ (heavyEps d / 3) <
    indScale t₀ n ^ heavyEps d
  occ : β < indScale t₀ n ^ (5 * indDelta d) →
    (((9 ^ d + 1) * (2 ^ heavyLevel d n) ^ d * (2 * n) : ℕ) : ℝ) * β ≤
      indScale t₀ n ^ (heavyEps d / 3)
  pn : (n : ℝ) ^ 3 * (indScale t₀ n ^ heavyEps d + (389 / 100 : ℝ) ^ n) < (39 / 10 : ℝ) ^ n

theorem eventually_mul_pow_le (C : ℝ) (m : ℕ) {b : ℝ} (hb : 1 < b) :
    ∃ N : ℕ, ∀ n ≥ N, C * (n : ℝ) ^ m ≤ b ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt m hb
  have hC : 0 < |C| + 1 := by positivity
  have := h.eventually (gt_mem_nhds (show (0 : ℝ) < (|C| + 1)⁻¹ by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 this
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have hbn : 0 < b ^ n := by positivity
  rw [div_lt_iff₀ hbn] at h1
  have h2 : (|C| + 1) * (n : ℝ) ^ m < b ^ n := by
    rw [inv_mul_eq_div, lt_div_iff₀ hC] at h1
    linarith
  have h3 : C * (n : ℝ) ^ m ≤ (|C| + 1) * (n : ℝ) ^ m :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (by positivity)
  linarith

theorem pow4_rpow (m : ℕ) (c : ℝ) : ((4 : ℝ) ^ m) ^ c = (4 : ℝ) ^ ((m : ℝ) * c) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

theorem rpow4_nat (c : ℝ) (n : ℕ) : (4 : ℝ) ^ (c * n) = ((4 : ℝ) ^ c) ^ n := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]

theorem rpow4_pos_lt (c : ℝ) (hc : 0 < c) : 1 < (4 : ℝ) ^ c :=
  Real.one_lt_rpow (by norm_num) hc

theorem eventually_rpow4 (C : ℝ) (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ n ≥ N, C * (n : ℝ) ^ m ≤ (4 : ℝ) ^ (c * n) := by
  obtain ⟨N, hN⟩ := eventually_mul_pow_le C m (rpow4_pos_lt c hc)
  exact ⟨N, fun n hn => by rw [rpow4_nat]; exact hN n hn⟩

section arith

variable {d : ℕ}

theorem eps_pos (hd : 5 ≤ d) : 0 < heavyEps d := by
  unfold heavyEps
  have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  positivity

theorem eps_le (hd : 5 ≤ d) : heavyEps d ≤ 1 / 1500 := by
  unfold heavyEps
  have : (5 : ℝ) ≤ d := by exact_mod_cast hd
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem delta_eps (hd : 5 ≤ d) : 4 * indDelta d ≤ heavyEps d / 3 := by
  unfold indDelta heavyEps
  have : (5 : ℝ) ≤ d := by exact_mod_cast hd
  rw [show 4 * (1 / (3000 * (d : ℝ) ^ 2)) = 4 / (3000 * (d : ℝ) ^ 2) by ring,
    show 1 / (300 * (d : ℝ)) / 3 = 1 / (900 * (d : ℝ)) by field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem delta_eps2 (hd : 5 ≤ d) :
    indDelta d * (2 * d + 5) ≤ 3 * heavyEps d / 10 := by
  unfold indDelta heavyEps
  have : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  rw [show 1 / (3000 * (d : ℝ) ^ 2) * (2 * d + 5) = (2 * d + 5) / (3000 * (d : ℝ) ^ 2) by ring,
    show 3 * (1 / (300 * (d : ℝ))) / 10 = 3 / (3000 * (d : ℝ)) by field_simp; norm_num]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem level_le (hd : 5 ≤ d) (n : ℕ) : (heavyLevel d n : ℝ) ≤ heavyEps d / 3 * n := by
  have h1 := heavyLevel_le (d := d) (by omega) n
  have h2 := delta_eps hd
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end arith

end ElboimSly.Paper.Step

end
