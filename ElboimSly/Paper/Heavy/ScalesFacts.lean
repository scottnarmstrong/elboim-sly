/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.ScalesBasic

/-!
# Elementary facts about the scales: parts (a) and (c)

Elementary facts about the scales (a), (c) (supplement).  The remaining parts are in
`ScalesFactsB`.  Hypotheses: `d ≥ 5`, `n₀ ≥ 8d`, `t₀ ∈ (1, 4]` and the thresholds `HeavyT` at `n`.
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly

theorem logb_four_eq (x : ℝ) : Real.logb 4 x = Real.logb 2 x / 2 := by
  unfold Real.logb
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [this]; field_simp

theorem logb_four_tkPrime {d n : ℕ} {t₀ : ℝ} (ht0 : 0 < t₀) (hk : 1 ≤ heavyLevel d n) :
    Real.logb 4 (heavyTkPrime d t₀ n) =
      heavyLevel d n + Real.logb 4 t₀ - 2 * Real.logb 2 (heavyLevel d n) := by
  have hk0 : (0 : ℝ) < heavyLevel d n := by exact_mod_cast hk
  unfold heavyTkPrime indScale
  rw [Real.logb_div (by positivity) (by positivity), Real.logb_mul (by positivity) ht0.ne',
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num),
    logb_four_eq (heavyLevel d n : ℝ)]
  push_cast
  ring

theorem logb_four_pos_le {t₀ : ℝ} (h1 : 1 < t₀) (h4 : t₀ ≤ 4) :
    0 < Real.logb 4 t₀ ∧ Real.logb 4 t₀ ≤ 1 := by
  refine ⟨Real.logb_pos (by norm_num) h1, ?_⟩
  calc Real.logb 4 t₀ ≤ Real.logb 4 4 := Real.logb_le_logb_of_le (by norm_num) (by linarith) h4
    _ = 1 := Real.logb_self_eq_one (by norm_num)

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {t₀ : ℝ}

/-- `k' + 1 = ⌈log₄ t'_k⌉` and the two-sided bound on `log₄ t'_k`. -/
theorem heavyLevelPrime_bounds (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hk : 16 ≤ heavyLevel d n) :
    (heavyKappa d n : ℝ) ≤ heavyLevelPrime d t₀ n ∧ heavyLevelPrime d t₀ n + 8 ≤ heavyLevel d n := by
  have hk1 : 1 ≤ heavyLevel d n := by omega
  have hid := logb_four_tkPrime (d := d) (n := n) (by linarith) hk1
  obtain ⟨hl0, hl1⟩ := logb_four_pos_le ht1 ht4
  have hL4 := four_le_logb_two hk
  have hLh := logb_two_lt_half hk
  have hk16 : (16 : ℝ) ≤ heavyLevel d n := by exact_mod_cast hk
  set x := Real.logb 4 (heavyTkPrime d t₀ n) with hx
  have hxpos : 0 < x := by rw [hid]; linarith
  have hceil_pos : 0 < ⌈x⌉₊ := Nat.ceil_pos.2 hxpos
  constructor
  · have h1 : x ≤ ⌈x⌉₊ := Nat.le_ceil x
    have h2 : (heavyLevelPrime d t₀ n : ℝ) = ⌈x⌉₊ - 1 := by
      unfold heavyLevelPrime
      rw [← hx, Nat.cast_sub (by omega)]; simp
    rw [h2]; unfold heavyKappa; linarith [h1, hid]
  · have h2 : ⌈x⌉₊ ≤ heavyLevel d n - 7 := by
      rw [Nat.ceil_le]
      have : ((heavyLevel d n - 7 : ℕ) : ℝ) = (heavyLevel d n : ℝ) - 7 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [this, hid]; linarith
    unfold heavyLevelPrime
    rw [← hx]; omega

/-- Elementary facts about the scales (a). -/
theorem scales_facts_a (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hT : HeavyT d n₀ E n) :
    (heavyKappa d n ≤ heavyLevelPrime d t₀ n ∧ heavyLevelPrime d t₀ n ≤ heavyLevel d n - 2) ∧
      (n₀ ≤ heavyLevelPrime d t₀ n ∧ heavyLevelPrime d t₀ n < heavyLevel d n ∧
        heavyLevel d n + 1 < n) ∧ 10 ≤ heavyLevelPrime d t₀ n := by
  have hk := hT.t1.2
  obtain ⟨hb1, hb2⟩ := heavyLevelPrime_bounds (d := d) (n := n) ht1 ht4 hk
  have hn0' : 40 ≤ n₀ := by omega
  have hkp : n₀ ≤ heavyLevelPrime d t₀ n := by
    have : (n₀ : ℝ) ≤ heavyLevelPrime d t₀ n := hT.t1.1.trans hb1
    exact_mod_cast this
  refine ⟨⟨hb1, by omega⟩, ⟨hkp, by omega, ?_⟩, by omega⟩
  have h4 : (4 : ℝ) ≤ n := by exact_mod_cast hT.t4
  have hle := heavyLevel_le (d := d) (by omega) n
  have hd4 := four_indDelta_le hd
  have : ((heavyLevel d n + 1 : ℕ) : ℝ) < n := by
    push_cast
    nlinarith
  exact_mod_cast this

end ElboimSly.Paper
