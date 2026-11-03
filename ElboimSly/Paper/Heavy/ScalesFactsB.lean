/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IndThetaH
public import ElboimSly.Paper.Heavy.ScalesFacts

/-!
# Elementary facts about the scales: parts (b)-(e)

Elementary facts about the scales (b)-(e) (supplement).
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {t₀ : ℝ}

theorem indScale_gt_four_pow (ht1 : 1 < t₀) (n : ℕ) : (4 : ℝ) ^ n < indScale t₀ n := by
  unfold indScale
  have : (0 : ℝ) < 4 ^ n := by positivity
  nlinarith

theorem indScale_le_four_pow (ht4 : t₀ ≤ 4) (n : ℕ) : indScale t₀ n ≤ (4 : ℝ) ^ (n + 1) := by
  unfold indScale
  have : (0 : ℝ) < 4 ^ n := by positivity
  rw [pow_succ]; nlinarith

/-- Elementary facts about the scales (b). -/
theorem scales_facts_b (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) :
    heavyScaleJ n ≤ heavyM0 d t₀ n ∧ heavyM0 d t₀ n ≤ heavyLevel d n := by
  have hδ := heavy_indDelta_pos (d := d) (by omega)
  have hn2 : 2 ≤ n := by have := hT.t4; omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hT2a, hT2b, hT2c⟩ := hT.t2
  have hlog4 : 2 * (n : ℝ) < Real.logb 2 (indScale t₀ n) := by
    have h := indScale_gt_four_pow ht1 n
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by unfold indScale; positivity)]
    calc (2 : ℝ) ^ (2 * (n : ℝ)) = 4 ^ n := by
          rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
            pow_mul]; norm_num
      _ < _ := h
  have hlog4' : Real.logb 2 (indScale t₀ n) ≤ 2 * ((n : ℝ) + 1) := by
    have h := indScale_le_four_pow ht4 n
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by unfold indScale; positivity)]
    calc indScale t₀ n ≤ 4 ^ (n + 1) := h
      _ = (2 : ℝ) ^ (2 * ((n : ℝ) + 1)) := by
          rw [show (2 * ((n : ℝ) + 1)) = ((2 * (n + 1) : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_natCast, pow_mul]; norm_num
  have hspec := heavyScaleJ_spec hn2
  have hj : (heavyScaleJ n : ℝ) < 1 + 20 * Real.logb 2 n := by
    have h2 : ((2 : ℝ) ^ heavyScaleJ n) < 2 * (n : ℝ) ^ 20 := by exact_mod_cast hspec.2
    have := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h2
    rw [Real.logb_pow] at this
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
    simp at this
    linarith
  constructor
  · have hm : 2 * indDelta d * n - 1 < heavyM0 d t₀ n := by
      have := Nat.lt_floor_add_one (indDelta d * Real.logb 2 (indScale t₀ n))
      unfold heavyM0
      nlinarith
    have : (heavyScaleJ n : ℝ) < heavyM0 d t₀ n := by linarith
    exact_mod_cast this.le
  · have hm : (heavyM0 d t₀ n : ℝ) ≤ 2 * indDelta d * n + 2 * indDelta d := by
      have := Nat.floor_le (show 0 ≤ indDelta d * Real.logb 2 (indScale t₀ n) by
        have : 0 ≤ Real.logb 2 (indScale t₀ n) := by linarith
        positivity)
      unfold heavyM0
      nlinarith
    have hk := lt_heavyLevel_add_one d n
    have : (heavyM0 d t₀ n : ℝ) < heavyLevel d n := by nlinarith
    exact_mod_cast this.le

/-- Elementary facts about the scales (c). -/
theorem scales_facts_c (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hk : 16 ≤ heavyLevel d n) :
    2 ≤ (4 : ℝ) ^ heavyLevel d n / (heavyLevel d n : ℝ) ^ 4 ∧
      (4 : ℝ) ^ heavyLevel d n / (heavyLevel d n : ℝ) ^ 4 < heavyTkPrime d t₀ n ∧
      heavyTkPrime d t₀ n ≤ (4 : ℝ) ^ (heavyLevel d n + 1) / (heavyLevel d n : ℝ) ^ 4 ∧
      heavyTkPrime d t₀ n ^ indThetaH ≤ (2 : ℝ) ^ (heavyLevel d n - 2) := by
  have hk0 : (0 : ℝ) < (heavyLevel d n : ℝ) ^ 4 := by
    have : (0 : ℝ) < heavyLevel d n := by exact_mod_cast (by omega : 0 < heavyLevel d n)
    positivity
  have hk1 : (1 : ℝ) ≤ (heavyLevel d n : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ heavyLevel d n := by exact_mod_cast (by omega : 1 ≤ heavyLevel d n)
    exact one_le_pow₀ this
  have e : heavyTkPrime d t₀ n = 4 ^ heavyLevel d n * t₀ / (heavyLevel d n : ℝ) ^ 4 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hk0]
    have := two_mul_pow_four_le _ hk
    have h : ((2 * heavyLevel d n ^ 4 : ℕ) : ℝ) ≤ ((4 ^ heavyLevel d n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h
    linarith
  · rw [e]
    have : (0 : ℝ) < 4 ^ heavyLevel d n := by positivity
    apply div_lt_div_of_pos_right _ hk0
    have ht0 : 0 < t₀ := by linarith
    nlinarith
  · rw [e, pow_succ (4 : ℝ) (heavyLevel d n)]
    apply div_le_div_of_nonneg_right _ hk0.le
    have : (0 : ℝ) < 4 ^ heavyLevel d n := by positivity
    nlinarith
  · have h4pos : (0 : ℝ) < 4 ^ heavyLevel d n := by positivity
    have ht0 : 0 < t₀ := by linarith
    have hp : heavyTkPrime d t₀ n ≤ (4 : ℝ) ^ (heavyLevel d n + 1) := by
      rw [e, pow_succ (4 : ℝ) (heavyLevel d n), div_le_iff₀ hk0]
      nlinarith
    have hpos : 0 < heavyTkPrime d t₀ n := by rw [e]; positivity
    have hθ : (0 : ℝ) ≤ indThetaH := by unfold indThetaH; norm_num
    calc heavyTkPrime d t₀ n ^ indThetaH ≤ ((4 : ℝ) ^ (heavyLevel d n + 1)) ^ indThetaH :=
          Real.rpow_le_rpow hpos.le hp hθ
      _ = (4 : ℝ) ^ (((heavyLevel d n : ℝ) + 1) * indThetaH) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; rfl
      _ ≤ (4 : ℝ) ^ (((heavyLevel d n : ℝ) - 2) / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          unfold indThetaH
          have : (16 : ℝ) ≤ heavyLevel d n := by exact_mod_cast hk
          linarith
      _ = (2 : ℝ) ^ (heavyLevel d n - 2) := by
          have h2 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
          rw [h2, ← Real.rpow_mul (by norm_num)]
          rw [show (2 : ℝ) * (((heavyLevel d n : ℝ) - 2) / 2) = ((heavyLevel d n - 2 : ℕ) : ℝ) by
            rw [Nat.cast_sub (by omega)]; push_cast; ring, Real.rpow_natCast]

/-- Elementary facts about the scales (d). -/
theorem scales_facts_d (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) :
    heavyTkPrime d t₀ n < indScale t₀ (heavyLevel d n) ∧
      indScale t₀ (heavyLevel d n) < indScale t₀ n ^ (5 * indDelta d) ∧
      (2 : ℝ) ^ (d * heavyLevel d n) ≤ indScale t₀ n ^ (2 * indDelta d * d) := by
  have hδ := heavy_indDelta_pos (d := d) (by omega)
  have hk : 16 ≤ heavyLevel d n := hT.t1.2
  have hk0 : (0 : ℝ) < (heavyLevel d n : ℝ) ^ 4 := by
    have : (0 : ℝ) < heavyLevel d n := by exact_mod_cast (by omega : 0 < heavyLevel d n)
    positivity
  have hk1 : (1 : ℝ) < (heavyLevel d n : ℝ) ^ 4 := by
    have : (1 : ℝ) < heavyLevel d n := by exact_mod_cast (by omega : 1 < heavyLevel d n)
    exact one_lt_pow₀ this (by norm_num)
  have hpos : 0 < indScale t₀ (heavyLevel d n) := by
    unfold indScale; have : 0 < t₀ := by linarith
    positivity
  have hkle := heavyLevel_le (d := d) (by omega) n
  obtain ⟨_, _, hT2c⟩ := hT.t2
  have hn : (0 : ℝ) < n := by have := hT.t4; exact_mod_cast (by omega : 0 < n)
  have htn : (4 : ℝ) ^ n ≤ indScale t₀ n := (indScale_gt_four_pow ht1 n).le
  refine ⟨?_, ?_, ?_⟩
  · unfold heavyTkPrime
    rw [div_lt_iff₀ hk0]; nlinarith
  · have h1 := indScale_le_four_pow ht4 (heavyLevel d n)
    have h2 : (4 : ℝ) ^ (heavyLevel d n + 1) < (4 : ℝ) ^ (5 * indDelta d * n) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      have := lt_heavyLevel_add_one d n
      push_cast
      nlinarith
    have h3 : (4 : ℝ) ^ (5 * indDelta d * n) ≤ indScale t₀ n ^ (5 * indDelta d) := by
      calc (4 : ℝ) ^ (5 * indDelta d * n) = ((4 : ℝ) ^ n) ^ (5 * indDelta d) := by
            rw [mul_comm (5 * indDelta d), Real.rpow_mul (by norm_num), Real.rpow_natCast]
        _ ≤ _ := Real.rpow_le_rpow (by positivity) htn (by positivity)
    exact lt_of_le_of_lt h1 (h2.trans_le h3)
  · have h3 : (4 : ℝ) ^ ((2 * indDelta d * d) * n) ≤ indScale t₀ n ^ (2 * indDelta d * d) := by
      calc (4 : ℝ) ^ ((2 * indDelta d * d) * n) = ((4 : ℝ) ^ n) ^ (2 * indDelta d * d) := by
            rw [mul_comm (2 * indDelta d * d), Real.rpow_mul (by norm_num), Real.rpow_natCast]
        _ ≤ _ := Real.rpow_le_rpow (by positivity) htn (by positivity)
    refine le_trans ?_ h3
    have h2 : (2 : ℝ) ^ (d * heavyLevel d n) = (4 : ℝ) ^ (((d * heavyLevel d n : ℕ) : ℝ) / 2) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      rw [show (2 : ℝ) * (((d * heavyLevel d n : ℕ) : ℝ) / 2) = ((d * heavyLevel d n : ℕ) : ℝ) by ring,
        Real.rpow_natCast]
    rw [h2]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    have hd0 : (0 : ℝ) ≤ d := by positivity
    nlinarith

/-- Elementary facts about the scales (e). -/
theorem scales_facts_e (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hT : HeavyT d n₀ E n) :
    5 / (n : ℝ) ≤ 1 / (heavyLevelPrime d t₀ n : ℝ) ∧
      1 / (8 * indDelta d * n) ≤ 1 / (heavyLevelPrime d t₀ n : ℝ) - 4 / n := by
  have hδ := heavy_indDelta_pos (d := d) (by omega)
  have hd4 := four_indDelta_le hd
  obtain ⟨⟨_, hk2⟩, ⟨_, hlt, _⟩, h10⟩ := scales_facts_a hd hn0 ht1 ht4 hT
  have hkle := heavyLevel_le (d := d) (by omega) n
  have hn : (0 : ℝ) < n := by have := hT.t4; exact_mod_cast (by omega : 0 < n)
  have hkp : (10 : ℝ) ≤ heavyLevelPrime d t₀ n := by exact_mod_cast h10
  have hkp2 : (heavyLevelPrime d t₀ n : ℝ) ≤ 4 * indDelta d * n := by
    have : (heavyLevelPrime d t₀ n : ℝ) < heavyLevel d n := by exact_mod_cast hlt
    linarith
  have hinv : 1 / (4 * indDelta d * n) ≤ 1 / (heavyLevelPrime d t₀ n : ℝ) :=
    one_div_le_one_div_of_le (by linarith) hkp2
  have hA : 18750 / (n : ℝ) ≤ 1 / (4 * indDelta d * n) := by
    rw [div_le_div_iff₀ hn (by positivity)]
    nlinarith
  have hB : 1 / (8 * indDelta d * n) = (1 / (4 * indDelta d * n)) / 2 := by
    field_simp; ring
  constructor
  · have : 5 / (n : ℝ) ≤ 18750 / n := by
      apply div_le_div_of_nonneg_right (by norm_num) hn.le
    linarith
  · rw [hB]
    have : 4 / (n : ℝ) ≤ 18750 / n / 2 := by
      rw [div_div, div_le_div_iff₀ hn (by positivity)]; nlinarith
    have h2 : 18750 / (n : ℝ) / 2 ≤ (1 / (4 * indDelta d * n)) / 2 := by
      apply div_le_div_of_nonneg_right hA (by norm_num)
    linarith

end ElboimSly.Paper
