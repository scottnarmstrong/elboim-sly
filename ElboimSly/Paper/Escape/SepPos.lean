/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Sep
public import Mathlib

/-!
# Old history is far (old history is far): history in phases `i' ∈ [1, i-2]`

Old history is far, cases `1 ≤ i' ≤ i - 2`.
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly.Brownian

variable {k : ℕ}

lemma conv16 (T : ℝ) (n : ℕ) : T / (16 * 2 ^ n) = T / 16 * (1 / 2 ^ n) := by
  field_simp

lemma conv64 (T : ℝ) (n : ℕ) : T / (64 * 2 ^ n) = T / 64 * (1 / 2 ^ n) := by
  field_simp

lemma conv_c (c : ℝ) (n : ℕ) : c / 2 ^ n = c * (1 / 2 ^ n) := by
  field_simp

lemma one_div_pow_le_one (n : ℕ) : 1 / (2 : ℝ) ^ n ≤ 1 :=
  (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))

/-- Old history is far, history in phase `i' ∈ [1, i-2]`. -/
theorem sep_core_pos {j : ℕ} {u v z : Fin (k + 2) → ℤ} (h : EscGeom j u v z) {β t : ℝ}
    (hβ : (2 : ℝ) ^ 40 ≤ β) (hβj : β < 4 ^ j) (ht2 : t ≤ 4 ^ j) (ht : 0 < t) {m : ℕ}
    (hm : (2 : ℝ) ^ m * Real.sqrt (Real.sqrt β) ≤ Real.sqrt t) {i i' : ℕ} (hi'1 : 1 ≤ i')
    (hii : i' + 2 ≤ i) (him : i ≤ 2 * m) {s s' : ℝ} (hs1 : escPhaseA t m (i - 1) ≤ s)
    (hs2 : s ≤ es56B t m i) (hs1' : escPhaseA t m (i' - 1) ≤ s') (hs2' : s' ≤ es56B t m i')
    (_hss : β ≤ s - s') {y w' : Fin (k + 2) → ℤ}
    (hy : ‖escCast y - escCurve j u v z t s‖ ≤ escR t m i)
    (hw : ‖escCast w' - escCurve j u v z t s'‖ ≤ escR t m i') :
    2 ≤ ‖escCast y - escCast w'‖ := by
  have ha := h.a_ge
  have hT := esc_sqrt_le_two_pow ht2
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hsb' : (2 : ℝ) ^ 20 ≤ Real.sqrt β := by
    apply Real.le_sqrt_of_sq_le
    calc ((2 : ℝ) ^ 20) ^ 2 = 2 ^ 40 := by rw [← pow_mul]
      _ ≤ β := hβ
  have hsb : Real.sqrt β < 2 ^ j := by
    refine (Real.sqrt_lt' (by positivity)).2 ?_
    calc β < 4 ^ j := hβj
      _ = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have ha20 : (2 : ℝ) ^ 20 ≤ 2 ^ j := by linarith
  have hQ : (1024 : ℝ) ≤ Real.sqrt (Real.sqrt β) := by
    apply Real.le_sqrt_of_sq_le
    norm_num at hsb' ⊢; linarith
  have hT0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have htri := tri_norm (escCurve j u v z t s) (escCast y) (escCurve j u v z t s')
    (escCast w')
  have hrel : ‖escCurve j u v z t s - escCurve j u v z t s'‖ - escR t m i - escR t m i' ≤
      ‖escCast y - escCast w'‖ := by linarith
  have hQm : ∀ n, n ≤ m → 1024 ≤ 1 / (2 : ℝ) ^ n * Real.sqrt t := fun n hn =>
    le_trans hQ (quarter_root_le (by linarith) hm hn)
  rcases phase_cases ht (by omega : 1 ≤ i) him hs1 hs2 with
      ⟨n, hn1, hn, hs, hl, hlu, hR⟩ | ⟨n, hn, hs, hl, hlu, hR⟩ <;>
    rcases phase_cases ht hi'1 (by omega : i' ≤ 2 * m) hs1' hs2' with
      ⟨n', hn1', hn', hs', hl', hlu', hR'⟩ | ⟨n', hn', hs', hl', hlu', hR'⟩
  · -- first half, first half
    have hnn : n + 2 ≤ n' := by omega
    have hq := inv_pow_le_quarter hnn
    have pf := pair_first h hs hs'
    have key := ar_FF (a := 2 ^ j) (T := Real.sqrt t) (e := 1 / 2 ^ n) (e' := 1 / 2 ^ n')
      (l := Real.sqrt (2 * s / t)) (l' := Real.sqrt (2 * s' / t)) (R := escR t m i)
      (R' := escR t m i') hT
      (by positivity) hq hl (by rw [← conv_c]; exact hlu')
      (by rw [← conv16]; exact hR) (by rw [← conv16]; exact hR')
      (by linarith [hQm n (by omega)]) hT0
    have hab : Real.sqrt (2 * s / t) - Real.sqrt (2 * s' / t) ≤
        |Real.sqrt (2 * s / t) - Real.sqrt (2 * s' / t)| := le_abs_self _
    have := mul_le_mul_of_nonneg_right hab (by positivity : (0 : ℝ) ≤ 2 ^ j / 4)
    linarith only [key, this, pf, hrel]
  · -- first half, second half: impossible
    exfalso; linarith
  · -- second half, first half
    have pm := pair_mixed h ht hs hs'
    have hnn : (0 : ℝ) ≤ 2 ^ j / 12 - 1 := by linarith
    by_cases hn2 : 2 ≤ n
    · have h4 : (4 : ℝ) ≤ 2 ^ n := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn2
      have h2' : (2 : ℝ) ≤ 2 ^ n' := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n' := pow_le_pow_right₀ (by norm_num) hn1'
      have hmu : Real.sqrt (2 * (t - s) / t) ≤ 1 / 2 := by
        refine hlu.trans ?_
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [h4]
      have hR1 : escR t m i ≤ Real.sqrt t / 256 := by
        refine hR.trans ?_
        apply div_le_div_of_nonneg_left hT0 (by norm_num); linarith only [h4]
      have hR2 : escR t m i' ≤ Real.sqrt t / 32 := by
        refine hR'.trans ?_
        apply div_le_div_of_nonneg_left hT0 (by norm_num); linarith only [h2']
      have key := ar_mixed_far (a := 2 ^ j) (T := Real.sqrt t) (mu := Real.sqrt (2 * (t - s) / t))
        hT ha20 hmu hR1 hR2 hT0
      have := mul_le_mul_of_nonneg_right (le_max_left (1 - Real.sqrt (2 * (t - s) / t))
        (1 - Real.sqrt (2 * s' / t))) hnn
      linarith only [key, this, pm, hrel]
    · have hn2' : 2 ≤ n' := by omega
      have h4 : (4 : ℝ) ≤ 2 ^ n' := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n' := pow_le_pow_right₀ (by norm_num) hn2'
      have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hl2 : Real.sqrt (2 * s' / t) ≤ 55 / 100 := by
        refine hlu'.trans ?_
        rw [div_le_iff₀ (by positivity)]; linarith only [h4]
      have hR1 : escR t m i ≤ Real.sqrt t / 64 := by
        refine hR.trans ?_
        apply div_le_div_of_nonneg_left hT0 (by norm_num); linarith only [h1]
      have hR2 : escR t m i' ≤ Real.sqrt t / 64 := by
        refine hR'.trans ?_
        apply div_le_div_of_nonneg_left hT0 (by norm_num); linarith only [h4]
      have key := ar_mixed_near (a := 2 ^ j) (T := Real.sqrt t) (l' := Real.sqrt (2 * s' / t))
        hT ha20 hl2 hR1 hR2 hT0
      have := mul_le_mul_of_nonneg_right (le_max_right (1 - Real.sqrt (2 * (t - s) / t))
        (1 - Real.sqrt (2 * s' / t))) hnn
      linarith only [key, this, pm, hrel]
  · -- second half, second half
    have hnn : n' + 2 ≤ n := by omega
    have hq := inv_pow_le_quarter hnn
    have ps := pair_second h ht hs hs'
    have hab : Real.sqrt (2 * (t - s') / t) - Real.sqrt (2 * (t - s) / t) ≤
        |Real.sqrt (2 * (t - s) / t) - Real.sqrt (2 * (t - s') / t)| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have hq1 : 0 ≤ (2 : ℝ) ^ j / 4 - 1 := by linarith
    have := mul_le_mul_of_nonneg_right hab hq1
    have key := ar_SS (a := 2 ^ j) (T := Real.sqrt t) (e := 1 / 2 ^ n) (e' := 1 / 2 ^ n')
      (mu := Real.sqrt (2 * (t - s) / t)) (mu' := Real.sqrt (2 * (t - s') / t))
      (R := escR t m i) (R' := escR t m i') hT (by positivity) (one_div_pow_le_one n')
      (by positivity) hq (by rw [← conv_c]; exact hl') (by rw [← conv_c]; exact hlu)
      (by rw [← conv64]; exact hR) (by rw [← conv64]; exact hR')
      (by linarith [hQm n' (by omega)]) hT0
    linarith only [key, this, ps, hrel]

end ElboimSly.Paper
