/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Lemma82A
public import Mathlib

/-!
# The SRW content of Lemma 8.2: part (e), numerics

SRW content of Lemma 8.2 (e): the threshold `n₂(d)`.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal Real

namespace ElboimSly
namespace SRW

theorem sqrt_pow_eq (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : √(a ^ n) = (√a) ^ n := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
    Real.mul_self_sqrt ha]

theorem q_ratio_pow_le : (1.9 / √(3.89 : ℝ)) ^ 3 ≤ 0.895 := by
  have hs : (0 : ℝ) < √3.89 := Real.sqrt_pos.2 (by norm_num)
  have hsq : √(3.89 : ℝ) ^ 2 = 3.89 := Real.sq_sqrt (by norm_num)
  have hlow : (1.972 : ℝ) ≤ √3.89 := Real.le_sqrt_of_sq_le (by norm_num)
  rw [div_pow, div_le_iff₀ (by positivity)]
  have : √(3.89 : ℝ) ^ 3 = 3.89 * √3.89 := by rw [pow_succ, hsq]
  rw [this]
  nlinarith

theorem q_ratio_lt_one : (1.9 / √(3.89 : ℝ)) < 1 := by
  have hlow : (1.97 : ℝ) ≤ √3.89 := Real.le_sqrt_of_sq_le (by norm_num)
  rw [div_lt_one (by linarith)]
  linarith

/-- SRW content of Lemma 8.2 (e), the existence of `n₂(d)`. -/
theorem lemma82_n2 {d : ℕ} (hd : 5 ≤ d) (hC : 0 ≤ Chit d) :
    ∃ n₂ : ℕ, ∀ n ≥ n₂, ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 →
      (lem82T n t₀ / (3.6 : ℝ) ^ n + 2) * Chit d *
        (1.9 ^ (n + 2) / √((3.89 : ℝ) ^ n)) ^ (d - 2) ≤ 1 / 2 := by
  set q : ℝ := 1.9 / √3.89 with hq
  have hq0 : 0 < q := by
    have := Real.sqrt_pos.2 (show (0 : ℝ) < 3.89 by norm_num); positivity
  have hq1 := q_ratio_lt_one
  have hq3 := q_ratio_pow_le
  set r : ℝ := 10 / 9 * q ^ (d - 2) with hr
  have hqd : q ^ (d - 2) ≤ q ^ 3 := pow_le_pow_of_le_one hq0.le hq1.le (by omega)
  have hr0 : 0 ≤ r := by positivity
  have hq3' : q ^ 3 ≤ 0.895 := by rw [hq]; exact hq3
  have hr1 : r < 1 := by
    rw [hr]
    linarith
  set K : ℝ := 10 * Chit d * 3.61 ^ (d - 2) with hK
  have hlim : Tendsto (fun n : ℕ => K * r ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul K
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hlim).2 (1 / 2) (by norm_num))
  refine ⟨max n₂ 4, fun n hn t₀ ht1 ht4 => ?_⟩
  have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn
  have hnn : n₂ ≤ n := le_trans (le_max_left _ _) hn
  have hT : lem82T n t₀ ≤ 8 * 4 ^ n / 256 := by
    unfold lem82T
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have hn4' : (256 : ℝ) ≤ (n : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 16), sq_nonneg (n : ℝ)]
    have h4n : (0 : ℝ) < 4 ^ n := by positivity
    rw [show 2 * (4 ^ n * t₀ / (n : ℝ) ^ 4) = 2 * t₀ * 4 ^ n / (n : ℝ) ^ 4 by ring,
      div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have h36 : (0 : ℝ) < (3.6 : ℝ) ^ n := by positivity
  have hratio : (4 : ℝ) ^ n / 3.6 ^ n = (10 / 9) ^ n := by
    rw [← div_pow]; congr 1; norm_num
  have h109 : (1 : ℝ) ≤ (10 / 9) ^ n := one_le_pow₀ (by norm_num)
  have hM : lem82T n t₀ / (3.6 : ℝ) ^ n + 2 ≤ 10 * (10 / 9) ^ n := by
    have : lem82T n t₀ / (3.6 : ℝ) ^ n ≤ 8 * (10 / 9) ^ n / 256 := by
      rw [div_le_iff₀ h36]
      calc lem82T n t₀ ≤ 8 * 4 ^ n / 256 := hT
        _ = 8 * ((4 : ℝ) ^ n / 3.6 ^ n) / 256 * 3.6 ^ n := by field_simp
        _ = _ := by rw [hratio]
    linarith
  have hpow : (1.9 ^ (n + 2) / √((3.89 : ℝ) ^ n)) ^ (d - 2) =
      3.61 ^ (d - 2) * (q ^ (d - 2)) ^ n := by
    have hs : (0 : ℝ) < √3.89 := Real.sqrt_pos.2 (by norm_num)
    have e : (1.9 : ℝ) ^ (n + 2) / √((3.89 : ℝ) ^ n) = 3.61 * q ^ n := by
      rw [sqrt_pow_eq _ (by norm_num), hq, div_pow, pow_add]
      field_simp
      norm_num
    rw [e, mul_pow, ← pow_mul, ← pow_mul, mul_comm n (d - 2)]
  have hfin : (lem82T n t₀ / (3.6 : ℝ) ^ n + 2) * Chit d *
        (1.9 ^ (n + 2) / √((3.89 : ℝ) ^ n)) ^ (d - 2) ≤ K * r ^ n := by
    rw [hpow]
    have hqn : 0 ≤ (q ^ (d - 2)) ^ n := by positivity
    have h3 : (0 : ℝ) ≤ 3.61 ^ (d - 2) := by positivity
    calc (lem82T n t₀ / (3.6 : ℝ) ^ n + 2) * Chit d * (3.61 ^ (d - 2) * (q ^ (d - 2)) ^ n)
        ≤ (10 * (10 / 9) ^ n) * Chit d * (3.61 ^ (d - 2) * (q ^ (d - 2)) ^ n) := by gcongr
      _ = K * r ^ n := by
          rw [hK, hr, mul_pow]; ring
  have := hn₂ n hnn
  linarith

end SRW
end ElboimSly
