/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Blocks
public import Mathlib

/-!
# The inclusion at ES22 §5: the escape event (pathwise part)

The inclusion at ES22 §5, last claim (`ℰ(ξ_B)` holds).  This file proves it from the
identification `W(t' + s') = W_i(s')` (the first two claims of the lemma, which concern the cyclic
walk) and from conditions (2), (6) of the walks W_i and the stopping times tau_i; it is `es5_inclusion_escape_event`.
-/

@[expose] public section

namespace ElboimSly.Paper

lemma log_le_of_div_four_hundred {n : ℝ} (hn : 400 ≤ n) : Real.log n ≤ 5 + n / 400 := by
  have h400 : Real.log 400 ≤ 6 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have : Real.exp 6 = (Real.exp 1) ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h2 : (2.7182818283 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) h.le 6
    nlinarith [h2]
  have h1 := Real.log_le_sub_one_of_pos (show 0 < n / 400 by positivity)
  have h2 : Real.log (n / 400) = Real.log n - Real.log 400 := Real.log_div (by positivity) (by norm_num)
  linarith

lemma log_four_le : Real.log 4 ≤ 1.3863 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h := Real.log_two_lt_d9
  linarith

lemma log_thirtysix_le : Real.log 36 ≤ 4 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have h2 : (2.7182818283 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h.le 4
  have : Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith [h2]

/-- The real-number core of the escape-event bound at ES22 §5. -/
lemma incl_core {n a s s' : ℝ} (hn : 2000 ≤ n) (ha1 : 1 ≤ a) (ha2 : a < 2 * n ^ 20)
    (hs1 : n ^ 2 * a ^ 2 / 64 < s) (hL : Real.log s ≤ n * Real.log 4) (hs's : s' ≤ s)
    (hs' : s - a ^ 2 ≤ s') (hs'1 : 1 < s') :
    Real.sqrt s / n + a ≤ 2 * Real.sqrt s' / Real.log s' := by
  have hn0 : 0 < n := by linarith
  have hs0 : 0 < s := by linarith
  have hlog' : 0 < Real.log s' := Real.log_pos hs'1
  have hlogle : Real.log s' ≤ Real.log s := Real.log_le_log (by linarith) hs's
  have hL0 : 0 < Real.log s := lt_of_lt_of_le hlog' hlogle
  set u := Real.sqrt s with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hs0
  have hu2 : u ^ 2 = s := Real.sq_sqrt hs0.le
  -- `n a < 8 u`
  have hna : n * a < 8 * u := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hn0 (by linarith : (0 : ℝ) < a)]
  -- `√s' ≥ 0.99 u`
  have hs'_ge : (0.99 * u) ^ 2 ≤ s' := by
    have h1 : a ^ 2 < 64 * s / n ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    have h2 : 64 / n ^ 2 ≤ 0.0001 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h3 : a ^ 2 ≤ 0.0001 * s := by
      have : 64 * s / n ^ 2 = 64 / n ^ 2 * s := by ring
      rw [this] at h1
      nlinarith [mul_le_mul_of_nonneg_right h2 hs0.le]
    nlinarith
  have hsq : 0.99 * u ≤ Real.sqrt s' := by
    apply Real.le_sqrt_of_sq_le hs'_ge
  -- reduce to `(u / n + a) * log s ≤ 1.98 u`
  have key : (u / n + a) * Real.log s ≤ 1.98 * u := by
    by_cases hc : 3 * n * a ≤ u
    · have h1 : a ≤ u / (3 * n) := by rw [le_div_iff₀ (by positivity)]; nlinarith
      have h2 : u / n + a ≤ 4 / 3 * (u / n) := by
        have : u / (3 * n) = u / n / 3 := by field_simp
        linarith
      have h4 := log_four_le
      calc (u / n + a) * Real.log s ≤ 4 / 3 * (u / n) * (n * 1.3863) := by
            apply mul_le_mul h2 (hL.trans (by nlinarith)) hL0.le (by positivity)
        _ = 4 / 3 * 1.3863 * u := by field_simp
        _ ≤ 1.98 * u := by nlinarith
    · push Not at hc
      have hu36 : s ≤ 36 * n ^ 42 := by
        have h1 : u < 3 * n * a := hc
        have h2 : u ^ 2 < (3 * n * a) ^ 2 := by nlinarith
        have h3 : a ^ 2 < 4 * n ^ 40 := by
          have : a ^ 2 < (2 * n ^ 20) ^ 2 := by nlinarith
          nlinarith [this]
        nlinarith [pow_pos hn0 2]
      have hlog36 : Real.log s ≤ 4 + 42 * (5 + n / 400) := by
        calc Real.log s ≤ Real.log (36 * n ^ 42) := Real.log_le_log hs0 hu36
          _ = Real.log 36 + 42 * Real.log n := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
          _ ≤ 4 + 42 * (5 + n / 400) := by
            have := log_thirtysix_le
            have := log_le_of_div_four_hundred (n := n) (by linarith)
            nlinarith
      have h2 : u / n + a < 9 * (u / n) := by
        have : a < 8 * u / n := by rw [lt_div_iff₀ hn0]; linarith
        have e : 8 * u / n = 8 * (u / n) := by ring
        linarith
      have h5 : 9 * (4 + 42 * (5 + n / 400)) ≤ 1.98 * n := by nlinarith
      calc (u / n + a) * Real.log s ≤ 9 * (u / n) * (4 + 42 * (5 + n / 400)) := by
            apply mul_le_mul h2.le hlog36 hL0.le (by positivity)
        _ = u / n * (9 * (4 + 42 * (5 + n / 400))) := by ring
        _ ≤ u / n * (1.98 * n) := by
            apply mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = 1.98 * u := by field_simp
  rw [le_div_iff₀ hlog']
  calc (u / n + a) * Real.log s' ≤ (u / n + a) * Real.log s :=
        mul_le_mul_of_nonneg_left hlogle (by positivity)
    _ ≤ 1.98 * u := key
    _ ≤ 2 * Real.sqrt s' := by linarith

lemma norm_castR {d : ℕ} (x : Fin d → ℤ) : ‖fun c => (x c : ℝ)‖ = ‖x‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => ?_
    rw [Int.norm_cast_real]; exact norm_le_pi_norm x c
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => ?_
    have := norm_le_pi_norm (fun c => (x c : ℝ)) c
    rwa [Int.norm_cast_real] at this

/-- **the inclusion at ES22 §5**, last claim: `ℰ(ξ_B)` holds, given the identification
`W(t' + s') = W_i(s')` for `s' ∈ [0, 4^n)` (the first two claims), `ξ + 4^j - 1 < t' ≤ ξ + 4^j`,
conditions (2) and (6) for `W_i` on `[0, 4^n)`, `W(ξ) ∈ B^-` and `‖W(ξ) - p_i‖ ≤ 2^j` (both
points lie in `B`). -/
theorem es5_inclusion_escape_event {d n j : ℕ} {β ξ t' : ℝ} (hn : 2000 ≤ n)
    (hj1 : (n : ℝ) ^ 20 ≤ 2 ^ j) (hj2 : (2 : ℝ) ^ j < 2 * n ^ 20)
    (hlb : Real.log β ≤ (n : ℝ) ^ 40) (ht1 : ξ + 4 ^ j - 1 < t') (ht2 : t' ≤ ξ + 4 ^ j)
    {W Wi : ℝ → Fin d → ℤ} {p : Fin d → ℤ} {Bm : Set (Fin d → ℤ)}
    (hrestart : ∀ s' : ℝ, 0 ≤ s' → s' < 4 ^ n → W (t' + s') = Wi s')
    (h2 : ∀ t : ℝ, 0 < t → t < 4 ^ n → Real.log β ≤ t →
      2 * Real.sqrt t / Real.log t < ‖Wi t - p‖)
    (h6 : ∀ t : ℝ, 0 ≤ t → t < 4 ^ n →
      (2 : ℝ) ^ j / 8 < Metric.infDist (fun c => (Wi t c : ℝ)) ((fun x c => (x c : ℝ)) '' Bm))
    (hWξ : W ξ ∈ Bm) (hpB : ‖W ξ - p‖ ≤ 2 ^ j) : EscEvent n j W ξ := by
  intro s hs1 hs2
  have hn' : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  set a : ℝ := 2 ^ j with ha
  have hj4 : (4 : ℝ) ^ j = a ^ 2 := by
    rw [ha, ← pow_mul, mul_comm, pow_mul]; norm_num
  have ha1 : 1 ≤ a := one_le_pow₀ (by norm_num)
  have ha2 : a < 2 * (n : ℝ) ^ 20 := hj2
  have hn0 : (0 : ℝ) < n := by linarith
  rw [hj4] at hs1 ht1 ht2
  set s' : ℝ := s - (t' - ξ) with hs'def
  have hs'0 : 0 ≤ s' := by linarith
  have hs'le : s' ≤ s := by nlinarith
  have hs'ge : s - a ^ 2 ≤ s' := by linarith
  have h4n : (a ^ 2 : ℝ) ≤ 4 ^ n := hs1.trans hs2
  have ha21 : 1 ≤ a ^ 2 := by nlinarith
  have hs'4n : s' < 4 ^ n := by linarith
  have hW : W (ξ + s) = Wi s' := by
    have := hrestart s' hs'0 hs'4n
    rw [← this]; congr 1; rw [hs'def]; ring
  rw [hW]
  rcases le_or_gt s (n ^ 2 * a ^ 2 / 64) with hc | hc
  · -- small `s`
    have hsq : Real.sqrt s / n ≤ a / 8 := by
      rw [div_le_iff₀ hn0]
      apply Real.sqrt_le_iff.2
      refine ⟨by positivity, ?_⟩
      nlinarith
    refine hsq.trans ?_
    have h := h6 s' hs'0 hs'4n
    have hinf : Metric.infDist (fun c => (Wi s' c : ℝ)) ((fun x c => (x c : ℝ)) '' Bm) ≤
        ‖Wi s' - W ξ‖ := by
      refine (Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem _ hWξ)).trans ?_
      rw [dist_eq_norm, ← norm_castR]
      refine le_of_eq (congrArg norm ?_)
      ext c; simp
    linarith
  · -- large `s`
    have hn2 : (128 : ℝ) ≤ n ^ 2 := by nlinarith
    have hs'ge2 : a ^ 2 ≤ s' := by
      have : s - a ^ 2 ≥ a ^ 2 := by nlinarith
      linarith
    have hn40 : (n : ℝ) ^ 40 ≤ a ^ 2 := by
      have : ((n : ℝ) ^ 20) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) hj1 2
      nlinarith [this]
    have hs'1 : 1 < s' := by nlinarith
    have hL : Real.log s ≤ n * Real.log 4 := by
      calc Real.log s ≤ Real.log (4 ^ n) := Real.log_le_log (by linarith) hs2
        _ = n * Real.log 4 := by rw [Real.log_pow]
    have hcore := incl_core hn' ha1 ha2 hc hL hs'le hs'ge hs'1
    have hh2 := h2 s' (by linarith) hs'4n (hlb.trans (hn40.trans hs'ge2))
    have htri : ‖Wi s' - p‖ ≤ ‖Wi s' - W ξ‖ + ‖W ξ - p‖ := by
      calc ‖Wi s' - p‖ = ‖(Wi s' - W ξ) + (W ξ - p)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith

end ElboimSly.Paper
