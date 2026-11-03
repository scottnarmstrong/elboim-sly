/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Num
public import Mathlib

/-!
# The asymptotic numerics of Lemma 7.8: proofs
-/

@[expose] public section

open Filter

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {t₀ : ℝ} {n : ℕ}

theorem four_pow_level_le (hd : 5 ≤ d) (n : ℕ) :
    (4 : ℝ) ^ heavyLevel d n ≤ (4 : ℝ) ^ (heavyEps d / 3 * n) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (level_le hd n)

theorem tkPrime_le (ht4 : t₀ ≤ 4) (hk : 16 ≤ heavyLevel d n) (ht1 : 1 < t₀) :
    heavyTkPrime d t₀ n ≤ 4 * (4 : ℝ) ^ heavyLevel d n := by
  have h := (scales_facts_c (d := d) (n := n) ht1 ht4 hk).2.2.1
  have hk1 : (1 : ℝ) ≤ (heavyLevel d n : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ heavyLevel d n := by exact_mod_cast (by omega : 1 ≤ heavyLevel d n)
    exact one_le_pow₀ this
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  rw [pow_succ]
  nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) (heavyLevel d n)]

theorem tkPrime_nonneg (ht1 : 1 < t₀) : 0 ≤ heavyTkPrime d t₀ n := by
  unfold heavyTkPrime indScale
  have : 0 < t₀ := by linarith
  positivity

/-- `t'_k + 3 ≤ t'_n`. -/
theorem asym_tk_le (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hk : 16 ≤ heavyLevel d n)
    (hN : 7 * (n : ℝ) ^ 4 ≤ (4 : ℝ) ^ (3 / 4 * (n : ℝ))) (hn : 1 ≤ n) :
    heavyTkPrime d t₀ n + 3 ≤ indScaleReduced t₀ n := by
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
  unfold indScaleReduced
  rw [le_div_iff₀ hn0]
  have h1 := tkPrime_le ht4 hk ht1 (n := n) (d := d)
  have h2 : (4 : ℝ) ^ heavyLevel d n ≤ (4 : ℝ) ^ ((n : ℝ) / 4) := by
    refine (four_pow_level_le hd n).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have := eps_le hd
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h3 : (4 : ℝ) ^ ((n : ℝ) / 4) * (4 : ℝ) ^ (3 / 4 * (n : ℝ)) = (4 : ℝ) ^ n := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast]
    congr 1; ring
  have h4 : (4 : ℝ) ^ n ≤ indScale t₀ n := (indScale_gt_four_pow ht1 n).le
  have h5 : (1 : ℝ) ≤ (4 : ℝ) ^ heavyLevel d n := one_le_pow₀ (by norm_num)
  have hX : (0 : ℝ) < (4 : ℝ) ^ ((n : ℝ) / 4) := by positivity
  calc (heavyTkPrime d t₀ n + 3) * (n : ℝ) ^ 4
      ≤ (7 * (4 : ℝ) ^ heavyLevel d n) * (n : ℝ) ^ 4 := by
        refine mul_le_mul_of_nonneg_right ?_ hn0.le
        linarith
    _ ≤ (7 * (4 : ℝ) ^ ((n : ℝ) / 4)) * (n : ℝ) ^ 4 := by
        refine mul_le_mul_of_nonneg_right ?_ hn0.le
        linarith
    _ = ((4 : ℝ) ^ ((n : ℝ) / 4)) * (7 * (n : ℝ) ^ 4) := by ring
    _ ≤ ((4 : ℝ) ^ ((n : ℝ) / 4)) * (4 : ℝ) ^ (3 / 4 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hN hX.le
    _ = (4 : ℝ) ^ n := h3
    _ ≤ _ := h4

theorem tn_rpow_le (ht4 : t₀ ≤ 4) (ht1 : 1 < t₀) {c : ℝ} (hc : 0 ≤ c) :
    indScale t₀ n ^ c ≤ (4 : ℝ) ^ (((n : ℝ) + 1) * c) := by
  have h1 := indScale_le_four_pow ht4 n
  have hpos : 0 ≤ indScale t₀ n := (by positivity : (0 : ℝ) ≤ 4 ^ n).trans (indScale_gt_four_pow ht1 n).le
  calc indScale t₀ n ^ c ≤ ((4 : ℝ) ^ (n + 1)) ^ c := Real.rpow_le_rpow hpos h1 hc
    _ = _ := by rw [pow4_rpow]; push_cast; rfl

theorem tn_rpow_ge (ht1 : 1 < t₀) {c : ℝ} (hc : 0 ≤ c) :
    (4 : ℝ) ^ ((n : ℝ) * c) ≤ indScale t₀ n ^ c := by
  rw [← pow4_rpow]
  exact Real.rpow_le_rpow (by positivity) (indScale_gt_four_pow ht1 n).le hc

/-- `2 t'_k + 4 + t_n^{ε/3} < t_n^ε`. -/
theorem asym_L2 (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hk : 16 ≤ heavyLevel d n)
    (hn : 900 * (d : ℝ) < n) :
    2 * heavyTkPrime d t₀ n + 4 + indScale t₀ n ^ (heavyEps d / 3) < indScale t₀ n ^ heavyEps d := by
  have hε := eps_pos hd
  set X : ℝ := (4 : ℝ) ^ (heavyEps d / 3 * n) with hX
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hX4 : 4 < X := by
    have : (4 : ℝ) = (4 : ℝ) ^ (1 : ℝ) := by simp
    rw [this, hX]
    refine Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_
    unfold heavyEps
    rw [show 1 / (300 * (d : ℝ)) / 3 * n = n / (900 * d) by field_simp; ring, lt_div_iff₀ (by positivity)]
    linarith
  have hXe : X ^ 3 = (4 : ℝ) ^ ((n : ℝ) * heavyEps d) := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; push_cast; ring
  have htk : heavyTkPrime d t₀ n ≤ 4 * X :=
    (tkPrime_le ht4 hk ht1).trans (mul_le_mul_of_nonneg_left (four_pow_level_le hd n) (by norm_num))
  have hg : indScale t₀ n ^ (heavyEps d / 3) ≤ 4 * X := by
    refine (tn_rpow_le ht4 ht1 (by positivity)).trans ?_
    have : (4 : ℝ) ^ (((n : ℝ) + 1) * (heavyEps d / 3)) = X * (4 : ℝ) ^ (heavyEps d / 3) := by
      rw [hX, ← Real.rpow_add (by norm_num)]; congr 1; ring
    rw [this]
    have h4 : (4 : ℝ) ^ (heavyEps d / 3) ≤ 4 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 4 by norm_num)
        (show heavyEps d / 3 ≤ 1 by linarith [eps_le hd])
      simpa using this
    nlinarith
  have hL := tn_rpow_ge (n := n) ht1 hε.le
  rw [← hXe] at hL
  have hX1 : 1 ≤ X := by linarith
  nlinarith [mul_pos (by linarith : (0 : ℝ) < X) (by linarith : (0 : ℝ) < X - 4)]

theorem two_pow_level_le (hd : 5 ≤ d) (n : ℕ) :
    (2 : ℝ) ^ heavyLevel d n ≤ (4 : ℝ) ^ (2 * indDelta d * n) := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
  rw [h4, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have := heavyLevel_le (d := d) (by omega) n
  nlinarith

/-- `β < t_n^{5δ}` gives `(9^d + 1) 2^{kd} (2n) β ≤ t_n^{ε/3}`. -/
theorem asym_occ (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hN : 8 * ((9 : ℝ) ^ d + 1) * n ≤ (4 : ℝ) ^ (heavyEps d / 30 * n)) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β < indScale t₀ n ^ (5 * indDelta d)) :
    (((9 ^ d + 1) * (2 ^ heavyLevel d n) ^ d * (2 * n) : ℕ) : ℝ) * β ≤
      indScale t₀ n ^ (heavyEps d / 3) := by
  have hε := eps_pos hd
  have hδ : 0 < indDelta d := heavy_indDelta_pos (by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set Y : ℝ := (4 : ℝ) ^ (5 * indDelta d * n) with hY
  have hβ1 : β ≤ 4 * Y := by
    refine hβ.le.trans ((tn_rpow_le ht4 ht1 (by positivity)).trans ?_)
    have : (4 : ℝ) ^ (((n : ℝ) + 1) * (5 * indDelta d)) = Y * (4 : ℝ) ^ (5 * indDelta d) := by
      rw [hY, ← Real.rpow_add (by norm_num)]; congr 1; ring
    rw [this]
    have h4 : (4 : ℝ) ^ (5 * indDelta d) ≤ 4 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 4 by norm_num)
        (show 5 * indDelta d ≤ 1 by
          have := delta_eps hd; have := eps_le hd; linarith)
      simpa using this
    nlinarith [(by positivity : (0 : ℝ) ≤ Y)]
  have hk2 : (2 : ℝ) ^ heavyLevel d n ≤ (4 : ℝ) ^ (2 * indDelta d * n) := two_pow_level_le hd n
  have hkd : ((2 : ℝ) ^ heavyLevel d n) ^ d ≤ (4 : ℝ) ^ (2 * indDelta d * n * d) := by
    refine (pow_le_pow_left₀ (by positivity) hk2 d).trans (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hexp : (4 : ℝ) ^ (2 * indDelta d * n * d) * Y = (4 : ℝ) ^ (indDelta d * (2 * d + 5) * n) := by
    rw [hY, ← Real.rpow_add (by norm_num)]; congr 1; ring
  have hexp2 : (4 : ℝ) ^ (indDelta d * (2 * d + 5) * n) ≤ (4 : ℝ) ^ (3 * heavyEps d / 10 * n) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have := delta_eps2 hd
    nlinarith
  have hfin : (4 : ℝ) ^ (heavyEps d / 30 * n) * (4 : ℝ) ^ (3 * heavyEps d / 10 * n) =
      (4 : ℝ) ^ (n * (heavyEps d / 3)) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  have hg := tn_rpow_ge (n := n) ht1 (show 0 ≤ heavyEps d / 3 by positivity)
  push_cast
  have hC9 : (0 : ℝ) ≤ (9 : ℝ) ^ d + 1 := by positivity
  have hkd0 : (0 : ℝ) ≤ ((2 : ℝ) ^ heavyLevel d n) ^ d := by positivity
  calc ((9 : ℝ) ^ d + 1) * ((2 : ℝ) ^ heavyLevel d n) ^ d * (2 * n) * β
      ≤ ((9 : ℝ) ^ d + 1) * (4 : ℝ) ^ (2 * indDelta d * n * d) * (2 * n) * (4 * Y) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hkd hC9) le_rfl (by positivity)
          (by positivity)) hβ1 hβ0 (by positivity)
    _ = (8 * ((9 : ℝ) ^ d + 1) * n) * ((4 : ℝ) ^ (2 * indDelta d * n * d) * Y) := by ring
    _ ≤ (4 : ℝ) ^ (heavyEps d / 30 * n) * (4 : ℝ) ^ (3 * heavyEps d / 10 * n) := by
        rw [hexp]
        exact mul_le_mul hN hexp2 (by positivity) (by positivity)
    _ = _ := hfin
    _ ≤ _ := hg

/-- `n³ (t_n^ε + 3.89^n) < 3.9^n`. -/
theorem asym_pn (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hn : 1 ≤ n)
    (hN : 4 * (n : ℝ) ^ 3 ≤ ((39 / 10 : ℝ) / (389 / 100)) ^ n) :
    (n : ℝ) ^ 3 * (indScale t₀ n ^ heavyEps d + (389 / 100 : ℝ) ^ n) < (39 / 10 : ℝ) ^ n := by
  have hε := eps_pos hd
  set a : ℝ := (4 : ℝ) ^ heavyEps d with ha
  have ha2 : a ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 4 by norm_num)
      (show heavyEps d ≤ 1 / 2 by linarith [eps_le hd])
    have h2 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h2] at this
    exact this
  have ha1 : 1 ≤ a := (rpow4_pos_lt _ hε).le
  have hL : indScale t₀ n ^ heavyEps d ≤ 2 * (389 / 100 : ℝ) ^ n := by
    refine (tn_rpow_le ht4 ht1 hε.le).trans ?_
    have : (4 : ℝ) ^ (((n : ℝ) + 1) * heavyEps d) = a ^ n * a := by
      rw [ha, ← rpow4_nat, ← Real.rpow_add (by norm_num)]; congr 1; ring
    rw [this]
    have h1 : a ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) ha2 n
    have h2 : (2 : ℝ) ^ n ≤ (389 / 100 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    nlinarith [pow_pos (show (0 : ℝ) < a by linarith) n]
  have h3n : (0 : ℝ) < (389 / 100 : ℝ) ^ n := by positivity
  have hnn : (0 : ℝ) < (n : ℝ) ^ 3 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  calc (n : ℝ) ^ 3 * (indScale t₀ n ^ heavyEps d + (389 / 100 : ℝ) ^ n)
      ≤ (n : ℝ) ^ 3 * (3 * (389 / 100 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left (by linarith) hnn.le
    _ < ((39 / 10 : ℝ) / (389 / 100)) ^ n * (389 / 100 : ℝ) ^ n := by
        have : 3 * (n : ℝ) ^ 3 < ((39 / 10 : ℝ) / (389 / 100)) ^ n := by linarith
        nlinarith
    _ = _ := by rw [← mul_pow]; congr 1; norm_num

/-- All the asymptotic numerics hold for `n` large (uniformly in `t₀ ∈ (1, 4]` and `β ≥ 0`). -/
theorem step78_asym (hd : 5 ≤ d) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 → 16 ≤ heavyLevel d n → ∀ β : ℝ, 0 ≤ β →
      Step78Asym d t₀ n β := by
  have hε := eps_pos hd
  obtain ⟨N1, h1⟩ := eventually_rpow4 7 4 (show (0 : ℝ) < 3 / 4 by norm_num)
  obtain ⟨N2, h2⟩ := eventually_rpow4 (8 * ((9 : ℝ) ^ d + 1)) 1 (show 0 < heavyEps d / 30 by positivity)
  obtain ⟨N3, h3⟩ := eventually_mul_pow_le 4 3 (show (1 : ℝ) < (39 / 10 : ℝ) / (389 / 100) by norm_num)
  refine ⟨max (max N1 N2) (max N3 (900 * d + 1)), fun n hn t₀ ht1 ht4 hk β hβ0 => ?_⟩
  have hn1 : N1 ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : N2 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn3 : N3 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn4 : 900 * d + 1 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn1' : 1 ≤ n := by omega
  refine ⟨?_, ?_, fun hβ => ?_, ?_⟩
  · have := h1 n hn1
    exact asym_tk_le hd ht1 ht4 hk this hn1'
  · exact asym_L2 hd ht1 ht4 hk (by exact_mod_cast (by omega : 900 * d < n))
  · have := h2 n hn2
    exact asym_occ hd ht1 ht4 (by simpa using this) hβ0 hβ
  · exact asym_pn hd ht1 ht4 hn1' (by simpa using h3 n hn3)

end ElboimSly.Paper.Step

end
