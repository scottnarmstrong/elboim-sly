/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Numerical inequalities for x1θ with the explicit threshold ell_0(d)=max100,10d

X1θ with the explicit threshold ell_0(d)=max100,10d (Part II).

We use the threshold `ℓ ≥ max (10^5) (10 d)` (the written proof's `max 100 (10 d)` is also valid, but
this larger threshold makes the elementary estimates below simpler).
-/

@[expose] public section

namespace ElboimSly.StrongApprox

lemma four_le_log {ℓ : ℝ} (hℓ : 100 ≤ ℓ) : 4 ≤ Real.log ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  rw [Real.le_log_iff_exp_le hℓ0]
  have h := Real.exp_one_lt_d9
  have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h1 : 0 < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ h1.le h.le 4
  norm_num at h2
  linarith

lemma log_cube_le {ℓ : ℝ} (hℓ : 46656 ≤ ℓ) : Real.log ℓ ^ 3 ≤ ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  set L := Real.log ℓ with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have h1 : L / 6 ≤ Real.exp (L / 6) := by linarith [Real.add_one_le_exp (L / 6)]
  have h2 : (L / 6) ^ 6 ≤ ℓ := by
    calc (L / 6) ^ 6 ≤ Real.exp (L / 6) ^ 6 := pow_le_pow_left₀ (by positivity) h1 6
      _ = Real.exp L := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      _ = ℓ := Real.exp_log hℓ0
  have h3 : L ^ 6 ≤ 46656 * ℓ := by
    have : (L / 6) ^ 6 = L ^ 6 / 46656 := by ring
    rw [this, div_le_iff₀ (by norm_num)] at h2
    linarith
  have h4 : (L ^ 3) ^ 2 ≤ ℓ ^ 2 := by
    calc (L ^ 3) ^ 2 = L ^ 6 := by ring
      _ ≤ 46656 * ℓ := h3
      _ ≤ ℓ * ℓ := by nlinarith
      _ = ℓ ^ 2 := by ring
  exact le_of_sq_le_sq h4 hℓ0.le |>.trans le_rfl

lemma thr_le {M L ℓ : ℝ} (hℓ : 0 < ℓ) (_hM1 : 1 ≤ M) (hM : M ≤ L ^ 3) (hL : 4 ≤ L) :
    59 * M * ℓ ^ (1 / 4 : ℝ) * (2 * L ^ 3) ^ (3 / 4 : ℝ) ≤ ℓ ^ ((1 : ℝ) / 4) * L ^ 12 := by
  have hL0 : 0 < L := by linarith
  set E : ℝ := L ^ (9 / 4 : ℝ) with hE
  have hE0 : 0 < E := Real.rpow_pos_of_pos hL0 _
  have hℓ4 : 0 < ℓ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hℓ _
  have h1 : (2 * L ^ 3) ^ (3 / 4 : ℝ) = 2 ^ (3 / 4 : ℝ) * E := by
    rw [Real.mul_rpow (by norm_num) (by positivity), hE, ← Real.rpow_natCast L 3,
      ← Real.rpow_mul hL0.le]
    norm_num
  have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h3 : L ^ 12 = L ^ 3 * E * L ^ (27 / 4 : ℝ) := by
    rw [hE, ← Real.rpow_natCast L 3, ← Real.rpow_natCast L 12, ← Real.rpow_add hL0,
      ← Real.rpow_add hL0]
    norm_num
  have h4 : (4096 : ℝ) ≤ L ^ (27 / 4 : ℝ) := by
    calc (4096 : ℝ) = 4 ^ (6 : ℕ) := by norm_num
      _ ≤ L ^ (6 : ℕ) := pow_le_pow_left₀ (by norm_num) hL 6
      _ = L ^ (6 : ℝ) := (Real.rpow_natCast L 6).symm
      _ ≤ L ^ (27 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h5 : (2 : ℝ) ^ (3 / 4 : ℝ) > 0 := by positivity
  have hone : (1 : ℝ) / 4 = 1 / 4 := rfl
  rw [h1, h3, hone]
  calc 59 * M * ℓ ^ (1 / 4 : ℝ) * (2 ^ (3 / 4 : ℝ) * E)
      ≤ 59 * L ^ 3 * ℓ ^ (1 / 4 : ℝ) * (2 * E) := by gcongr
    _ = 118 * (L ^ 3 * E) * ℓ ^ (1 / 4 : ℝ) := by ring
    _ ≤ L ^ (27 / 4 : ℝ) * (L ^ 3 * E) * ℓ ^ (1 / 4 : ℝ) := by
        gcongr; linarith
    _ = ℓ ^ (1 / 4 : ℝ) * (L ^ 3 * E * L ^ (27 / 4 : ℝ)) := by ring

lemma tail_le {d ℓ : ℕ} (hℓ0 : 0 < (ℓ : ℝ)) (h10d : 10 * d ≤ ℓ) (hL4 : 4 ≤ Real.log ℓ) :
    10 * (d : ℝ) * ℓ * Real.exp (-(2 * Real.log ℓ ^ 3)) ≤ Real.exp (-(Real.log ℓ ^ 3)) := by
  set L := Real.log ℓ with hL
  have hexp : Real.exp L = ℓ := Real.exp_log hℓ0
  have h10 : (10 : ℝ) * d ≤ ℓ := by exact_mod_cast h10d
  have h1 : 10 * (d : ℝ) * ℓ ≤ Real.exp (L ^ 3) := by
    calc 10 * (d : ℝ) * ℓ ≤ ℓ * ℓ := by nlinarith
      _ = Real.exp (2 * L) := by rw [← hexp, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (L ^ 3) := Real.exp_le_exp.2 (by nlinarith [sq_nonneg L])
  have h2 : Real.exp (-(2 * L ^ 3)) = Real.exp (-(L ^ 3)) * Real.exp (-(L ^ 3)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  have h3 : Real.exp (L ^ 3) * Real.exp (-(L ^ 3)) = 1 := by
    rw [← Real.exp_add]; simp
  calc 10 * (d : ℝ) * ℓ * (Real.exp (-(L ^ 3)) * Real.exp (-(L ^ 3)))
      ≤ Real.exp (L ^ 3) * (Real.exp (-(L ^ 3)) * Real.exp (-(L ^ 3))) := by gcongr
    _ = Real.exp (-(L ^ 3)) := by rw [← mul_assoc, h3, one_mul]

end ElboimSly.StrongApprox
