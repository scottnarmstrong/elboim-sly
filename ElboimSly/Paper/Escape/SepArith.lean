/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Real-number inequalities for old history is far

Pure arithmetic: the case inequalities of the written proof proof of old history is far, with the geometric
quantities abstracted into real variables.  `T = √t`, `a = 2^j`, `e = 2^{-n}`.
-/

@[expose] public section

namespace ElboimSly.Paper

/-- Both points in the first half, phases `i` and `i' ≤ i - 2`. -/
lemma ar_FF {a T e e' l l' R R' : ℝ} (hTa : T ≤ a) (he : 0 < e) (he' : e' ≤ e / 4)
    (hl : e ≤ l) (hl' : l' ≤ 22 / 10 * e') (hR : R ≤ T / 16 * e) (hR' : R' ≤ T / 16 * e')
    (hQ : 100 ≤ e * T) (hT : 0 ≤ T) : 2 ≤ (l - l') * (a / 4) - R - R' := by
  have h1 : (45 / 100) * e ≤ l - l' := by linarith
  have ha : 0 ≤ a := le_trans hT hTa
  have h2 : (45 / 100) * e * (a / 4) ≤ (l - l') * (a / 4) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : e * T ≤ e * a := mul_le_mul_of_nonneg_left hTa he.le
  have h5 : T / 16 * e' ≤ T / 16 * (e / 4) := mul_le_mul_of_nonneg_left he' (by linarith)
  nlinarith

/-- Mixed case, `i ≥ m + 2`: use `1 - μ ≥ 1/2`. -/
lemma ar_mixed_far {a T mu R R' : ℝ} (hTa : T ≤ a) (ha : 2 ^ 20 ≤ a) (hmu : mu ≤ 1 / 2)
    (hR : R ≤ T / 256) (hR' : R' ≤ T / 32) (_hT : 0 ≤ T) :
    2 ≤ (1 - mu) * (a / 12 - 1) - R - R' := by
  have h1 : (1 / 2) * (a / 12 - 1) ≤ (1 - mu) * (a / 12 - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith

/-- Mixed case, `i ∈ {m, m+1}`: use `1 - λ' ≥ 0.45`. -/
lemma ar_mixed_near {a T l' R R' : ℝ} (hTa : T ≤ a) (ha : 2 ^ 20 ≤ a) (hl' : l' ≤ 55 / 100)
    (hR : R ≤ T / 64) (hR' : R' ≤ T / 64) (_hT : 0 ≤ T) :
    2 ≤ (1 - l') * (a / 12 - 1) - R - R' := by
  have h1 : (45 / 100) * (a / 12 - 1) ≤ (1 - l') * (a / 12 - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith

/-- Both points in the second half. -/
lemma ar_SS {a T e e' mu mu' R R' : ℝ} (hTa : T ≤ a) (he : 0 < e) (he' : e' ≤ 1)
    (he'0 : 0 < e') (hee : e ≤ e' / 4) (hmu' : 77 / 100 * e' ≤ mu') (hmu : mu ≤ 2 * e)
    (hR : R ≤ T / 64 * e) (hR' : R' ≤ T / 64 * e') (hQ : 1000 ≤ e' * T) (hT : 0 ≤ T) :
    2 ≤ (mu' - mu) * (a / 4 - 1) - R - R' := by
  have ha : 0 ≤ a := le_trans hT hTa
  have h1 : (27 / 100) * e' ≤ mu' - mu := by linarith
  have h3 : e' * T ≤ e' * a := mul_le_mul_of_nonneg_left hTa he'0.le
  have h2 : (27 / 100) * e' * (a / 4 - 1) ≤ (mu' - mu) * (a / 4 - 1) :=
    mul_le_mul_of_nonneg_right h1 (by nlinarith)
  have h5 : T / 64 * e ≤ T / 64 * (e' / 4) := mul_le_mul_of_nonneg_left hee (by linarith)
  nlinarith

/-- `i' = 0`, `s` in the first half: `λ a/4 - R ≥ (3/16) a λ ≥ (3/16) √β`. -/
lemma ar_far_first {a T l R b : ℝ} (_hTa : T ≤ a) (_hT : 0 ≤ T) (hl : b / a ≤ l) (ha : 0 < a)
    (hR : R ≤ a / 16 * l) (_hb : 0 ≤ b) : 3 / 16 * b ≤ l * (a / 4) - R := by
  have : b ≤ l * a := by rwa [div_le_iff₀ ha] at hl
  nlinarith

end ElboimSly.Paper
