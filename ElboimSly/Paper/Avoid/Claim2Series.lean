/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# ES22 §4, Claim 4.2: the elementary series estimates

ES22 Claim 4.2, "Sum" step and the arithmetic of the window bounds. All lemmas here are
statements about real numbers; the constants depend only on `d` (and on the constants `C`, `c` of
ES22 Claim 2.3).
-/

@[expose] public section

open Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

/-- The geometric ratio `q = 2^{-1/15}`. -/
noncomputable def qSeries : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 15)

theorem qSeries_pos : 0 < qSeries := Real.rpow_pos_of_pos (by norm_num) _

theorem qSeries_lt_one : qSeries < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem qSeries_pow (ℓ : ℕ) : qSeries ^ ℓ = ((2 : ℝ) ^ ℓ) ^ (-(1 : ℝ) / 15) := by
  unfold qSeries
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), mul_comm]

/-- A geometric tail: `∑_{ℓ₀ < ℓ ≤ n} q^ℓ ≤ q^{ℓ₀+1} / (1 - q)`. -/
theorem sum_Ioc_geom_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ℓ₀ n : ℕ) :
    ∑ ℓ ∈ Finset.Ioc ℓ₀ n, q ^ ℓ ≤ q ^ (ℓ₀ + 1) / (1 - q) := by
  have h1 : 0 < 1 - q := by linarith
  have hpos : 0 ≤ q ^ (ℓ₀ + 1) / (1 - q) := by positivity
  by_cases hn : ℓ₀ ≤ n
  · have key : ∀ m, ℓ₀ ≤ m → ∑ ℓ ∈ Finset.Ioc ℓ₀ m, q ^ ℓ ≤
        (q ^ (ℓ₀ + 1) - q ^ (m + 1)) / (1 - q) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ m hm ih =>
        rw [Finset.sum_Ioc_succ_top hm]
        have : (q ^ (ℓ₀ + 1) - q ^ (m + 1 + 1)) / (1 - q) =
            (q ^ (ℓ₀ + 1) - q ^ (m + 1)) / (1 - q) + q ^ (m + 1) := by
          field_simp; ring
        rw [this]; linarith
    refine (key n hn).trans ?_
    have : 0 ≤ q ^ (n + 1) := by positivity
    exact div_le_div_of_nonneg_right (by linarith) h1.le
  · rw [Finset.Ioc_eq_empty (by omega)]
    simpa using hpos

/-- `e^{-(ℓ-1)²} ≤ e · 2^{-ℓ} ≤ 3 q^ℓ`. -/
theorem exp_sq_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    Real.exp (-(((ℓ : ℝ) - 1) ^ 2)) ≤ 3 * qSeries ^ ℓ := by
  have h1 : ((ℓ : ℝ) - 1) ≤ ((ℓ : ℝ) - 1) ^ 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    have : (m : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) m
    simpa using this
  have h2 : Real.exp (-(((ℓ : ℝ) - 1) ^ 2)) ≤ Real.exp (-((ℓ : ℝ) - 1)) :=
    Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-((ℓ : ℝ) - 1)) = Real.exp 1 * (Real.exp (-1)) ^ ℓ := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have he1 : Real.exp (-1) ≤ qSeries := by
    unfold qSeries
    have : Real.exp (-1) ≤ (1 / 2 : ℝ) ^ (1 / 15 : ℝ) := by
      have hl : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_eq_one_div]
        apply one_div_le_one_div_of_le (by norm_num)
        have := Real.exp_one_gt_d9
        linarith
      refine hl.trans ?_
      calc (1 / 2 : ℝ) = (1 / 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 / 2 : ℝ) ^ (1 / 15 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    have e : (2 : ℝ) ^ (-(1 : ℝ) / 15) = (1 / 2 : ℝ) ^ (1 / 15 : ℝ) := by
      rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      congr 1; ring
    rwa [e]
  have he2 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; linarith
  calc Real.exp (-(((ℓ : ℝ) - 1) ^ 2)) ≤ Real.exp 1 * (Real.exp (-1)) ^ ℓ := h3 ▸ h2
    _ ≤ 3 * qSeries ^ ℓ := by
      gcongr

/-- Polynomial times `q^ℓ` is bounded. -/
theorem poly_mul_q_bdd (k : ℕ) : ∃ M : ℝ, 0 < M ∧ ∀ ℓ : ℕ, (ℓ : ℝ) ^ k * qSeries ^ ℓ ≤ M := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ k * qSeries ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one k (by
      rw [abs_of_pos qSeries_pos]; exact qSeries_lt_one)
  obtain ⟨M, hM⟩ := ht.bddAbove_range
  refine ⟨max M 1, lt_max_of_lt_right one_pos, fun ℓ => ?_⟩
  exact (hM ⟨ℓ, rfl⟩).trans (le_max_left _ _)

/-- `16^ℓ e^{-c ℓ²} ≤ M q^ℓ`. -/
theorem exp_quad_le {c : ℝ} (hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧ ∀ ℓ : ℕ, (16 : ℝ) ^ ℓ * Real.exp (-(c * (ℓ : ℝ) ^ 2)) ≤ M * qSeries ^ ℓ := by
  set a : ℝ := Real.log 16 + Real.log 2 / 15 with ha
  have hu : ∀ ℓ : ℕ, (16 : ℝ) ^ ℓ * Real.exp (-(c * (ℓ : ℝ) ^ 2)) / qSeries ^ ℓ =
      Real.exp ((ℓ : ℝ) * a - c * (ℓ : ℝ) ^ 2) := by
    intro ℓ
    have e1 : (16 : ℝ) ^ ℓ = Real.exp ((ℓ : ℝ) * Real.log 16) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
    have e2 : qSeries ^ ℓ = Real.exp (-((ℓ : ℝ) * (Real.log 2 / 15))) := by
      unfold qSeries
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
      congr 1; ring
    rw [e1, e2, ← Real.exp_add, ← Real.exp_sub]
    congr 1; rw [ha]; ring
  have ht : Tendsto (fun ℓ : ℕ => Real.exp ((ℓ : ℝ) * a - c * (ℓ : ℝ) ^ 2)) atTop (𝓝 0) := by
    refine (Real.tendsto_exp_atBot).comp ?_
    rw [tendsto_atBot]
    intro b
    have : ∀ᶠ ℓ : ℕ in atTop, (ℓ : ℝ) ≥ (|a| + |b| + 1) / c + 1 :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
    filter_upwards [this] with ℓ hℓ
    have h1 : (1 : ℝ) ≤ ℓ := by
      have : 0 ≤ (|a| + |b| + 1) / c := by positivity
      linarith
    have h2 : c * ℓ ≥ |a| + |b| + 1 + c := by
      have := mul_le_mul_of_nonneg_left hℓ hc.le
      rw [mul_add, mul_div_cancel₀ _ hc.ne'] at this
      linarith
    have h3 : a - c * ℓ ≤ -(|b| + 1) := by
      have := le_abs_self a
      linarith
    have : (ℓ : ℝ) * a - c * (ℓ : ℝ) ^ 2 = (ℓ : ℝ) * (a - c * ℓ) := by ring
    rw [this]
    have h4 : (ℓ : ℝ) * (a - c * ℓ) ≤ (ℓ : ℝ) * (-(|b| + 1)) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    have h5 : (ℓ : ℝ) * (-(|b| + 1)) ≤ -(|b| + 1) := by nlinarith [abs_nonneg b]
    linarith [neg_abs_le b]
  obtain ⟨M, hM⟩ := ht.bddAbove_range
  refine ⟨max M 1, lt_max_of_lt_right one_pos, fun ℓ => ?_⟩
  have hq : 0 < qSeries ^ ℓ := pow_pos qSeries_pos ℓ
  have := hM ⟨ℓ, rfl⟩
  simp only at this
  rw [← hu ℓ] at this
  rw [div_le_iff₀ hq] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq.le)

/-- The arithmetic of the integer-time bound: for `d ≥ 5` and `ℓ ≥ 1`,
`4^ℓ · (3ℓ²)^d · (2ℓ² 2^ℓ)^{8/3} · (4^{ℓ-1})^{-d/2+1/10} ≤ K ℓ^{2d+6} q^{2ℓ}`. -/
theorem box_arith (d : ℕ) (hd : 5 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
      (4 : ℝ) ^ ℓ * ((3 * (ℓ : ℝ) ^ 2) ^ d * (2 * (ℓ : ℝ) ^ 2 * 2 ^ ℓ) ^ (8 / 3 : ℝ)) *
          ((4 : ℝ) ^ (ℓ - 1)) ^ (-(d : ℝ) / 2 + 1 / 10) ≤
        K * (ℓ : ℝ) ^ (2 * d + 6) * (qSeries ^ ℓ) ^ 2 := by
  set e : ℝ := (d : ℝ) / 2 - 1 / 10 with he
  refine ⟨3 ^ d * 2 ^ (8 / 3 : ℝ) * 4 ^ e, by positivity, fun ℓ hℓ => ?_⟩
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  set x : ℝ := (2 : ℝ) ^ ℓ with hx
  have hx1 : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hx0 : 0 < x := by linarith
  have h4l : (4 : ℝ) ^ ℓ = x ^ 2 := by rw [hx, ← pow_mul, mul_comm, pow_mul]; norm_num
  have h4l1 : (4 : ℝ) ^ (ℓ - 1) = x ^ 2 / 4 := by
    have : (4 : ℝ) ^ ℓ = 4 ^ (ℓ - 1) * 4 := by
      rw [← pow_succ]; congr 1; omega
    rw [eq_div_iff (by norm_num), ← h4l, this]
  have hq2 : (qSeries ^ ℓ) ^ 2 = x ^ (-(2 : ℝ) / 15) := by
    rw [qSeries_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1; push_cast; ring
  rw [h4l, h4l1, hq2]
  have h3 : (x ^ 2 / 4) ^ (-(d : ℝ) / 2 + 1 / 10) = x ^ (-(d : ℝ) + 1 / 5) * 4 ^ e := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul hx0.le]
    have : (4 : ℝ) ^ (-(d : ℝ) / 2 + 1 / 10) = (4 ^ e)⁻¹ := by
      rw [← Real.rpow_neg (by norm_num)]; congr 1; rw [he]; ring
    rw [this]
    have : (↑(2 : ℕ) : ℝ) * (-(d : ℝ) / 2 + 1 / 10) = -(d : ℝ) + 1 / 5 := by push_cast; ring
    rw [this, div_eq_mul_inv]
    have hp : (0 : ℝ) < 4 ^ e := by positivity
    field_simp
  have h2 : (2 * (ℓ : ℝ) ^ 2 * x) ^ (8 / 3 : ℝ) ≤ 2 ^ (8 / 3 : ℝ) * (ℓ : ℝ) ^ 6 * x ^ (8 / 3 : ℝ) := by
    rw [Real.mul_rpow (by positivity) hx0.le, Real.mul_rpow (by norm_num) (by positivity)]
    have : ((ℓ : ℝ) ^ 2) ^ (8 / 3 : ℝ) ≤ (ℓ : ℝ) ^ 6 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hℓ1
      push_cast; norm_num
    gcongr
  have hxe : x ^ 2 * x ^ (8 / 3 : ℝ) * x ^ (-(d : ℝ) + 1 / 5) ≤ x ^ (-(2 : ℝ) / 15) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    have : (5 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast; linarith
  have hpow : ((3 : ℝ) * (ℓ : ℝ) ^ 2) ^ d = 3 ^ d * (ℓ : ℝ) ^ (2 * d) := by
    rw [mul_pow, ← pow_mul]
  rw [h3, hpow]
  calc x ^ 2 * (3 ^ d * (ℓ : ℝ) ^ (2 * d) * (2 * (ℓ : ℝ) ^ 2 * x) ^ (8 / 3 : ℝ)) *
        (x ^ (-(d : ℝ) + 1 / 5) * 4 ^ e)
      ≤ x ^ 2 * (3 ^ d * (ℓ : ℝ) ^ (2 * d) * (2 ^ (8 / 3 : ℝ) * (ℓ : ℝ) ^ 6 * x ^ (8 / 3 : ℝ))) *
        (x ^ (-(d : ℝ) + 1 / 5) * 4 ^ e) := by gcongr
    _ = 3 ^ d * 2 ^ (8 / 3 : ℝ) * 4 ^ e * (ℓ : ℝ) ^ (2 * d + 6) *
        (x ^ 2 * x ^ (8 / 3 : ℝ) * x ^ (-(d : ℝ) + 1 / 5)) := by rw [pow_add]; ring
    _ ≤ 3 ^ d * 2 ^ (8 / 3 : ℝ) * 4 ^ e * (ℓ : ℝ) ^ (2 * d + 6) * x ^ (-(2 : ℝ) / 15) := by
        gcongr

end ElboimSly.Paper

end
