/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Elementary inequalities for the hitting estimates

Elementary inequalities. Throughout `d ≥ 3` is a natural
number and `d/2` is read as a real exponent. The sums in (a) and (b) are stated for all finite
partial sums, which is what the union bounds need.

* `sum_add_mul_rpow_le`: (a);
* `sum_Ioc_mul_rpow_le`: (b);
* `rpow_mul_exp_neg_div_le`: (c);
* `pow_mul_exp_neg_sq_le`: (d).
-/

@[expose] public section

namespace ElboimSly.Brownian

open Finset

/-- One step of the integral comparison: for `0 < y < x` and `p > 1`,
`(p - 1) (x - y) x^{-p} ≤ y^{1-p} - x^{1-p}`. -/
lemma step_rpow_le {p : ℝ} (hp : 1 < p) {y x : ℝ} (hy : 0 < y) (hyx : y < x) :
    (p - 1) * (x - y) * x ^ (-p) ≤ y ^ (1 - p) - x ^ (1 - p) := by
  have hderiv : ∀ t ∈ Set.Ioo y x, HasDerivAt (fun t : ℝ => t ^ (1 - p)) ((1 - p) * t ^ (-p)) t := by
    intro t ht
    have ht0 : 0 < t := hy.trans ht.1
    have := Real.hasDerivAt_rpow_const (x := t) (p := 1 - p) (Or.inl ht0.ne')
    convert this using 2
    ring_nf
  have hcont : ContinuousOn (fun t : ℝ => t ^ (1 - p)) (Set.Icc y x) :=
    fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (hy.trans_le ht.1).ne')).continuousWithinAt
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (1 - p))
    (fun t => (1 - p) * t ^ (-p)) hyx hcont hderiv
  have hc0 : 0 < c := hy.trans hc.1
  have hxy : 0 < x - y := sub_pos.2 hyx
  have e : x ^ (1 - p) - y ^ (1 - p) = (1 - p) * c ^ (-p) * (x - y) := by
    field_simp at hc'
    linarith
  have hmono : x ^ (-p) ≤ c ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hc0 hc.2.le (by linarith)
  have hp1 : 0 < p - 1 := sub_pos.2 hp
  nlinarith [mul_le_mul_of_nonneg_left hmono (mul_nonneg hp1.le hxy.le)]

/-- Elementary inequalities (a), partial sums. For `a, h > 0` and every `n`,
`∑_{k<n} (a + k h)^{-d/2} ≤ a^{-d/2} + 2/((d-2) h) a^{1-d/2}`. -/
lemma sum_add_mul_rpow_le {d : ℕ} (hd : 3 ≤ d) {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (n : ℕ) :
    ∑ k ∈ range n, (a + k * h) ^ (-(d : ℝ) / 2) ≤
      a ^ (-(d : ℝ) / 2) + 2 / ((d - 2) * h) * a ^ (1 - (d : ℝ) / 2) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set p : ℝ := (d : ℝ) / 2 with hp
  have hp1 : 1 < p := by rw [hp]; linarith
  have hneg : -(d : ℝ) / 2 = -p := by rw [hp]; ring
  rw [hneg]
  have hC : 2 / ((d - 2) * h) = 1 / ((p - 1) * h) := by
    rw [hp]; field_simp
  rw [hC]
  have hp1' : 0 < p - 1 := sub_pos.2 hp1
  -- telescoping bound for the terms with `k ≥ 1`
  have key : ∀ m : ℕ, ∑ k ∈ range m, (a + (k + 1 : ℕ) * h) ^ (-p) ≤
      1 / ((p - 1) * h) * (a ^ (1 - p) - (a + m * h) ^ (1 - p)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      have hy : 0 < a + m * h := by positivity
      have hyx : a + m * h < a + ((m + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
      have hs := step_rpow_le hp1 hy hyx
      have hdiff : a + ((m + 1 : ℕ) : ℝ) * h - (a + m * h) = h := by push_cast; ring
      rw [hdiff] at hs
      have : (a + ((m + 1 : ℕ) : ℝ) * h) ^ (-p) ≤
          1 / ((p - 1) * h) * ((a + m * h) ^ (1 - p) - (a + ((m + 1 : ℕ) : ℝ) * h) ^ (1 - p)) := by
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
        nlinarith
      have e : (a + (((m + 1 : ℕ) : ℝ)) * h) = a + ((m : ℝ) + 1) * h := by push_cast; ring
      have e2 : (a + ((m + 1 : ℕ) : ℝ) * h) = a + ((m + 1 : ℕ) : ℝ) * h := rfl
      calc _ ≤ 1 / ((p - 1) * h) * (a ^ (1 - p) - (a + m * h) ^ (1 - p)) +
            1 / ((p - 1) * h) *
              ((a + m * h) ^ (1 - p) - (a + ((m + 1 : ℕ) : ℝ) * h) ^ (1 - p)) := by
            refine add_le_add ih ?_
            simpa [Nat.cast_add] using this
        _ = _ := by ring
  cases n with
  | zero =>
    simp only [range_zero, sum_empty]
    positivity
  | succ n =>
    rw [sum_range_succ']
    have h0 : ∑ k ∈ range n, (a + ((k + 1 : ℕ) : ℝ) * h) ^ (-p) ≤
        1 / ((p - 1) * h) * a ^ (1 - p) := by
      refine (key n).trans ?_
      have : 0 ≤ (a + n * h) ^ (1 - p) := by positivity
      have : 0 ≤ 1 / ((p - 1) * h) := by positivity
      nlinarith [Real.rpow_nonneg (show 0 ≤ a + n * h by positivity) (1 - p)]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have e : ∀ k : ℕ, a + ((k + 1 : ℕ) : ℝ) * h = a + ((k + 1 : ℕ) : ℝ) * h := fun _ => rfl
    calc _ = ∑ k ∈ range n, (a + ((k + 1 : ℕ) : ℝ) * h) ^ (-p) + a ^ (-p) := by
          simp [Nat.cast_add, Nat.cast_one]
      _ ≤ _ := by linarith

/-- Elementary inequalities (b), partial sums. For `h > 0` and an integer `K ≥ 1`,
`∑_{K < k ≤ K+n} (k h)^{-d/2} ≤ 2/(d-2) h^{-d/2} K^{1-d/2}`. -/
lemma sum_Ioc_mul_rpow_le {d : ℕ} (hd : 3 ≤ d) {h : ℝ} (hh : 0 < h) {K : ℕ} (hK : 1 ≤ K) (n : ℕ) :
    ∑ k ∈ range n, (((K + 1 + k : ℕ) : ℝ) * h) ^ (-(d : ℝ) / 2) ≤
      2 / (d - 2) * h ^ (-(d : ℝ) / 2) * (K : ℝ) ^ (1 - (d : ℝ) / 2) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set p : ℝ := (d : ℝ) / 2 with hp
  have hp1 : 1 < p := by rw [hp]; linarith
  have hneg : -(d : ℝ) / 2 = -p := by rw [hp]; ring
  rw [hneg]
  have hp1' : 0 < p - 1 := sub_pos.2 hp1
  have hC : 2 / ((d : ℝ) - 2) = 1 / (p - 1) := by rw [hp]; field_simp
  rw [hC]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have key : ∀ m : ℕ, ∑ k ∈ range m, (((K + 1 + k : ℕ) : ℝ)) ^ (-p) ≤
      1 / (p - 1) * ((K : ℝ) ^ (1 - p) - ((K + m : ℕ) : ℝ) ^ (1 - p)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      have hy : 0 < ((K + m : ℕ) : ℝ) := by positivity
      have hyx : ((K + m : ℕ) : ℝ) < ((K + 1 + m : ℕ) : ℝ) := by push_cast; linarith
      have hs := step_rpow_le hp1 hy hyx
      have hdiff : ((K + 1 + m : ℕ) : ℝ) - ((K + m : ℕ) : ℝ) = 1 := by push_cast; ring
      rw [hdiff] at hs
      have e : ((K + (m + 1) : ℕ) : ℝ) = ((K + 1 + m : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      have : ((K + 1 + m : ℕ) : ℝ) ^ (-p) ≤
          1 / (p - 1) * (((K + m : ℕ) : ℝ) ^ (1 - p) - ((K + 1 + m : ℕ) : ℝ) ^ (1 - p)) := by
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hp1']
        nlinarith
      calc _ ≤ 1 / (p - 1) * ((K : ℝ) ^ (1 - p) - ((K + m : ℕ) : ℝ) ^ (1 - p)) +
            1 / (p - 1) * (((K + m : ℕ) : ℝ) ^ (1 - p) - ((K + 1 + m : ℕ) : ℝ) ^ (1 - p)) :=
            add_le_add ih this
        _ = _ := by ring
  have hh' : ∀ k : ℕ, (((K + 1 + k : ℕ) : ℝ) * h) ^ (-p) =
      h ^ (-p) * ((K + 1 + k : ℕ) : ℝ) ^ (-p) := fun k => by
    rw [mul_comm, Real.mul_rpow hh.le (by positivity)]
  simp_rw [hh']
  rw [← mul_sum]
  have := key n
  have hnn : 0 ≤ ((K + n : ℕ) : ℝ) ^ (1 - p) := by positivity
  have hpos : 0 ≤ h ^ (-p) := by positivity
  calc h ^ (-p) * ∑ k ∈ range n, ((K + 1 + k : ℕ) : ℝ) ^ (-p)
      ≤ h ^ (-p) * (1 / (p - 1) * ((K : ℝ) ^ (1 - p))) := by
        refine mul_le_mul_of_nonneg_left (this.trans ?_) hpos
        have : 0 ≤ 1 / (p - 1) := by positivity
        nlinarith
    _ = _ := by ring

/-- The basic one-variable bound: `v^p e^{-v} ≤ (p/e)^p` for `v > 0` and `p > 0`. -/
lemma rpow_mul_exp_neg_le {p : ℝ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    v ^ p * Real.exp (-v) ≤ (p / Real.exp 1) ^ p := by
  have hl : Real.log (v / p) ≤ v / p - 1 := Real.log_le_sub_one_of_pos (div_pos hv hp)
  have h2 : p * (Real.log v - Real.log p) ≤ v - p := by
    rw [Real.log_div hv.ne' hp.ne'] at hl
    have := mul_le_mul_of_nonneg_left hl hp.le
    have e : p * (v / p - 1) = v - p := by field_simp
    linarith
  have hpe : 0 < p / Real.exp 1 := div_pos hp (Real.exp_pos 1)
  rw [Real.rpow_def_of_pos hv, ← Real.exp_add, Real.rpow_def_of_pos hpe,
    Real.log_div hp.ne' (Real.exp_pos 1).ne', Real.log_exp]
  refine Real.exp_le_exp.2 ?_
  nlinarith

/-- Elementary inequalities (c), the upper bound: for `b > 0` and `u > 0`,
`u^{-d/2} e^{-b/u} ≤ (d/(2 e b))^{d/2}`. -/
lemma rpow_mul_exp_neg_div_le {d : ℕ} (hd : 0 < d) {b u : ℝ} (hb : 0 < b) (hu : 0 < u) :
    u ^ (-(d : ℝ) / 2) * Real.exp (-b / u) ≤ ((d : ℝ) / (2 * Real.exp 1 * b)) ^ ((d : ℝ) / 2) := by
  have hp : 0 < (d : ℝ) / 2 := by positivity
  have h := rpow_mul_exp_neg_le hp (div_pos hb hu)
  have e1 : u ^ (-(d : ℝ) / 2) = (b / u) ^ ((d : ℝ) / 2) * (b ^ ((d : ℝ) / 2))⁻¹ := by
    rw [Real.div_rpow hb.le hu.le, div_mul_eq_mul_div, mul_inv_cancel₀ (by positivity)]
    rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hu.le]
    field_simp
  have e2 : ((d : ℝ) / (2 * Real.exp 1 * b)) ^ ((d : ℝ) / 2) =
      (((d : ℝ) / 2) / Real.exp 1) ^ ((d : ℝ) / 2) * (b ^ ((d : ℝ) / 2))⁻¹ := by
    rw [← Real.inv_rpow hb.le, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  have hbinv : 0 ≤ (b ^ ((d : ℝ) / 2))⁻¹ := by positivity
  have e3 : -b / u = -(b / u) := by ring
  rw [e1, e2, e3]
  calc _ = ((b / u) ^ ((d : ℝ) / 2) * Real.exp (-(b / u))) * (b ^ ((d : ℝ) / 2))⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h hbinv

/-- Elementary inequalities (d), the upper bound: `x^d e^{-x²/32} ≤ (16 d / e)^{d/2}` for `x > 0`. -/
lemma pow_mul_exp_neg_sq_le {d : ℕ} (hd : 0 < d) {x : ℝ} (hx : 0 < x) :
    x ^ d * Real.exp (-x ^ 2 / 32) ≤ (16 * d / Real.exp 1) ^ ((d : ℝ) / 2) := by
  have hp : 0 < (d : ℝ) / 2 := by positivity
  have h := rpow_mul_exp_neg_le hp (show 0 < x ^ 2 / 32 by positivity)
  have e1 : x ^ d = (x ^ 2 / 32) ^ ((d : ℝ) / 2) * 32 ^ ((d : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity), div_mul_cancel₀ _ (by norm_num),
      ← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x d]
    congr 1; push_cast; ring
  have e2 : (16 * (d : ℝ) / Real.exp 1) ^ ((d : ℝ) / 2) =
      (((d : ℝ) / 2) / Real.exp 1) ^ ((d : ℝ) / 2) * 32 ^ ((d : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1; ring
  have e3 : -x ^ 2 / 32 = -(x ^ 2 / 32) := by ring
  rw [e1, e2, e3]
  calc _ = ((x ^ 2 / 32) ^ ((d : ℝ) / 2) * Real.exp (-(x ^ 2 / 32))) * 32 ^ ((d : ℝ) / 2) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

end ElboimSly.Brownian
