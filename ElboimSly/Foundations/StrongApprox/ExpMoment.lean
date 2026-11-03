/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# From a geometric tail to an exponential moment

Exit times of Brownian motion from symmetric intervals (d) (Part II).

If `P(τ > k h) ≤ (2/5)^k` for all `k : ℕ`, with `h > 0`, and `τ < ∞` a.s., then
`E exp(τ / (9h/4)) ≤ 6`. (With `h = 16 r²` this reads `E exp(τ/(36 r²)) ≤ 6`.)
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma exp_four_ninths_le : Real.exp (4 / 9) ≤ 17 / 10 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 := Real.exp_pos (1 / 2)
  have h4 : Real.exp (1 / 2) ≤ 17 / 10 := by nlinarith
  exact (Real.exp_le_exp.2 (by norm_num)).trans h4

lemma geom_identity (a : ℝ) (N : ℕ) :
    a ^ (N + 1) = a + (a - 1) * ∑ k ∈ Finset.range N, a ^ (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    linear_combination ih

lemma exp_div_le_pow {x h : ℝ} (hh : 0 < h) (_hx : 0 ≤ x) :
    Real.exp (x / (9 / 4 * h)) ≤ Real.exp (4 / 9) ^ (⌊x / h⌋₊ + 1) := by
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.2 ?_
  have h1 : x / h < ⌊x / h⌋₊ + 1 := Nat.lt_floor_add_one _
  have e : x / (9 / 4 * h) = (x / h) * (4 / 9) := by field_simp
  rw [e]
  push_cast
  nlinarith

lemma final_numeric {a : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 17 / 10) :
    a + (a - 1) * (a * (1 - 2 / 5 * a)⁻¹) ≤ 6 := by
  have h1 : 0 < 1 - 2 / 5 * a := by linarith
  have : (a - 1) * (a * (1 - 2 / 5 * a)⁻¹) = (a - 1) * a / (1 - 2 / 5 * a) := by
    field_simp
  have key : (a - 1) * a / (1 - 2 / 5 * a) ≤ 6 - a := by
    rw [div_le_iff₀ h1]; nlinarith
  rw [this]; linarith

/-- Exit times of Brownian motion from symmetric intervals (d), from the tail bound. -/
theorem lintegral_exp_le_of_tail [IsProbabilityMeasure P] {τ : Ω → ℝ≥0∞} (hτ : Measurable τ)
    (_hfin : ∀ᵐ ω ∂P, τ ω < ⊤) {h : ℝ≥0} (hh : 0 < h)
    (htail : ∀ k : ℕ, P {ω | ((k * h : ℝ≥0) : ℝ≥0∞) < τ ω} ≤ (2 / 5) ^ k) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp ((τ ω).toReal / (9 / 4 * h))) ∂P ≤ 6 := by
  set a : ℝ := Real.exp (4 / 9) with ha
  have ha1 : 1 ≤ a := Real.one_le_exp (by norm_num)
  have ha2 : a ≤ 17 / 10 := exp_four_ninths_le
  have hhR : (0 : ℝ) < h := hh
  set N : Ω → ℕ := fun ω => ⌊(τ ω).toReal / h⌋₊ with hN
  have hNm : Measurable N :=
    Nat.measurable_floor.comp ((ENNReal.measurable_toReal.comp hτ).div_const _)
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp ((τ ω).toReal / (9 / 4 * h))) ≤
      ENNReal.ofReal a + ENNReal.ofReal (a - 1) *
        ∑' k : ℕ, {ω | k < N ω}.indicator (fun _ => ENNReal.ofReal (a ^ (k + 1))) ω := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have h1 := exp_div_le_pow (x := (τ ω).toReal) hhR ENNReal.toReal_nonneg
    have h2 := geom_identity a (N ω)
    have hS : 0 ≤ ∑ k ∈ Finset.range (N ω), a ^ (k + 1) :=
      Finset.sum_nonneg fun k _ => by positivity
    have h3 : ENNReal.ofReal (Real.exp ((τ ω).toReal / (9 / 4 * h))) ≤
        ENNReal.ofReal (a + (a - 1) * ∑ k ∈ Finset.range (N ω), a ^ (k + 1)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← h2]; exact h1
    refine h3.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) (mul_nonneg (by linarith) hS),
      ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
    congr 2
    rw [tsum_eq_sum (s := Finset.range (N ω))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Set.indicator_of_mem]
      simpa using hk
    · intro k hk
      rw [Set.indicator_of_notMem]
      simpa using hk
  have hmeasI : ∀ k : ℕ, Measurable ({ω | k < N ω}.indicator
      (fun _ => ENNReal.ofReal (a ^ (k + 1)))) := fun k =>
    measurable_const.indicator (measurableSet_lt measurable_const hNm)
  have hterm : ∀ k : ℕ, ENNReal.ofReal (a ^ (k + 1)) * P {ω | k < N ω} ≤
      ENNReal.ofReal (a ^ (k + 1) * (2 / 5) ^ k) := by
    intro k
    have hsub : {ω | k < N ω} ⊆ {ω | ((k * h : ℝ≥0) : ℝ≥0∞) < τ ω} := by
      intro ω hk
      have hk' : k < ⌊(τ ω).toReal / h⌋₊ := hk
      have h1 : ((k : ℝ) + 1) ≤ (τ ω).toReal / h := by
        have := (Nat.le_floor_iff (div_nonneg ENNReal.toReal_nonneg hhR.le)).1
          (Nat.succ_le_of_lt hk')
        simpa using this
      have hne : τ ω ≠ ⊤ := by
        intro htop
        rw [htop] at h1
        simp at h1
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      show ((k * h : ℝ≥0) : ℝ≥0∞) < τ ω
      lift τ ω to ℝ≥0 using hne with t ht
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
      rw [ENNReal.coe_toReal, le_div_iff₀ hhR] at h1
      push_cast
      nlinarith
    calc ENNReal.ofReal (a ^ (k + 1)) * P {ω | k < N ω}
        ≤ ENNReal.ofReal (a ^ (k + 1)) * (2 / 5) ^ k := by
          gcongr; exact (measure_mono hsub).trans (htail k)
      _ = ENNReal.ofReal (a ^ (k + 1) * (2 / 5) ^ k) := by
          have e1 : ENNReal.ofReal ((2 / 5 : ℝ) ^ k) = (2 / 5 : ℝ≥0∞) ^ k := by
            rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
            simp
          rw [ENNReal.ofReal_mul (by positivity), e1]
  have hq : 2 / 5 * a < 1 := by linarith
  have hsum : Summable fun k : ℕ => a ^ (k + 1) * (2 / 5) ^ k := by
    have : (fun k : ℕ => a ^ (k + 1) * (2 / 5) ^ k) = fun k => a * (2 / 5 * a) ^ k := by
      funext k; rw [mul_pow, pow_succ]; ring
    rw [this]
    exact (summable_geometric_of_lt_one (by positivity) hq).mul_left a
  have hval : ∑' k : ℕ, a ^ (k + 1) * (2 / 5) ^ k = a * (1 - 2 / 5 * a)⁻¹ := by
    have : (fun k : ℕ => a ^ (k + 1) * (2 / 5) ^ k) = fun k => a * (2 / 5 * a) ^ k := by
      funext k; rw [mul_pow, pow_succ]; ring
    rw [this, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hq]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((τ ω).toReal / (9 / 4 * h))) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal a + ENNReal.ofReal (a - 1) *
        ∑' k : ℕ, {ω | k < N ω}.indicator (fun _ => ENNReal.ofReal (a ^ (k + 1))) ω) ∂P :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal a + ENNReal.ofReal (a - 1) *
        ∑' k : ℕ, ENNReal.ofReal (a ^ (k + 1)) * P {ω | k < N ω} := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (Measurable.tsum fun k => hmeasI k),
          lintegral_tsum fun k => (hmeasI k).aemeasurable]
        congr 3
        funext k
        rw [lintegral_indicator_const (measurableSet_lt measurable_const hNm)]
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal (a - 1) *
        ∑' k : ℕ, ENNReal.ofReal (a ^ (k + 1) * (2 / 5) ^ k) := by
        gcongr with k
        exact hterm k
    _ = ENNReal.ofReal (a + (a - 1) * (a * (1 - 2 / 5 * a)⁻¹)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum, hval,
          ← ENNReal.ofReal_mul (by linarith),
          ← ENNReal.ofReal_add (by linarith) (mul_nonneg (by linarith)
            (mul_nonneg (by linarith) (inv_nonneg.2 (by linarith))))]
    _ ≤ ENNReal.ofReal 6 := ENNReal.ofReal_le_ofReal (final_numeric ha1 ha2)
    _ = 6 := by simp

end ElboimSly.StrongApprox
