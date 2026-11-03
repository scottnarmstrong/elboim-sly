/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Comparison of second moments (the σ-estimate, Case 1)

The σ-estimate, Case 1: "By Minkowski, splitting on `𝒜' ∩ E'`... and using
Cauchy-Schwarz off it". `second_moment_close` is the elementary form used here: if `a, b` are
close (`|a - b| ≤ e`) on a good event `G`, `|a| ≤ A`, and `b` has second moment `s²` and fourth
moment at most `M`, then `|E a² - s²| ≤ e (A + (1 + s²)/2) + A² q + √(M q)`, `q ≥ ℙ(Gᶜ)`.
The Cauchy-Schwarz step is replaced by the pointwise inequality `𝟙 b² ≤ (c 𝟙 + b⁴/c)/2`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

variable {Θ : Type*} [MeasurableSpace Θ] {Q : Measure Θ}

theorem second_moment_close [IsProbabilityMeasure Q] {a b : Θ → ℝ} (ha : Measurable a)
    (hb : Measurable b) {G : Set Θ} (hGm : MeasurableSet G) {e A s M q : ℝ} (he : 0 ≤ e)
    (hA : 0 ≤ A) (hq : 0 < q)
    (hG : ∀ p ∈ G, |a p - b p| ≤ e) (hab : ∀ p, |a p| ≤ A)
    (hb2 : Integrable (fun p => b p ^ 2) Q) (hb4 : Integrable (fun p => b p ^ 4) Q)
    (hs : ∫ p, b p ^ 2 ∂Q = s ^ 2) (hM : ∫ p, b p ^ 4 ∂Q ≤ M) (hM0 : 0 < M)
    (hGc : Q.real Gᶜ ≤ q) :
    |(∫ p, a p ^ 2 ∂Q) - s ^ 2| ≤ e * (A + (1 + s ^ 2) / 2) + A ^ 2 * q + Real.sqrt (M * q) := by
  have ha2 : Integrable (fun p => a p ^ 2) Q := by
    refine Integrable.mono' (integrable_const (A ^ 2)) (ha.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    calc a p ^ 2 = |a p| ^ 2 := (sq_abs _).symm
      _ ≤ A ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hab p) 2
  set ind : Θ → ℝ := Gᶜ.indicator fun _ => (1 : ℝ) with hind
  have hindm : Integrable ind Q := (integrable_const (1 : ℝ)).indicator hGm.compl
  have hindI : ∫ p, ind p ∂Q = Q.real Gᶜ := by
    rw [hind, integral_indicator_const (1 : ℝ) hGm.compl, smul_eq_mul, mul_one]
  -- the pointwise bound on |a² - b²|
  set c : ℝ := Real.sqrt (M / q) with hc
  have hMq : 0 ≤ M / q := by positivity
  -- case q-dependence: c may be 0 if M = 0
  have hpt : ∀ p, |a p ^ 2 - b p ^ 2| ≤
      e * A + e * ((1 + b p ^ 2) / 2) + A ^ 2 * ind p + ind p * b p ^ 2 := by
    intro p
    by_cases hp : p ∈ G
    · have hind0 : ind p = 0 := by rw [hind]; exact Set.indicator_of_notMem (by simpa using hp) _
      rw [hind0]
      have h1 : |a p ^ 2 - b p ^ 2| = |a p - b p| * |a p + b p| := by
        rw [← abs_mul]; congr 1; ring
      have h2 : |a p + b p| ≤ A + (1 + b p ^ 2) / 2 := by
        calc |a p + b p| ≤ |a p| + |b p| := abs_add_le _ _
          _ ≤ A + (1 + b p ^ 2) / 2 := by
              have := hab p
              nlinarith [sq_nonneg (|b p| - 1), sq_abs (b p)]
      calc |a p ^ 2 - b p ^ 2| = |a p - b p| * |a p + b p| := h1
        _ ≤ e * (A + (1 + b p ^ 2) / 2) := mul_le_mul (hG p hp) h2 (abs_nonneg _) he
        _ = e * A + e * ((1 + b p ^ 2) / 2) + A ^ 2 * 0 + 0 * b p ^ 2 := by ring
    · have hind1 : ind p = 1 := by rw [hind]; exact Set.indicator_of_mem (by simpa using hp) _
      rw [hind1]
      have h1 : |a p ^ 2 - b p ^ 2| ≤ a p ^ 2 + b p ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a p), sq_nonneg (b p)]
      have h2 : a p ^ 2 ≤ A ^ 2 := by
        calc a p ^ 2 = |a p| ^ 2 := (sq_abs _).symm
          _ ≤ A ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hab p) 2
      have h3 : 0 ≤ e * A + e * ((1 + b p ^ 2) / 2) := by positivity
      nlinarith
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = M / q := Real.sq_sqrt hMq
  have hMc : M / c = c * q := by
    field_simp
    have : M = c ^ 2 * q := by rw [hc2]; field_simp
    nlinarith
  have hint_ind_b : Integrable (fun p => ind p * b p ^ 2) Q := by
    refine Integrable.mono' hb2 ((hindm.aestronglyMeasurable.mul (hb.pow_const 2).aestronglyMeasurable))
      (Filter.Eventually.of_forall fun p => ?_)
    have h0 : 0 ≤ ind p := by rw [hind]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) p
    have h1 : ind p ≤ 1 := by
      rw [hind]; by_cases hp : p ∈ Gᶜ
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]; norm_num
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (b p)]
  have hAMGM : ∀ p, ind p * b p ^ 2 ≤ (c * ind p + b p ^ 4 / c) / 2 := by
    intro p
    by_cases hp : p ∈ Gᶜ
    · have : ind p = 1 := by rw [hind]; exact Set.indicator_of_mem hp _
      rw [this]
      have h1 : c + b p ^ 4 / c - 2 * b p ^ 2 = (c - b p ^ 2) ^ 2 / c := by field_simp; ring
      have h2 : 0 ≤ (c - b p ^ 2) ^ 2 / c := by positivity
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
    · have : ind p = 0 := by rw [hind]; exact Set.indicator_of_notMem hp _
      rw [this]
      have : 0 ≤ b p ^ 4 / c := by positivity
      linarith
  have hint_ind_b' : ∫ p, ind p * b p ^ 2 ∂Q ≤ c * q := by
    have hI : Integrable (fun p => (c * ind p + b p ^ 4 / c) / 2) Q :=
      ((hindm.const_mul c).add (hb4.div_const c)).div_const 2
    calc ∫ p, ind p * b p ^ 2 ∂Q ≤ ∫ p, (c * ind p + b p ^ 4 / c) / 2 ∂Q :=
          integral_mono hint_ind_b hI hAMGM
      _ = (c * Q.real Gᶜ + (∫ p, b p ^ 4 ∂Q) / c) / 2 := by
          rw [integral_div, integral_add (hindm.const_mul c) (hb4.div_const c), integral_const_mul,
            integral_div, hindI]
      _ ≤ (c * q + M / c) / 2 := by
          have h1 : c * Q.real Gᶜ ≤ c * q := mul_le_mul_of_nonneg_left hGc hc0.le
          have h2 : (∫ p, b p ^ 4 ∂Q) / c ≤ M / c := div_le_div_of_nonneg_right hM hc0.le
          linarith
      _ = c * q := by rw [hMc]; ring
  have hcq : c * q = Real.sqrt (M * q) := by
    have hh : (c * q) ^ 2 = M * q := by rw [mul_pow, hc2]; field_simp
    rw [← hh]; exact (Real.sqrt_sq (by positivity)).symm
  have hbound_int : Integrable (fun p => e * A + e * ((1 + b p ^ 2) / 2) + A ^ 2 * ind p +
      ind p * b p ^ 2) Q := by
    have h1 : Integrable (fun p => e * ((1 + b p ^ 2) / 2)) Q :=
      (((integrable_const (1 : ℝ)).add hb2).div_const 2).const_mul e
    exact (((integrable_const (e * A)).add h1).add (hindm.const_mul (A ^ 2))).add hint_ind_b
  have hdiff : Integrable (fun p => a p ^ 2 - b p ^ 2) Q := ha2.sub hb2
  have h1 : |(∫ p, a p ^ 2 ∂Q) - s ^ 2| ≤ ∫ p, |a p ^ 2 - b p ^ 2| ∂Q := by
    rw [← hs, ← integral_sub ha2 hb2]
    exact abs_integral_le_integral_abs
  refine h1.trans ?_
  calc ∫ p, |a p ^ 2 - b p ^ 2| ∂Q
      ≤ ∫ p, (e * A + e * ((1 + b p ^ 2) / 2) + A ^ 2 * ind p + ind p * b p ^ 2) ∂Q :=
        integral_mono hdiff.abs hbound_int hpt
    _ = e * A + e * ((1 + s ^ 2) / 2) + A ^ 2 * Q.real Gᶜ + ∫ p, ind p * b p ^ 2 ∂Q := by
        have hu0 : Integrable (fun p => e * ((1 + b p ^ 2) / 2)) Q :=
          (((integrable_const (1 : ℝ)).add hb2).div_const 2).const_mul e
        have hu1 : Integrable (fun p => e * A + e * ((1 + b p ^ 2) / 2)) Q :=
          (integrable_const (e * A)).add hu0
        have hu2 : Integrable (fun p => A ^ 2 * ind p) Q := hindm.const_mul _
        have I1 : ∫ p, (e * A + e * ((1 + b p ^ 2) / 2)) ∂Q = e * A + e * ((1 + s ^ 2) / 2) := by
          rw [integral_add (integrable_const _) hu0, integral_const, integral_const_mul,
            integral_div, integral_add (integrable_const (1 : ℝ)) hb2, hs]
          simp
        have I2 : ∫ p, A ^ 2 * ind p ∂Q = A ^ 2 * Q.real Gᶜ := by
          rw [integral_const_mul, hindI]
        have hu12 : Integrable (fun p => e * A + e * ((1 + b p ^ 2) / 2) + A ^ 2 * ind p) Q :=
          hu1.add hu2
        rw [integral_add (f := fun p => e * A + e * ((1 + b p ^ 2) / 2) + A ^ 2 * ind p)
          (g := fun p => ind p * b p ^ 2) hu12 hint_ind_b,
          integral_add (f := fun p => e * A + e * ((1 + b p ^ 2) / 2))
          (g := fun p => A ^ 2 * ind p) hu1 hu2, I1, I2]
    _ ≤ e * A + e * ((1 + s ^ 2) / 2) + A ^ 2 * q + c * q := by
        have : A ^ 2 * Q.real Gᶜ ≤ A ^ 2 * q := mul_le_mul_of_nonneg_left hGc (by positivity)
        linarith
    _ = e * (A + (1 + s ^ 2) / 2) + A ^ 2 * q + Real.sqrt (M * q) := by rw [hcq]; ring

end ElboimSly.Paper.Step
