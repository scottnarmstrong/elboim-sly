/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TravelEv
public import ElboimSly.Paper.Step.TravelBlocks
public import Mathlib

/-!
# Numerics of the σ-estimate

The σ-estimate. For blocks `T ∈ [t_n^{121/200}/2, t_n^{121/200}]` all powers of `T`
are exponentials of linear functions of `n` (`log_T_bounds`), and the two final inequalities
(`sigma_numeric_small`, `sigma_numeric_big`) reduce to "linear versus quadratic or cubic" and
"polynomial versus exponential" statements, collected in `sigma_eventually`.
-/

@[expose] public section

open Filter Topology
open scoped NNReal

namespace ElboimSly.Paper.Step

/-- `log T` is between `a n - log 2` and `a (n+1)`, `a = (121/200) log 4`. -/
theorem log_T_bounds {n : ℕ} {tn T : ℝ} (ht1 : (4 : ℝ) ^ n < tn) (ht2 : tn ≤ 4 ^ (n + 1))
    (hT1 : tn ^ ((121 : ℝ) / 200) / 2 ≤ T) (hT2 : T ≤ tn ^ ((121 : ℝ) / 200)) :
    121 * Real.log 4 / 200 * n - Real.log 2 ≤ Real.log T ∧
      Real.log T ≤ 121 * Real.log 4 / 200 * ((n : ℝ) + 1) ∧
      (79 : ℝ) / 200 * Real.log tn ≤ Real.log tn - Real.log T := by
  have htn0 : 0 < tn := lt_trans (by positivity) ht1
  have hr0 : 0 < tn ^ ((121 : ℝ) / 200) := Real.rpow_pos_of_pos htn0 _
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT1
  have hlogtn_lo : Real.log 4 * n ≤ Real.log tn := by
    have : Real.log ((4 : ℝ) ^ n) ≤ Real.log tn := Real.log_le_log (by positivity) ht1.le
    rw [Real.log_pow] at this
    linarith
  have hlogtn_hi : Real.log tn ≤ Real.log 4 * ((n : ℝ) + 1) := by
    have : Real.log tn ≤ Real.log ((4 : ℝ) ^ (n + 1)) := Real.log_le_log htn0 ht2
    rw [Real.log_pow] at this
    push_cast at this; linarith
  have hlogr : Real.log (tn ^ ((121 : ℝ) / 200)) = 121 / 200 * Real.log tn :=
    Real.log_rpow htn0 _
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Real.log (tn ^ ((121 : ℝ) / 200) / 2) ≤ Real.log T := Real.log_le_log (by positivity) hT1
    rw [Real.log_div hr0.ne' (by norm_num), hlogr] at h1
    nlinarith
  · have h1 : Real.log T ≤ Real.log (tn ^ ((121 : ℝ) / 200)) := Real.log_le_log hT0 hT2
    rw [hlogr] at h1
    nlinarith
  · have h1 : Real.log T ≤ Real.log (tn ^ ((121 : ℝ) / 200)) := Real.log_le_log hT0 hT2
    rw [hlogr] at h1
    linarith

/-- The largeness conditions on `n` of the σ-estimate. -/
theorem sigma_eventually {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 100 ≤ n ∧
      Real.sqrt 355 * Real.exp (-(c * (n : ℝ) ^ 3) / 2) ≤
        2 * Real.exp (-(Real.log 4 * ((n : ℝ) + 1) / 16)) ∧
      6 * ((n : ℝ) ^ 2 + 3) ≤
        Real.exp (11 / 400 * (121 * Real.log 4 / 200 * n - Real.log 2)) ∧
      2 * (n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 / 4)) +
        Real.sqrt 2560 * Real.exp (-((n : ℝ) ^ 2 / 8)) ≤
        Real.exp (-(121 * Real.log 4 / 200 * ((n : ℝ) + 1) / 16)) / 3 ∧
      1 ≤ 4 * c * n := by
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set a : ℝ := 121 * Real.log 4 / 200 with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have e1 : ∀ᶠ n : ℕ in atTop, 100 ≤ n := eventually_ge_atTop 100
  have e2 : ∀ᶠ n : ℕ in atTop, Real.sqrt 355 * Real.exp (-(c * (n : ℝ) ^ 3) / 2) ≤
      2 * Real.exp (-(Real.log 4 * ((n : ℝ) + 1) / 16)) := by
    have := eventually_linear_le_cube (Real.log 4 / 16) (Real.log 4 / 16 + Real.log (Real.sqrt 355))
      (c := c / 2) (by positivity)
    filter_upwards [this] with n hn
    have hs : 0 < Real.sqrt 355 := Real.sqrt_pos.2 (by norm_num)
    have h1 : Real.sqrt 355 * Real.exp (-(c * (n : ℝ) ^ 3) / 2) =
        Real.exp (Real.log (Real.sqrt 355) + -(c * (n : ℝ) ^ 3) / 2) := by
      rw [Real.exp_add, Real.exp_log hs]
    rw [h1]
    have h2 : Real.exp (Real.log (Real.sqrt 355) + -(c * (n : ℝ) ^ 3) / 2) ≤
        Real.exp (-(Real.log 4 * ((n : ℝ) + 1) / 16)) := Real.exp_le_exp.2 (by nlinarith)
    have := Real.exp_pos (-(Real.log 4 * ((n : ℝ) + 1) / 16))
    linarith
  have e3 : ∀ᶠ n : ℕ in atTop, 6 * ((n : ℝ) ^ 2 + 3) ≤
      Real.exp (11 / 400 * (a * n - Real.log 2)) := by
    set κ : ℝ := 11 / 400 * a with hκ
    have hκ0 : 0 < κ := by positivity
    set C : ℝ := Real.exp (-(11 / 400 * Real.log 2)) with hC
    have hC0 : 0 < C := Real.exp_pos _
    have h1 := eventually_pow_mul_exp_neg_le 2 (c := κ) (δ := C / 12) hκ0 (by positivity)
    have h2 : ∀ᶠ n : ℕ in atTop, 36 ≤ C * Real.exp (κ * n) := by
      have : Tendsto (fun n : ℕ => C * Real.exp (κ * n)) atTop atTop :=
        (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hκ0)).const_mul_atTop hC0
      exact this.eventually_ge_atTop 36
    filter_upwards [h1, h2] with n hn1 hn2
    have hexp : Real.exp (11 / 400 * (a * n - Real.log 2)) = C * Real.exp (κ * n) := by
      rw [hC, ← Real.exp_add]; congr 1; rw [hκ]; ring
    rw [hexp]
    have h3 : (n : ℝ) ^ 2 ≤ C / 12 * Real.exp (κ * n) := by
      have := mul_le_mul_of_nonneg_right hn1 (Real.exp_pos (κ * n)).le
      rw [mul_assoc, ← Real.exp_add] at this
      simp only [neg_add_cancel, Real.exp_zero, mul_one] at this
      exact this
    nlinarith
  have e4 : ∀ᶠ n : ℕ in atTop, 2 * (n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 / 4)) +
      Real.sqrt 2560 * Real.exp (-((n : ℝ) ^ 2 / 8)) ≤
      Real.exp (-(a * ((n : ℝ) + 1) / 16)) / 3 := by
    have hs : 0 < Real.sqrt 2560 := Real.sqrt_pos.2 (by norm_num)
    have h1 := eventually_linear_le_sq (a / 16 + 1) (a / 16) (c := 1 / 4) (by norm_num)
    have h2 := eventually_linear_le_sq (a / 16) (a / 16 + Real.log (6 * Real.sqrt 2560))
      (c := 1 / 8) (by norm_num)
    have h3 := eventually_pow_mul_exp_neg_le 4 (c := 1) (δ := 1 / 12) one_pos (by norm_num)
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
    set E := Real.exp (-(a * ((n : ℝ) + 1) / 16)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have t1 : 2 * (n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 / 4)) ≤ E / 6 := by
      have h4 : Real.exp (-((n : ℝ) ^ 2 / 4)) ≤ E * Real.exp (-(1 * n)) := by
        rw [hE, ← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith
      calc 2 * (n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 / 4)) ≤
          2 * (n : ℝ) ^ 4 * (E * Real.exp (-(1 * n))) := by gcongr
        _ = 2 * E * ((n : ℝ) ^ 4 * Real.exp (-(1 * n))) := by ring
        _ ≤ 2 * E * (1 / 12) := by gcongr
        _ = E / 6 := by ring
    have t2 : Real.sqrt 2560 * Real.exp (-((n : ℝ) ^ 2 / 8)) ≤ E / 6 := by
      have h5 : Real.exp (Real.log (6 * Real.sqrt 2560) + -((n : ℝ) ^ 2 / 8)) ≤ E := by
        rw [hE]; apply Real.exp_le_exp.2; nlinarith
      rw [Real.exp_add, Real.exp_log (by positivity)] at h5
      nlinarith
    linarith
  have e5 : ∀ᶠ n : ℕ in atTop, 1 ≤ 4 * c * n := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / (4 * c))] with n hn
    rw [div_le_iff₀ (by positivity)] at hn
    linarith
  filter_upwards [e1, e2, e3, e4, e5] with n a b c' d' e
  exact ⟨a, b, c', d', e⟩

/-- `|√V - √2| ≤ δ` from `2 - δ ≤ V ≤ 2`. -/
theorem abs_sqrt_sub_sqrt_two_le {V δ : ℝ} (hV0 : 0 ≤ V) (h1 : 2 - δ ≤ V) (h2 : V ≤ 2) :
    |Real.sqrt V - Real.sqrt 2| ≤ δ := by
  have hle : Real.sqrt V ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h2
  have hx : 0 ≤ Real.sqrt 2 - Real.sqrt V := sub_nonneg.2 hle
  have hS : 1 ≤ Real.sqrt 2 + Real.sqrt V := by
    have : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
    linarith [Real.sqrt_nonneg V]
  have hprod : (Real.sqrt 2 - Real.sqrt V) * (Real.sqrt 2 + Real.sqrt V) = 2 - V := by
    have h2' := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hV' := Real.sq_sqrt hV0
    nlinarith
  rw [abs_sub_comm, abs_of_nonneg hx]
  nlinarith

/-- Case 2 numerics: `√(355 e^{-c n³}) ≤ 2 β^{-1/16}`. -/
theorem sigma_numeric_small {c : ℝ} {n : ℕ} {tn β : ℝ} (hβ0 : 0 < β) (hβtn : β < tn)
    (htn : tn ≤ 4 ^ (n + 1))
    (h : Real.sqrt 355 * Real.exp (-(c * (n : ℝ) ^ 3) / 2) ≤
      2 * Real.exp (-(Real.log 4 * ((n : ℝ) + 1) / 16))) :
    Real.sqrt (355 * Real.exp (-(c * (n : ℝ) ^ 3))) ≤
      3 * β ^ (-(1 : ℝ) / 16) - tn ^ (-(1 : ℝ) / 16) := by
  have htn0 : 0 < tn := by linarith
  have e1 : Real.sqrt (355 * Real.exp (-(c * (n : ℝ) ^ 3))) =
      Real.sqrt 355 * Real.exp (-(c * (n : ℝ) ^ 3) / 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (Real.exp (-(c * (n : ℝ) ^ 3))),
      ← Real.exp_mul]
    congr 2; ring
  rw [e1]
  have hlog : Real.log β ≤ Real.log 4 * ((n : ℝ) + 1) := by
    have h1 : Real.log β ≤ Real.log ((4 : ℝ) ^ (n + 1)) :=
      Real.log_le_log hβ0 (hβtn.le.trans htn)
    rw [Real.log_pow] at h1
    push_cast at h1; linarith
  have hb : Real.exp (-(Real.log 4 * ((n : ℝ) + 1) / 16)) ≤ β ^ (-(1 : ℝ) / 16) := by
    rw [Real.rpow_def_of_pos hβ0]
    apply Real.exp_le_exp.2
    nlinarith
  have hlt : tn ^ (-(1 : ℝ) / 16) ≤ β ^ (-(1 : ℝ) / 16) :=
    Real.rpow_le_rpow_of_nonpos hβ0 hβtn.le (by norm_num)
  linarith

/-- Case 1 numerics: the coupling error is at most half of `T^{-1/16}`, hence at most
`T^{-1/16} - t_n^{-1/16}`. -/
theorem sigma_numeric_big {n : ℕ} {tn T σ' q : ℝ} (hn : 100 ≤ n)
    (ht1 : (4 : ℝ) ^ n < tn) (ht2 : tn ≤ 4 ^ (n + 1))
    (hT1 : tn ^ ((121 : ℝ) / 200) / 2 ≤ T) (hT2 : T ≤ tn ^ ((121 : ℝ) / 200))
    (hσ1 : 1 ≤ σ') (hσ2 : σ' ≤ 2) (hq0 : 0 ≤ q) (hq : q ≤ 2 * Real.exp (-((n : ℝ) ^ 2 / 4)))
    (e3 : 6 * ((n : ℝ) ^ 2 + 3) ≤
      Real.exp (11 / 400 * (121 * Real.log 4 / 200 * n - Real.log 2)))
    (e4 : 2 * (n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 / 4)) +
        Real.sqrt 2560 * Real.exp (-((n : ℝ) ^ 2 / 8)) ≤
        Real.exp (-(121 * Real.log 4 / 200 * ((n : ℝ) + 1) / 16)) / 3) :
    T ^ ((41 : ℝ) / 100) / Real.sqrt T * ((n : ℝ) ^ 2 + (1 + σ' ^ 2) / 2) +
        ((n : ℝ) ^ 2) ^ 2 * q + Real.sqrt (80 * σ' ^ 4 * q) ≤
      T ^ (-(1 : ℝ) / 16) - tn ^ (-(1 : ℝ) / 16) := by
  have htn0 : 0 < tn := lt_trans (by positivity) ht1
  have hT0 : 0 < T := lt_of_lt_of_le (by have := Real.rpow_pos_of_pos htn0 ((121 : ℝ) / 200); positivity) hT1
  obtain ⟨hy1, hy2, hy3⟩ := log_T_bounds ht1 ht2 hT1 hT2
  set y := Real.log T with hy
  set a : ℝ := 121 * Real.log 4 / 200 with ha
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  set E : ℝ := Real.exp (-(y / 16)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hTpow : ∀ z : ℝ, T ^ z = Real.exp (z * y) := fun z => by
    rw [Real.rpow_def_of_pos hT0, mul_comm]
  -- T^{-1/16} = E
  have hT16 : T ^ (-(1 : ℝ) / 16) = E := by
    rw [hTpow, hE]; congr 1; ring
  -- tn^{-1/16} ≤ E / 2
  have hlogtn : 0 < Real.log tn := Real.log_pos (by
    have : (1 : ℝ) < 4 ^ n := one_lt_pow₀ (by norm_num) (by omega)
    linarith)
  have hlogtn_lo : Real.log 4 * n ≤ Real.log tn := by
    have : Real.log ((4 : ℝ) ^ n) ≤ Real.log tn := Real.log_le_log (by positivity) ht1.le
    rw [Real.log_pow] at this
    linarith
  have htn16 : tn ^ (-(1 : ℝ) / 16) ≤ E / 2 := by
    rw [Real.rpow_def_of_pos htn0]
    have h1 : Real.log tn * (-(1 : ℝ) / 16) ≤ -(y / 16) - Real.log 2 := by
      have : Real.log tn - y ≥ 16 * Real.log 2 := by
        have h2 : (79 : ℝ) / 200 * Real.log tn ≥ 79 / 200 * (Real.log 4 * 100) := by
          have := mul_le_mul_of_nonneg_left (hlogtn_lo.trans' (mul_le_mul_of_nonneg_left hn' hl4.le))
            (by norm_num : (0 : ℝ) ≤ 79 / 200)
          linarith
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        rw [h4] at h2
        linarith
      linarith
    calc Real.exp (Real.log tn * (-(1 : ℝ) / 16)) ≤ Real.exp (-(y / 16) - Real.log 2) :=
          Real.exp_le_exp.2 h1
      _ = E / 2 := by rw [Real.exp_sub, Real.exp_log (by norm_num)]
  -- the three terms
  have hE_a : Real.exp (-(a * ((n : ℝ) + 1) / 16)) ≤ E := Real.exp_le_exp.2 (by nlinarith)
  have hθT : T ^ ((41 : ℝ) / 100) / Real.sqrt T = Real.exp (-(9 / 100) * y) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hT0, hTpow]; congr 1; ring
  have t1 : T ^ ((41 : ℝ) / 100) / Real.sqrt T * ((n : ℝ) ^ 2 + (1 + σ' ^ 2) / 2) ≤ E / 6 := by
    rw [hθT]
    have h6 : Real.exp (-(9 / 100) * y) * (6 * ((n : ℝ) ^ 2 + 3)) ≤ E := by
      have h7 : 6 * ((n : ℝ) ^ 2 + 3) ≤ Real.exp (11 / 400 * y) :=
        e3.trans (Real.exp_le_exp.2 (by nlinarith))
      calc Real.exp (-(9 / 100) * y) * (6 * ((n : ℝ) ^ 2 + 3))
          ≤ Real.exp (-(9 / 100) * y) * Real.exp (11 / 400 * y) :=
            mul_le_mul_of_nonneg_left h7 (Real.exp_pos _).le
        _ = E := by rw [← Real.exp_add, hE]; congr 1; ring
    have hσ4 : (1 + σ' ^ 2) / 2 ≤ 5 / 2 := by nlinarith
    have hpos := Real.exp_pos (-(9 / 100) * y)
    nlinarith
  have t2 : ((n : ℝ) ^ 2) ^ 2 * q ≤ 2 * (n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 / 4)) := by
    have : ((n : ℝ) ^ 2) ^ 2 = (n : ℝ) ^ 4 := by ring
    rw [this]
    calc (n : ℝ) ^ 4 * q ≤ (n : ℝ) ^ 4 * (2 * Real.exp (-((n : ℝ) ^ 2 / 4))) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = 2 * (n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 / 4)) := by ring
  have t3 : Real.sqrt (80 * σ' ^ 4 * q) ≤ Real.sqrt 2560 * Real.exp (-((n : ℝ) ^ 2 / 8)) := by
    have h1 : 80 * σ' ^ 4 * q ≤ 2560 * Real.exp (-((n : ℝ) ^ 2 / 4)) := by
      have : σ' ^ 4 ≤ 16 := by nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ σ') hσ2 4]
      nlinarith [Real.exp_pos (-((n : ℝ) ^ 2 / 4))]
    calc Real.sqrt (80 * σ' ^ 4 * q) ≤ Real.sqrt (2560 * Real.exp (-((n : ℝ) ^ 2 / 4))) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt 2560 * Real.exp (-((n : ℝ) ^ 2 / 8)) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (Real.exp _), ← Real.exp_mul]
          congr 2; ring
  have hT16' : T ^ (-(1 : ℝ) / 16) = E := hT16
  rw [hT16']
  linarith

/-- `|√V - σ'| ≤ |V - σ'²|` for `σ' ≥ 1`. -/
theorem abs_sqrt_sub_le {V σ' : ℝ} (hV0 : 0 ≤ V) (hσ : 1 ≤ σ') :
    |Real.sqrt V - σ'| ≤ |V - σ' ^ 2| := by
  have hprod : (Real.sqrt V - σ') * (Real.sqrt V + σ') = V - σ' ^ 2 := by
    have := Real.sq_sqrt hV0
    nlinarith
  have hS : 1 ≤ |Real.sqrt V + σ'| := by
    rw [abs_of_nonneg (by linarith [Real.sqrt_nonneg V])]
    linarith [Real.sqrt_nonneg V]
  calc |Real.sqrt V - σ'| = |Real.sqrt V - σ'| * 1 := (mul_one _).symm
    _ ≤ |Real.sqrt V - σ'| * |Real.sqrt V + σ'| := by gcongr
    _ = |V - σ' ^ 2| := by rw [← abs_mul, hprod]

end ElboimSly.Paper.Step
