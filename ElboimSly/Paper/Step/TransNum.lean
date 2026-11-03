/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TravelBlocks
public import ElboimSly.Paper.Step.TravelEv
public import ElboimSly.Paper.Heavy.Scales
public import Mathlib

/-!
# Numerics of Lemma 7.7

ES22 Lemma 7.7. The final display of the proof: for `n` large and `t ∈ [t_n/4, t_n]`,
with `r = t^{2θ_H}`, `s₁ = t - r`, `ρ = n²√r`,
`e^{-c₁n³} + (4 t_n^{2ε}+1)^d (e^{-m²} + r^{-d/2+0.1}(e^{-c₂ n³} + (2(ρ+t_n^{θ_H}))^d
(2π σ² s₁)^{-d/2})) ≤ t^{-d/2+0.1}`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

/-- The number of lattice points in the coupling-error ball: `(4 t_n^{2ε} + 1)^d ≤ 5^d · 4 t^{1/150}`. -/
theorem trans_K_le {d : ℕ} (hd : 1 ≤ d) {t tn : ℝ} (ht : 0 < t)
    (htn1 : 1 ≤ tn) (htn : tn ≤ 4 * t) :
    (2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d ≤ 5 ^ d * (4 * t ^ ((1 : ℝ) / 150)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have htn0 : 0 < tn := by linarith
  set x : ℝ := tn ^ (2 * heavyEps d) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow htn1 (by unfold heavyEps; positivity)
  have hxd : x ^ d = tn ^ ((1 : ℝ) / 150) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul htn0.le]
    congr 1
    unfold heavyEps
    field_simp
    ring
  have h1 : (2 * (2 * x) + 1) ^ d ≤ (5 * x) ^ d := by
    gcongr; linarith
  rw [mul_pow, hxd] at h1
  refine h1.trans ?_
  gcongr
  calc tn ^ ((1 : ℝ) / 150) ≤ (4 * t) ^ ((1 : ℝ) / 150) :=
        Real.rpow_le_rpow htn0.le htn (by norm_num)
    _ = 4 ^ ((1 : ℝ) / 150) * t ^ ((1 : ℝ) / 150) := Real.mul_rpow (by norm_num) ht.le
    _ ≤ 4 * t ^ ((1 : ℝ) / 150) := by
        gcongr
        calc (4 : ℝ) ^ ((1 : ℝ) / 150) ≤ 4 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := Real.rpow_one 4

/-- The last term of Lemma 7.7, up to constants. -/
theorem trans_T4 {d : ℕ} (hd : 1 ≤ d) {n t tn s₁ σ ρ : ℝ} (hn : 0 ≤ n) (ht : 64 ≤ t)
    (htn1 : 1 ≤ tn) (htn : tn ≤ 4 * t) (hσ : 1 ≤ σ) (hs₁ : t / 2 ≤ s₁)
    (hρ : ρ = n ^ 2 * Real.sqrt (t ^ ((41 : ℝ) / 50))) (hθ : tn ^ indThetaH ≤ ρ) :
    (2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d *
      ((t ^ ((41 : ℝ) / 50)) ^ (-(d : ℝ) / 2 + 1 / 10) *
        ((2 * (ρ + tn ^ indThetaH)) ^ d * (2 * Real.pi * (σ ^ 2 * s₁)) ^ (-(d : ℝ) / 2))) ≤
      4 * 40 ^ d * n ^ (2 * d) * t ^ ((133 : ℝ) / 1500 - d / 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ht0 : 0 < t := by linarith
  have htn0 : 0 < tn := by linarith
  set r : ℝ := t ^ ((41 : ℝ) / 50) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos ht0 _
  -- (a)
  have hA := trans_K_le hd ht0 htn1 htn
  -- (b)
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hB : (2 * (ρ + tn ^ indThetaH)) ^ d ≤ 4 ^ d * (n ^ (2 * d) * r ^ ((d : ℝ) / 2)) := by
    have h1 : (2 * (ρ + tn ^ indThetaH)) ^ d ≤ (4 * ρ) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    have hsq : (Real.sqrt r) ^ d = r ^ ((d : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
      congr 1; ring
    refine h1.trans (le_of_eq ?_)
    rw [mul_pow, hρ, mul_pow, ← pow_mul, hsq]
  -- (c)
  have hs₁0 : 0 < s₁ := by linarith
  have hC : (2 * Real.pi * (σ ^ 2 * s₁)) ^ (-(d : ℝ) / 2) ≤ 2 ^ d * t ^ (-(d : ℝ) / 2) := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h1 : s₁ ≤ 2 * Real.pi * (σ ^ 2 * s₁) := by
      have h1' : 1 ≤ σ ^ 2 := one_le_pow₀ hσ
      have h2pi : 1 ≤ 2 * Real.pi * σ ^ 2 := by nlinarith
      calc s₁ = 1 * s₁ := (one_mul _).symm
        _ ≤ (2 * Real.pi * σ ^ 2) * s₁ := mul_le_mul_of_nonneg_right h2pi hs₁0.le
        _ = 2 * Real.pi * (σ ^ 2 * s₁) := by ring
    have h2 : (2 * Real.pi * (σ ^ 2 * s₁)) ^ (-(d : ℝ) / 2) ≤ s₁ ^ (-(d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hs₁0 h1 (by linarith)
    have h3 : s₁ ^ (-(d : ℝ) / 2) ≤ (t / 2) ^ (-(d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hs₁ (by linarith)
    refine h2.trans (h3.trans ?_)
    rw [Real.div_rpow ht0.le (by norm_num)]
    have h4 : (2 : ℝ) ^ (-(d : ℝ) / 2) = ((2 : ℝ) ^ ((d : ℝ) / 2))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num)]; congr 1; ring
    rw [h4, div_inv_eq_mul, mul_comm]
    gcongr
    calc (2 : ℝ) ^ ((d : ℝ) / 2) ≤ 2 ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 ^ d := Real.rpow_natCast 2 d
  -- (d)
  have hD : r ^ (-(d : ℝ) / 2 + 1 / 10) * r ^ ((d : ℝ) / 2) = t ^ ((41 : ℝ) / 500) := by
    rw [← Real.rpow_add hr0, hr, ← Real.rpow_mul ht0.le]
    congr 1; ring
  have hn2 : 0 ≤ n ^ (2 * d) := by positivity
  have hr1 : 0 ≤ r ^ (-(d : ℝ) / 2 + 1 / 10) := by positivity
  calc (2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d * (r ^ (-(d : ℝ) / 2 + 1 / 10) *
        ((2 * (ρ + tn ^ indThetaH)) ^ d * (2 * Real.pi * (σ ^ 2 * s₁)) ^ (-(d : ℝ) / 2)))
      ≤ (5 ^ d * (4 * t ^ ((1 : ℝ) / 150))) * (r ^ (-(d : ℝ) / 2 + 1 / 10) *
        (4 ^ d * (n ^ (2 * d) * r ^ ((d : ℝ) / 2)) * (2 ^ d * t ^ (-(d : ℝ) / 2)))) := by
        gcongr
    _ = 5 ^ d * 4 * 4 ^ d * 2 ^ d * n ^ (2 * d) * t ^ ((1 : ℝ) / 150) *
          (r ^ (-(d : ℝ) / 2 + 1 / 10) * r ^ ((d : ℝ) / 2)) * t ^ (-(d : ℝ) / 2) := by ring
    _ = 4 * 40 ^ d * n ^ (2 * d) * t ^ ((133 : ℝ) / 1500 - d / 2) := by
        rw [hD]
        have e : t ^ ((1 : ℝ) / 150) * t ^ ((41 : ℝ) / 500) * t ^ (-(d : ℝ) / 2) =
            t ^ ((133 : ℝ) / 1500 - d / 2) := by
          rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]; congr 1; ring
        have e2 : (40 : ℝ) ^ d = 5 ^ d * 4 ^ d * 2 ^ d := by
          rw [← mul_pow, ← mul_pow]; norm_num
        rw [e2]
        calc 5 ^ d * 4 * 4 ^ d * 2 ^ d * n ^ (2 * d) * t ^ ((1 : ℝ) / 150) *
              t ^ ((41 : ℝ) / 500) * t ^ (-(d : ℝ) / 2)
            = 4 * (5 ^ d * 4 ^ d * 2 ^ d) * n ^ (2 * d) *
              (t ^ ((1 : ℝ) / 150) * t ^ ((41 : ℝ) / 500) * t ^ (-(d : ℝ) / 2)) := by ring
          _ = _ := by rw [e]

/-- `exp(-Λ(n+1)) ≤ t^{-d/2+1/10}` for `1 ≤ t ≤ 4^{n+1}`, `Λ = (d/2) log 4`. -/
theorem trans_L_lower {d n : ℕ} {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 4 ^ (n + 1)) :
    Real.exp (-((d : ℝ) / 2 * Real.log 4 * ((n : ℝ) + 1))) ≤ t ^ (-(d : ℝ) / 2 + 1 / 10) := by
  have ht0 : 0 < t := by linarith
  have h1 : t ^ (-(d : ℝ) / 2) ≤ t ^ (-(d : ℝ) / 2 + 1 / 10) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  refine le_trans ?_ h1
  have h2 : ((4 : ℝ) ^ (n + 1)) ^ (-(d : ℝ) / 2) ≤ t ^ (-(d : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos ht0 ht2 (by have : (0 : ℝ) ≤ d := by positivity
                                            linarith)
  refine le_trans (le_of_eq ?_) h2
  rw [four_pow_eq_exp, ← Real.exp_mul]
  congr 1
  push_cast
  ring

/-- All the largeness conditions on `n` of Lemma 7.7. -/
theorem trans_eventually (d : ℕ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∀ᶠ n : ℕ in atTop, 100 ≤ n ∧
      4 * Real.exp (-(c₁ * (n : ℝ) ^ 3)) ≤
        Real.exp (-((d : ℝ) / 2 * Real.log 4 * ((n : ℝ) + 1))) ∧
      16 * 5 ^ d * (4 : ℝ) ^ (n + 1) * Real.exp (-((4 / 5 * (n : ℝ)) ^ 2)) ≤
        Real.exp (-((d : ℝ) / 2 * Real.log 4 * ((n : ℝ) + 1))) ∧
      16 * 5 ^ d * (4 : ℝ) ^ (n + 1) * Real.exp (-(c₂ * (n : ℝ) ^ 3)) ≤
        Real.exp (-((d : ℝ) / 2 * Real.log 4 * ((n : ℝ) + 1))) ∧
      16 * 40 ^ d * (n : ℝ) ^ (2 * d) ≤ Real.exp (17 * Real.log 4 / 1500 * ((n : ℝ) - 1)) := by
  set Λ : ℝ := (d : ℝ) / 2 * Real.log 4 with hΛ
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have e1 : ∀ᶠ n : ℕ in atTop, 100 ≤ n := eventually_ge_atTop 100
  have e2 : ∀ᶠ n : ℕ in atTop, 4 * Real.exp (-(c₁ * (n : ℝ) ^ 3)) ≤
      Real.exp (-(Λ * ((n : ℝ) + 1))) := by
    filter_upwards [eventually_linear_le_cube (Λ + Real.log 4 * 0) (Λ + Real.log 4) hc₁]
      with n hn
    have h4 : (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
    calc 4 * Real.exp (-(c₁ * (n : ℝ) ^ 3)) = Real.exp (Real.log 4 + -(c₁ * (n : ℝ) ^ 3)) := by
          rw [Real.exp_add, ← h4]
      _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)
  have hA₀ : ∀ c : ℝ, 0 < c → ∀ k : ℕ, (∀ᶠ n : ℕ in atTop,
      Real.log (16 * 5 ^ d) + Real.log 4 * ((n : ℝ) + 1) + Λ * ((n : ℝ) + 1) ≤ c * (n : ℝ) ^ k) →
      ∀ᶠ n : ℕ in atTop, 16 * 5 ^ d * (4 : ℝ) ^ (n + 1) * Real.exp (-(c * (n : ℝ) ^ k)) ≤
        Real.exp (-(Λ * ((n : ℝ) + 1))) := by
    intro c hc k h
    filter_upwards [h] with n hn
    have h16 : (16 * 5 ^ d : ℝ) = Real.exp (Real.log (16 * 5 ^ d)) :=
      (Real.exp_log (by positivity)).symm
    have h4 : (4 : ℝ) ^ (n + 1) = Real.exp (Real.log 4 * ((n : ℝ) + 1)) := by
      rw [four_pow_eq_exp]; push_cast; ring_nf
    rw [h4]
    nth_rewrite 1 [h16]
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have e3 : ∀ᶠ n : ℕ in atTop, 16 * 5 ^ d * (4 : ℝ) ^ (n + 1) * Real.exp (-((4 / 5 * (n : ℝ)) ^ 2)) ≤
      Real.exp (-(Λ * ((n : ℝ) + 1))) := by
    have := hA₀ (16 / 25) (by norm_num) 2 (by
      filter_upwards [eventually_linear_le_sq (Real.log 4 + Λ)
        (Real.log (16 * 5 ^ d) + Real.log 4 + Λ) (c := 16 / 25) (by norm_num)] with n hn
      nlinarith)
    filter_upwards [this] with n hn
    have : (4 / 5 * (n : ℝ)) ^ 2 = 16 / 25 * (n : ℝ) ^ 2 := by ring
    rw [this]; exact hn
  have e4 : ∀ᶠ n : ℕ in atTop, 16 * 5 ^ d * (4 : ℝ) ^ (n + 1) * Real.exp (-(c₂ * (n : ℝ) ^ 3)) ≤
      Real.exp (-(Λ * ((n : ℝ) + 1))) :=
    hA₀ c₂ hc₂ 3 (by
      filter_upwards [eventually_linear_le_cube (Real.log 4 + Λ)
        (Real.log (16 * 5 ^ d) + Real.log 4 + Λ) hc₂] with n hn
      nlinarith)
  have e5 : ∀ᶠ n : ℕ in atTop, 16 * 40 ^ d * (n : ℝ) ^ (2 * d) ≤
      Real.exp (17 * Real.log 4 / 1500 * ((n : ℝ) - 1)) := by
    have hκ : 0 < 17 * Real.log 4 / 1500 := by positivity
    have := eventually_pow_mul_exp_neg_le (2 * d) (c := 17 * Real.log 4 / 1500)
      (δ := Real.exp (-(17 * Real.log 4 / 1500)) / (16 * 40 ^ d)) hκ (by positivity)
    filter_upwards [this] with n hn
    have hpos : (0 : ℝ) < 16 * 40 ^ d := by positivity
    set κ : ℝ := 17 * Real.log 4 / 1500 with hκdef
    have h5 : (n : ℝ) ^ (2 * d) ≤ Real.exp (-κ) / (16 * 40 ^ d) * Real.exp (κ * n) := by
      calc (n : ℝ) ^ (2 * d) = (n : ℝ) ^ (2 * d) * Real.exp (-(κ * n)) * Real.exp (κ * n) := by
            rw [mul_assoc, ← Real.exp_add]; simp
        _ ≤ _ := by gcongr
    calc 16 * 40 ^ d * (n : ℝ) ^ (2 * d)
        ≤ 16 * 40 ^ d * (Real.exp (-κ) / (16 * 40 ^ d) * Real.exp (κ * n)) := by gcongr
      _ = Real.exp (-κ) * Real.exp (κ * n) := by field_simp
      _ = Real.exp (κ * ((n : ℝ) - 1)) := by rw [← Real.exp_add]; congr 1; ring
  filter_upwards [e1, e2, e3, e4, e5] with n a b c d' e
  exact ⟨a, b, c, d', e⟩

/-- `t^{41/50} ≤ t / 2` for `t ≥ 64`. -/
theorem rpow_le_half {t : ℝ} (ht : 64 ≤ t) : t ^ ((41 : ℝ) / 50) ≤ t / 2 := by
  have ht0 : 0 < t := by linarith
  have h1 : (2 : ℝ) ≤ t ^ ((9 : ℝ) / 50) := by
    have h2 : (64 : ℝ) ^ ((9 : ℝ) / 50) ≤ t ^ ((9 : ℝ) / 50) :=
      Real.rpow_le_rpow (by norm_num) ht (by norm_num)
    have h3 : (2 : ℝ) ≤ (64 : ℝ) ^ ((9 : ℝ) / 50) := by
      have : (64 : ℝ) = 2 ^ (6 : ℝ) := by norm_num
      rw [this, ← Real.rpow_mul (by norm_num)]
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ 2 ^ (6 * ((9 : ℝ) / 50)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith
  have h4 : t = t ^ ((41 : ℝ) / 50) * t ^ ((9 : ℝ) / 50) := by
    rw [← Real.rpow_add ht0]; norm_num
  have h5 : 0 < t ^ ((41 : ℝ) / 50) := Real.rpow_pos_of_pos ht0 _
  nlinarith

/-- **The numerics of Lemma 7.7.** -/
theorem trans_numeric {d : ℕ} (hd : 1 ≤ d) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ {t tn m σ r s₁ ρ : ℝ},
      (4 : ℝ) ^ n < tn → tn ≤ 4 ^ (n + 1) → tn / 4 ≤ t → t ≤ tn → 1 ≤ σ → 4 / 5 * (n : ℝ) ≤ m →
      r = t ^ ((41 : ℝ) / 50) → s₁ = t - r → ρ = (n : ℝ) ^ 2 * Real.sqrt r →
      tn ^ indThetaH ≤ ρ →
      Real.exp (-(c₁ * (n : ℝ) ^ 3)) + (2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d *
        (Real.exp (-(m ^ 2)) + r ^ (-(d : ℝ) / 2 + 1 / 10) *
          (Real.exp (-(c₂ * (n : ℝ) ^ 3)) + (2 * (ρ + tn ^ indThetaH)) ^ d *
            (2 * Real.pi * (σ ^ 2 * s₁)) ^ (-(d : ℝ) / 2))) ≤ t ^ (-(d : ℝ) / 2 + 1 / 10) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (trans_eventually d hc₁ hc₂)
  refine ⟨N, fun n hn t tn m σ r s₁ ρ h1 h2 h3 h4 hσ hm hr hs hρ hθ => ?_⟩
  obtain ⟨h100, E1, E2, E3, E4⟩ := hN n hn
  subst hr
  have hn100 : (100 : ℝ) ≤ n := by exact_mod_cast h100
  have h4n : (4 : ℝ) ^ n ≥ 4 ^ 100 := pow_le_pow_right₀ (by norm_num) h100
  have ht64 : 64 ≤ t := by
    have : (64 : ℝ) ≤ 4 ^ 100 / 4 := by norm_num
    linarith
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have htn1 : 1 ≤ tn := by linarith
  have htn4 : tn ≤ 4 * t := by linarith
  have ht2 : t ≤ 4 ^ (n + 1) := h4.trans h2
  have hr0 : 1 ≤ t ^ ((41 : ℝ) / 50) := Real.one_le_rpow ht1 (by norm_num)
  have hs₁ : t / 2 ≤ s₁ := by
    have := rpow_le_half ht64
    rw [hs]; linarith
  have hL := trans_L_lower (d := d) (n := n) ht1 ht2
  have hK := trans_K_le hd ht0 htn1 htn4
  have hK' : (2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d ≤ 5 ^ d * 4 * 4 ^ (n + 1) := by
    refine hK.trans ?_
    have : t ^ ((1 : ℝ) / 150) ≤ 4 ^ (n + 1) :=
      (Real.rpow_le_self_of_one_le ht1 (by norm_num)).trans ht2
    calc 5 ^ d * (4 * t ^ ((1 : ℝ) / 150)) = 5 ^ d * 4 * t ^ ((1 : ℝ) / 150) := by ring
      _ ≤ 5 ^ d * 4 * 4 ^ (n + 1) := by gcongr
  have hK0 : 0 ≤ (2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d := by positivity
  have hexp2 : Real.exp (-(m ^ 2)) ≤ Real.exp (-((4 / 5 * (n : ℝ)) ^ 2)) := by
    apply Real.exp_le_exp.2
    have : 0 ≤ 4 / 5 * (n : ℝ) := by positivity
    nlinarith
  have hre : (t ^ ((41 : ℝ) / 50)) ^ (-(d : ℝ) / 2 + 1 / 10) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr0 (by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith)
  have hre0 : 0 ≤ (t ^ ((41 : ℝ) / 50)) ^ (-(d : ℝ) / 2 + 1 / 10) := by positivity
  -- the four terms
  set L := t ^ (-(d : ℝ) / 2 + 1 / 10) with hLdef
  have T1 : 4 * Real.exp (-(c₁ * (n : ℝ) ^ 3)) ≤ L := E1.trans hL
  have T2 : 4 * ((2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d * Real.exp (-(m ^ 2))) ≤ L := by
    calc 4 * ((2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d * Real.exp (-(m ^ 2)))
        ≤ 4 * (5 ^ d * 4 * 4 ^ (n + 1) * Real.exp (-((4 / 5 * (n : ℝ)) ^ 2))) := by gcongr
      _ = 16 * 5 ^ d * 4 ^ (n + 1) * Real.exp (-((4 / 5 * (n : ℝ)) ^ 2)) := by ring
      _ ≤ _ := E2.trans hL
  have T3 : 4 * ((2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d *
      ((t ^ ((41 : ℝ) / 50)) ^ (-(d : ℝ) / 2 + 1 / 10) * Real.exp (-(c₂ * (n : ℝ) ^ 3)))) ≤ L := by
    calc 4 * ((2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d *
          ((t ^ ((41 : ℝ) / 50)) ^ (-(d : ℝ) / 2 + 1 / 10) * Real.exp (-(c₂ * (n : ℝ) ^ 3))))
        ≤ 4 * (5 ^ d * 4 * 4 ^ (n + 1) * (1 * Real.exp (-(c₂ * (n : ℝ) ^ 3)))) := by gcongr
      _ = 16 * 5 ^ d * 4 ^ (n + 1) * Real.exp (-(c₂ * (n : ℝ) ^ 3)) := by ring
      _ ≤ _ := E3.trans hL
  have T4 : 4 * ((2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d *
      ((t ^ ((41 : ℝ) / 50)) ^ (-(d : ℝ) / 2 + 1 / 10) *
        ((2 * (ρ + tn ^ indThetaH)) ^ d * (2 * Real.pi * (σ ^ 2 * s₁)) ^ (-(d : ℝ) / 2)))) ≤ L := by
    have h := trans_T4 hd (n := (n : ℝ)) (by positivity) ht64 htn1 htn4 hσ hs₁ hρ hθ
    have ht17 : Real.exp (17 * Real.log 4 / 1500 * ((n : ℝ) - 1)) ≤ t ^ ((17 : ℝ) / 1500) := by
      have h4t : (4 : ℝ) ^ (n - 1) ≤ t := by
        have : (4 : ℝ) ^ n = 4 ^ (n - 1) * 4 := by
          rw [← pow_succ]; congr 1; omega
        linarith
      calc Real.exp (17 * Real.log 4 / 1500 * ((n : ℝ) - 1))
          = ((4 : ℝ) ^ (n - 1)) ^ ((17 : ℝ) / 1500) := by
            rw [four_pow_eq_exp, ← Real.exp_mul]
            congr 1
            have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega)]; simp
            rw [this]; ring
        _ ≤ t ^ ((17 : ℝ) / 1500) := Real.rpow_le_rpow (by positivity) h4t (by norm_num)
    have hpow : t ^ ((17 : ℝ) / 1500) * t ^ ((133 : ℝ) / 1500 - d / 2) = L := by
      rw [← Real.rpow_add ht0, hLdef]; congr 1; ring
    have ht133 : 0 ≤ t ^ ((133 : ℝ) / 1500 - d / 2) := by positivity
    calc 4 * ((2 * (2 * tn ^ (2 * heavyEps d)) + 1) ^ d *
        ((t ^ ((41 : ℝ) / 50)) ^ (-(d : ℝ) / 2 + 1 / 10) *
          ((2 * (ρ + tn ^ indThetaH)) ^ d * (2 * Real.pi * (σ ^ 2 * s₁)) ^ (-(d : ℝ) / 2))))
        ≤ 4 * (4 * 40 ^ d * (n : ℝ) ^ (2 * d) * t ^ ((133 : ℝ) / 1500 - d / 2)) := by gcongr
      _ = 16 * 40 ^ d * (n : ℝ) ^ (2 * d) * t ^ ((133 : ℝ) / 1500 - d / 2) := by ring
      _ ≤ t ^ ((17 : ℝ) / 1500) * t ^ ((133 : ℝ) / 1500 - d / 2) := by
          gcongr; exact E4.trans ht17
      _ = L := hpow
  nlinarith [T1, T2, T3, T4]

end ElboimSly.Paper.Step
