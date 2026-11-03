/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Claim2Series
public import ElboimSly.Frozen.Defs.IndThetaH
public import ElboimSly.Foundations.Brownian.FarHit
public import Mathlib

/-!
# ES22 §4, Claim 4.3: the summation over windows

ES22 Claim 4.3, "Summing over `ℓ ≥ ℓ₀`". With `m = d - 2` and `θ = θ_H = 41/100`:
`∑_{ℓ₀ ≤ ℓ ≤ n} (e^{-(ℓ-1)²} + C_far ((L + 4^{θℓ}) / 2^{ℓ-1})^m) ≤ C L^m t^{-m/2}`
whenever `4^{ℓ₀-1} < t ≤ 4^{ℓ₀}`, `ℓ₀ ≥ 8d` and `t^θ ≤ L`.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

theorem add_pow_le_two_pow_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
    (a + b) ^ m ≤ 2 ^ m * (a ^ m + b ^ m) := by
  have h : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  calc (a + b) ^ m ≤ (2 * max a b) ^ m := pow_le_pow_left₀ (by positivity) h m
    _ = 2 ^ m * (max a b) ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (a ^ m + b ^ m) := by
        gcongr
        rcases le_total a b with h' | h'
        · rw [max_eq_right h']; have := pow_nonneg ha m; linarith
        · rw [max_eq_left h']; have := pow_nonneg hb m; linarith

theorem sum_Icc_geom_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {ℓ₀ : ℕ} (h1 : 1 ≤ ℓ₀) (n : ℕ) :
    ∑ ℓ ∈ Finset.Icc ℓ₀ n, q ^ ℓ ≤ q ^ ℓ₀ / (1 - q) := by
  have : Finset.Icc ℓ₀ n = Finset.Ioc (ℓ₀ - 1) n := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [this]
  have h := sum_Ioc_geom_le hq0 hq1 (ℓ₀ - 1) n
  rwa [Nat.sub_add_cancel h1] at h

/-- For `ℓ ≥ m + 2`: `e^{-(ℓ-1)²} ≤ (1/2)^{mℓ}`. -/
theorem exp_sq_le_half_pow {m ℓ : ℕ} (h : m + 2 ≤ ℓ) :
    Real.exp (-(((ℓ - 1 : ℕ) : ℝ) ^ 2)) ≤ ((1 / 2 : ℝ) ^ m) ^ ℓ := by
  have hℓ : 1 ≤ ℓ := by omega
  have e : ((1 / 2 : ℝ) ^ m) ^ ℓ = Real.exp (-((m * ℓ : ℕ) : ℝ) * Real.log 2) := by
    rw [← pow_mul, one_div, inv_pow, ← Real.exp_log (show (0 : ℝ) < 2 ^ (m * ℓ) by positivity),
      ← Real.exp_neg, Real.log_pow]
    congr 1; push_cast; ring
  rw [e]
  apply Real.exp_le_exp.2
  have hlog : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Nat.cast_sub hℓ]
  have hm : (m : ℝ) + 2 ≤ ℓ := by exact_mod_cast h
  have h1 : ((m * ℓ : ℕ) : ℝ) * Real.log 2 ≤ ((ℓ : ℝ) - 1) ^ 2 := by
    push_cast
    have hℓ0 : (0 : ℝ) ≤ ℓ := by positivity
    have hm0 : (0 : ℝ) ≤ m := by positivity
    calc (m : ℝ) * ℓ * Real.log 2 ≤ (m : ℝ) * ℓ * 1 := by gcongr
      _ ≤ ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
  push_cast at h1 ⊢
  linarith

theorem rpow_two_mul_nat (c : ℝ) (ℓ : ℕ) : (2 : ℝ) ^ (c * ℓ) = ((2 : ℝ) ^ c) ^ ℓ := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]

theorem sqrt_le_two_pow {t : ℝ} {ℓ₀ : ℕ} (ht : t ≤ (4 : ℝ) ^ ℓ₀) : Real.sqrt t ≤ 2 ^ ℓ₀ := by
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  rwa [show ((2 : ℝ) ^ ℓ₀) ^ 2 = 4 ^ ℓ₀ by rw [← pow_mul, mul_comm, pow_mul]; norm_num]

/-- The three-term bound on one window. -/
theorem window3_term_le (d : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {L : ℝ} (hL : 1 ≤ L) :
    ElboimSly.Brownian.Cfar d * ((L + ((4 : ℝ) ^ ℓ) ^ indThetaH) / 2 ^ (ℓ - 1)) ^ (d - 2) ≤
      ElboimSly.Brownian.Cfar d * 4 ^ (d - 2) *
        (L ^ (d - 2) * ((1 / 2 : ℝ) ^ (d - 2)) ^ ℓ +
          ((2 : ℝ) ^ ((2 * indThetaH - 1) * ((d - 2 : ℕ) : ℝ))) ^ ℓ) := by
  set m := d - 2 with hm
  set y : ℝ := ((4 : ℝ) ^ ℓ) ^ indThetaH with hy
  have hy0 : 0 ≤ y := by positivity
  have hC := (ElboimSly.Brownian.Cfar_pos d).le
  have hx : (0 : ℝ) < 2 ^ ℓ := by positivity
  have h2 : (2 : ℝ) ^ (ℓ - 1) = 2 ^ ℓ / 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    simp [pow_succ]
  have hy' : y = (2 : ℝ) ^ (2 * indThetaH * ℓ) := by
    rw [hy, show (4 : ℝ) ^ ℓ = (2 : ℝ) ^ ((2 : ℝ) * ℓ) by
      rw [rpow_two_mul_nat]; norm_num, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  have hym : y ^ m = (2 : ℝ) ^ (2 * indThetaH * ℓ * m) := by
    rw [hy', ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hxm : ((2 : ℝ) ^ ℓ) ^ m = (2 : ℝ) ^ ((ℓ : ℝ) * m) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ℓ) m, ← Real.rpow_natCast (2 : ℝ) ℓ,
      ← Real.rpow_mul (by norm_num)]
  have hρ1 : ((1 / 2 : ℝ) ^ m) ^ ℓ = 1 / ((2 : ℝ) ^ ℓ) ^ m := by
    rw [← pow_mul, mul_comm, pow_mul, one_div, inv_pow, one_div, inv_pow]
  have hρ2 : y ^ m / ((2 : ℝ) ^ ℓ) ^ m = ((2 : ℝ) ^ ((2 * indThetaH - 1) * (m : ℝ))) ^ ℓ := by
    rw [hym, hxm, ← rpow_two_mul_nat, ← Real.rpow_sub (by norm_num)]
    congr 1; ring
  have e1 : ((L + y) / 2 ^ (ℓ - 1)) ^ m = 2 ^ m * (L + y) ^ m / ((2 : ℝ) ^ ℓ) ^ m := by
    rw [h2, div_pow, div_pow]; field_simp
  have e2 : (L + y) ^ m ≤ 2 ^ m * (L ^ m + y ^ m) := add_pow_le_two_pow_mul (by linarith) hy0 m
  have hxp : 0 < ((2 : ℝ) ^ ℓ) ^ m := by positivity
  calc ElboimSly.Brownian.Cfar d * ((L + y) / 2 ^ (ℓ - 1)) ^ m
      = ElboimSly.Brownian.Cfar d * (2 ^ m * (L + y) ^ m / ((2 : ℝ) ^ ℓ) ^ m) := by rw [e1]
    _ ≤ ElboimSly.Brownian.Cfar d * (2 ^ m * (2 ^ m * (L ^ m + y ^ m)) / ((2 : ℝ) ^ ℓ) ^ m) := by
        gcongr
    _ = ElboimSly.Brownian.Cfar d * 4 ^ m * (L ^ m * (1 / ((2 : ℝ) ^ ℓ) ^ m) +
          y ^ m / ((2 : ℝ) ^ ℓ) ^ m) := by
        rw [show (4 : ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
        field_simp
    _ = _ := by rw [hρ1, hρ2]

/-- **The sum over windows** of ES22 Claim 4.3. -/
theorem claim3_sum (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ₀ n : ℕ) (t L : ℝ), 8 * d ≤ ℓ₀ → (4 : ℝ) ^ (ℓ₀ - 1) < t →
      t ≤ (4 : ℝ) ^ ℓ₀ → t ^ indThetaH ≤ L →
      ∑ ℓ ∈ Finset.Icc ℓ₀ n, (Real.exp (-(((ℓ - 1 : ℕ) : ℝ) ^ 2)) +
        ElboimSly.Brownian.Cfar d * ((L + ((4 : ℝ) ^ ℓ) ^ indThetaH) / 2 ^ (ℓ - 1)) ^ (d - 2)) ≤
        C * L ^ (d - 2) * t ^ (-((d - 2 : ℕ) : ℝ) / 2) := by
  set m : ℕ := d - 2 with hm
  have hθ : indThetaH = 41 / 100 := rfl
  set ρ1 : ℝ := (1 / 2 : ℝ) ^ m with hρ1
  set ρ2 : ℝ := (2 : ℝ) ^ ((2 * indThetaH - 1) * (m : ℝ)) with hρ2
  have hm3 : (3 : ℝ) ≤ m := by
    have : 3 ≤ m := by omega
    exact_mod_cast this
  have hρ10 : 0 < ρ1 := by positivity
  have hρ11 : ρ1 < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hρ20 : 0 < ρ2 := by positivity
  have hρ21 : ρ2 < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    rw [hθ]; nlinarith
  set Cf := ElboimSly.Brownian.Cfar d with hCf
  have hCf0 : 0 < Cf := ElboimSly.Brownian.Cfar_pos d
  set B : ℝ := Cf * 4 ^ m with hB
  have hB0 : 0 < B := by positivity
  refine ⟨(1 + B) / (1 - ρ1) + B / (1 - ρ2), by
    have : 0 < 1 - ρ1 := by linarith
    have : 0 < 1 - ρ2 := by linarith
    positivity, ?_⟩
  intro ℓ₀ n t L h8 ht1 ht2 htL
  have hℓ₀1 : 1 ≤ ℓ₀ := by omega
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht1
  have hL1 : 1 ≤ L := by
    refine le_trans ?_ htL
    have : (1 : ℝ) ≤ t := le_trans (one_le_pow₀ (by norm_num)) ht1.le
    exact Real.one_le_rpow this (by rw [hθ]; norm_num)
  have hLm : 1 ≤ L ^ m := one_le_pow₀ hL1
  -- termwise bound
  have hterm : ∀ ℓ ∈ Finset.Icc ℓ₀ n, Real.exp (-(((ℓ - 1 : ℕ) : ℝ) ^ 2)) +
      Cf * ((L + ((4 : ℝ) ^ ℓ) ^ indThetaH) / 2 ^ (ℓ - 1)) ^ m ≤
      (1 + B * L ^ m) * ρ1 ^ ℓ + B * ρ2 ^ ℓ := by
    intro ℓ hℓ
    have hℓ' := (Finset.mem_Icc.1 hℓ).1
    have h1 := exp_sq_le_half_pow (m := m) (ℓ := ℓ) (by omega)
    have h2 := window3_term_le d (ℓ := ℓ) (by omega) hL1
    have : (1 + B * L ^ m) * ρ1 ^ ℓ + B * ρ2 ^ ℓ =
        ρ1 ^ ℓ + B * (L ^ m * ρ1 ^ ℓ + ρ2 ^ ℓ) := by ring
    rw [this]
    exact add_le_add h1 h2
  calc ∑ ℓ ∈ Finset.Icc ℓ₀ n, (Real.exp (-(((ℓ - 1 : ℕ) : ℝ) ^ 2)) +
        Cf * ((L + ((4 : ℝ) ^ ℓ) ^ indThetaH) / 2 ^ (ℓ - 1)) ^ m)
      ≤ ∑ ℓ ∈ Finset.Icc ℓ₀ n, ((1 + B * L ^ m) * ρ1 ^ ℓ + B * ρ2 ^ ℓ) :=
        Finset.sum_le_sum hterm
    _ = (1 + B * L ^ m) * ∑ ℓ ∈ Finset.Icc ℓ₀ n, ρ1 ^ ℓ + B * ∑ ℓ ∈ Finset.Icc ℓ₀ n, ρ2 ^ ℓ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (1 + B * L ^ m) * (ρ1 ^ ℓ₀ / (1 - ρ1)) + B * (ρ2 ^ ℓ₀ / (1 - ρ2)) := by
        gcongr
        · exact sum_Icc_geom_le hρ10 hρ11 hℓ₀1 n
        · exact sum_Icc_geom_le hρ20 hρ21 hℓ₀1 n
    _ ≤ _ := by
        have hs : Real.sqrt t ≤ 2 ^ ℓ₀ := sqrt_le_two_pow ht2
        have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
        have hx0 : (0 : ℝ) < 2 ^ ℓ₀ := by positivity
        have hrt : t ^ (-(m : ℝ) / 2) = ((Real.sqrt t) ^ m)⁻¹ := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
            ← Real.rpow_neg ht0.le]
          congr 1; ring
        have a1 : ρ1 ^ ℓ₀ ≤ t ^ (-(m : ℝ) / 2) := by
          rw [hρ1, hrt, ← pow_mul, mul_comm, pow_mul, one_div, inv_pow, inv_pow]
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_left₀ hs0.le hs m
        have a2 : ρ2 ^ ℓ₀ ≤ L ^ m * t ^ (-(m : ℝ) / 2) := by
          have e : ρ2 ^ ℓ₀ = ((2 : ℝ) ^ ℓ₀) ^ ((2 * indThetaH - 1) * (m : ℝ)) := by
            rw [hρ2, ← rpow_two_mul_nat, ← Real.rpow_natCast (2 : ℝ) ℓ₀, ← Real.rpow_mul (by norm_num),
              mul_comm]
          have hneg : (2 * indThetaH - 1) * (m : ℝ) ≤ 0 := by
            rw [hθ]; nlinarith
          have step1 : ((2 : ℝ) ^ ℓ₀) ^ ((2 * indThetaH - 1) * (m : ℝ)) ≤
              (Real.sqrt t) ^ ((2 * indThetaH - 1) * (m : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hs0 hs hneg
          have step2 : (Real.sqrt t) ^ ((2 * indThetaH - 1) * (m : ℝ)) =
              (t ^ indThetaH) ^ m * t ^ (-(m : ℝ) / 2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]
            have : (t ^ indThetaH) ^ m = t ^ (indThetaH * m) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
            rw [this, ← Real.rpow_add ht0]
            congr 1; ring
          have step3 : (t ^ indThetaH) ^ m ≤ L ^ m :=
            pow_le_pow_left₀ (Real.rpow_nonneg ht0.le _) htL m
          rw [e]
          refine step1.trans (step2 ▸ ?_)
          gcongr
        have hq1 : 0 < 1 - ρ1 := by linarith
        have hq2 : 0 < 1 - ρ2 := by linarith
        have hT : 0 < t ^ (-(m : ℝ) / 2) := Real.rpow_pos_of_pos ht0 _
        calc (1 + B * L ^ m) * (ρ1 ^ ℓ₀ / (1 - ρ1)) + B * (ρ2 ^ ℓ₀ / (1 - ρ2))
            ≤ ((1 + B) * L ^ m) * (t ^ (-(m : ℝ) / 2) / (1 - ρ1)) +
              B * (L ^ m * t ^ (-(m : ℝ) / 2) / (1 - ρ2)) := by
              gcongr
              · nlinarith [hLm, hB0]
          _ = _ := by
              rw [hm]; field_simp

end ElboimSly.Paper

end
