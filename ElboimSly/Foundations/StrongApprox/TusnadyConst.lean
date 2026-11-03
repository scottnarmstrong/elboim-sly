/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Shift
public import ElboimSly.Foundations.StrongApprox.BinomialLocal

/-!
# Constants for the Tusnády-type bound

Tusn'ady-type bound for Bin(m,frac12), the constants `ε₁ = 1/4800`, `C₁ = 2500`, `m₀ = 2·10⁹` and the
numerical consequences (`eq:sa-m0`, `eq:sa-ld`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal Real

namespace ElboimSly
namespace StrongApprox

/-- `V = ε₁ √m` with `ε₁ = 1/4800`. -/
noncomputable def tV (m : ℕ) : ℝ := √(m : ℝ) / 4800

theorem tV_sq (m : ℕ) : tV m ^ 2 = (m : ℝ) / 4800 ^ 2 := by
  unfold tV; rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg m)]

theorem tV_pos {m : ℕ} (hm : 1 ≤ m) : 0 < tV m := by
  unfold tV; have : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

/-- Written proof `eq:sa-m0`: `100 s e^{-3V²/16} ≤ 1` for `m ≥ 2·10⁹`. -/
theorem tus_m0 {m : ℕ} (hm : 2000000000 ≤ m) :
    100 * sbS m * Real.exp (-3 * tV m ^ 2 / 16) ≤ 1 := by
  have hm' : (2000000000 : ℝ) ≤ m := by exact_mod_cast hm
  set c : ℝ := 3 / (16 * 4800 ^ 2) with hc
  have hexp : -3 * tV m ^ 2 / 16 = -(c * m) := by
    rw [tV_sq, hc]; field_simp
  rw [hexp, Real.exp_neg]
  have hs : 100 * sbS m = 50 * √((m : ℝ) + 1) := by unfold sbS; ring
  rw [hs]
  rw [← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  set A : ℝ := 2000000001 with hA
  set h : ℝ := (m : ℝ) - 2000000000 with hh
  have hh0 : 0 ≤ h := by linarith
  have hA0 : 0 < A := by norm_num [hA]
  have hsA : √A ^ 2 = A := Real.sq_sqrt hA0.le
  have h1 : √((m : ℝ) + 1) ≤ √A * (1 + h / (2 * A)) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : (√A * (1 + h / (2 * A))) ^ 2 = A + h + h ^ 2 / (4 * A) := by
      rw [mul_pow, hsA]; field_simp; ring
    rw [this]
    have : 0 ≤ h ^ 2 / (4 * A) := by positivity
    have : (m : ℝ) + 1 = A + h := by rw [hh, hA]; ring
    linarith
  have h2 : Real.exp 16 * (1 + c * h) ≤ Real.exp (c * m) := by
    have e : c * (m : ℝ) = c * 2000000000 + c * h := by rw [hh]; ring
    rw [e, Real.exp_add]
    have h16 : Real.exp 16 ≤ Real.exp (c * 2000000000) := Real.exp_le_exp.2 (by rw [hc]; norm_num)
    have h17 : 1 + c * h ≤ Real.exp (c * h) := by linarith [Real.add_one_le_exp (c * h)]
    have h18 : 0 ≤ 1 + c * h := by have : 0 ≤ c * h := by rw [hc]; positivity
                                   linarith
    calc Real.exp 16 * (1 + c * h) ≤ Real.exp (c * 2000000000) * (1 + c * h) := by gcongr
      _ ≤ _ := by gcongr
  have h3 : 50 * √A ≤ Real.exp 16 := by
    have hsq : √A ≤ 44722 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num [hA]
    have : (2.7 : ℝ) ^ 16 ≤ Real.exp 16 := by
      have e1 : Real.exp 16 = Real.exp 1 ^ 16 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e1]
      have := Real.exp_one_gt_d9
      gcongr
      linarith
    have h5 : (50 * 44722 : ℝ) ≤ 2.7 ^ 16 := by norm_num
    linarith
  have h4 : 1 + h / (2 * A) ≤ 1 + c * h := by
    have : h / (2 * A) ≤ c * h := by
      rw [div_le_iff₀ (by positivity), hc, hA]
      have : 0 ≤ h := hh0
      nlinarith [mul_nonneg this this]
    linarith
  calc 50 * √((m : ℝ) + 1) ≤ 50 * (√A * (1 + h / (2 * A))) := by gcongr
    _ = (50 * √A) * (1 + h / (2 * A)) := by ring
    _ ≤ Real.exp 16 * (1 + c * h) := by
        have : 0 ≤ 1 + h / (2 * A) := by positivity
        have h6 : 0 ≤ 1 + c * h := by have : 0 ≤ c * h := by rw [hc]; positivity
                                      linarith
        calc (50 * √A) * (1 + h / (2 * A)) ≤ Real.exp 16 * (1 + h / (2 * A)) := by gcongr
          _ ≤ _ := by gcongr
    _ ≤ _ := h2

theorem sqrt_le_two_mul_sbS (m : ℕ) : √(m : ℝ) ≤ 2 * sbS m := by
  unfold sbS
  have : √(m : ℝ) ≤ √((m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  linarith

theorem four_thousand_le_sbS {m : ℕ} (hm : 2000000000 ≤ m) : 4000 ≤ sbS m := by
  have hm' : (2000000000 : ℝ) ≤ m := by exact_mod_cast hm
  unfold sbS
  have : (8000 : ℝ) ≤ √((m : ℝ) + 1) := by
    calc (8000 : ℝ) = √(8000 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  linarith

theorem sbS_mul_tV_le {m : ℕ} : sbS m * tV m ≤ ((m : ℝ) + 1) / 9600 := by
  unfold sbS tV
  have h1 : √(m : ℝ) ≤ √((m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have h2 : √((m : ℝ) + 1) * √((m : ℝ) + 1) = (m : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  have h3 : 0 ≤ √(m : ℝ) := Real.sqrt_nonneg _
  have : √((m : ℝ) + 1) / 2 * (√(m : ℝ) / 4800) = √((m : ℝ) + 1) * √(m : ℝ) / 9600 := by ring
  rw [this]
  have : √((m : ℝ) + 1) * √(m : ℝ) ≤ (m : ℝ) + 1 := by nlinarith
  linarith

theorem sbS_mul_tV_ge {m : ℕ} : (m : ℝ) / 9600 ≤ sbS m * tV m := by
  unfold sbS tV
  have h1 : √(m : ℝ) ≤ √((m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have h2 : √(m : ℝ) * √(m : ℝ) = (m : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg m)
  have h3 : 0 ≤ √(m : ℝ) := Real.sqrt_nonneg _
  have : √((m : ℝ) + 1) / 2 * (√(m : ℝ) / 4800) = √((m : ℝ) + 1) * √(m : ℝ) / 9600 := by ring
  rw [this]
  have : √(m : ℝ) * √(m : ℝ) ≤ √((m : ℝ) + 1) * √(m : ℝ) := by gcongr
  linarith

theorem tV_le_sbS {m : ℕ} : tV m ≤ sbS m / 2400 := by
  have := sqrt_le_two_mul_sbS m
  unfold tV; linarith

theorem sbS_sq_ge {m : ℕ} : (m : ℝ) / 4 ≤ sbS m ^ 2 := by
  rw [sbS_sq]; linarith

/-- Written proof `eq:sa-ld`, in the three parts used later. -/
theorem tus_ld {m : ℕ} (hm : 2000000000 ≤ m) {x : ℝ} (_hx0 : 0 ≤ x) (hx : x ≤ tV m / 4) :
    Real.exp (-(tV m ^ 2 / 4)) ≤ saPhib x / (12 * sbS m) ∧
    Real.exp (-(tV m ^ 2 / 2)) ≤ saPhib x ∧
    saPhib (tV m) < saPhib x / (6 * sbS m) := by
  have hs := four_thousand_le_sbS hm
  have hs0 : 0 < sbS m := by linarith
  have hV0 : 0 ≤ tV m := (tV_pos (by omega)).le
  have hm0 := tus_m0 hm
  set V := tV m with hV
  set s := sbS m with hsdef
  set E := Real.exp (-(V ^ 2 / 16)) with hE
  set F := Real.exp (-3 * V ^ 2 / 16) with hF
  have hEpos : 0 < E := Real.exp_pos _
  have hFle : F ≤ 1 / (100 * s) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hFpos : 0 < F := Real.exp_pos _
  -- lower bound for the tail
  have hc0 : (0.146 : ℝ) ≤ (√(2 * π))⁻¹ * Real.exp (-1) := by
    have h1 := sqrt_two_pi_le
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have h4 : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
    rw [h3, ← mul_inv, le_inv_comm₀ (by norm_num) (by positivity)]
    have : √(2 * π) * Real.exp 1 ≤ 2.51 * 2.7182818286 := by
      have := Real.exp_pos 1
      nlinarith
    norm_num at this ⊢
    linarith
  have hPb : 0.146 * E ≤ saPhib x := by
    have h1 : saPhib (V / 4) ≤ saPhib x := saPhib_antitone hx
    have h2 := saPhib_ge_exp (t := V / 4) (by positivity)
    have h3 : Real.exp (-((V / 4) ^ 2)) = E := by rw [hE]; congr 1; ring
    rw [h3] at h2
    calc 0.146 * E ≤ (√(2 * π))⁻¹ * Real.exp (-1) * E := by gcongr
      _ ≤ saPhib (V / 4) := h2
      _ ≤ _ := h1
  have e4 : Real.exp (-(V ^ 2 / 4)) = E * F := by
    rw [hE, hF, ← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(V ^ 2 / 2)) ≤ E * F := by
    have h1 : Real.exp (-(V ^ 2 / 2)) = Real.exp (-(V ^ 2 / 4)) * Real.exp (-(V ^ 2 / 4)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-(V ^ 2 / 4)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg V])
    have h3 : 0 < Real.exp (-(V ^ 2 / 4)) := Real.exp_pos _
    rw [h1]
    calc Real.exp (-(V ^ 2 / 4)) * Real.exp (-(V ^ 2 / 4)) ≤ Real.exp (-(V ^ 2 / 4)) * 1 := by
          gcongr
      _ = E * F := by rw [mul_one, e4]
  have hEF : E * F ≤ E / (100 * s) := by
    calc E * F ≤ E * (1 / (100 * s)) := by gcongr
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e4, le_div_iff₀ (by positivity)]
    calc E * F * (12 * s) ≤ E / (100 * s) * (12 * s) := by gcongr
      _ = E * (12 / 100) := by field_simp
      _ ≤ 0.146 * E := by nlinarith
      _ ≤ _ := hPb
  · refine e2.trans (hEF.trans ?_)
    have : E / (100 * s) ≤ 0.146 * E := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact this.trans hPb
  · have h1 := saPhib_le_half_exp hV0
    have h2 : Real.exp (-(V ^ 2) / 2) = Real.exp (-(V ^ 2 / 2)) := by congr 1; ring
    rw [h2] at h1
    refine lt_of_le_of_lt h1 ?_
    rw [lt_div_iff₀ (by positivity)]
    calc Real.exp (-(V ^ 2 / 2)) / 2 * (6 * s) ≤ E / (100 * s) / 2 * (6 * s) := by
          gcongr; exact e2.trans hEF
      _ = E * (3 / 100) := by field_simp; ring
      _ < 0.146 * E := by nlinarith
      _ ≤ _ := hPb

end StrongApprox
end ElboimSly
