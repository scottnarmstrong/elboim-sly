/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.TusnadyDensity

/-!
# The step-density error

Tusn'ady-type bound for Bin(m,frac12), Step 1, the bound `eq:sa-step-err`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal Real ENNReal

namespace ElboimSly
namespace StrongApprox

/-- The error `Ẽ(v) = log(s f(μ + s v)) - log φ(v)` of Step 1 in tusn'ady-type bound for Bin(m,frac12). -/
noncomputable def tE (m : ℕ) (v : ℝ) : ℝ := Real.log (tG m v) - Real.log (saphi v)

theorem measurable_tE (m : ℕ) : Measurable (tE m) := by
  unfold tE
  exact (Real.measurable_log.comp (measurable_tG m)).sub
    (Real.measurable_log.comp continuous_saphi.measurable)

theorem four_pow_le {t c : ℝ} (_ht : 0 ≤ t) (_hc : 0 ≤ c) : (t + c) ^ 4 ≤ 8 * (t ^ 4 + c ^ 4) := by
  have h1 : (t + c) ^ 2 ≤ 2 * (t ^ 2 + c ^ 2) := by nlinarith [sq_nonneg (t - c)]
  have h2 : 0 ≤ (t + c) ^ 2 := sq_nonneg _
  calc (t + c) ^ 4 = ((t + c) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (t ^ 2 + c ^ 2)) ^ 2 := by gcongr
    _ ≤ 8 * (t ^ 4 + c ^ 4) := by nlinarith [sq_nonneg (t ^ 2 - c ^ 2)]

/-- The algebraic core of `eq:sa-step-err`. -/
theorem tE_alg {s v q d E1 : ℝ} (hs : 4000 ≤ s) (hv0 : 0 ≤ v) (hvV : v ≤ s / 2400)
    (hq : q = s * v) (hd : |d - q| ≤ 1 / 2)
    (hE1 : |E1| ≤ 2 / s + 32 * (|d| + 1) ^ 4 / (4 * s ^ 2) ^ 3) :
    |E1 - d ^ 2 / (2 * s ^ 2) + v ^ 2 / 2| ≤ 24 / s * (1 + v ^ 3) := by
  have hs0 : 0 < s := by linarith
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hv3 : 0 ≤ v ^ 3 := by positivity
  -- Part 1: the quadratic term
  have hw : |v ^ 2 / 2 - d ^ 2 / (2 * s ^ 2)| ≤ (1 + v ^ 3) / s := by
    have e : v ^ 2 / 2 - d ^ 2 / (2 * s ^ 2) = (q ^ 2 - d ^ 2) / (2 * s ^ 2) := by
      rw [hq]; field_simp
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * s ^ 2), div_le_div_iff₀ (by positivity) hs0]
    have h1 : |q ^ 2 - d ^ 2| ≤ q + 1 / 4 := by
      have h2 : q ^ 2 - d ^ 2 = (q - d) * (q + d) := by ring
      rw [h2, abs_mul]
      have h3 : |q + d| ≤ 2 * q + 1 / 2 := by
        rw [abs_le] at hd ⊢; constructor <;> nlinarith [hd.1, hd.2]
      have h4 : 0 ≤ |q - d| := abs_nonneg _
      have h5 : |q - d| ≤ 1 / 2 := by rw [abs_sub_comm]; exact hd
      calc |q - d| * |q + d| ≤ (1 / 2) * (2 * q + 1 / 2) := by
            apply mul_le_mul h5 h3 (abs_nonneg _) (by norm_num)
        _ = q + 1 / 4 := by ring
    have h6 : v ≤ 1 + v ^ 3 := by
      by_cases hv1 : v ≤ 1
      · linarith
      · push Not at hv1; nlinarith [sq_nonneg v]
    calc |q ^ 2 - d ^ 2| * s ≤ (q + 1 / 4) * s := by gcongr
      _ = (s * v + 1 / 4) * s := by rw [hq]
      _ ≤ (1 + v ^ 3) * (2 * s ^ 2) := by nlinarith [mul_nonneg hs0.le hv3, sq_nonneg s]
  -- Part 2: the binomial error
  have hK : |d| + 1 ≤ s * v + 3 / 2 := by
    have : |d| ≤ q + 1 / 2 := by
      rw [abs_le] at hd ⊢; constructor <;> linarith [hd.1, hd.2]
    rw [hq] at this; linarith
  have hK0 : 0 ≤ |d| + 1 := by positivity
  have hK4 : (|d| + 1) ^ 4 ≤ 8 * ((s * v) ^ 4 + (3 / 2) ^ 4) := by
    calc (|d| + 1) ^ 4 ≤ (s * v + 3 / 2) ^ 4 := by gcongr
      _ ≤ _ := four_pow_le (by positivity) (by norm_num)
  have hE1' : |E1| ≤ (23 + v ^ 3) / s := by
    refine hE1.trans ?_
    have h1 : 32 * (|d| + 1) ^ 4 / (4 * s ^ 2) ^ 3 ≤ 4 * v ^ 4 / s ^ 2 + 81 / (4 * s ^ 6) := by
      rw [div_le_iff₀ (by positivity)]
      have e1 : (4 * v ^ 4 / s ^ 2 + 81 / (4 * s ^ 6)) * (4 * s ^ 2) ^ 3 = 256 * (s * v) ^ 4 + 1296 := by
        field_simp; ring
      rw [e1]; nlinarith
    have h2 : 4 * v ^ 4 / s ^ 2 ≤ v ^ 3 / (600 * s) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : v ^ 4 = v ^ 3 * v := by ring
      have h3 : v ^ 3 * v ≤ v ^ 3 * (s / 2400) := by gcongr
      nlinarith [mul_nonneg hv3 hs0.le]
    have h3 : 81 / (4 * s ^ 6) ≤ 21 / s := by
      rw [div_le_div_iff₀ (by positivity) hs0]
      have : s ^ 6 = s * s ^ 5 := by ring
      have h5 : (1 : ℝ) ≤ s ^ 5 := one_le_pow₀ (by linarith)
      nlinarith [mul_nonneg hs0.le (sub_nonneg.2 h5)]
    have h4 : v ^ 3 / (600 * s) ≤ v ^ 3 / s := by
      rw [div_le_div_iff₀ (by positivity) hs0]; nlinarith [mul_nonneg hv3 hs0.le]
    have e : (23 + v ^ 3) / s = 2 / s + 21 / s + v ^ 3 / s := by ring
    rw [e]; linarith
  have hfinal : 24 / s * (1 + v ^ 3) = 24 * (1 + v ^ 3) / s := by ring
  calc |E1 - d ^ 2 / (2 * s ^ 2) + v ^ 2 / 2|
      = |E1 + (v ^ 2 / 2 - d ^ 2 / (2 * s ^ 2))| := by ring_nf
    _ ≤ |E1| + |v ^ 2 / 2 - d ^ 2 / (2 * s ^ 2)| := abs_add_le _ _
    _ ≤ (23 + v ^ 3) / s + (1 + v ^ 3) / s := add_le_add hE1' hw
    _ ≤ 24 * (1 + v ^ 3) / s := by
        rw [← add_div]; gcongr; nlinarith
    _ = _ := hfinal.symm

/-- The cell index `⌈μ + s v - 1/2⌉` of `μ + s v`, and its basic properties. -/
theorem tus_cell {m : ℕ} (hm : 2000000000 ≤ m) {v : ℝ} (hv0 : 0 ≤ v) (hvV : v ≤ tV m) :
    1 ≤ ⌈sbS m * v + m / 2 - 1 / 2⌉ ∧ ⌈sbS m * v + m / 2 - 1 / 2⌉ ≤ m ∧
      (⌈sbS m * v + m / 2 - 1 / 2⌉ : ℝ) < sbS m * v + m / 2 + 1 / 2 ∧
      sbS m * v + m / 2 - 1 / 2 ≤ (⌈sbS m * v + m / 2 - 1 / 2⌉ : ℝ) := by
  have hm' : (2000000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hsV := sbS_mul_tV_le (m := m)
  have hs0 := sbS_pos m
  have hsv : sbS m * v ≤ sbS m * tV m := by gcongr
  have hsv0 : 0 ≤ sbS m * v := by positivity
  have h1 := Int.ceil_lt_add_one (sbS m * v + m / 2 - 1 / 2)
  have h2 := Int.le_ceil (sbS m * v + m / 2 - 1 / 2)
  refine ⟨?_, ?_, by linarith, h2⟩
  · have : (0 : ℝ) < (⌈sbS m * v + m / 2 - 1 / 2⌉ : ℝ) := by linarith
    have : (0 : ℤ) < ⌈sbS m * v + m / 2 - 1 / 2⌉ := by exact_mod_cast this
    omega
  · have : (⌈sbS m * v + m / 2 - 1 / 2⌉ : ℝ) < m := by linarith
    have : ⌈sbS m * v + m / 2 - 1 / 2⌉ < (m : ℤ) := by exact_mod_cast this
    omega

theorem tG_pos {m : ℕ} (hm : 2000000000 ≤ m) {v : ℝ} (hv0 : 0 ≤ v) (hvV : v ≤ tV m) :
    0 < tG m v := by
  obtain ⟨h1, h2, -, -⟩ := tus_cell hm hv0 hvV
  unfold tG tf
  have := sab_pos (m := m) (j := ⌈sbS m * v + m / 2 - 1 / 2⌉) (by omega) h2
  have := sbS_pos m
  rw [show sbS m * v + m / 2 - 1 / 2 = sbS m * v + m / 2 - 1 / 2 from rfl]
  positivity

theorem tG_eq {m : ℕ} (hm : 2000000000 ≤ m) {v : ℝ} (hv0 : 0 ≤ v) (hvV : v ≤ tV m) :
    tG m v = saphi v * Real.exp (tE m v) := by
  unfold tE
  rw [Real.exp_sub, Real.exp_log (tG_pos hm hv0 hvV), Real.exp_log (saphi_pos v)]
  have := (saphi_pos v).ne'
  field_simp

/-- Tusn'ady-type bound for Bin(m,frac12), `eq:sa-step-err` (`a = 24/s`). -/
theorem tE_abs_le {m : ℕ} (hm : 2000000000 ≤ m) {v : ℝ} (hv0 : 0 ≤ v) (hvV : v ≤ tV m) :
    |tE m v| ≤ 24 / sbS m * (1 + v ^ 3) := by
  obtain ⟨h1, h2, h3, h4⟩ := tus_cell hm hv0 hvV
  set i : ℤ := ⌈sbS m * v + m / 2 - 1 / 2⌉ with hi
  have hm' : (2000000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hs := four_thousand_le_sbS hm
  have hs0 := sbS_pos m
  have hsV := sbS_mul_tV_le (m := m)
  have hVs := tV_le_sbS (m := m)
  have hsv : sbS m * v ≤ sbS m * tV m := by gcongr
  have hsv0 : 0 ≤ sbS m * v := by positivity
  -- the local expansion
  have hloc := binom_local (m := m) (by omega) (j := i) (by
    rw [abs_le]; constructor <;> linarith)
  have hpos : 0 < sab m i := sab_pos (by omega) h2
  have hsq := sbS_sq m
  have hcell : tG m v = sbS m * sab m i := by
    unfold tG tf; rw [← hi]
  have hlogφ : Real.log (saphi v) = -Real.log (√(2 * π)) - v ^ 2 / 2 := by
    rw [saphi_eq, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_inv]
    ring
  have hlogA : Real.log (√(2 * π) * sbS m) = Real.log (√(2 * π)) + Real.log (sbS m) :=
    Real.log_mul (Real.sqrt_pos.2 (by positivity)).ne' hs0.ne'
  have htE : tE m v = (Real.log (sab m i) -
      (-Real.log (√(2 * π) * sbS m) - (((i : ℤ) : ℝ) - m / 2) ^ 2 / (2 * sbS m ^ 2))) -
      (((i : ℤ) : ℝ) - m / 2) ^ 2 / (2 * sbS m ^ 2) + v ^ 2 / 2 := by
    unfold tE
    rw [hcell, Real.log_mul hs0.ne' hpos.ne', hlogφ, hlogA]
    ring
  rw [htE]
  have hm4 : (4 * sbS m ^ 2) = (m : ℝ) + 1 := by rw [hsq]; ring
  refine tE_alg (q := sbS m * v) hs hv0 (by linarith) rfl ?_ ?_
  · rw [abs_le]; constructor <;> linarith
  · rw [hm4]; exact hloc

end StrongApprox
end ElboimSly
