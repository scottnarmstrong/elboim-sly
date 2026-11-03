/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Claim56Small
public import ElboimSly.Foundations.Brownian.Tube
public import Mathlib

/-!
# The constant `γ` of ES22 §5

The constant γ; Properties of γ.
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Brownian

/-- The constant γ: `K_* = 4·10⁴`. -/
def escKstar : ℝ := 4 * 10 ^ 4

/-- The constant γ: `c_* = c_tube(d, K_*)/2`. -/
noncomputable def escCstar (d : ℕ) : ℝ := ctube d escKstar / 2

/-- The constant γ: `D = 50.5 d C₁`. -/
noncomputable def escD (d : ℕ) : ℝ := (101 / 2 : ℝ) * d * CBox

/-- The constant γ: `k₀ = c₁^{202d} 4^{-201 d C₁} 6^{-d C₁}/4`. -/
noncomputable def escK0 (d : ℕ) : ℝ :=
  cBox ^ (202 * d) * ((4 : ℝ) ^ (201 * d * CBox))⁻¹ * ((6 : ℝ) ^ (d * CBox))⁻¹ / 4

/-- The constant γ: `γ₅₆(d)`. -/
noncomputable def escGamma56 (d : ℕ) : ℝ :=
  1 + 40 * escD d + 40 * Real.logb 2 (1 / escCstar d) +
    Real.logb 2 ((4 : ℝ) ^ escD d / (escK0 d * escCstar d ^ 2))

/-- The constant γ: `γ(d) = max(3, γ₁(d), γ₅₆(d))`. -/
noncomputable def escGamma (d : ℕ) : ℝ := max 3 (max (gamma1 d) (escGamma56 d))

lemma tubeC0_pos' (d : ℕ) (K : ℝ) : 0 < tubeC0 d K := by unfold tubeC0; positivity

lemma tubeC0_le_one (d : ℕ) {K : ℝ} (hK : 0 ≤ K) : tubeC0 d K ≤ 1 := by
  unfold tubeC0
  rw [Real.exp_le_one_iff]
  have : (0 : ℝ) ≤ tubeH K := le_trans (by norm_num) (le_max_right _ _)
  have h2 : 0 ≤ 4 / 100 * tubeH K * d * (tubeH K * K + 1) := by positivity
  linarith

lemma escCstar_pos (d : ℕ) : 0 < escCstar d := by
  unfold escCstar ctube; have := tubeC0_pos' d (8 * escKstar); have := tubeC0_pos' d (52 * escKstar)
  positivity

lemma escCstar_le_half (d : ℕ) : escCstar d ≤ 1 / 2 := by
  unfold escCstar ctube
  have hK : (0 : ℝ) ≤ escKstar := by unfold escKstar; norm_num
  have h1 := tubeC0_le_one d (K := 8 * escKstar) (by positivity)
  have h2 := tubeC0_le_one d (K := 52 * escKstar) (by positivity)
  have h3 := tubeC0_pos' d (8 * escKstar)
  have h4 := tubeC0_pos' d (52 * escKstar)
  have : tubeC0 d (8 * escKstar) * tubeC0 d (52 * escKstar) ≤ 1 := by nlinarith
  linarith

lemma escK0_pos (d : ℕ) : 0 < escK0 d := by
  have := cBox_pos; unfold escK0; positivity

lemma escK0_le (d : ℕ) : escK0 d ≤ 1 / 4 := by
  have h0 := cBox_pos
  have h1 := cBox_le_one
  unfold escK0
  have a : cBox ^ (202 * d) ≤ 1 := pow_le_one₀ h0.le h1
  have b : ((4 : ℝ) ^ (201 * d * CBox))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have c : ((6 : ℝ) ^ (d * CBox))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hb : 0 < ((4 : ℝ) ^ (201 * d * CBox))⁻¹ := by positivity
  have hc : 0 < ((6 : ℝ) ^ (d * CBox))⁻¹ := by positivity
  have : cBox ^ (202 * d) * ((4 : ℝ) ^ (201 * d * CBox))⁻¹ * ((6 : ℝ) ^ (d * CBox))⁻¹ ≤ 1 := by
    have ha : 0 < cBox ^ (202 * d) := by positivity
    have h2 : cBox ^ (202 * d) * ((4 : ℝ) ^ (201 * d * CBox))⁻¹ ≤ 1 := by nlinarith
    have h3 : 0 < cBox ^ (202 * d) * ((4 : ℝ) ^ (201 * d * CBox))⁻¹ := by positivity
    nlinarith
  linarith

lemma escD_nonneg (d : ℕ) : 0 ≤ escD d := by unfold escD; positivity

/-- Properties of γ(a). -/
theorem escGamma_gt_two (d : ℕ) : 2 < escGamma d :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem gamma1_le_escGamma (d : ℕ) : gamma1 d ≤ escGamma d :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem escGamma56_le_escGamma (d : ℕ) : escGamma56 d ≤ escGamma d :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- Properties of γ(c). -/
theorem escGamma_lower_bound (d : ℕ) {n β γ' : ℝ} (hn : 2 ≤ n) (hβ1 : 1 ≤ β)
    (hβ : β < 4 * n ^ 40) {m : ℕ} (hm : (m : ℝ) ≤ 20 * Real.logb 2 n + 1)
    (hγ : escGamma56 d ≤ γ') :
    n ^ (-γ' + 1) ≤ escK0 d * β ^ (-escD d) * escCstar d ^ (2 * m) := by
  have hc := escCstar_pos d
  have hc1 : escCstar d ≤ 1 := by linarith [escCstar_le_half d]
  have hk := escK0_pos d
  have hk4 := escK0_le d
  have hD := escD_nonneg d
  have hn0 : 0 < n := by linarith
  have hβ0 : 0 < β := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have hlc0 : Real.log (escCstar d) ≤ 0 := Real.log_nonpos hc.le hc1
  have hlk0 : Real.log (escK0 d) ≤ -Real.log 4 := by
    have : Real.log (escK0 d) ≤ Real.log (1 / 4) := Real.log_le_log hk hk4
    rw [one_div, Real.log_inv] at this; exact this
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  obtain ⟨lX, hlX⟩ : ∃ lX, lX = escD d * Real.log 4 - Real.log (escK0 d)
      - 2 * Real.log (escCstar d) := ⟨_, rfl⟩
  have hlX0 : 0 ≤ lX := by
    have : 0 ≤ escD d * Real.log 4 := by positivity
    linarith
  have hlogb : Real.logb 2 n = Real.log n / Real.log 2 := rfl
  have hγ56 : escGamma56 d = 1 + 40 * escD d + 40 * (-Real.log (escCstar d) / Real.log 2)
      + lX / Real.log 2 := by
    unfold escGamma56
    rw [Real.logb, Real.logb, one_div, Real.log_inv, Real.log_div (by positivity)
      (by positivity), Real.log_rpow (by norm_num), Real.log_mul hk.ne' (by positivity),
      Real.log_pow, hlX]
    push_cast; ring
  have hβl : Real.log β ≤ Real.log 4 + 40 * Real.log n := by
    have : Real.log β ≤ Real.log (4 * n ^ 40) := Real.log_le_log hβ0 hβ.le
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    push_cast at this
    exact this
  have hm2 : (2 * m : ℝ) ≤ 2 + 40 * (Real.log n / Real.log 2) := by
    rw [hlogb] at hm; linarith
  have hmlc : (2 + 40 * (Real.log n / Real.log 2)) * Real.log (escCstar d)
      ≤ (2 * m : ℝ) * Real.log (escCstar d) :=
    mul_le_mul_of_nonpos_right hm2 hlc0
  have hr : 1 ≤ Real.log n / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
  have hkey : lX ≤ lX * (Real.log n / Real.log 2) := by nlinarith
  have hDl : escD d * Real.log β ≤ escD d * (Real.log 4 + 40 * Real.log n) :=
    mul_le_mul_of_nonneg_left hβl hD
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  rw [Real.log_rpow hn0, Real.log_mul (by positivity) (by positivity),
    Real.log_mul hk.ne' (by positivity), Real.log_rpow hβ0, Real.log_pow]
  have h56 : (-γ' + 1) * Real.log n ≤ (1 - escGamma56 d) * Real.log n :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hexp : (1 - escGamma56 d) * Real.log n
      = -(40 * escD d) * Real.log n
        + 40 * Real.log (escCstar d) * (Real.log n / Real.log 2)
        - lX * (Real.log n / Real.log 2) := by
    rw [hγ56]; field_simp; ring
  push_cast
  nlinarith [hexp, h56, hmlc, hDl, hkey]

end ElboimSly.Paper
