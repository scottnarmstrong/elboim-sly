/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.BoxMain
public import Mathlib

/-!
# Confined lower bound in boxes; Claim 5.6 for `4^j ≤ β`

Confined lower bound in boxes; ES22 Claim 5.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- A box `∏ [m_i, m_i + L_i - 1]`. -/
def boxSet (m : Fin d → ℤ) (L : Fin d → ℕ) : Set (Fin d → ℤ) :=
  {v | ∀ i, v i ∈ Icc (m i) (m i + L i - 1)}

/-- Confined lower bound in boxes, for the kernel. -/
theorem box_d (m : Fin d → ℤ) (L : Fin d → ℕ) (hL : ∀ i, 1 ≤ L i) {y z : Fin d → ℤ}
    (hy : y ∈ boxSet m L) (hz : z ∈ boxSet m L) {r : ℝ≥0}
    (hr1 : ∀ i, (L i : ℝ) ^ 2 / 16 ≤ r) (hr2 : ∀ i, (r : ℝ) ≤ 16 * (L i : ℝ) ^ 2) :
    ∏ i, cBox / (L i : ℝ) ^ CBox ≤ kernel (boxSet m L) r y z := by
  have e : boxSet m L = {v : Fin d → ℤ | ∀ i, v i ∈ Icc (m i) (m i + L i - 1)} := rfl
  rw [e, kernel_pi]
  refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
  · exact div_nonneg cBox_pos.le (by positivity)
  · exact box (hL i) (hy i) (hz i) (hr1 i) (hr2 i)

/-- The side lengths of the box `B^-` of Claim 5.6: `2^(j-1)` in the first coordinate and
`2^j` in the others. -/
def sideLen (d j : ℕ) (i : Fin d) : ℕ := if i.val = 0 then 2 ^ (j - 1) else 2 ^ j

/-- The box `B^- = u + ([0, N_j/2 - 1] × [0, N_j - 1]^{d-1})`. -/
def claimBox (u : Fin d → ℤ) (j : ℕ) : Set (Fin d → ℤ) := boxSet u (sideLen d j)

/-- ES22 Claim 5.6, kernel form. -/
theorem claim56_small_kernel {j : ℕ} (hj : 2 ≤ j) (u : Fin d → ℤ) {v w : Fin d → ℤ}
    (hv : v ∈ claimBox u j) (hw : w ∈ claimBox u j) {t : ℝ≥0}
    (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : (t : ℝ) ≤ 4 ^ j) :
    cBox ^ d / ((2 : ℝ) ^ j) ^ (d * CBox) ≤ kernel (claimBox u j) t v w := by
  have hL : ∀ i, 1 ≤ sideLen d j i := by
    intro i; unfold sideLen; split_ifs <;> exact Nat.one_le_two_pow
  have hj1 : (4 : ℝ) ^ j = 4 * 4 ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hLsq : ∀ i, ((sideLen d j i : ℕ) : ℝ) ^ 2 = if i.val = 0 then 4 ^ (j - 1) else 4 ^ j := by
    intro i
    unfold sideLen
    split_ifs
    · push_cast
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    · push_cast
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h4pos : (0 : ℝ) < 4 ^ (j - 1) := by positivity
  have h := box_d u (sideLen d j) hL hv hw (r := t) (fun i => ?_) (fun i => ?_)
  · refine le_trans ?_ h
    have hle : ∀ i, sideLen d j i ≤ 2 ^ j := by
      intro i; unfold sideLen; split_ifs
      · exact Nat.pow_le_pow_right (by norm_num) (by omega)
      · exact le_rfl
    calc cBox ^ d / ((2 : ℝ) ^ j) ^ (d * CBox)
        = ∏ _i : Fin d, cBox / ((2 : ℝ) ^ j) ^ CBox := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow]
          congr 1
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ ≤ _ := by
          refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
          · exact div_nonneg cBox_pos.le (by positivity)
          · have hl : (1 : ℝ) ≤ sideLen d j i := by exact_mod_cast hL i
            have : (sideLen d j i : ℝ) ≤ 2 ^ j := by exact_mod_cast hle i
            exact div_le_div_of_nonneg_left cBox_pos.le (pow_pos (by linarith) _)
              (pow_le_pow_left₀ (by linarith) this _)
  · rw [hLsq]; split_ifs <;> nlinarith
  · rw [hLsq]; split_ifs <;> nlinarith

theorem cE_le_one : cE ≤ 1 := by
  unfold cE
  have h1 : Real.exp (-2) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  have h2 : (1 : ℝ) ≤ ((72 : ℕ).factorial : ℝ) * 1100 := by
    have h : 1 ≤ (72 : ℕ).factorial := Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero 72)
    have : (1 : ℝ) ≤ ((72 : ℕ).factorial : ℝ) := by exact_mod_cast h
    nlinarith
  rw [div_le_one (by positivity)]
  linarith

theorem cBox_le_one : cBox ≤ 1 :=
  (min_le_left _ _).trans (by
    have := cE_pos
    have := cE_le_one
    nlinarith)

/-- The threshold `γ₁(d)` of Claim 5.6. -/
noncomputable def gamma1 (d : ℕ) : ℝ :=
  1 + 21 * d * CBox + d * Real.logb 2 (1 / cBox)

/-- ES22 Claim 5.6: the bound is at least `n^{-γ+1}`. -/
theorem claim56_small_gamma {j n : ℕ} (hn : 2 ≤ n) (_h1 : n ^ 20 ≤ 2 ^ j) (h2 : 2 ^ j < 2 * n ^ 20)
    {γ : ℝ} (hγ : gamma1 d ≤ γ) :
    (n : ℝ) ^ (-γ + 1) ≤ cBox ^ d / ((2 : ℝ) ^ j) ^ (d * CBox) := by
  have hc := cBox_pos
  have hc1 := cBox_le_one
  have hn0 : (0 : ℝ) < n := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set A : ℕ := d * CBox with hA
  have hN : ((2 : ℝ) ^ j) ^ A ≤ (2 * (n : ℝ) ^ 20) ^ A := by
    have : (2 : ℝ) ^ j ≤ 2 * (n : ℝ) ^ 20 := by exact_mod_cast h2.le
    exact pow_le_pow_left₀ (by positivity) this _
  have hlog : 0 ≤ Real.logb 2 (1 / cBox) := by
    apply Real.logb_nonneg (by norm_num)
    rw [le_div_iff₀ hc]; linarith
  set e : ℝ := γ - 1 - 20 * A with he
  have hE0 : (A : ℝ) + d * Real.logb 2 (1 / cBox) ≤ e := by
    unfold gamma1 at hγ
    rw [he]
    have : (21 * d * CBox : ℝ) = 21 * A := by rw [hA]; push_cast; ring
    linarith
  have hE0nn : 0 ≤ (A : ℝ) + d * Real.logb 2 (1 / cBox) := by positivity
  have h2e : (2 : ℝ) ^ ((A : ℝ) + d * Real.logb 2 (1 / cBox)) = 2 ^ A * (1 / cBox) ^ d := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, mul_comm (d : ℝ),
      Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
      Real.rpow_natCast]
  have hne : (2 : ℝ) ^ ((A : ℝ) + d * Real.logb 2 (1 / cBox)) ≤ (n : ℝ) ^ e := by
    calc (2 : ℝ) ^ ((A : ℝ) + d * Real.logb 2 (1 / cBox)) ≤ (2 : ℝ) ^ e :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hE0
      _ ≤ (n : ℝ) ^ e := Real.rpow_le_rpow (by norm_num) hn2 (hE0nn.trans hE0)
  have hlhs : (n : ℝ) ^ (-γ + 1) = (n : ℝ) ^ (-e) / (n : ℝ) ^ (20 * A : ℝ) := by
    rw [← Real.rpow_sub hn0]; congr 1; rw [he]; ring
  have hn20 : (n : ℝ) ^ (20 * A : ℝ) = ((n : ℝ) ^ 20) ^ A := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
  have hmid : (n : ℝ) ^ (-e) * 2 ^ A ≤ cBox ^ d := by
    have hinv : (n : ℝ) ^ (-e) = ((n : ℝ) ^ e)⁻¹ := Real.rpow_neg hn0.le e
    rw [hinv]
    have hpos : (0 : ℝ) < 2 ^ A * (1 / cBox) ^ d := by positivity
    have : ((n : ℝ) ^ e)⁻¹ ≤ (2 ^ A * (1 / cBox) ^ d)⁻¹ := by
      apply inv_anti₀ hpos; rw [← h2e]; exact hne
    calc ((n : ℝ) ^ e)⁻¹ * 2 ^ A ≤ (2 ^ A * (1 / cBox) ^ d)⁻¹ * 2 ^ A := by gcongr
      _ = cBox ^ d := by
        rw [one_div, inv_pow, mul_inv, inv_inv]; field_simp
  rw [hlhs, hn20, le_div_iff₀ (by positivity)]
  have hpos : (0 : ℝ) < ((n : ℝ) ^ 20) ^ A := by positivity
  calc (n : ℝ) ^ (-e) / ((n : ℝ) ^ 20) ^ A * ((2 : ℝ) ^ j) ^ A
      ≤ (n : ℝ) ^ (-e) / ((n : ℝ) ^ 20) ^ A * (2 * (n : ℝ) ^ 20) ^ A := by gcongr
    _ = (n : ℝ) ^ (-e) * 2 ^ A := by rw [mul_pow]; field_simp
    _ ≤ cBox ^ d := hmid

end SRW
end ElboimSly
