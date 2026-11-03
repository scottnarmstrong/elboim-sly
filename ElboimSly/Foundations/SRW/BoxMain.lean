/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.BoxInner
public import Mathlib

/-!
# Confined point-to-point lower bound

Confined point-to-point lower bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

theorem sum_kernel1_mul_le (J : Set ℤ) (D : Finset ℤ) (r₁ r₂ : ℝ≥0) (x z : ℤ) :
    ∑ a ∈ D, kernel1 J r₁ x a * kernel1 J r₂ a z ≤ kernel1 J (r₁ + r₂) x z := by
  rw [kernel1_add]
  exact (summable_kernel1_mul J r₁ r₂ x z).sum_le_tsum D fun i _ =>
    mul_nonneg (kernel1_nonneg _ _ _ _) (kernel1_nonneg _ _ _ _)

/-- The large-`L` case, for the interval `[0, L-1]`. -/
theorem box_large {L : ℤ} (hL : 50000 ≤ L) {y z : ℤ} (hy : y ∈ Icc (0 : ℤ) (L - 1))
    (hz : z ∈ Icc (0 : ℤ) (L - 1)) {r : ℝ≥0} (hr1 : (L : ℝ) ^ 2 / 16 ≤ r)
    (hr2 : (r : ℝ) ≤ 16 * (L : ℝ) ^ 2) :
    cE ^ 2 / (L : ℝ) ^ CBox ≤ kernel1 (Icc 0 (L - 1)) r y z := by
  have hLr : (50000 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨s₁, hs1, hs2, hesc⟩ := escape (show (6000 : ℤ) ≤ L by omega)
  set J : Set ℤ := Icc 0 (L - 1) with hJ
  have hs1r : (0 : ℝ) ≤ s₁ := s₁.2
  have h2s : 2 * s₁ ≤ r := by
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith
  set r' : ℝ≥0 := r - 2 * s₁ with hr'
  have hr'c : (r' : ℝ) = r - 2 * s₁ := by
    rw [hr', NNReal.coe_sub h2s]; push_cast; ring
  have hr'1 : (L : ℝ) ^ 2 / 17 ≤ r' := by
    rw [hr'c]; nlinarith [sq_nonneg (L : ℝ)]
  have hr'2 : (r' : ℝ) ≤ 16 * (L : ℝ) ^ 2 := by
    rw [hr'c]; linarith
  have hrr : r = s₁ + (r' + s₁) := by
    rw [← NNReal.coe_inj]; push_cast; rw [hr'c]; ring
  set D := escD L with hD
  have hA : ∑ a ∈ D, kernel1 J s₁ y a * kernel1 J (r' + s₁) a z ≤ kernel1 J r y z := by
    rw [hrr]; exact sum_kernel1_mul_le J D s₁ (r' + s₁) y z
  have hB : ∀ a ∈ D, (1 / (L : ℝ)) ^ boxK * ∑ b ∈ D, kernel1 J s₁ z b ≤
      kernel1 J (r' + s₁) a z := by
    intro a ha
    refine le_trans ?_ (sum_kernel1_mul_le J D r' s₁ a z)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [kernel1_symm J s₁ z b]
    exact mul_le_mul_of_nonneg_right (box_inner hL hr'1 hr'2 ha hb) (kernel1_nonneg _ _ _ _)
  have hSy := hesc y hy
  have hSz := hesc z hz
  have hc0 : 0 ≤ cE / (L : ℝ) ^ 256 := by have := cE_pos; positivity
  have hcE : cE = Real.exp (-2) / ((72 : ℕ).factorial * 1100) := rfl
  rw [← hcE] at hSy hSz
  have hpos : (0 : ℝ) ≤ (1 / (L : ℝ)) ^ boxK := by positivity
  calc cE ^ 2 / (L : ℝ) ^ CBox
      = (cE / (L : ℝ) ^ 256) * ((1 / (L : ℝ)) ^ boxK * (cE / (L : ℝ) ^ 256)) := by
        unfold CBox
        rw [pow_add, one_div, inv_pow]
        field_simp
    _ ≤ (∑ a ∈ D, kernel1 J s₁ y a) * ((1 / (L : ℝ)) ^ boxK * ∑ b ∈ D, kernel1 J s₁ z b) := by
        exact mul_le_mul hSy (mul_le_mul_of_nonneg_left hSz hpos) (mul_nonneg hpos hc0)
          (Finset.sum_nonneg fun _ _ => kernel1_nonneg _ _ _ _)
    _ = ∑ a ∈ D, kernel1 J s₁ y a * ((1 / (L : ℝ)) ^ boxK * ∑ b ∈ D, kernel1 J s₁ z b) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ a ∈ D, kernel1 J s₁ y a * kernel1 J (r' + s₁) a z := by
        refine Finset.sum_le_sum fun a ha => ?_
        exact mul_le_mul_of_nonneg_left (hB a ha) (kernel1_nonneg _ _ _ _)
    _ ≤ _ := hA

theorem box_small {L : ℕ} (hL : 1 ≤ L) (hL' : L < 50000) {m y z : ℤ}
    (hy : y ∈ Icc m (m + L - 1)) (hz : z ∈ Icc m (m + L - 1)) {r : ℝ≥0}
    (hr1 : (L : ℝ) ^ 2 / 16 ≤ r) (hr2 : (r : ℝ) ≤ 16 * (L : ℝ) ^ 2) :
    cBox ≤ kernel1 (Icc m (m + L - 1)) r y z := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLr' : (L : ℝ) < 50000 := by exact_mod_cast hL'
  have hr_lo : (1 / 16 : ℝ) ≤ r := by nlinarith
  have hr_hi : (r : ℝ) ≤ 4 * 10 ^ 10 := by nlinarith
  have key : ∀ {y z : ℤ}, y ∈ Icc m (m + L - 1) → z ∈ Icc m (m + L - 1) → y ≤ z →
      cBox ≤ kernel1 (Icc m (m + L - 1)) r y z := by
    intro y z hy hz hyz
    have hk : (z - y).toNat ≤ 50000 := by
      simp only [mem_Icc] at hy hz
      omega
    refine le_trans ?_ (kernel1_ge_up _ hyz (fun x hx => ?_) r)
    · exact (min_le_right _ _).trans (po_pair_lower hk hr_lo hr_hi)
    · simp only [mem_Icc] at hy hz hx ⊢
      omega
  rcases le_total y z with h | h
  · exact key hy hz h
  · rw [kernel1_symm]; exact key hz hy h

/-- Confined point-to-point lower bound: confined point-to-point lower bound. -/
theorem box {L : ℕ} (hL : 1 ≤ L) {m y z : ℤ} (hy : y ∈ Icc m (m + L - 1))
    (hz : z ∈ Icc m (m + L - 1)) {r : ℝ≥0} (hr1 : (L : ℝ) ^ 2 / 16 ≤ r)
    (hr2 : (r : ℝ) ≤ 16 * (L : ℝ) ^ 2) :
    cBox / (L : ℝ) ^ CBox ≤ kernel1 (Icc m (m + L - 1)) r y z := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  rcases lt_or_ge L 50000 with hs | hl
  · refine le_trans ?_ (box_small hL hs hy hz hr1 hr2)
    exact div_le_self cBox_pos.le (one_le_pow₀ hLr)
  · have hl' : (50000 : ℤ) ≤ L := by exact_mod_cast hl
    have e : (fun q => q + m) '' Icc (0 : ℤ) ((L : ℤ) - 1) = Icc m (m + L - 1) := by
      ext x
      simp only [mem_image, mem_Icc]
      constructor
      · rintro ⟨q, ⟨h1, h2⟩, rfl⟩; constructor <;> omega
      · rintro ⟨h1, h2⟩; exact ⟨x - m, ⟨by omega, by omega⟩, by ring⟩
    have ht := kernel1_translate (Icc (0 : ℤ) ((L : ℤ) - 1)) m r (y - m) (z - m)
    rw [e, sub_add_cancel, sub_add_cancel] at ht
    rw [ht]
    have hy' : y - m ∈ Icc (0 : ℤ) ((L : ℤ) - 1) := by
      simp only [mem_Icc] at hy ⊢; omega
    have hz' : z - m ∈ Icc (0 : ℤ) ((L : ℤ) - 1) := by
      simp only [mem_Icc] at hz ⊢; omega
    have hcast : (((L : ℕ) : ℤ) : ℝ) = (L : ℝ) := by norm_cast
    have := box_large hl' hy' hz' (r := r) (by rw [hcast]; exact hr1) (by rw [hcast]; exact hr2)
    rw [hcast] at this
    refine le_trans ?_ this
    have hp : (0 : ℝ) < (L : ℝ) ^ CBox := by positivity
    exact div_le_div_of_nonneg_right (min_le_left _ _) hp.le

end SRW
end ElboimSly
