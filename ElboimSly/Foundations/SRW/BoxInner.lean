/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.BoxChain
public import Mathlib

/-!
# The inner bound of confined point-to-point lower bound

For `a, b ∈ D_L` and `r' ∈ [L²/17, 16 L²]`, `q^J_{r'}(a, b) ≥ L^{-K}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

theorem kernel1_window_translate (g : ℤ) (ℓ : ℤ) (ρ : ℝ≥0) (g' : ℤ) :
    kernel1 (Icc (-ℓ) ℓ) ρ 0 (g' - g) = kernel1 (Icc (g - ℓ) (g + ℓ)) ρ g g' := by
  have h := kernel1_translate (Icc (-ℓ) ℓ) g ρ 0 (g' - g)
  have e : (fun q => q + g) '' Icc (-ℓ) ℓ = Icc (g - ℓ) (g + ℓ) := by
    ext x
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨q, ⟨h1, h2⟩, rfl⟩; constructor <;> omega
    · rintro ⟨h1, h2⟩; exact ⟨x - g, ⟨by omega, by omega⟩, by ring⟩
  rw [e] at h
  rw [← h]
  simp

theorem pow_le_prod_range (c : ℝ) (hc : 0 ≤ c) (f : ℕ → ℝ) :
    ∀ n : ℕ, (∀ k < n, c ≤ f k) → c ^ n ≤ ∏ k ∈ Finset.range n, f k
  | 0, _ => by simp
  | n + 1, h => by
    rw [Finset.prod_range_succ, pow_succ]
    exact mul_le_mul (pow_le_prod_range c hc f n fun k hk => h k (by omega)) (h n (by omega)) hc
      (Finset.prod_nonneg fun k hk => hc.trans (h k (by have := Finset.mem_range.1 hk; omega)))

theorem box_inner {L : ℤ} (hL : 50000 ≤ L) {r' : ℝ≥0} (h1 : (L : ℝ) ^ 2 / 17 ≤ r')
    (h2 : (r' : ℝ) ≤ 16 * (L : ℝ) ^ 2) {a b : ℤ} (ha : a ∈ escD L) (hb : b ∈ escD L) :
    (1 / (L : ℝ)) ^ boxK ≤ kernel1 (Icc 0 (L - 1)) r' a b := by
  have hLr : (50000 : ℝ) ≤ L := by exact_mod_cast hL
  have hKr := boxK_real
  have hK1 : (0 : ℝ≥0) < (boxK : ℝ≥0) := by norm_num [boxK]
  set ρ : ℝ≥0 := r' / (boxK : ℝ≥0) with hρ
  have hρK : (ρ : ℝ) = r' / 26214400 := by
    rw [hρ]; push_cast; rw [hKr]
  have hρ_lo : (L : ℝ) ^ 2 / (17 * 26214400) ≤ ρ := by
    rw [hρK, div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  have hρ_hi : (ρ : ℝ) ≤ ((L : ℝ) / 1280) ^ 2 := by
    rw [hρK]
    have : ((L : ℝ) / 1280) ^ 2 = 16 * (L : ℝ) ^ 2 / 26214400 := by ring
    rw [this]
    gcongr
  have hρ2 : 2 ≤ (ρ : ℝ) := by
    refine le_trans ?_ hρ_lo
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hs_lo : (L : ℝ) / 22000 ≤ √(ρ : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    refine le_trans ?_ hρ_lo
    rw [div_pow, div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith [sq_nonneg (L : ℝ)]
  have hs_hi : √(ρ : ℝ) ≤ (L : ℝ) / 1280 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hρ_hi⟩
  have hs0 : 0 < √(ρ : ℝ) := by linarith
  set ℓ : ℤ := ⌊(L : ℝ) / 40⌋ - 1 with hℓ
  have hℓ1 : (L : ℝ) / 40 - 2 < ℓ := by
    have := Int.lt_floor_add_one ((L : ℝ) / 40)
    rw [hℓ]; push_cast; linarith
  have hℓ2 : (ℓ : ℝ) ≤ (L : ℝ) / 40 - 1 := by
    have := Int.floor_le ((L : ℝ) / 40)
    rw [hℓ]; push_cast; linarith
  have hℓ16 : 16 * √(ρ : ℝ) ≤ ℓ := by linarith
  set g : ℕ → ℤ := gInterp a b with hg
  have ha' := mem_escD.1 ha
  have hb' := mem_escD.1 hb
  have hgD : ∀ k, k ≤ boxK → g k ∈ escD L := by
    intro k hk
    obtain ⟨h1, h2⟩ := gInterp_between a b hk
    rw [mem_escD]
    have e1 : ((min a b : ℤ) : ℝ) = min (a : ℝ) b := by push_cast; rfl
    have e2 : ((max a b : ℤ) : ℝ) = max (a : ℝ) b := by push_cast; rfl
    have h1' : min (a : ℝ) b ≤ g k := by rw [← e1]; exact_mod_cast h1
    have h2' : (g k : ℝ) ≤ max (a : ℝ) b := by rw [← e2]; exact_mod_cast h2
    constructor
    · exact le_trans (le_min ha'.1 hb'.1) h1'
    · exact le_trans h2' (max_le ha'.2 hb'.2)
  have hdab : |(b : ℝ) - a| ≤ L := by
    rw [abs_le]
    constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]
  have hwin : ∀ k < boxK, 1 / (L : ℝ) ≤ kernel1 (Icc 0 (L - 1)) ρ (g k) (g (k + 1)) := by
    intro k hk
    have hgk := mem_escD.1 (hgD k hk.le)
    have hstep := gInterp_step a b k
    have hδ : |((g (k + 1) - g k : ℤ) : ℝ)| ≤ √(ρ : ℝ) := by
      refine hstep.trans ?_
      have : |(b : ℝ) - a| / boxK ≤ L / 26214400 := by
        rw [hKr]; gcongr
      linarith
    have hw := window hρ2 hδ hℓ16
    rw [kernel1_window_translate] at hw
    have hsub : Icc (g k - ℓ) (g k + ℓ) ⊆ Icc 0 (L - 1) := by
      intro x hx
      simp only [mem_Icc] at hx ⊢
      have e1 : (L : ℝ) / 40 ≤ g k := hgk.1
      have e2 : (g k : ℝ) ≤ L - 1 - L / 40 := hgk.2
      have c1 : (0 : ℝ) < (g k : ℝ) - ℓ := by linarith
      have c2 : (g k : ℝ) + ℓ < L - 1 := by linarith
      have c1' : (0 : ℤ) < g k - ℓ := by exact_mod_cast c1
      have c2' : g k + ℓ < L - 1 := by exact_mod_cast c2
      omega
    refine le_trans ?_ (hw.trans (kernel1_mono hsub ρ _ _))
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have := exp_neg_four_ge
    nlinarith
  have hchain := kernel1_chain (Icc 0 (L - 1)) ρ g (boxK - 1)
  have hK1' : boxK - 1 + 1 = boxK := by norm_num [boxK]
  rw [hK1'] at hchain
  have hKρ : ((boxK : ℕ) : ℝ≥0) * ρ = r' := by
    rw [hρ]; exact mul_div_cancel₀ _ hK1.ne'
  rw [hKρ, show g 0 = a from gInterp_zero a b, show g boxK = b from gInterp_K a b] at hchain
  refine le_trans ?_ hchain
  refine pow_le_prod_range (1 / (L : ℝ)) (by positivity) _ (boxK - 1 + 1) ?_ |>.trans' ?_
  · intro k hk
    exact hwin k (by omega)
  · rw [hK1']

end SRW
end ElboimSly
