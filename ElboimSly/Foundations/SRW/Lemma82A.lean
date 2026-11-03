/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.AvoidBalls
public import ElboimSly.Foundations.SRW.Maximal
public import ElboimSly.Foundations.SRW.TransienceDiff
public import Mathlib

/-!
# The SRW content of Lemma 8.2: parts (a) and (d)

SRW content of Lemma 8.2 (a), (d).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- The time horizon `T = 2 t_n' = 2 · 4^n t₀ / n⁴`. -/
noncomputable def lem82T (n : ℕ) (t₀ : ℝ) : ℝ := 2 * (4 ^ n * t₀ / (n : ℝ) ^ 4)

theorem lem82T_pos {n : ℕ} (hn : 4 ≤ n) {t₀ : ℝ} (ht₀ : 1 < t₀) : 0 < lem82T n t₀ := by
  unfold lem82T
  have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  positivity

theorem four_lem82T_le {n : ℕ} (hn : 4 ≤ n) {t₀ : ℝ} (ht₀ : t₀ ≤ 4) :
    4 * lem82T n t₀ ≤ 4 ^ n / 8 := by
  unfold lem82T
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn4 : (256 : ℝ) ≤ (n : ℝ) ^ 4 := by nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 16), sq_nonneg (n : ℝ)]
  have h4n : (0 : ℝ) < 4 ^ n := by positivity
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 4 := by linarith
  rw [show 4 * (2 * (4 ^ n * t₀ / (n : ℝ) ^ 4)) = 8 * t₀ * 4 ^ n / (n : ℝ) ^ 4 by ring]
  rw [div_le_div_iff₀ hn0 (by norm_num)]
  nlinarith

theorem exp_19_le {n : ℕ} (hn : 2 ≤ n) : (1.9 : ℝ) ^ n ≤ 4 ^ n / 3 := by
  have h1 : (1.9 : ℝ) ^ n = (1.9 / 4) ^ n * 4 ^ n := by
    rw [← mul_pow]; norm_num
  rw [h1]
  have h2 : ((1.9 : ℝ) / 4) ^ n ≤ (1.9 / 4) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h4n : (0 : ℝ) < 4 ^ n := by positivity
  nlinarith

/-- SRW content of Lemma 8.2 (a), deterministic part. -/
theorem lemma82_a_det {n : ℕ} (hn : 2 ≤ n) {T : ℝ≥0} {v : Fin d → ℤ} (hv : (4 : ℝ) ^ n ≤ ‖v‖)
    (y0 yv : ℝ≥0 → Fin d → ℤ) {s₁ s₂ : ℝ≥0} (hs₁ : s₁ ≤ T) (hs₂ : s₂ ≤ T)
    (hclose : ‖fun i => ((yv s₂ i - y0 s₁ i : ℤ) : ℝ)‖ ≤ 1.9 ^ n) :
    (∃ s : ℝ≥0, s ≤ T ∧ ‖v‖ / 3 ≤ ‖y0 s‖) ∨ (∃ s : ℝ≥0, s ≤ T ∧ ‖v‖ / 3 ≤ ‖yv s - v‖) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1⟩ := hcon
  have a0 := h0 s₁ hs₁
  have a1 := h1 s₂ hs₂
  have hc : ‖fun i => ((yv s₂ i - y0 s₁ i : ℤ) : ℝ)‖ = ‖yv s₂ - y0 s₁‖ := norm_cast_vec _
  have e : v = (yv s₂ - y0 s₁) + y0 s₁ - (yv s₂ - v) := by abel
  have : ‖v‖ ≤ ‖yv s₂ - y0 s₁‖ + ‖y0 s₁‖ + ‖yv s₂ - v‖ := by
    calc ‖v‖ = ‖(yv s₂ - y0 s₁) + y0 s₁ - (yv s₂ - v)‖ := by rw [← e]
      _ ≤ ‖(yv s₂ - y0 s₁) + y0 s₁‖ + ‖yv s₂ - v‖ := norm_sub_le _ _
      _ ≤ ‖yv s₂ - y0 s₁‖ + ‖y0 s₁‖ + ‖yv s₂ - v‖ := by gcongr; exact norm_add_le _ _
  have h19 := exp_19_le hn
  rw [hc] at hclose
  linarith

/-- The spacing `3.6^n`. -/
noncomputable def lem82h (n : ℕ) : ℝ≥0 := ((3.6 : ℝ) ^ n).toNNReal

theorem coe_lem82h (n : ℕ) : (lem82h n : ℝ) = (3.6 : ℝ) ^ n :=
  Real.coe_toNNReal _ (by positivity)

/-- The grid times `g_l = min (l · 3.6^n, T)`. -/
noncomputable def lem82g (n : ℕ) (T : ℝ≥0) (l : ℕ) : ℝ≥0 := min (l * lem82h n) T

/-- SRW content of Lemma 8.2 (d): covering (deterministic). -/
theorem lemma82_d {n : ℕ} {T : ℝ≥0} (γ : ℝ≥0 → Fin d → ℤ)
    (hγ : ∀ s s' : ℝ≥0, s ≤ s' → s' ≤ T → s' - s ≤ lem82h n → ‖γ s' - γ s‖ ≤ 1.9 ^ n)
    {z : Fin d → ℤ} (hz : ∃ s : ℝ≥0, s ≤ T ∧ ‖z - γ s‖ ≤ 1.9 ^ (n + 1)) :
    ∃ l : ℕ, l ≤ ⌈(T : ℝ) / lem82h n⌉₊ ∧ ‖z - γ (lem82g n T l)‖ ≤ 1.9 ^ (n + 2) := by
  obtain ⟨s, hsT, hs⟩ := hz
  have hh : (0 : ℝ) < lem82h n := by rw [coe_lem82h]; positivity
  set l : ℕ := ⌈(s : ℝ) / lem82h n⌉₊ with hl
  refine ⟨l, Nat.ceil_mono (div_le_div_of_nonneg_right (by exact_mod_cast hsT) hh.le), ?_⟩
  have hsl : (s : ℝ) ≤ l * lem82h n := by
    have := Nat.le_ceil ((s : ℝ) / lem82h n)
    rwa [div_le_iff₀ hh] at this
  have hl2 : (l : ℝ) * lem82h n < s + lem82h n := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (s : ℝ) / lem82h n by positivity)
    have := mul_lt_mul_of_pos_right this hh
    rw [add_mul, div_mul_cancel₀ _ hh.ne'] at this
    simpa using this
  have hg1 : s ≤ lem82g n T l := by
    unfold lem82g
    refine le_min ?_ hsT
    rw [← NNReal.coe_le_coe]; push_cast; exact hsl
  have hg2 : lem82g n T l - s ≤ lem82h n := by
    unfold lem82g
    rw [tsub_le_iff_left]
    have : min ((l : ℝ≥0) * lem82h n) T ≤ (l : ℝ≥0) * lem82h n := min_le_left _ _
    refine this.trans ?_
    rw [← NNReal.coe_le_coe]; push_cast
    linarith
  have hg3 : lem82g n T l ≤ T := min_le_right _ _
  have h1 := hγ s _ hg1 hg3 hg2
  have h19 : (0 : ℝ) < 1.9 ^ n := by positivity
  calc ‖z - γ (lem82g n T l)‖ = ‖(z - γ s) - (γ (lem82g n T l) - γ s)‖ := by congr 1; abel
    _ ≤ ‖z - γ s‖ + ‖γ (lem82g n T l) - γ s‖ := norm_sub_le _ _
    _ ≤ 1.9 ^ (n + 1) + 1.9 ^ n := add_le_add hs h1
    _ ≤ 1.9 ^ (n + 2) := by
        rw [pow_succ, pow_succ, pow_succ]; nlinarith

end SRW
end ElboimSly
