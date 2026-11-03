/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Sup
import Mathlib

/-!
# Oscillation of Brownian motion

Oscillation.

For `T, h, λ, σ > 0`:
`P(∃ s s' ∈ [0,T], |s - s'| ≤ h, ‖σB(s) - σB(s')‖ ≥ λ) ≤ 4 d ⌈T/h⌉ exp(-λ²/(16 σ² h))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- Oscillation. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.oscillation_le [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {T h : ℝ≥0}
    (hT : T ≠ 0) (hh : h ≠ 0) {l σ : ℝ} (hl : 0 < l) (hσ : 0 < σ) :
    P {ω | ∃ s s' : ℝ≥0, s ≤ T ∧ s' ≤ T ∧ dist s s' ≤ h ∧ l ≤ ‖σ • B s ω - σ • B s' ω‖} ≤
      (4 * d * (⌈T / h⌉₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-l ^ 2 / (16 * σ ^ 2 * h))) := by
  classical
  have hhpos : (0 : ℝ) < h := by positivity
  set K : ℕ := ⌈T / h⌉₊ with hK
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (by
    rw [hK]; exact (Nat.ceil_pos.2 (by positivity)).ne')
  have hTK : (T : ℝ) ≤ K * h := by
    have : ((T / h : ℝ≥0) : ℝ) ≤ K := Nat.le_ceil _
    rw [NNReal.coe_div, div_le_iff₀ hhpos] at this
    exact this
  let W : ℕ → Set Ω := fun k => {ω | ∃ u ≤ 2 * h, l / (2 * σ) ≤ ‖B (k * h + u) ω - B (k * h) ω‖}
  -- the ordered inclusion
  have hord : ∀ ω, ∀ s s' : ℝ≥0, s ≤ s' → s' ≤ T → (s' : ℝ) ≤ s + h →
      l ≤ ‖σ • B s ω - σ • B s' ω‖ → ω ∈ ⋃ k ∈ Finset.range K, W k := by
    intro ω s s' hss' hs'T hs'h hnorm
    set A : ℕ := ⌊(s : ℝ) / h⌋₊ with hA
    have hA1 : (A : ℝ) ≤ s / h := Nat.floor_le (by positivity)
    have hA2 : (s : ℝ) / h < A + 1 := Nat.lt_floor_add_one _
    have hAh : (A : ℝ) * h ≤ s := by rwa [le_div_iff₀ hhpos] at hA1
    have hAh2 : (s : ℝ) < (A + 1) * h := by rwa [div_lt_iff₀ hhpos] at hA2
    set k : ℕ := min A (K - 1) with hk
    have hkA : k ≤ A := min_le_left _ _
    have hkK : k < K := by have := min_le_right A (K - 1); omega
    have hkh : (k : ℝ) * h ≤ s := by
      refine le_trans ?_ hAh
      gcongr
    have hs'k : (s' : ℝ) ≤ (k + 2) * h := by
      rcases le_total A (K - 1) with hle | hle
      · have : k = A := min_eq_left hle
        rw [this]; nlinarith
      · have : k = K - 1 := min_eq_right hle
        have hKk : (K : ℝ) = k + 1 := by
          rw [this]; have : (1 : ℕ) ≤ K := hK1
          push_cast [Nat.cast_sub this]; ring
        have hs'T' : (s' : ℝ) ≤ T := hs'T
        nlinarith
    -- the two shifted times
    have hkhs : (k : ℝ≥0) * h ≤ s := by exact_mod_cast hkh
    have hkhs' : (k : ℝ≥0) * h ≤ s' := hkhs.trans hss'
    set u1 : ℝ≥0 := s - k * h with hu1
    set u2 : ℝ≥0 := s' - k * h with hu2
    have e1 : (k : ℝ≥0) * h + u1 = s := add_tsub_cancel_of_le hkhs
    have e2 : (k : ℝ≥0) * h + u2 = s' := add_tsub_cancel_of_le hkhs'
    have hu1h : u1 ≤ 2 * h := by
      have : (u1 : ℝ) ≤ 2 * h := by
        rw [hu1, NNReal.coe_sub hkhs]; push_cast; nlinarith [(NNReal.coe_le_coe.2 hss' : (s : ℝ) ≤ s')]
      exact_mod_cast this
    have hu2h : u2 ≤ 2 * h := by
      have : (u2 : ℝ) ≤ 2 * h := by
        rw [hu2, NNReal.coe_sub hkhs']; push_cast; nlinarith
      exact_mod_cast this
    -- triangle inequality
    have hdiff : B s ω - B s' ω =
        (B (k * h + u1) ω - B (k * h) ω) - (B (k * h + u2) ω - B (k * h) ω) := by
      rw [e1, e2]; abel
    have hnorm' : l / σ ≤ ‖B (k * h + u1) ω - B (k * h) ω‖ +
        ‖B (k * h + u2) ω - B (k * h) ω‖ := by
      have : σ • B s ω - σ • B s' ω = σ • (B s ω - B s' ω) := by rw [smul_sub]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hσ, hdiff] at hnorm
      rw [div_le_iff₀ hσ]
      have := norm_sub_le (B (k * h + u1) ω - B (k * h) ω) (B (k * h + u2) ω - B (k * h) ω)
      nlinarith
    refine Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 hkK, ?_⟩
    have hl2 : l / (2 * σ) = (l / σ) / 2 := by field_simp
    by_cases hc : l / (2 * σ) ≤ ‖B (k * h + u1) ω - B (k * h) ω‖
    · exact ⟨u1, hu1h, hc⟩
    · refine ⟨u2, hu2h, ?_⟩
      push Not at hc
      linarith
  -- the general inclusion
  have hcover : {ω | ∃ s s' : ℝ≥0, s ≤ T ∧ s' ≤ T ∧ dist s s' ≤ h ∧
      l ≤ ‖σ • B s ω - σ • B s' ω‖} ⊆ ⋃ k ∈ Finset.range K, W k := by
    rintro ω ⟨s, s', hsT, hs'T, hd, hn⟩
    rw [NNReal.dist_eq, abs_le] at hd
    rcases le_total s s' with hle | hle
    · exact hord ω s s' hle hs'T (by linarith) hn
    · refine hord ω s' s hle hsT (by linarith) ?_
      rwa [norm_sub_rev]
  -- measure of each `W k`
  have hW : ∀ k, P (W k) ≤ (4 * d : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-l ^ 2 / (16 * σ ^ 2 * h))) := by
    intro k
    have hsh := hB.shift (k * h)
    have h2h : (2 * h : ℝ≥0) ≠ 0 := by positivity
    have := hsh.sup_norm_le h2h (l := l / (2 * σ)) (by positivity)
    refine this.trans (le_of_eq ?_)
    congr 3
    push_cast
    field_simp
    ring
  calc _ ≤ P (⋃ k ∈ Finset.range K, W k) := measure_mono hcover
    _ ≤ ∑ k ∈ Finset.range K, P (W k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range K, (4 * d : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-l ^ 2 / (16 * σ ^ 2 * h))) :=
        Finset.sum_le_sum fun k _ => hW k
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- Oscillation, the "in particular" form (`σ = 1`, `T = ℓ h`). -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.oscillation_grid_le [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {h : ℝ≥0}
    (hh : h ≠ 0) {l : ℝ} (hl : 0 < l) (ℓ : ℕ) :
    P {ω | ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ ∃ s : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) * h ≤ s ∧ s ≤ j * h ∧
        l ≤ ‖B s ω - B (j * h) ω‖} ≤
      (4 * d * ℓ : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-l ^ 2 / (16 * h))) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have : {ω | ∃ j : ℕ, 1 ≤ j ∧ j ≤ 0 ∧ ∃ s : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) * h ≤ s ∧ s ≤ j * h ∧
        l ≤ ‖B s ω - B (j * h) ω‖} = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨j, h1, h2, -⟩; omega
    simp
  have hTne : ((ℓ : ℝ≥0) * h) ≠ 0 := by positivity
  have := hB.oscillation_le (T := ℓ * h) hTne hh hl one_pos
  have hceil : ⌈(ℓ : ℝ≥0) * h / h⌉₊ = ℓ := by
    rw [mul_div_cancel_right₀ _ hh]; simp
  rw [hceil] at this
  refine le_trans (measure_mono ?_) (this.trans (le_of_eq ?_))
  · rintro ω ⟨j, hj1, hjℓ, s, hs1, hs2, hn⟩
    refine ⟨s, j * h, ?_, ?_, ?_, ?_⟩
    · exact hs2.trans (by gcongr)
    · gcongr
    · rw [NNReal.dist_eq, abs_le]
      have h1 : (((j - 1 : ℕ) : ℝ≥0) : ℝ) * h ≤ s := by exact_mod_cast hs1
      have h2 : (((j - 1 : ℕ) : ℝ≥0) : ℝ) = j - 1 := by
        rw [NNReal.coe_natCast, Nat.cast_sub hj1]; simp
      have h3 : (s : ℝ) ≤ (j : ℝ) * h := by exact_mod_cast hs2
      rw [h2] at h1
      push_cast
      constructor <;> nlinarith
    · simpa using hn
  · simp only [one_pow, mul_one]

end ElboimSly.Brownian
