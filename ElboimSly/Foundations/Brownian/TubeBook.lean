/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.TubeChain
import Mathlib

/-!
# Bookkeeping for the tube lemma

Tube lemma, basic form, "Targets", "Bookkeeping" and "What the events give".
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

section Book

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

lemma tubeZ_zero_idx (v : Fin d → ℝ) : tubeZ v 0 = v := by simp [tubeZ]

lemma tubeZ_eq_zero (v : Fin d → ℝ) {k : ℕ} (hk : 12 ≤ k) : tubeZ v k = 0 := by
  have : (12 : ℝ) ≤ k := by exact_mod_cast hk
  simp only [tubeZ]
  rw [max_eq_right (by linarith)]
  simp

lemma tubeZ_norm_le (v : Fin d → ℝ) (k : ℕ) : ‖tubeZ v k‖ ≤ ‖v‖ := by
  simp only [tubeZ, norm_smul, Real.norm_eq_abs]
  have h0 : 0 ≤ max (1 - (k : ℝ) / 12) 0 := le_max_right _ _
  have h1 : max (1 - (k : ℝ) / 12) 0 ≤ 1 := by
    refine max_le ?_ zero_le_one
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  rw [abs_of_nonneg h0]
  nlinarith [norm_nonneg v]

lemma tubeZ_diff_le (v : Fin d → ℝ) (k : ℕ) : ‖tubeZ v (k + 1) - tubeZ v k‖ ≤ ‖v‖ / 12 := by
  have e : tubeZ v (k + 1) - tubeZ v k =
      (max (1 - ((k + 1 : ℕ) : ℝ) / 12) 0 - max (1 - (k : ℝ) / 12) 0) • v := by
    simp [tubeZ, sub_smul]
  rw [e, norm_smul, Real.norm_eq_abs]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc : |max (1 - ((k + 1 : ℕ) : ℝ) / 12) 0 - max (1 - (k : ℝ) / 12) 0| ≤ 1 / 12 := by
    push_cast
    rw [abs_le]
    constructor <;> rcases le_total (1 - ((k : ℝ) + 1) / 12) 0 with h1 | h1 <;>
      rcases le_total (1 - (k : ℝ) / 12) 0 with h2 | h2 <;>
      simp [h1, h2] <;> linarith
  calc _ ≤ 1 / 12 * ‖v‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg v)
    _ = ‖v‖ / 12 := by ring

variable {B : ℝ≥0 → Ω → (Fin d → ℝ)} {x : Fin d → ℝ} {f : ℝ → Fin d → ℝ} {h : ℝ≥0} {ρ : ℝ}

/-- The error `e_j = x + B(u_j) - f(u_j) - z_j`. -/
noncomputable def tubeErr (B : ℝ≥0 → Ω → (Fin d → ℝ)) (x : Fin d → ℝ) (f : ℝ → Fin d → ℝ)
    (h : ℝ≥0) (j : ℕ) (ω : Ω) : Fin d → ℝ :=
  x + B ((j : ℝ≥0) * h) ω - f (((j : ℝ≥0) * h : ℝ≥0)) - tubeZ (x - f 0) j

lemma tubeErr_zero (hB : IsStandardBrownianMotion d B P) (ω : Ω) :
    tubeErr B x f h 0 ω = 0 := by
  simp [tubeErr, tubeZ_zero_idx, (hB.continuous_zero ω).2]

omit mΩ in
lemma tubeErr_succ (k : ℕ) (ω : Ω) :
    tubeErr B x f h (k + 1) ω = (B (((k + 1 : ℕ) : ℝ≥0) * h) ω - B ((k : ℝ≥0) * h) ω) -
      tubeP B x f h k ω := by
  simp only [tubeErr, tubeP]
  abel

omit mΩ in
lemma tubeP_eq (k : ℕ) (ω : Ω) :
    tubeP B x f h k ω = -tubeErr B x f h k ω + (tubeZ (x - f 0) (k + 1) - tubeZ (x - f 0) k) +
      (f (((k + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) - f (((k : ℝ≥0) * h : ℝ≥0))) := by
  simp only [tubeErr, tubeP]
  abel

/-- On `E_k`, all errors `e_j`, `j ≤ k`, are at most `ρ/20`, and `p_k` is at most `3ρ/20`. -/
theorem tubeE_errors (hB : IsStandardBrownianMotion d B P) {N : ℕ} (_hN12 : 12 ≤ N)
    (hρ : 0 < ρ) {K : ℝ} (hx : ‖x - f 0‖ ≤ 3 * ρ / 5)
    (hLip : ∀ u ∈ Set.Icc (0 : ℝ) ((N : ℝ) * h), ∀ v ∈ Set.Icc (0 : ℝ) ((N : ℝ) * h),
      ‖f u - f v‖ ≤ K / ρ * |u - v|)
    (hKh : K / ρ * h ≤ ρ / 20) :
    ∀ k ≤ N, ∀ ω ∈ tubeE B x f h ρ k, (∀ j ≤ k, ‖tubeErr B x f h j ω‖ ≤ ρ / 20) ∧
      (k < N → ‖tubeP B x f h k ω‖ ≤ 3 * ρ / 20) := by
  have hP : ∀ k < N, ∀ ω, ‖tubeErr B x f h k ω‖ ≤ ρ / 20 → ‖tubeP B x f h k ω‖ ≤ 3 * ρ / 20 := by
    intro k hk ω he
    rw [tubeP_eq]
    have h1 := tubeZ_diff_le (x - f 0) k
    have h2 : ‖f (((k + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) - f (((k : ℝ≥0) * h : ℝ≥0))‖ ≤ ρ / 20 := by
      have hk1 : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
      have hh : (0 : ℝ) ≤ h := h.2
      have := hLip (((k + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) ⟨by positivity, by push_cast at hk1 ⊢; nlinarith [mul_nonneg (sub_nonneg.2 hk1) hh]⟩
        (((k : ℝ≥0) * h : ℝ≥0)) ⟨by positivity, by push_cast at hk1 ⊢; nlinarith [mul_nonneg (sub_nonneg.2 (by linarith : (k : ℝ) ≤ N)) hh]⟩
      refine this.trans ?_
      have e : |(((k + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) - (((k : ℝ≥0) * h : ℝ≥0) : ℝ)| = h := by
        push_cast
        rw [show ((k : ℝ) + 1) * h - k * h = h by ring, abs_of_nonneg hh]
      rw [e]; exact hKh
    calc _ ≤ ‖-tubeErr B x f h k ω + (tubeZ (x - f 0) (k + 1) - tubeZ (x - f 0) k)‖ +
          ‖f (((k + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) - f (((k : ℝ≥0) * h : ℝ≥0))‖ := norm_add_le _ _
      _ ≤ (‖tubeErr B x f h k ω‖ + ‖tubeZ (x - f 0) (k + 1) - tubeZ (x - f 0) k‖) + ρ / 20 := by
          gcongr
          calc _ ≤ _ := norm_add_le _ _
            _ = _ := by rw [norm_neg]
      _ ≤ 3 * ρ / 20 := by
          have : ‖x - f 0‖ / 12 ≤ ρ / 20 := by linarith
          linarith
  intro k
  induction k with
  | zero =>
    intro _ ω _
    refine ⟨fun j hj => ?_, fun hk => hP 0 hk ω ?_⟩
    · obtain rfl : j = 0 := by omega
      rw [tubeErr_zero hB]; simp; positivity
    · rw [tubeErr_zero hB]; simp; positivity
  | succ k ih =>
    intro hk ω hω
    obtain ⟨hω1, hω2⟩ := hω
    obtain ⟨ih1, ih2⟩ := ih (by omega) ω hω1
    have hpk := ih2 (by omega)
    have hnew : ‖tubeErr B x f h (k + 1) ω‖ ≤ ρ / 20 := by
      rw [tubeErr_succ]
      have : (tubeP B x f h k ω, shiftPath B ((k : ℝ≥0) * h) ω) ∈ stepSet d h (ρ / 4) (ρ / 20) :=
        hω2
      have h3 := this.2
      simp only [shiftPath] at h3
      have e : B (((k + 1 : ℕ) : ℝ≥0) * h) ω - B ((k : ℝ≥0) * h) ω - tubeP B x f h k ω =
          (B ((k : ℝ≥0) * h + h) ω - B ((k : ℝ≥0) * h) ω) - tubeP B x f h k ω := by
        rw [succ_mul_eq]
      rw [e]
      exact h3
    refine ⟨fun j hj => ?_, fun hk' => hP (k + 1) hk' ω hnew⟩
    rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
    · exact ih1 j (by omega)
    · obtain rfl : j = k + 1 := by omega
      exact hnew

end Book

end ElboimSly.Brownian
