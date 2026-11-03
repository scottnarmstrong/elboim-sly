/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.WindowIntegral
import Mathlib

/-!
# Hitting a cube after time `s²`

ES22 Lemma 9.2: hitting a cube after time s^2 (ES22 Lemma 9.2, deviation F20, F29), proved by time discretization
with one time window.

* `Cfar d`: the constant `C_far(d) = max {1, (2π)^{-d/2} C_win (1 + 2/(d-2))}`;
* `far_hit_exists_le`: Step 1 (`σ = 1`, the event of hitting);
* `far_hit_le`: the statement, with the infimum, for all `y`, `r, s, σ > 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- ES22 Lemma 9.2: hitting a cube after time s^2. The constant
`C_far(d) = max {1, (2π)^{-d/2} C_win (1 + 2/(d-2))}`. -/
noncomputable def Cfar (d : ℕ) : ℝ :=
  max 1 ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Cwin d * (1 + 2 / ((d : ℝ) - 2)))

lemma one_le_Cfar (d : ℕ) : 1 ≤ Cfar d := le_max_left _ _

lemma Cfar_pos (d : ℕ) : 0 < Cfar d := lt_of_lt_of_le one_pos (one_le_Cfar d)

/-- A sum of nonnegative reals, bounded on all finite partial sums, bounds the `ENNReal` sum. -/
lemma tsum_ofReal_le_of_partial {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) {C : ℝ}
    (hC : ∀ n, ∑ k ∈ Finset.range n, f k ≤ C) :
    ∑' k, ENNReal.ofReal (f k) ≤ ENNReal.ofReal C := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hf k]
  exact ENNReal.ofReal_le_ofReal (hC n)

lemma far_hit_core {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (m : ℕ) (hm : (1 : ℝ) ≤ m) :
    r ^ (m + 2) * ((s ^ (m + 2))⁻¹ + 2 / (m * r ^ 2) * (s ^ 2 * (s ^ (m + 2))⁻¹)) =
      (r / s) ^ m * ((r / s) ^ 2 + 2 / (m : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  obtain ⟨q, hq⟩ : ∃ q, r = q * s := ⟨r / s, by field_simp⟩
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq; linarith
  subst hq
  have hs0 : s ≠ 0 := hs.ne'
  rw [mul_div_assoc, div_self hs0, mul_one]
  field_simp
  ring

lemma sq_rpow_neg_half {s : ℝ} (hs : 0 < s) (d : ℕ) :
    (s ^ 2) ^ (-(d : ℝ) / 2) = ((s ^ d)⁻¹) := by
  rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le, ← Real.rpow_natCast s d,
    ← Real.rpow_neg hs.le]
  congr 1; push_cast; ring

lemma sq_rpow_one_sub_half {s : ℝ} (hs : 0 < s) (d : ℕ) :
    (s ^ 2) ^ (1 - (d : ℝ) / 2) = s ^ 2 * (s ^ d)⁻¹ := by
  rw [show (1 - (d : ℝ) / 2) = 1 + (-(d : ℝ) / 2) by ring, Real.rpow_add (by positivity),
    Real.rpow_one, sq_rpow_neg_half hs d]

/-- The arithmetic at the end of Step 1. -/
lemma far_hit_arith {d : ℕ} (hd : 3 ≤ d) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    (2 * Real.pi) ^ (-(d : ℝ) / 2) * Cwin d * r ^ d *
      ((s ^ 2) ^ (-(d : ℝ) / 2) + 2 / (((d : ℝ) - 2) * r ^ 2) * (s ^ 2) ^ (1 - (d : ℝ) / 2)) ≤
    Cfar d * (r / s) ^ (d - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  rw [sq_rpow_neg_half hs, sq_rpow_one_sub_half hs]
  set K : ℝ := (2 * Real.pi) ^ (-((m + 2 : ℕ) : ℝ) / 2) * Cwin (m + 2) with hK
  have hK0 : 0 ≤ K := by have := Cwin_nonneg (m + 2); positivity
  have hq : r / s ≤ 1 := (div_le_one hs).2 hrs
  have hq0 : 0 ≤ r / s := by positivity
  have e : (2 * Real.pi) ^ (-((m + 2 : ℕ) : ℝ) / 2) * Cwin (m + 2) * r ^ (m + 2) *
      ((s ^ (m + 2))⁻¹ + 2 / ((((m + 2 : ℕ) : ℝ) - 2) * r ^ 2) * (s ^ 2 * (s ^ (m + 2))⁻¹)) =
      K * (r / s) ^ m * ((r / s) ^ 2 + 2 / (m : ℝ)) := by
    have hc : ((m + 2 : ℕ) : ℝ) - 2 = m := by push_cast; ring
    rw [hK, hc, mul_assoc, mul_assoc, mul_assoc, far_hit_core hr hs m hm]
    ring
  rw [e, Nat.add_sub_cancel]
  have hCf : K * (1 + 2 / (m : ℝ)) ≤ Cfar (m + 2) := by
    refine le_trans (le_of_eq ?_) (le_max_right _ _)
    rw [hK]; push_cast; ring_nf
  calc K * (r / s) ^ m * ((r / s) ^ 2 + 2 / (m : ℝ))
      ≤ K * (r / s) ^ m * (1 + 2 / (m : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : (r / s) ^ 2 ≤ 1 := pow_le_one₀ hq0 hq
        linarith
    _ = (K * (1 + 2 / (m : ℝ))) * (r / s) ^ m := by ring
    _ ≤ Cfar (m + 2) * (r / s) ^ m :=
        mul_le_mul_of_nonneg_right hCf (by positivity)

/-- ES22 Lemma 9.2: hitting a cube after time s^2, Step 1: for `σ = 1`, the probability of hitting the cube of
radius `r` around `-y` after time `s²` is at most `C_far (r/s)^{d-2}`. -/
theorem far_hit_exists_le [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) (hd : 3 ≤ d) (y : Fin d → ℝ) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) :
    P {ω | ∃ t : ℝ≥0, s ^ 2 ≤ (t : ℝ) ∧ ‖y + B t ω‖ ≤ r} ≤
      ENNReal.ofReal (Cfar d * (r / s) ^ (d - 2)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases hrs : s < r
  · refine le_trans prob_le_one ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 ≤ r / s := by rw [le_div_iff₀ hs]; linarith
    calc (1 : ℝ) ≤ Cfar d * 1 := by rw [mul_one]; exact one_le_Cfar d
      _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_pow₀ h1) (Cfar_pos d).le
  · have hrs := not_lt.1 hrs
    set h : ℝ≥0 := (r ^ 2).toNNReal with hhdef
    have hhR : (h : ℝ) = r ^ 2 := Real.coe_toNNReal _ (sq_nonneg r)
    have hh0 : h ≠ 0 := by
      intro h0; rw [h0] at hhR; have := pow_pos hr 2; simp at hhR; linarith
    let a : ℕ → ℝ≥0 := fun k => (s ^ 2 + k * r ^ 2).toNNReal
    have haR : ∀ k, (a k : ℝ) = s ^ 2 + k * r ^ 2 := fun k =>
      Real.coe_toNNReal _ (by positivity)
    have hsub : {ω | ∃ t : ℝ≥0, s ^ 2 ≤ (t : ℝ) ∧ ‖y + B t ω‖ ≤ r} ⊆
        ⋃ k : ℕ, {ω | ∃ u, a k ≤ u ∧ u ≤ a k + h ∧ ‖y + B u ω‖ ≤ r} := by
      rintro ω ⟨t, hst, ht⟩
      set k := ⌊((t : ℝ) - s ^ 2) / r ^ 2⌋₊ with hk
      have hr2 : 0 < r ^ 2 := by positivity
      have h1 : (k : ℝ) ≤ ((t : ℝ) - s ^ 2) / r ^ 2 := Nat.floor_le (div_nonneg (by linarith) hr2.le)
      have h2 : ((t : ℝ) - s ^ 2) / r ^ 2 < k + 1 := Nat.lt_floor_add_one _
      rw [le_div_iff₀ hr2] at h1
      rw [div_lt_iff₀ hr2] at h2
      refine Set.mem_iUnion.2 ⟨k, t, ?_, ?_, ht⟩
      · rw [← NNReal.coe_le_coe, haR]; linarith
      · rw [← NNReal.coe_le_coe, NNReal.coe_add, haR, hhR]; linarith
    have hterm : ∀ k : ℕ, P {ω | ∃ u, a k ≤ u ∧ u ≤ a k + h ∧ ‖y + B u ω‖ ≤ r} ≤
        ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Cwin d * r ^ d *
          (s ^ 2 + k * r ^ 2) ^ (-(d : ℝ) / 2)) := by
      intro k
      refine (window_shift_le hB (a k) hh0 y r).trans ?_
      have ha0 : a k ≠ 0 := by
        intro h0
        have := haR k
        rw [h0] at this
        simp at this
        have : 0 < s ^ 2 + k * r ^ 2 := by positivity
        linarith
      have := lintegral_winG_brownian_le hB ha0 y hr
      rw [hhR]
      refine this.trans (le_of_eq ?_)
      congr 1
      rw [haR k, Real.mul_rpow (by positivity) (by positivity)]
      ring
    calc _ ≤ P (⋃ k : ℕ, {ω | ∃ u, a k ≤ u ∧ u ≤ a k + h ∧ ‖y + B u ω‖ ≤ r}) := measure_mono hsub
      _ ≤ ∑' k : ℕ, P {ω | ∃ u, a k ≤ u ∧ u ≤ a k + h ∧ ‖y + B u ω‖ ≤ r} := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Cwin d * r ^ d *
          (s ^ 2 + k * r ^ 2) ^ (-(d : ℝ) / 2)) := ENNReal.tsum_le_tsum hterm
      _ ≤ ENNReal.ofReal (Cfar d * (r / s) ^ (d - 2)) := by
        refine tsum_ofReal_le_of_partial (fun k => by have := Cwin_nonneg d; positivity) fun n => ?_
        rw [← Finset.mul_sum]
        have hsum := sum_add_mul_rpow_le hd (a := s ^ 2) (h := r ^ 2) (by positivity)
          (by positivity) n
        have hc0 : 0 ≤ (2 * Real.pi) ^ (-(d : ℝ) / 2) * Cwin d * r ^ d := by
          have := Cwin_nonneg d; positivity
        exact (mul_le_mul_of_nonneg_left hsum hc0).trans (far_hit_arith hd hr hs hrs)

lemma norm_add_smul_eq {σ : ℝ} (hσ : 0 < σ) (y x : Fin d → ℝ) :
    ‖y + σ • x‖ = σ * ‖σ⁻¹ • y + x‖ := by
  have : y + σ • x = σ • (σ⁻¹ • y + x) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hσ]

/-- ES22 Lemma 9.2: hitting a cube after time s^2 (ES22 Lemma 9.2, deviation F20, F29). For `d ≥ 3`, every
standard Brownian motion, every `y` and all `r, s, σ > 0`:
`P(inf_{t ≥ s²} ‖y + σ B(t)‖ ≤ r) ≤ C_far (r/(σ s))^{d-2}`. -/
theorem far_hit_le [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) (hd : 3 ≤ d) (y : Fin d → ℝ) {r s σ : ℝ} (hr : 0 < r)
    (hs : 0 < s) (hσ : 0 < σ) :
    P {ω | ⨅ (t : ℝ≥0) (_ : s ^ 2 ≤ (t : ℝ)), ((‖y + σ • B t ω‖ : ℝ) : EReal) ≤ (r : EReal)} ≤
      ENNReal.ofReal (Cfar d * (r / (σ * s)) ^ (d - 2)) := by
  set g : ℝ → ℝ≥0∞ := fun ε => ENNReal.ofReal (Cfar d * ((r + ε) / (σ * s)) ^ (d - 2)) with hg
  have hε : ∀ ε : ℝ, 0 < ε → P {ω | ⨅ (t : ℝ≥0) (_ : s ^ 2 ≤ (t : ℝ)),
      ((‖y + σ • B t ω‖ : ℝ) : EReal) ≤ (r : EReal)} ≤ g ε := by
    intro ε hε
    have hr' : 0 < (r + ε) / σ := by positivity
    have := far_hit_exists_le hB hd (σ⁻¹ • y) hr' hs
    refine le_trans (measure_mono ?_) (this.trans (le_of_eq ?_))
    · intro ω hω
      have hlt : ⨅ (t : ℝ≥0) (_ : s ^ 2 ≤ (t : ℝ)), ((‖y + σ • B t ω‖ : ℝ) : EReal) <
          ((r + ε : ℝ) : EReal) :=
        lt_of_le_of_lt hω (EReal.coe_lt_coe_iff.2 (by linarith))
      simp only [iInf_lt_iff] at hlt
      obtain ⟨t, ht, hlt⟩ := hlt
      refine ⟨t, ht, ?_⟩
      have := EReal.coe_lt_coe_iff.1 hlt
      rw [norm_add_smul_eq hσ] at this
      rw [le_div_iff₀ hσ]
      linarith
    · rw [hg]
      simp only
      congr 2
      rw [div_div]
  have hcont : Continuous fun ε : ℝ => g ε := by
    rw [hg]
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have h0 : g 0 = ENNReal.ofReal (Cfar d * (r / (σ * s)) ^ (d - 2)) := by simp [hg]
  rw [h0] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε' using hε ε hε'
  
end ElboimSly.Brownian
