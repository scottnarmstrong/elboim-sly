/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.H1Cover
public import ElboimSly.Foundations.Brownian.SelfIntersection
public import ElboimSly.Foundations.Brownian.Invariance
public import Mathlib

/-!
# (H1) at the base: the lag condition (R2)

ES22 Lemma 8.1, Step 3.

With `b = β^δ`, `c = 2 b²` and `L = b/2` (so `β^{3δ} = b³ = c L`), the times at which (R2) fails
are contained in `c · T_L(B*)`, where `B*(u) = c^{-1/2} B(c u)` is again a standard Brownian
motion (`h1Scaled`).

* `h1Scaled_isBM`: `B*` is a standard Brownian motion.
* `bad_mem_sep`: a failure of (R2) at `t` puts `t/c` in the separation set of `B*`.
* `h1_bad_volume`: the failure set has measure at most `c · |T_L(B*)|`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Brownian

variable {d : ℕ}

/-- The rescaled Brownian motion `B*(u) = c^{-1/2} B(c u)`, `c = 2 b²`. -/
noncomputable def h1Scaled {Ω : Type*} (b : ℝ) (B : ℝ≥0 → Ω → Fin d → ℝ) :
    ℝ≥0 → Ω → Fin d → ℝ :=
  fun u ω => (1 / (Real.sqrt 2 * b)) • B ((2 * b ^ 2).toNNReal * u) ω

theorem h1Scaled_isBM {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStandardBrownianMotion d B P) {b : ℝ} (hb : 0 < b) :
    IsStandardBrownianMotion d (h1Scaled b B) P := by
  have hc : (2 * b ^ 2).toNNReal ≠ 0 := by
    intro h
    have := Real.toNNReal_eq_zero.1 h
    nlinarith [sq_pos_of_pos hb]
  refine hB.scaling (a := 1 / (Real.sqrt 2 * b)) hc ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  rw [h2]

theorem volume_image_coe_le (S : Set ℝ≥0) :
    volume (((↑) : ℝ≥0 → ℝ) '' S) ≤ Brownian.nnLebesgue S := by
  rw [measure_eq_iInf S]
  refine le_iInf₂ fun t hSt => le_iInf fun ht => ?_
  calc volume (((↑) : ℝ≥0 → ℝ) '' S) ≤ volume (((↑) : ℝ≥0 → ℝ) '' t) :=
        measure_mono (image_mono hSt)
    _ = Brownian.nnLebesgue t := by
        unfold Brownian.nnLebesgue
        rw [Measure.comap_apply _ NNReal.coe_injective (fun s hs =>
          hs.image_of_continuousOn_injOn NNReal.continuous_coe.continuousOn
            NNReal.coe_injective.injOn) _ ht]

/-- A failure of (R2) at `t` puts `t/c` into the separation set of the rescaled motion. -/
theorem bad_mem_sep {Ω : Type*} (B : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) (γ : SRW.PathSpace d)
    (T : ℝ≥0) {n : ℕ} {b : ℝ} (hb : 0 < b) (hn : 2 * (n : ℝ) ^ 10 ≤ b)
    (hcpl : ∀ s : ℝ≥0, s ≤ T → ‖latR (γ s) - Real.sqrt 2 • B s ω‖ < (n : ℝ) ^ 10)
    {t s : ℝ} (ht : t ≤ T) (hs0 : 0 ≤ s) (hst : s ≤ t - b ^ 3)
    (hfail : ‖γ t.toNNReal - γ s.toNNReal‖ < b) :
    (t / (2 * b ^ 2)).toNNReal ∈ sepSet (h1Scaled b B) 1 (b / 2).toNNReal
      (T / (2 * b ^ 2)).toNNReal ω := by
  have hb2 : 0 < 2 * b ^ 2 := by positivity
  have ht0 : 0 ≤ t := by nlinarith [pow_pos hb 3]
  have hcoe : ∀ r : ℝ, 0 ≤ r → (2 * b ^ 2).toNNReal * (r / (2 * b ^ 2)).toNNReal = r.toNNReal := by
    intro r hr
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hb2.le, Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ hr]
    field_simp
  have htT : t.toNNReal ≤ T := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0]; exact ht
  have hsT : s.toNNReal ≤ T := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]
    linarith [pow_pos hb 3]
  refine ⟨?_, (s / (2 * b ^ 2)).toNNReal, ?_, ?_⟩
  · exact Real.toNNReal_le_toNNReal (div_le_div_of_nonneg_right ht hb2.le)
  · rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
    rw [div_add' _ _ _ hb2.ne', div_le_div_iff_of_pos_right hb2]
    nlinarith
  · have e1 := hcoe t ht0
    have e2 := hcoe s hs0
    simp only [one_smul, h1Scaled]
    rw [e1, e2, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have c1 := hcpl t.toNNReal htT
    have c2 := hcpl s.toNNReal hsT
    have hsq : (0 : ℝ) < Real.sqrt 2 := by positivity
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have k1 := norm_sub_le_norm_sub_add_norm_sub (Real.sqrt 2 • B t.toNNReal ω)
      (latR (γ t.toNNReal)) (Real.sqrt 2 • B s.toNNReal ω)
    have k2 := norm_sub_le_norm_sub_add_norm_sub (latR (γ t.toNNReal))
      (latR (γ s.toNNReal)) (Real.sqrt 2 • B s.toNNReal ω)
    have k3 : ‖Real.sqrt 2 • B t.toNNReal ω - latR (γ t.toNNReal)‖ =
        ‖latR (γ t.toNNReal) - Real.sqrt 2 • B t.toNNReal ω‖ := norm_sub_rev _ _
    have k4 : ‖latR (γ t.toNNReal) - latR (γ s.toNNReal)‖ =
        ‖γ t.toNNReal - γ s.toNNReal‖ := norm_latR_sub _ _
    have key : ‖Real.sqrt 2 • B t.toNNReal ω - Real.sqrt 2 • B s.toNNReal ω‖ < 2 * b := by
      linarith
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hsq] at key
    have hq : ‖B t.toNNReal ω - B s.toNNReal ω‖ ≤ Real.sqrt 2 * b := by
      by_contra hcon
      push Not at hcon
      nlinarith
    calc 1 / (Real.sqrt 2 * b) * ‖B t.toNNReal ω - B s.toNNReal ω‖
        ≤ 1 / (Real.sqrt 2 * b) * (Real.sqrt 2 * b) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = 1 := by field_simp

/-- The failure set of (R2) has measure at most `c |T_L(B*)|`. -/
theorem h1_bad_volume {Ω : Type*} (B : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) (γ : SRW.PathSpace d)
    (T : ℝ≥0) {n : ℕ} {b : ℝ} (hb : 0 < b) (hn : 2 * (n : ℝ) ^ 10 ≤ b)
    (hcpl : ∀ s : ℝ≥0, s ≤ T → ‖latR (γ s) - Real.sqrt 2 • B s ω‖ < (n : ℝ) ^ 10)
    {Bad : Set ℝ}
    (hBad : ∀ t ∈ Bad, 0 ≤ t ∧ t ≤ T ∧ ∃ s, 0 ≤ s ∧ s ≤ t - b ^ 3 ∧
      ‖γ t.toNNReal - γ s.toNNReal‖ < b) :
    volume Bad ≤ ENNReal.ofReal (2 * b ^ 2) *
      Brownian.nnLebesgue (sepSet (h1Scaled b B) 1 (b / 2).toNNReal
        (T / (2 * b ^ 2)).toNNReal ω) := by
  have hb2 : 0 < 2 * b ^ 2 := by positivity
  set S := sepSet (h1Scaled b B) 1 (b / 2).toNNReal (T / (2 * b ^ 2)).toNNReal ω with hS
  have hsub : Bad ⊆ (fun x : ℝ => (2 * b ^ 2)⁻¹ * x) ⁻¹' (((↑) : ℝ≥0 → ℝ) '' S) := by
    intro t ht
    obtain ⟨ht0, htT, s, hs0, hst, hf⟩ := hBad t ht
    refine ⟨(t / (2 * b ^ 2)).toNNReal, bad_mem_sep B ω γ T hb hn hcpl htT hs0 hst hf, ?_⟩
    rw [Real.coe_toNNReal _ (by positivity)]
    simp [div_eq_inv_mul]
  calc volume Bad ≤ volume ((fun x : ℝ => (2 * b ^ 2)⁻¹ * x) ⁻¹' (((↑) : ℝ≥0 → ℝ) '' S)) :=
        measure_mono hsub
    _ = ENNReal.ofReal |((2 * b ^ 2)⁻¹)⁻¹| * volume (((↑) : ℝ≥0 → ℝ) '' S) :=
        Real.volume_preimage_mul_left (by positivity) _
    _ ≤ _ := by
        rw [inv_inv, abs_of_pos hb2]
        exact mul_le_mul_right (volume_image_coe_le S) _

end ElboimSly.Paper

end
