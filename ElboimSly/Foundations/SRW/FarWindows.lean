/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.WindowCount
public import Mathlib

/-!
# Crude count bound and fluctuations over short windows

Crude count bound; Lemma 2.2 for the SRW; Fluctuations over short windows.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

theorem measureReal_mono_ae' {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {s t : Set α} (h : s ≤ᵐ[μ] t) : μ.real s ≤ μ.real t :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h)

theorem exp_one_sub_one_le : Real.exp 1 - 1 ≤ 2 := by
  have := Real.exp_one_lt_d9
  norm_num at this
  linarith

/-- Crude count bound; Lemma 2.2 for the SRW: `P(∃ s ≤ t, ‖X(s)‖₁ ≥ a) ≤ exp (2d(e-1)t - a)`. -/
theorem IsSRW.far (hZ : IsSRW P Z) (t : ℝ≥0) (a : ℝ) :
    P.real {ω | ∃ s, s ≤ t ∧ a ≤ l1 (Z ω s)} ≤
      Real.exp (2 * d * (Real.exp 1 - 1) * t - a) := by
  have := hZ.isProbabilityMeasure
  obtain ⟨Ω', _, P', N', hN', hE⟩ := hZ.exists_canonical_Icc t {x | a ≤ l1 x}
  have e : P {ω | ∃ s, s ≤ t ∧ a ≤ l1 (Z ω s)} =
      P' {ω | ∃ s, s ≤ t ∧ a ≤ l1 (canonical d N' ω s)} := hE
  rw [Measure.real, e]
  have := hN'.isProbabilityMeasure
  have hsub : {ω | ∃ s, s ≤ t ∧ canonical d N' ω s ∈ {x : Fin d → ℤ | a ≤ l1 x}} ≤ᵐ[P']
      {ω | a ≤ (winCount N' 0 t ω : ℝ)} := by
    filter_upwards [l1_walk_sub_le hN'] with ω hω ⟨s, hs, h⟩
    have := hω 0 s 0 t le_rfl le_rfl s.2 (by exact_mod_cast hs)
    rw [walk_zero, sub_zero] at this
    exact le_trans h this
  have h1 := winCount_tail hN' (le_refl (0 : ℝ)) t.2 a
  rw [sub_zero] at h1
  rw [← Measure.real]
  exact (measureReal_mono_ae' hsub).trans h1

/-- Crude count bound; Lemma 2.2 for the SRW: for `L, t ≥ 1`, `P(sup_{s ≤ t} ‖X(s)‖ ≥ 10dLt) ≤ e^{-6dLt}`. -/
theorem IsSRW.far_sup (hZ : IsSRW P Z) {t L : ℝ} (ht : 1 ≤ t) (hL : 1 ≤ L) (hd : 1 ≤ d) :
    P.real {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ t ∧ 10 * d * L * t ≤ ‖Z ω s‖} ≤ Real.exp (-(6 * d * L * t)) ∧
      Real.exp (-(6 * d * L * t)) ≤ Real.exp (-(L * t)) := by
  have := hZ.isProbabilityMeasure
  have ht0 : 0 ≤ t := by linarith
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmain := hZ.far t.toNNReal (10 * d * L * t)
  refine ⟨le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hmain.trans ?_), ?_⟩
  · rintro ω ⟨s, hs, h⟩
    refine ⟨s, ?_, h.trans (norm_le_l1 _)⟩
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0]; exact hs
  · apply Real.exp_le_exp.2
    rw [Real.coe_toNNReal _ ht0]
    have h2 := exp_one_sub_one_le
    have hdLt : 0 ≤ (d : ℝ) * t := by positivity
    nlinarith [mul_nonneg hdLt (sub_nonneg.2 hL)]
  · apply Real.exp_le_exp.2
    have : 0 ≤ L * t := by positivity
    nlinarith [mul_nonneg this (sub_nonneg.2 hd')]

/-- Crude count bound; Lemma 2.2 for the SRW: for `P ~ Poi(t)`, `L, t ≥ 1`: `P(P ≥ 10Lt) ≤ e^{-8Lt}`. -/
theorem poisson_far {μ : Measure Ω} {Q : Ω → ℕ} {r : ℝ≥0}
    (hQ : HasLaw Q (poissonMeasure r) μ) [IsProbabilityMeasure μ] {L : ℝ} (hL : 1 ≤ L)
    (hr : 1 ≤ (r : ℝ)) :
    μ.real {ω | 10 * L * r ≤ (Q ω : ℝ)} ≤ Real.exp (-(8 * L * r)) := by
  refine (poisson_chernoff_one hQ _).trans (Real.exp_le_exp.2 ?_)
  have h2 := exp_one_sub_one_le
  have h0 : (0 : ℝ) ≤ r := by linarith
  nlinarith [mul_nonneg h0 (sub_nonneg.2 hL)]

/-- Fluctuations over short windows. -/
theorem IsSRW.unit_windows (hZ : IsSRW P Z) (T h : ℝ≥0) (hh : 0 < h) (a : ℝ) :
    P.real {ω | ∃ s s', s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ h ∧ a ≤ l1 (Z ω s' - Z ω s)} ≤
      ((T : ℝ) / h + 1) * Real.exp (4 * d * h * (Real.exp 1 - 1) - a) := by
  have := hZ.isProbabilityMeasure
  obtain ⟨Ω', _, P', N', hN', hE⟩ := hZ.exists_canonical_pair T h (fun x y => a ≤ l1 (y - x))
  have e : P {ω | ∃ s s', s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ h ∧ a ≤ l1 (Z ω s' - Z ω s)} =
      P' {ω | ∃ s s', s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ h ∧
        a ≤ l1 (canonical d N' ω s' - canonical d N' ω s)} := hE
  rw [Measure.real, e]
  have := hN'.isProbabilityMeasure
  have hh' : (0 : ℝ) < h := hh
  set K : ℕ := ⌊(T : ℝ) / h⌋₊ with hK
  let A : ℕ → Set Ω' := fun k => {ω | a ≤ (winCount N' (k * h) ((k + 2) * h) ω : ℝ)}
  have hsub : {ω | ∃ s s', s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ h ∧
        a ≤ l1 (canonical d N' ω s' - canonical d N' ω s)} ≤ᵐ[P']
      ⋃ k ∈ Finset.range (K + 1), A k := by
    filter_upwards [l1_walk_sub_le hN'] with ω hω ⟨s, s', hss', hs'T, hsh, hl⟩
    simp only [mem_iUnion]
    have hs0 : (0 : ℝ) ≤ s := s.2
    have hss'r : (s : ℝ) ≤ s' := by exact_mod_cast hss'
    have hshr : (s' : ℝ) - s ≤ h := by
      have := hsh
      rw [← NNReal.coe_le_coe, NNReal.coe_sub hss'] at this
      exact this
    set k : ℕ := ⌊(s : ℝ) / h⌋₊ with hk
    have hk1 : (k : ℝ) * h ≤ s := by
      have := Nat.floor_le (show 0 ≤ (s : ℝ) / h by positivity)
      rw [← hk, le_div_iff₀ hh'] at this; exact this
    have hk2 : (s : ℝ) < (k + 1) * h := by
      have := Nat.lt_floor_add_one ((s : ℝ) / h)
      rw [← hk, div_lt_iff₀ hh'] at this; exact this
    have hkK : k ≤ K := by
      apply Nat.floor_le_floor
      exact div_le_div_of_nonneg_right (by exact_mod_cast hss'.trans hs'T) hh'.le
    refine ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hkK), ?_⟩
    have h0 : (0 : ℝ) ≤ k * h := by positivity
    have := hω s s' (k * h) ((k + 2) * h) h0 hk1 hss'r (by nlinarith)
    exact le_trans hl this
  have hcard : ((Finset.range (K + 1)).card : ℝ) ≤ (T : ℝ) / h + 1 := by
    rw [Finset.card_range]
    push_cast
    have := Nat.floor_le (show 0 ≤ (T : ℝ) / h by positivity)
    linarith
  have hA : ∀ k : ℕ, P'.real (A k) ≤ Real.exp (4 * d * h * (Real.exp 1 - 1) - a) := by
    intro k
    have h0 : (0 : ℝ) ≤ k * h := by positivity
    have := winCount_tail hN' h0 (show (k : ℝ) * h ≤ (k + 2) * h by nlinarith) a
    refine this.trans (le_of_eq ?_)
    congr 1
    ring
  rw [← Measure.real]
  calc P'.real _ ≤ P'.real (⋃ k ∈ Finset.range (K + 1), A k) :=
        measureReal_mono_ae' hsub
    _ ≤ ∑ k ∈ Finset.range (K + 1), P'.real (A k) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (K + 1), Real.exp (4 * d * h * (Real.exp 1 - 1) - a) :=
        Finset.sum_le_sum fun k _ => hA k
    _ = (Finset.range (K + 1)).card * Real.exp (4 * d * h * (Real.exp 1 - 1) - a) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((T : ℝ) / h + 1) * Real.exp (4 * d * h * (Real.exp 1 - 1) - a) := by
        gcongr

end SRW
end ElboimSly
